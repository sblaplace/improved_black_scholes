"""
Black-Scholes baseline formulas, used ONLY as a numerical handrail for the
formal theory (Lean 4). Kept deliberately dependency-free (stdlib math only)
so it audits trivially: it is a *sanity oracle*, not the artifact.

For notation and the formal statements, see docs/01_baseline.md and
ImprovedBS/Core.lean.

All times in years, all rates/vols annualized decimals (not percent).

DERIVATION INDEPENDENCE (this is the point of the file)
-------------------------------------------------------
Every identity this oracle is used to check must be checked between two
*independently derived* expressions. A check that compares a quantity
against itself cannot fail, and a test that cannot fail is not evidence.
So:

  * `d2` is computed from its OWN explicit formula
        d2 = (ln(S/K) + (r - q - s^2/2) tau) / (s sqrt tau)
    and NOT as `d1 - s*sqrt(tau)`. The identity d1 - d2 = s*sqrt(tau)
    (theorem T1) is then a real numerical claim.

  * the put is computed from its OWN closed form
        P = K e^{-r tau} Phi(-d2) - S e^{-q tau} Phi(-d1)
    and NOT as `C - S e^{-q tau} + K e^{-r tau}`. Put-call parity
    (theorem T2) is then a real numerical claim, and it is a claim about
    Phi's odd symmetry Phi(x) + Phi(-x) = 1 -- which is exactly what the
    Lean proof of T2 must cite (`Real.erf_neg`).

  Both routes are exposed (`bs_put` and `bs_put_by_parity`) so the two can
  be compared against each other directly; they agree to ~1e-15, which is
  the numerical content of T2.

ARGUMENT ORDER
--------------
Internal helpers use `(S, K, tau, r, q, s)` -- the same order, and the same
meaning, as the Lean declarations in ImprovedBS/Core.lean:

    d1 (S K tau r q sigma : ℝ) : ℝ

`bs_price` / `bs_pde_residual` keep their ORIGINAL public signature
`(S, K, T, t, r, s, q=0.0, option=...)`, in which `s` precedes `q`. That
public order is a frozen contract (tests and the briefs depend on it); the
translation across the boundary is pinned by
`tests/test_bs.py::test_public_api_argument_order` so it cannot drift
silently.
"""

from __future__ import annotations

import cmath
import math

# ---------------------------------------------------------------- normal


def norm_cdf(x: float) -> float:
    """Phi(x) = 1/2 (1 + erf(x/sqrt 2))."""
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def norm_pdf(x: float) -> float:
    """phi(x) = exp(-x^2/2)/sqrt(2 pi)."""
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


# ---------------------------------------------------------------- core
# Closed form for a European option under geometric Brownian motion.
#
#   tau = T - t > 0                      (years to expiry)
#   d1  = ( ln(S/K) + (r - q + s^2/2) tau ) / (s sqrt tau)
#   d2  = ( ln(S/K) + (r - q - s^2/2) tau ) / (s sqrt tau)     <- independent
#   C   = S e^{-q tau} Phi(d1) - K e^{-r tau} Phi(d2)
#   P   = K e^{-r tau} Phi(-d2) - S e^{-q tau} Phi(-d1)        <- independent
#
# and the THEOREMS these make checkable:
#   T1  d1 - d2 = s sqrt tau
#   T2  P = C - S e^{-q tau} + K e^{-r tau}     (needs Phi(x)+Phi(-x)=1)


def _d1d2(S: float, K: float, tau: float, r: float, q: float, s: float):
    """Return (d1, d2), each from its own explicit formula.

    Argument order matches the Lean declarations: (S K tau r q sigma).
    d2 is deliberately NOT returned as ``d1 - s*sqrt(tau)``; see the module
    docstring. That would make T1 true by construction and untestable.
    """
    sq = math.sqrt(tau)
    den = s * sq
    log_m = math.log(S / K)
    d1 = (log_m + (r - q + 0.5 * s * s) * tau) / den
    d2 = (log_m + (r - q - 0.5 * s * s) * tau) / den
    return d1, d2


def bs_call(S: float, K: float, tau: float, r: float, q: float, s: float) -> float:
    """BSM European call. Argument order matches Lean's `bsCall`."""
    d1, d2 = _d1d2(S, K, tau, r, q, s)
    return S * math.exp(-q * tau) * norm_cdf(d1) - K * math.exp(-r * tau) * norm_cdf(d2)


def bs_put(S: float, K: float, tau: float, r: float, q: float, s: float) -> float:
    """BSM European put, from its OWN closed form. Matches Lean's `bsPut`.

    This is the route `bs_price(..., option="put")` uses. Deriving the put
    this way -- rather than by parity -- is what makes put-call parity a
    falsifiable numerical claim instead of a tautology.
    """
    d1, d2 = _d1d2(S, K, tau, r, q, s)
    return K * math.exp(-r * tau) * norm_cdf(-d2) - S * math.exp(-q * tau) * norm_cdf(-d1)


def bs_put_by_parity(S: float, K: float, tau: float, r: float, q: float, s: float) -> float:
    """The put obtained from the call VIA put-call parity.

    Kept only as the other side of the T2 cross-check. Never used to produce
    a price that a parity test then consumes -- that is the circularity this
    module exists to avoid.
    """
    return bs_call(S, K, tau, r, q, s) - S * math.exp(-q * tau) + K * math.exp(-r * tau)


# ------------------------------------------------- risk-neutral expectation


def _simpson(f, a: float, b: float, n: int = 4000) -> float:
    """Composite Simpson on [a, b] (n even); stdlib only, no numpy."""
    if n % 2:
        n += 1
    h = (b - a) / n
    acc = f(a) + f(b)
    for i in range(1, n):
        acc += (4 if i % 2 else 2) * f(a + i * h)
    return acc * h / 3.0


def _risk_neutral_drift(tau: float, r: float, q: float, s: float) -> float:
    """The risk-neutral log-drift over the tenor, `(r - q - s^2/2) tau`.

    This is the ONE place the drift enters the expectation route; it is what
    makes `S e^{drift + s sqrt(tau) Z}` have mean `S e^{(r-q) tau}` (the
    martingale condition, Lean `integral_spot_mul_phi_eq_forward`). Written
    as `s * s / 2.0` rather than `0.5 * s * s` on purpose, so the mutation
    anchor for the `_d1d2` drift (tests/test_mutants.py M8b) does not also
    hit this line.
    """
    return (r - q - s * s / 2.0) * tau


def _expectation(payoff, S: float, K: float, tau: float, r: float, q: float, s: float,
                 n: int = 4000) -> float:
    """`E[payoff(S e^{m + s sqrt(tau) Z})]` for `Z ~ N(0,1)`, by Simpson against `norm_pdf`.

    The kink of the payoff sits at `z* = (ln(K/S) - m) / (s sqrt tau)` (this is
    `-d2`, computed here from scratch rather than through `_d1d2`, so the route
    does not lean on the closed form's own ingredients); the quadrature is split
    there so Simpson keeps its order. `[-12, 12]` truncates a tail below 1e-30.
    """
    m = _risk_neutral_drift(tau, r, q, s)
    sd = s * math.sqrt(tau)
    kink = (math.log(K / S) - m) / sd
    kink = min(max(kink, -12.0), 12.0)
    f = lambda z: payoff(S * math.exp(m + sd * z)) * norm_pdf(z)  # noqa: E731
    return _simpson(f, -12.0, kink, n) + _simpson(f, kink, 12.0, n)


def bs_call_by_expectation(S: float, K: float, tau: float, r: float, q: float, s: float) -> float:
    """The call as the DISCOUNTED RISK-NEUTRAL EXPECTATION `e^{-r tau} E[(S_T - K)^+]`.

    Independent of `bs_call` (no `norm_cdf`, no `_d1d2`): an integral of the
    payoff against the density, which is the right-hand side of Lean's
    `bsCall_eq_riskNeutral_expectation` (T6 sub-goal 3a). The two routes agree
    to ~1e-14 on the test grid; that agreement is the numerical content of the
    theorem, and `tests/test_mutants.py` M11 shows the comparison can fail.
    """
    return math.exp(-r * tau) * _expectation(lambda x: max(x - K, 0.0), S, K, tau, r, q, s)


def bs_put_by_expectation(S: float, K: float, tau: float, r: float, q: float, s: float) -> float:
    """The put as `e^{-r tau} E[(K - S_T)^+]`; Lean `bsPut_eq_riskNeutral_expectation`."""
    return math.exp(-r * tau) * _expectation(lambda x: max(K - x, 0.0), S, K, tau, r, q, s)


def forward_by_expectation(S: float, K: float, tau: float, r: float, q: float, s: float) -> float:
    """`E[S_T]`, which the risk-neutral drift makes equal to `S e^{(r-q) tau}`.

    (`K` is accepted only so the signature matches the other routes; the
    forward does not depend on it.)
    """
    return _expectation(lambda x: x, S, K, tau, r, q, s, n=8000)


# ------------------------------------------------- model-free skeleton


def model_free_prices(probs, spots, K, r, tau):
    """(discounted call, discounted put) of the payoffs `(s-K)+`, `(K-s)+`
    against an explicit discrete law `P(S_T = s_i) = p_i`.

    The numeric shadow of Lean's `modelFreeCall`/`modelFreePut`
    (ImprovedBS/Skeleton.lean): price by expectation against ANY law -- no
    `norm_cdf`, no `_d1d2`, no `phi`, no density at all. Parity at this layer
    is `call - put = e^{-r tau} (E[S_T] - K)` (Lean `model_free_parity_gap`),
    which becomes the forward spread exactly when the law's mean is the
    forward (`model_free_put_call_parity`), and the no-arb bounds hold at any
    law with nonnegative spots and the drift condition
    (`model_free_call_bounds`). `tests/test_mutants.py` M13/M14 show the
    identities can fail.
    """
    call = sum(p * max(s - K, 0.0) for p, s in zip(probs, spots)) * math.exp(-r * tau)
    put = sum(p * max(K - s, 0.0) for p, s in zip(probs, spots)) * math.exp(-r * tau)
    return call, put


def model_free_forward(probs, spots):
    """`E[S_T]` against an explicit discrete law.

    The right-hand side's `∫ s, X s ∂μ` of Lean's `model_free_parity_gap`.
    """
    return sum(p * s for p, s in zip(probs, spots))


def carr_madan_denom(alpha: float, u: float) -> complex:
    """The Carr–Madan strike-transform denominator `(α² + α − u²) + i(2α+1)u`."""
    return complex(alpha * alpha + alpha - u * u, (2.0 * alpha + 1.0) * u)


def bs_call_by_fourier_inversion(
    S: float, K: float, tau: float, r: float, q: float, s: float, alpha: float = 1.5, n: int = 6000
) -> float:
    """The call via CARR–MADAN FOURIER INVERSION of the pricing kernel.

    Inverts `carrMadanKernel(gbmCharFactor, alpha)` along the horizontal contour
    `v = u - i(alpha + 1)`, landing on `bs_call_by_expectation` and the closed
    form (T6 sub-goal 3b).

    Independent route: no `norm_cdf`, no `_d1d2`, no real-space integration of
    the payoff. The integral on [0, u_max] equals half the real part of the
    two-sided integral by Hermitian symmetry.
    """
    if alpha <= 0.0:
        raise ValueError("damping parameter alpha must be > 0")
    k = math.log(K / S)
    m = _risk_neutral_drift(tau, r, q, s)
    half_var = 0.5 * s * s * tau
    u_max = max(100.0, 10.0 / (s * math.sqrt(tau)))

    def integrand(u: float) -> float:
        v = complex(u, -(alpha + 1.0))
        cf = cmath.exp(1j * m * v - half_var * (v * v))
        denom = carr_madan_denom(alpha, u)
        kernel = cf / denom
        phase = cmath.exp(-1j * u * k)
        return (phase * kernel).real

    h = u_max / n
    tot = integrand(0.0) + integrand(u_max)
    for i in range(1, n):
        u = i * h
        tot += integrand(u) * (4 if i % 2 == 1 else 2)
    integral = tot * h / 3.0
    return math.exp(-r * tau) * S * math.exp(-alpha * k) / math.pi * integral


def bs_call_by_fourier_inversion_complex(
    S: float, K: float, tau: float, r: float, q: float, s: float, alpha: float = 1.5, n: int = 6000
) -> complex:
    """Full complex value of the two-sided Fourier inversion integral on [-u_max, u_max].

    Used to assert the real-valuedness theorem: the imaginary part vanishes to
    machine precision because the integrand's imaginary part is odd in `u`.
    """
    if alpha <= 0.0:
        raise ValueError("damping parameter alpha must be > 0")
    k = math.log(K / S)
    m = _risk_neutral_drift(tau, r, q, s)
    half_var = 0.5 * s * s * tau
    u_max = max(100.0, 10.0 / (s * math.sqrt(tau)))

    def integrand(u: float) -> complex:
        v = complex(u, -(alpha + 1.0))
        cf = cmath.exp(1j * m * v - half_var * (v * v))
        denom = carr_madan_denom(alpha, u)
        kernel = cf / denom
        phase = cmath.exp(-1j * u * k)
        return phase * kernel

    h = (2.0 * u_max) / n
    tot = integrand(-u_max) + integrand(u_max)
    for i in range(1, n):
        u = -u_max + i * h
        tot += integrand(u) * (4 if i % 2 == 1 else 2)
    integral = tot * h / 3.0
    return math.exp(-r * tau) * S * math.exp(-alpha * k) / (2.0 * math.pi) * integral


def bs_price(S, K, T, t, r, s, q=0.0, option="call"):
    """BSM European price. Raises ValueError on illegal (tau,s).

    PUBLIC SIGNATURE IS FROZEN: note `s` precedes `q` here, unlike the
    internal helpers and the Lean definitions. See the module docstring.
    """
    tau = T - t
    if tau <= 0.0:
        raise ValueError("tau = T - t must be > 0 (use exercise payoffs at maturity directly)")
    if s <= 0.0:
        raise ValueError("sigma must be > 0")
    if option not in ("call", "put"):
        raise ValueError("option must be 'call' or 'put'")

    disc_s, disc_k = math.exp(-q * tau), math.exp(-r * tau)

    # degenerate limits -- must be taken BEFORE d1/d2, which need ln(S/K)
    if S <= 0.0:
        return 0.0 if option == "call" else max(K * disc_k, 0.0)
    if K <= 0.0:
        return S * disc_s if option == "call" else 0.0

    if option == "call":
        return bs_call(S, K, tau, r, q, s)
    return bs_put(S, K, tau, r, q, s)  # independent closed form, NOT parity


# ---------------------------------------------------------------- PDE self-consistency
# The closed form should satisfy, for a dividend-yield-q underlying,
#
#   V_t + (r - q) S V_S + (s^2/2) S^2 V_SS = r V      (BSM diffusion equation)
#
# This finite-difference residual is an independent *numerical* falsifier of
# the formula: if it is not ~0 the closed form is misderived.  (The analytic
# identity is the Lean formal target T5; this just keeps it honest.)
#
# STEP-SIZE WINDOW (measured, do not guess):
#   central differences give an O(h^2) truncation error, but V_SS is formed
#   by differencing values of size ~10 at scale h^2, so round-off contributes
#   ~ eps*|V|/h^2 * (s^2 S^2 / 2). On the textbook case that crossover is
#   around h ~ 1e-3:
#       h=1e-1 -> 5.0e-3      h=1e-2 -> 5.0e-5   (100x, clean O(h^2))
#       h=1e-3 -> 3.6e-6      h=1e-4 -> 2.7e-5   (round-off floor; DIVERGES)
#   So h must stay in [1e-3, 1e-1]. Going smaller makes the residual WORSE,
#   and a test that assumes "smaller h is better" would pass a broken formula
#   or fail a correct one. tests/test_bs.py asserts the order in this window.


def bs_pde_residual(S, K, T, t, r, s, q=0.0, option="call", h=1e-3):
    """Central finite differences for V_t + (r-q)S V_S + (s^2/2) S^2 V_SS - r V."""
    if T - t <= 0.0 or s <= 0.0 or S - h <= 0.0:
        return float("nan")

    def V(x, tt):
        return bs_price(x, K, T, tt, r, s, q, option)

    # time derivative: central in calendar time t
    V_t = (V(S, t + h) - V(S, t - h)) / (2.0 * h)
    # first & second spot derivatives (central)
    V_S = (V(S + h, t) - V(S - h, t)) / (2.0 * h)
    V_SS = (V(S + h, t) - 2.0 * V(S, t) + V(S - h, t)) / (h * h)
    residual = V_t + (r - q) * S * V_S + 0.5 * s * s * S * S * V_SS - r * V(S, t)
    return residual
