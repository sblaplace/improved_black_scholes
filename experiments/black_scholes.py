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
from fractions import Fraction

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


# ------------------------------------------------- BRIEF_012: the non-uniqueness witness
#
# Data, not code. The two witness laws of ImprovedBS/NonUniqueness.lean at the
# brief's fixed contract S = K = tau = 1, r = q = 0 and spots (1/2, 1, 2), as
# exact dyadic rationals so that "E[S_T] = 1", "call(A) = 1/4", "call(B) = 1/8"
# and "call(A) != call(B)" are exact claims rather than float comparisons. They
# are priced by `model_free_prices`/`model_free_forward` above and by NOTHING
# else: the witness is a statement about the model-free layer, so it has to be
# expressible inside it (BRIEF_012's rule -- a new oracle function here would
# mean the witness had drifted off that layer). Both laws charge every spot
# (mutually absolutely continuous), both have the forward as mean, and only
# the up state pays the call, with weight 1/4 under A and 1/8 under B.
# `tests/test_bs.py::test_nonuniqueness_witness` asserts the whole table;
# `tests/test_mutants.py` M17 breaks B's drift (p3 : 1/8 -> 3/8), M18 corrupts
# the call payoff to the linear payoff (call(A) = call(B) = 0), M19 replaces B
# by A (every clause but the price disagreement survives).
NONUNIQ_SPOTS = (Fraction(1, 2), Fraction(1), Fraction(2))
NONUNIQ_WEIGHTS_A = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4))
NONUNIQ_WEIGHTS_B = (Fraction(1, 4), Fraction(5, 8), Fraction(1, 8))


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


def carr_madan_by_law(probs, spots, S, r, tau, alpha, k, u_max, n) -> complex:
    """Carr–Madan inversion at an ARBITRARY DISCRETE law `P(S_T = s_i) = p_i`.

    The numeric shadow of Lean's `cmPriceIntegral (contourCharFun μ)`
    (ImprovedBS/Pricing.lean, BRIEF_010): the characteristic function of
    `X = log(S_T/S)` is the sum `φ(v) = Σ p_j e^{i v log(s_j/S)}`, and the
    price is `e^{-rτ} S e^{-αk}/(2π) ∫_{-u_max}^{u_max} e^{-iuk}
    φ(u-i(α+1))/cmDenom(α,u) du` by Simpson. Conventions match
    `model_free_prices` (discrete `probs`/`spots`, no density, no `norm_cdf`).

    A discrete law's `φ` does not decay, so the error is truncation and the
    test tolerance is `1e-4`, not the GBM route's `2e-11` -- see
    `tests/test_bs.py::test_carr_madan_free_law`. An atom at `s <= 0`
    contributes `0` on the pricing contour (`e^{(α+1)X} → 0` as `X → -∞`).
    `tests/test_mutants.py` M16 (the `-(α+1)` shift off by one) is killed by
    the free-law test alone.
    """
    if alpha <= 0.0:
        raise ValueError("damping parameter alpha must be > 0")
    if n % 2:
        n += 1
    xs = [None if s <= 0.0 else math.log(s / S) for s in spots]

    def cf(v: complex) -> complex:
        tot = 0j
        for p, x in zip(probs, xs):
            if x is None:
                continue
            tot += p * cmath.exp(1j * v * x)
        return tot

    def integrand(u: float) -> complex:
        v = complex(u, -(alpha+1.0))
        kernel = cf(v) / carr_madan_denom(alpha, u)
        phase = cmath.exp(-1j * u * k)
        return phase * kernel

    h = (2.0 * u_max) / n
    tot = integrand(-u_max) + integrand(u_max)
    for i in range(1, n):
        u = -u_max + i * h
        tot += integrand(u) * (4 if i % 2 == 1 else 2)
    integral = tot * h / 3.0
    return math.exp(-r * tau) * S * math.exp(-alpha * k) / (2.0 * math.pi) * integral


# ---------------------------------------------------------------- CGMY

# The numerical shadow of ImprovedBS/CGMY.lean (BRIEF_011). The exponent is
#
#     psi(v) = C Gamma(-Y) [ (M - iv)^Y - M^Y + (G + iv)^Y - G^Y ],
#
# with `M` tempering the positive side of the Levy measure
# `nu(dx) = C e^{-Mx} x^{-1-Y} dx` (x > 0) and `G` the negative side
# (`C e^{-G|x|} |x|^{-1-Y} dx`, x < 0). Two conventions are pinned in this file
# because they are exactly the two places a silent sign/model error can hide:
#
#   * WHICH BASE OWNS WHICH TEMPERING RATE. `M` pairs with `M - iv`, `G` with
#     `G + iv` (`cgmy_exponent_one_sided` is the one-sided provenance of each
#     pairing, and `cgmy_exponent` must agree with their sum).
#   * WHICH LINE THE PRICING CONTOUR IS. `v = u - i(alpha+1)` (C12), defined in
#     ONE place, `cgmy_pricing_contour_v`, so tests/test_mutants.py M18 has a
#     single anchor. The old line `v = u + i alpha` (Fourier.lean's
#     `carrMadanKernel`) is exposed separately as `cgmy_old_contour_v`.


def cgmy_gamma_neg(Y: float) -> float:
    """`Gamma(-Y)`, the tempering weight of the CGMY exponent.

    Evaluated from Euler's reflection formula
    `Gamma(-Y) = -pi / (sin(pi Y) Gamma(1+Y))` rather than `math.gamma(-Y)`,
    so the oracle owns the sign itself. That sign is what Lean's
    `cgmy_tempered_sign` extracts: `Gamma(-Y) cos(pi Y/2) < 0` on `(0,2) \\ {1}`
    (both factors flip together at `Y = 1`), which is what makes the tempered
    rate positive. `Y = 1` is rejected -- the `Y = 1` limit form (`Gamma(-1)`
    is a pole) is a separate convention and is not in the machine-checked range.
    """
    if not (0.0 < Y < 2.0) or Y == 1.0:
        raise ValueError(
            "CGMY Y must satisfy 0 < Y < 2 with Y != 1 "
            "(the Y = 1 limit form is a separate convention)"
        )
    return -math.pi / (math.sin(math.pi * Y) * math.gamma(1.0 + Y))


def cgmy_pricing_contour_v(alpha: float, u: float) -> complex:
    """The pricing contour `v = u - i(alpha+1)` of BRIEF_010 / correction C12.

    The one place this file defines it: `cgmy_contour_re` (raw route),
    `cgmy_contour_re_split` (two-base route) and the decay test all go through
    here, so a shift-off-by-one is a single mutation anchor (M18) rather than a
    change that could be made consistently in one route and not the other.
    """
    return complex(u, -(alpha + 1.0))


def cgmy_old_contour_v(alpha: float, u: float) -> complex:
    """The line `v = u + i alpha` that `carrMadanKernel` sits on (Fourier.lean).

    Kept so the C14 correction is checkable numerically: on THIS line it is the
    base `G + iv` whose real part is `G - alpha` that can leave the right half
    plane (that line needs `alpha < G`), while on the pricing contour `G` never
    binds -- there `Re(G + iv) = G + alpha + 1 > 0` for free.
    """
    return complex(u, alpha)


def cgmy_exponent_one_sided(C: float, a: float, Y: float, v: complex) -> complex:
    """`C Gamma(-Y) [(a - iv)^Y - a^Y]`: the one-sided tempered integral

        int_0^inf (e^{ivx} - 1) e^{-a x} x^{-1-Y} dx,

    which converges (absolutely, for `0 < Y < 1`) exactly when the base stays
    in the right half plane, `Re(a - iv) > 0`. Written separately from
    `cgmy_exponent` on purpose: the two must agree, and their agreement is the
    numerical content of the `M <-> M - iv`, `G <-> G + iv` pairing.
    """
    return C * cgmy_gamma_neg(Y) * ((a - 1j * v) ** Y - a ** Y)


def cgmy_exponent(C: float, G: float, M: float, Y: float, v: complex) -> complex:
    """`psi_CGMY(v)`, the closed formula of ImprovedBS/CGMY.lean's `cgmyExponent`.

    `M` tempers the positive side and pairs with `M - iv`; `G` tempers the
    negative side and pairs with `G + iv`. Guarded like the Lean hypotheses
    (`0 < C`, `0 < G`, `0 < M`, `0 < Y < 2`, `Y != 1`).
    """
    if C <= 0.0 or G <= 0.0 or M <= 0.0:
        raise ValueError("CGMY parameters C, G, M must all be positive")
    return C * cgmy_gamma_neg(Y) * (
        (M - 1j * v) ** Y - M ** Y + (G + 1j * v) ** Y - G ** Y
    )


def cgmy_exponent_by_pieces(C: float, G: float, M: float, Y: float, v: complex) -> complex:
    """`psi` assembled from its two one-sided pieces (independent route).

    The `M` piece owns `M - iv`, the `G` piece owns `G + iv`; both come from
    `cgmy_exponent_one_sided`, i.e. from the integral identity rather than from
    the definition. `cgmy_exponent` must equal this for every `v` -- which is
    where a swapped pairing shows up as a number, not as a typo.
    """
    return cgmy_exponent_one_sided(C, M, Y, v) + cgmy_exponent_one_sided(C, G, Y, -v)


def cgmy_char_factor(C: float, G: float, M: float, Y: float, tau: float, v: complex) -> complex:
    """`exp(tau psi(v))` -- the model factor `cgmyCharFactor` of BRIEF_011.

    Affine in `tau` by construction: `cgmy_char_factor(..., tau1+tau2, v)`
    equals the product of the factors (Lean `cgmyCharFactor_add`).
    """
    return cmath.exp(tau * cgmy_exponent(C, G, M, Y, v))


def cgmy_contour_re(C: float, G: float, M: float, Y: float, alpha: float, u: float) -> float:
    """`Re psi(u - i(alpha+1))` -- the RAW route (through the closed formula)."""
    return cgmy_exponent(C, G, M, Y, cgmy_pricing_contour_v(alpha, u)).real


def cgmy_contour_re_split(C: float, G: float, M: float, Y: float, alpha: float, u: float) -> float:
    """`Re psi(u - i(alpha+1))` in the two-base form the Lean assembly uses.

    On the pricing contour the two bases are `M - iv = (M-(alpha+1)) - i u` and
    `G + iv = (G+alpha+1) + i u` (Lean `cgmyContour_base_left/right`), and the
    real part of a real power does not see the sign of the imaginary part
    (`re_cpow_conj_ofReal_add_mul_I`), so with `y = |u|`

        Re psi = C Gamma(-Y) [ Re((a1 + i y)^Y) + Re((a2 + i y)^Y) - M^Y - G^Y ],

    `a1 = M - (alpha+1)`, `a2 = G + (alpha+1)`. This route never forms `M - iv`,
    so agreement with `cgmy_contour_re` is a real numerical claim.
    """
    y = abs(u)
    a1 = M - (alpha + 1.0)
    a2 = G + (alpha + 1.0)
    return C * cgmy_gamma_neg(Y) * (
        ((a1 + 1j * y) ** Y).real + ((a2 + 1j * y) ** Y).real - M ** Y - G ** Y
    )


def cgmy_base_reals(G: float, M: float, alpha: float, u: float, line: str = "pricing"):
    """`(Re(M - iv), Re(G + iv))` by complex arithmetic on the named line.

    Used against the closed forms `(M-(alpha+1), G+alpha+1)` (pricing, C12) and
    `(M+alpha, G-alpha)` (old line) so the C14 correction is a number, not a
    reading of the prose. Note which base binds where: on the pricing contour it
    is `M - iv` (condition `alpha+1 < M`, `G` free), on the old line it is
    `G + iv` (condition `alpha < G`, `M` free) -- so the prose's
    `alpha+1 < min(G,M)` is sufficient for both and necessary for neither.
    """
    v = cgmy_pricing_contour_v(alpha, u) if line == "pricing" else cgmy_old_contour_v(alpha, u)
    return ((M - 1j * v).real, (G + 1j * v).real)


def cgmy_tempered_rate(C: float, Y: float) -> float:
    """`r = 2 C |Gamma(-Y) cos(pi Y/2)|` -- the asymptotic decay rate.

    `-Re psi(u - i(alpha+1)) / |u|^Y -> r` as `|u| -> inf` (two bases, each
    contributing `|u|^Y cos(pi Y/2)`, times `C Gamma(-Y)`), and `r > 0` on
    `(0,2) \\ {1}` by `cgmy_tempered_sign`.
    """
    return 2.0 * C * abs(cgmy_gamma_neg(Y) * math.cos(math.pi * Y / 2.0))


def cgmy_tempered_correction(C: float, G: float, M: float, Y: float) -> float:
    """`2^{Y-1} Y (M + G) |C Gamma(-Y)|` -- the `O(|u|^{Y-1})` coefficient.

    The `M + G` is `(M - (alpha+1)) + (G + (alpha+1))`: the two bases' real
    parts sum, which is why the correction carries no `alpha`. The `2^{Y-1}`
    (not `2^Y`) is what the mean-value estimate proves: the derivative of
    `t -> (t + iy)^Y` is bounded by `Y (2y)^{Y-1}` on `[0, a]` for `a <= y`,
    and `(2y)^{Y-1} = 2^{Y-1} y^{Y-1}`.
    """
    return 2.0 ** (Y - 1.0) * Y * (M + G) * abs(C * cgmy_gamma_neg(Y))


def cgmy_tempered_constant(C: float, G: float, M: float, Y: float) -> float:
    """`|C Gamma(-Y)| (M^Y + G^Y)` -- the two subtracted real powers."""
    return abs(C * cgmy_gamma_neg(Y)) * (M ** Y + G ** Y)


def cgmy_decay_threshold(C: float, G: float, M: float, Y: float) -> float:
    """The explicit tail threshold of Lean's `cgmyDecayThreshold`.

    Past it the correction and constant terms each cost at most a quarter of the
    leading term, leaving `r/2` as the exponent in

        ||exp(tau psi(u - i(alpha+1)))|| <= exp(-(tau/2) r |u|^Y).

    The bound is deliberately loose by a factor 2 against the true asymptotics
    (`-Re psi/|u|^Y -> r`, not `r/2`): the factor is the price of absorbing the
    lower-order terms with an explicit threshold. The sharpness test asserts the
    true rate, so a weakened `r` is caught even though a weaker bound is still
    true.
    """
    r = cgmy_tempered_rate(C, Y)
    return max(
        M + G,
        max(
            4.0 * cgmy_tempered_correction(C, G, M, Y) / r,
            max(1.0, (4.0 * cgmy_tempered_constant(C, G, M, Y) / r) ** (1.0 / Y)),
        ),
    )


# --------------------------------------------------------------- Esscher drift

# The numerical shadow of ImprovedBS/Esscher.lean (BRIEF_013). The Esscher
# tilt of an exponent is the shift
#
#     psi^theta(v) = psi(v - i theta) - psi(-i theta),
#
# and for CGMY the shift is INTERNAL: it just moves the tempering rates
# (G, M) -> (G + theta, M - theta) (Lean `esscher_cgmy_shift`). The drift the
# tilt delivers is g(theta) = kappa(theta+1) - kappa(theta), where kappa is
# the real cumulant psi(-iu) on the strip, and the martingale condition is
# g(theta) = r - q with theta admissible in (-G, M-1) -- nonempty exactly
# when 1 < G + M. Two conventions are pinned because they are the two places
# a silent sign/shape error can hide:
#
#   * WHICH SIGN THE SHIFT HAS. `esscher_exponent` applies the exponent at
#     `v - i theta` and subtracts the value at `-i theta` -- a wrong-sign
#     shift is mutant M20's target, and the closure assertion in
#     tests/test_bs.py::test_esscher_drift is its falsifier (resid O(1)).
#   * WHICH CLOSED FORM THE RANGE HALF-WIDTH CARRIES. `esscher_drift_bound`
#     is `|C Gamma(-Y)| * |s^Y - (s-1)^Y - 1|` at `s = G + M`, the Lean
#     `esscherDriftBound` -- the INNER absolute value is load-bearing (the
#     bracket has the sign of `Y - 1`), and dropping it is mutant M21.


def esscher_exponent(C: float, G: float, M: float, Y: float, theta: float,
                     v: complex) -> complex:
    """`psi^theta(v) = psi(v - i theta) - psi(-i theta)` -- the shift itself,
    evaluated through the COMPLEX route `cgmy_exponent`.

    The Lean `esscher_cgmy_shift` says this equals
    `cgmy_exponent(C, G + theta, M - theta, Y, v)` for every `v` -- term
    algebra on the two bases, no branch hypothesis. The test asserts that
    closure on a grid; a wrong-sign shift (M20) breaks it by O(1).
    """
    return cgmy_exponent(C, G, M, Y, v - 1j * theta) - cgmy_exponent(C, G, M, Y, -1j * theta)


def cgmy_cumulant(C: float, G: float, M: float, Y: float, u: float) -> float:
    """`kappa(u) = psi(-iu)` on the real section of the strip, the Lean
    `cgmyCumulant`: `C Gamma(-Y) [(M-u)^Y - M^Y + (G+u)^Y - G^Y]`.

    Real-valued exactly because on `u in (-G, M)` both bases are positive
    reals (Lean `cgmyExponent_strip`); no complex power is formed here.
    """
    return C * cgmy_gamma_neg(Y) * (
        (M - u) ** Y - M ** Y + (G + u) ** Y - G ** Y
    )


def esscher_drift_map(C: float, G: float, M: float, Y: float, theta: float) -> float:
    """`g(theta) = kappa(theta+1) - kappa(theta)` -- the drift the tilt at
    `theta` delivers (Lean `esscherDriftMap`). The martingale condition is
    `g(theta) = r - q`; antisymmetric about `(M-G-1)/2` (Lean
    `esscherDriftMap_reflect`), strictly increasing on `[-G, M-1]`.
    """
    return cgmy_cumulant(C, G, M, Y, theta + 1.0) - cgmy_cumulant(C, G, M, Y, theta)


def esscher_theta_zero(G: float, M: float) -> float:
    """`(M - G - 1) / 2` -- the zero-drift Esscher parameter (Lean
    `esscherThetaZero`), independent of `Y`: the fixed point of the
    reflection `theta |-> M - G - 1 - theta`.
    """
    return (M - G - 1.0) / 2.0


def esscher_drift_bound(C: float, G: float, M: float, Y: float) -> float:
    """`H = |C Gamma(-Y)| |s^Y - (s-1)^Y - 1|` at `s = G + M` -- the
    half-width of the attainable drift interval `(−H, H)` (Lean
    `esscherDriftBound`). A function of `(C, Y, G+M)` alone: the edge values
    `g(-G) = -H`, `g(M-1) = H` (Lean `esscherDriftMap_bound_eq`).

    The inner absolute value is part of the specification: the bracket
    `s^Y - (s-1)^Y - 1` has the sign of `Y - 1`, so dropping the abs makes
    `H` negative for every `Y < 1` set -- mutant M21, killed by the range
    assertions in test_esscher_drift.
    """
    s = G + M
    return abs(C * cgmy_gamma_neg(Y)) * abs(s ** Y - (s - 1.0) ** Y - 1.0)


def esscher_solve(C: float, G: float, M: float, Y: float, target: float,
                  iters: int = 200):
    """Bisection on `g(theta) = target` over the admissible interval
    `[-G, M-1]` -- the numerical `esscher_exists_unique_of_mem_range`.

    Returns `None` when the interval is EMPTY (`G + M <= 1`) or when there is
    no sign change (the target lies at or beyond the edge values, the
    `esscher_no_solution_of_outside_range` regime). Otherwise returns the
    midpoint after `iters` halvings; `g` is strictly monotone on the
    interval, so the bisection root is the unique Esscher parameter.
    """
    lo, hi = -G, M - 1.0
    if not lo < hi:
        return None
    flo = esscher_drift_map(C, G, M, Y, lo) - target
    fhi = esscher_drift_map(C, G, M, Y, hi) - target
    if flo * fhi > 0.0:
        return None
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        fm = esscher_drift_map(C, G, M, Y, mid) - target
        if flo * fm <= 0.0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return 0.5 * (lo + hi)


# ------------------------------------------------------- BRIEF_014: GBM corner

# The numerical shadow of ImprovedBS/Corner.lean (BRIEF_014). Two conventions
# are pinned here because they are the two places a silent scale/drift error
# hides, and neither is visible in a residual that is merely small:
#
#   * WHICH SCALE THE CORNER RUNS ON. `corner_scale` is `(σ²/2)(2−Y)` (the
#     Lean `cgmyCornerC`) -- a HALF-variance times the distance to the pole,
#     not `σ²(2−Y)`. Doubling it delivers twice the intended variance, and a
#     `C` that does not vanish like `2 − Y` does not converge at all: `Γ(−Y)`
#     has a pole at `Y = 2`, so at fixed `C` the exponent diverges (ledger
#     C17). Both failures are seeded -- the doubled scale is mutant M22.
#   * WHICH DRIFT THE FORWARD NORMALIZATION SUBTRACTS.
#     `corner_forward_exponent` is `ψ_Y(v) + i(r−q−κ_Y(1))v` (the Lean
#     `cornerForwardExponent`), with `κ_Y(1)` the REAL cumulant and not the
#     complex exponent at `v = −i`. Dropping the `−κ_Y(1)` leaves the
#     tempering asymmetry `G − M` inside the limit, which is mutant M23.
#
# The GBM TARGET these routes are compared against lives in the test, not
# here: it is an independently expanded polynomial, and putting both sides of
# one comparison in the same module is how an oracle stops being a falsifier.


def corner_scale(sigma: float, Y: float) -> float:
    """`C_Y = (σ²/2)·(2−Y)` -- the Lean `cgmyCornerC`.

    The scale the pole cancellation runs on: `C_Y Γ(−Y) → σ²/4`, so the
    bracket's `−2v²` becomes `−(σ²/2)v²` and the diffusion variance is `σ²`.
    Two ways to get it wrong, both of them quiet:

      * `σ²(2−Y)` (no half) -- twice the variance, same finite limit;
      * any `C` not vanishing like `2−Y` -- `Re ψ` diverges as `Y ↑ 2`.

    `Y < 2` is enforced, as everywhere in this oracle: `Y = 2` is the pole,
    and `Gamma(-2)` is not a value this file will produce.
    """
    if not Y < 2.0:
        raise ValueError("the corner approaches Y = 2 from BELOW; Y = 2 is a pole of Gamma(-Y)")
    return (sigma * sigma / 2.0) * (2.0 - Y)


def corner_forward_exponent(C: float, G: float, M: float, Y: float, r: float, q: float,
                            v: complex) -> complex:
    """`Ψ_Y(v) = ψ_Y(v) + i(r−q−κ_Y(1))v` -- the Lean `cornerForwardExponent`.

    A deterministic linear correction of the CGMY exponent, chosen so that
    `Ψ_Y(−i) = r − q` EXACTLY at every `Y` (the Lean
    `cornerForward_numeraire`) -- which is what the test asserts as a
    tolerance-free identity, and what makes route A an algebraic
    normalization rather than an Esscher tilt. `κ_Y(1)` is the real cumulant
    of BRIEF_013, i.e. the value of `ψ_Y` on the strip, not a second complex
    evaluation.
    """
    return cgmy_exponent(C, G, M, Y, v) + 1j * (r - q - cgmy_cumulant(C, G, M, Y, 1.0)) * v


def cgmy_levy_near_zero_mass(Y: float, M: float, x_min: float = 1e-9, n: int = 20000) -> float:
    """`int_{x_min}^1 x^{1-Y} e^{-M x} dx` -- the truncated `x^2` piece at 0.

    `int (1 and x^2) nu(dx)` near 0 reduces to this. The lower end is truncated
    at `x_min > 0` on purpose: for `Y > 1` the integrand has an *integrable*
    `x^{1-Y}` singularity, and a uniform mesh cannot resolve the nearly
    logarithmic mass it hides (at `Y = 1.99` the closed form is 100 while the
    mesh below sees 17). The finiteness claim is therefore checked against
    `cgmy_levy_mass_ceiling`, not against the quadrature; the quadrature is used
    where it is trustworthy (`Y <= 1`).
    """
    return _simpson(lambda x: x ** (1.0 - Y) * math.exp(-M * x), x_min, 1.0, n)


def cgmy_levy_mass_ceiling(Y: float) -> float:
    """`1/(2-Y)`: the closed-form `x^2` mass at 0 of the UNTEMPERED density.

    `int_0^1 x^{1-Y} dx = 1/(2-Y)` for `Y < 2`, and tempering only lowers it
    (the `e^{-Mx} <= 1` factor). So this is the ceiling `int_0^1 x^{1-Y}
    e^{-Mx} dx <= 1/(2-Y)` -- the near-zero half of `int (1 and x^2) nu < inf`.
    """
    if Y >= 2.0:
        raise ValueError("the near-zero x^2 mass is finite only for Y < 2")
    return 1.0 / (2.0 - Y)


def cgmy_levy_truncated_mass(Y: float, x_min: float) -> float:
    """`int_{x_min}^1 x^{1-Y} dx = (1 - x_min^{2-Y})/(2-Y)`, in closed form.

    As `x_min -> 0` this stays bounded for `Y < 2` and diverges for `Y >= 2`
    (`-log x_min` at `Y = 2`): the failure of `int (1 and x^2) nu < inf` at 0
    happens exactly at `Y >= 2`, and it is decided by this closed form rather
    than by quadrature.
    """
    if Y == 2.0:
        return -math.log(x_min)
    return (1.0 - x_min ** (2.0 - Y)) / (2.0 - Y)


def cgmy_levy_far_mass(Y: float, M: float, r_max: float, n: int = 20000) -> float:
    """`int_1^{r_max} x^{1-Y} e^{-M x} dx` -- the `x^2` piece at infinity.

    With `M > 0` this converges as `r_max -> inf`; with `M = 0` it does not
    (`int_1^R x^{1-Y} dx = (R^{2-Y}-1)/(2-Y) -> inf` for `Y < 2`). Tempering is
    what makes the far field finite.
    """
    return _simpson(lambda x: x ** (1.0 - Y) * math.exp(-M * x), 1.0, r_max, n)


def cgmy_levy_untempered_far_mass(Y: float, r_max: float) -> float:
    """`int_1^{r_max} x^{1-Y} dx = (r_max^{2-Y} - 1)/(2-Y)`, in closed form.

    The untempered far mass, so the failure of `int (1 and x^2) nu < inf` at
    `M = 0` is checked against a closed form rather than against quadrature.
    """
    if Y == 2.0:
        return math.log(r_max)
    return (r_max ** (2.0 - Y) - 1.0) / (2.0 - Y)


def _expm1_complex(z: complex) -> complex:
    """`e^z - 1`, evaluated without the small-`z` cancellation.

    `cmath` has no `expm1`. The Taylor branch is what makes the dyadic panels of
    `cgmy_levy_integral_one_sided` meaningful: a plain `cmath.exp(1j*v*x) - 1`
    cancels to ~`|v|x` ~ 1e-13 at the innermost panel and loses every digit.
    """
    if abs(z) < 1e-2:
        total, term = z, z
        for k in range(2, 14):
            term = term * z / k
            total += term
        return total
    return cmath.exp(z) - 1.0


def _expm1_minus_z_complex(z: complex) -> complex:
    """`e^z - 1 - z`, summed from `k = 2` so no subtraction is ever taken.

    `_expm1_complex(z) - z` would cancel away `1/|z| ~ 1e12` digits at the
    innermost dyadic panel; the series starts exactly where the difference
    starts, and converges in one pass for `|z|` far beyond the cutoff.
    """
    total, term = 1.0 + 0.0j, 1.0 + 0.0j
    term = z * z / 2.0  # the k = 2 term, where the difference starts
    total = term
    for k in range(3, 60):
        term = term * z / k
        total += term
        if abs(term) < 1e-30 * max(1.0, abs(total)):
            break
    return total


def cgmy_levy_integral_one_sided(
    a: float,
    Y: float,
    v: complex,
    x_max: float = 60.0,
    panels: int = 30,
    n_panel: int = 200,
    compensated: bool = False,
) -> complex:
    """`int_0^inf (e^{ivx} - 1 [- ivx]) e^{-a x} x^{-1-Y} dx` by graded Simpson.

    Dyadic panels `[2^{-k-1}, 2^{-k}]` resolve the `x^{-Y}` behaviour at 0 that
    a uniform mesh cannot, plus one Simpson pass on `[1, x_max]`. Compare with
    `cgmy_exponent_one_sided` (uncompensated) or
    `cgmy_exponent_one_sided_compensated` -- the numerical content of the
    tempered Levy-Khintchine identity that this oracle does NOT machine-check
    (mathlib v4.34.0 has no Levy-Khintchine theorem).

    WHICH INTEGRAND IS WHICH. The near-0 behaviour decides everything:

      * `compensated=False`: the integrand is `~ (i v) x^{-Y}` at 0, so the
        integral converges -- and then only -- for `0 < Y < 1`. For `Y >= 1`
        BOTH parts diverge like `x^{1-Y}` (the real part too: `Im v` feeds it
        through `i v x`), and shrinking `panels` makes the value grow without
        bound. This is the form that matches a measure with `int (1 and |x|) nu
        < inf`, i.e. the `Y < 1` corner only.
      * `compensated=True`: the `- i v x` is the Levy-Khintchine compensator,
        the integrand is `~ -(v x)^2/2 * x^{-1-Y} = O(x^{1-Y})` at 0, and the
        integral converges for the WHOLE range `0 < Y < 2` (this is the form
        that matches `int (1 and x^2) nu < inf`). It converges *slowly* as
        `Y -> 2`: the tail below the innermost panel is `~ |v|^2 x^{2-Y}`, which
        `x^{2-Y} -> const` stops from decaying, so the tail-loss estimate at
        `panels = 40` is a few percent at `Y = 1.9` and below `1e-6` at
        `Y <= 1.6`. Tests therefore assert *shrinking* residuals near `Y = 2`,
        not a tight bound.

    The exponential is damped as a separate factor (`exp(-a x)`, magnitude
    honest) so no intermediate exceeds `exp(|Im v| x_max)`; keep
    `|Im v| * x_max` well below 700.
    """
    total = 0j

    def f(x: float) -> complex:
        z = 1j * v * x
        if abs(z) < 1.0:
            # Small `x`: the graded panels live here, and `expm1` keeps every
            # digit of the `~ z` behaviour a plain difference would cancel away.
            step = _expm1_minus_z_complex(z) if compensated else _expm1_complex(z)
            return step * cmath.exp(-a * x) * x ** (-1.0 - Y)
        # Large `x`: take the two damped exponentials directly. This is the
        # SAME expression, not an approximation, and it cannot overflow because
        # `Re(a - iv) > 0` makes `|e^{(iv-a)x}| = e^{(Im(-v)-a)x}` decay.
        damp = cmath.exp(-a * x)
        step = cmath.exp(z - a * x) - damp
        if compensated:
            step -= z * damp  # the compensator carries the same damping
        return step * x ** (-1.0 - Y)

    inner = max(1.0 / 2.0 ** panels, 1e-12)
    edges = [inner * 2.0 ** k for k in range(panels + 1)]  # ascending: inner .. 1
    for lo, hi in zip(edges, edges[1:]):
        total += _simpson(f, lo, hi, n_panel)
    total += _simpson(f, 1.0, x_max, 4000)
    return total


def cgmy_exponent_one_sided_compensated(C: float, a: float, Y: float, v: complex) -> complex:
    """`C Gamma(-Y) [(a - iv)^Y - a^Y + iv Y a^{Y-1}]`: the COMPENSATED integral

        int_0^inf (e^{ivx} - 1 - ivx) e^{-a x} x^{-1-Y} dx   (0 < Y < 2, Y != 1)

    valid (as an ordinary, absolutely convergent integral) whenever the base
    stays in the right half plane, `Re(a - iv) > 0` -- the same condition as
    the uncompensated form, but no longer restricted to `Y < 1`. The extra
    `iv Y a^{Y-1}` is `-iv Gamma(1-Y) a^{Y-1} = iv Y Gamma(-Y) a^{Y-1}` after
    `Gamma(1-Y) = -Y Gamma(-Y)`; it is what item 3 of the BSM-2 kit (fixing the
    drift at a named measure) will pin down, and it drops out of `Re psi` only
    after that convention is chosen.
    """
    return C * cgmy_gamma_neg(Y) * ((a - 1j * v) ** Y - a ** Y + 1j * v * Y * a ** (Y - 1.0))


# ---------------------------------------------------------------------------
# BRIEF_015: the Pareto witness for Levy.lean's tail hypothesis.
#
# The numeric shadow of mathlib's `ProbabilityTheory.paretoPDFReal` and of the
# Lean `paretoMeasure_Ici`. The two are written INDEPENDENTLY: the tail below
# is the closed form `(t/x)^r`, never an integral of `pareto_pdf`, so the test
# comparing a quadrature of one against the other can fail.
# ---------------------------------------------------------------------------


def pareto_pdf(t: float, r: float, x: float) -> float:
    """`r t^r x^(-(r+1))` on `[t, inf)`, `0` below -- mathlib's `paretoPDFReal`."""
    if x < t:
        return 0.0
    return r * t ** r * x ** (-(r + 1.0))


def pareto_tail(t: float, r: float, x: float) -> float:
    """`mu[x, inf) = t^r x^(-r)` for `x >= t`, `1` below -- the Lean `paretoMeasure_Ici`.

    At `c = t^r`, `alpha = r`, `x0 = t` this is Levy.lean's `htail` WITH
    EQUALITY, which is why the test asserts equality: the inequality alone
    survives the `t^r -> t^(-r)` constant swap whenever `t > 1` (mutant M25).
    """
    if x < t:
        return 1.0
    return t ** r * x ** (-r)


# ---------------------------------------------------------------------------
# BRIEF_016: the external anchor (a published VG price table) and the
# term-structure falsifier (the model's ATM-skew power law vs the market's).
#
# The anchor is Carr & Madan (1999), Section 5 / Figure 2: a published price
# table for the Variance-Gamma model, which is CGMY at `Y = 0`. Two routes are
# exposed on purpose, and they must agree:
#
#   * the VG parameterization `(sigma, nu, theta)` -- the form the paper states;
#   * the CGMY `Y = 0` corner `(C, G, M)` -- the form this tree prices.
#
# `cgmy_zeroth_exponent` is written EXPLICITLY: `cgmy_gamma_neg(0)` is a pole
# (`Real.Gamma 0 = 0` in Lean makes the raw evaluation silently the Dirac law),
# so the corner is a LIMIT, never an evaluation of `cgmy_exponent` -- BRIEF_016
# F3, the `Y -> 2` pattern of BRIEF_014 one corner over. `cgmy_zeroth_
# corner_map` is the single place the F3 correspondence lives, so the corner
# route and the test cannot drift apart (mutants M26 and M29).
#
# The falsifier (BRIEF_016 section 2) measures the ATM implied-vol skew
# `psi(tau) = d sigma_BS/dk` at `k = log(K/F) = 0` for each maturity and fits
# `log|psi| = A - alpha_fit log tau`. The published exponents that pin the
# market side (`alpha in (0.3, 0.5)`) live in `tests/`, not here.
# ---------------------------------------------------------------------------


def vg_exponent(
    sigma: float, nu: float, theta: float, tau: float, r: float, q: float, v: complex
) -> complex:
    """The RISK-NEUTRAL variance-gamma log-characteristic function.

        psi(v) = i (r - q + omega) tau v
                 - (tau / nu) log(1 - i theta nu v + sigma^2 nu v^2 / 2),
        omega  = (1 / nu) log(1 - theta nu - sigma^2 nu / 2).

    `omega` is the martingale correction: `psi(-i) = (r - q) tau` exactly, so
    `E[S_T] = S e^{(r-q)tau}`. This is the `Y = 0` member of the CGMY family
    (BRIEF_016 F3) in the paper's own parameterization; the corner route below
    carries the same law in `(C, G, M)`, and the test asserts they agree.
    """
    if sigma <= 0.0 or nu <= 0.0:
        raise ValueError("VG needs sigma > 0 and nu > 0")
    m1 = 1.0 - theta * nu - 0.5 * sigma * sigma * nu
    if m1 <= 0.0:
        raise ValueError("VG moment condition violated: 1 - theta nu - sigma^2 nu/2 must be > 0")
    omega = math.log(m1) / nu
    w = 1.0 - 1j * theta * nu * v + 0.5 * sigma * sigma * nu * v * v
    if w == 0:
        raise ValueError("VG log singularity on the contour")
    return 1j * (r - q + omega) * tau * v - (tau / nu) * cmath.log(w)


def cgmy_zeroth_corner_map(sigma: float, nu: float, theta: float):
    """The F3 correspondence `(sigma, nu, theta) -> (C, G, M)`:

        C = 1/nu,   s = sqrt(theta^2 + 2 sigma^2 / nu),
        G = (s + theta)/sigma^2,   M = (s - theta)/sigma^2.

    `G` tempers the negative side and `M` the positive side, matching
    `cgmy_exponent`'s `G + iv` / `M - iv` pairing; `1 < M` is the numeraire
    condition (`cgmy_numeraire_strip`), so `u = 1` is inside the strip. The
    map reproduces the first two cumulants exactly:
    `C(1/M - 1/G) = theta`, `C(1/M^2 + 1/G^2) = sigma^2 + nu theta^2`.
    """
    if sigma <= 0.0 or nu <= 0.0:
        raise ValueError("the corner map needs sigma > 0 and nu > 0")
    C = 1.0 / nu
    s = math.sqrt(theta * theta + 2.0 * sigma * sigma / nu)
    return C, (s + theta) / (sigma * sigma), (s - theta) / (sigma * sigma)


def cgmy_zeroth_exponent(C: float, G: float, M: float, v: complex) -> complex:
    """`psi_0(v) = C [ log(M/(M - iv)) + log(G/(G + iv)) ]` -- the `Y -> 0` corner.

    The limit of `cgmy_exponent` as `Y -> 0`: `Gamma(-Y) ~ -1/Y` cancels the
    bracket's `Y`, leaving exactly this. Written explicitly because the landed
    `cgmy_gamma_neg` has a pole at `0` (and Lean's `Real.Gamma 0 = 0` would
    make a raw evaluation identically ZERO -- the Dirac law, not an error).
    """
    if C <= 0.0 or G <= 0.0 or M <= 0.0:
        raise ValueError("CGMY parameters C, G, M must all be positive")
    return C * (cmath.log(M / (M - 1j * v)) + cmath.log(G / (G + 1j * v)))


def cgmy_zeroth_forward_exponent(
    C: float, G: float, M: float, r: float, q: float, v: complex
) -> complex:
    """`Psi_0(v) = psi_0(v) + i (r - q - kappa_0(1)) v` -- the `Y = 0` value of
    `corner_forward_exponent` (BRIEF_014 route A).

    `kappa_0(1) = psi_0(-i)` is real and equals `-omega` of the VG
    parameterization; `Psi_0(-i) = r - q` exactly, so `exp(tau Psi_0)` is a
    martingale factor -- and, under the F3 map, the SAME function as
    `exp(vg_exponent(...))`.
    """
    kappa1 = cgmy_zeroth_exponent(C, G, M, -1j)
    if abs(kappa1.imag) > 1e-12 * max(1.0, abs(kappa1)):
        raise ValueError("kappa_0(1) = psi_0(-i) must be real")
    return cgmy_zeroth_exponent(C, G, M, v) + 1j * (r - q - kappa1.real) * v


def carr_madan_by_exponent(expf, S: float, K: float, tau: float, r: float, q: float,
                           alpha: float = 1.5, u_max: float = 2000.0, n: int = 80000) -> float:
    """Carr-Madan contour quadrature at an ARBITRARY log-characteristic function.

    The general form of the landed route: `bs_call_by_fourier_inversion` keeps
    its own `norm_cdf`-free derivation, while this one takes any `expf` -- the
    logarithm of the CF of `X = log(S_T/S)` -- and runs the same contour
    `v = u - i(alpha + 1)` with `carr_madan_denom`:

        e^{-r tau} S e^{-alpha k} / pi * int_0^{u_max} Re[e^{-i u k}
            exp(expf(u - i(alpha+1))) / carr_madan_denom(alpha, u)] du,

    by Simpson. The GBM exponent `i m v - (sigma^2 tau/2) v^2` is an instance.
    """
    if alpha <= 0.0:
        raise ValueError("damping parameter alpha must be > 0")
    k = math.log(K / S)
    h = u_max / n

    def integrand(u: float) -> float:
        v = complex(u, -(alpha + 1.0))
        return (cmath.exp(-1j * u * k) * cmath.exp(expf(v)) / carr_madan_denom(alpha, u)).real

    tot = integrand(0.0) + integrand(u_max)
    for i in range(1, n):
        tot += integrand(i * h) * (4 if i % 2 else 2)
    return math.exp(-r * tau) * S * math.exp(-alpha * k) / math.pi * (tot * h / 3.0)


def implied_vol_bs(price: float, S: float, K: float, tau: float, r: float, q: float,
                   lo: float = 1e-6, hi: float = 5.0, tol: float = 1e-12) -> float:
    """BS implied volatility by bisection on `bs_call` (the A4 parity floor is this `tol`)."""
    def f(s: float) -> float:
        return bs_call(S, K, tau, r, q, s) - price

    if f(lo) > 0.0 or f(hi) < 0.0:
        raise ValueError("price not bracketed by [lo, hi] implied vols")
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0.0:
            hi = mid
        else:
            lo = mid
        if hi - lo <= tol:
            break
    return 0.5 * (lo + hi)


def atm_skew(exponent_family, S: float, tau: float, r: float, q: float, h: float = 0.005,
             alpha: float = 1.5, u_max: float = 2000.0, n: int = 80000) -> float:
    """`psi(tau) = d sigma_BS(k, tau)/dk` at `k = 0`, central difference with step `h`.

    `exponent_family(tau)` returns the log-CF callable for that maturity; each
    model price comes from `carr_madan_by_exponent`, and each implied vol from
    `implied_vol_bs`. `k = log(K/F)` is log-moneyness (BRIEF_016 section 2).
    """
    F = S * math.exp((r - q) * tau)
    exf = exponent_family(tau)
    vols = []
    for k in (-h, h):
        K = F * math.exp(k)
        call = carr_madan_by_exponent(exf, S, K, tau, r, q, alpha, u_max, n)
        vols.append(implied_vol_bs(call, S, K, tau, r, q))
    return (vols[1] - vols[0]) / (2.0 * h)


def power_law_fit(taus, values) -> float:
    """Least-squares exponent of `|values| ~ tau^(-exponent)` on `log tau`.

    The fit alone, so a caller can run it on measurements this module did not
    take (the test's canary: a prescribed `tau^(-1/2)` skew must come back as
    `0.5`). Returns `-slope`, so `power_law_exponent` is `tau^(-a)`'s `a`.
    """
    xs = [math.log(t) for t in taus]
    ys = [math.log(abs(y)) for y in values]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return -num / den


def power_law_exponent(exponent_family, S: float, r: float, q: float, taus, h: float = 0.005,
                       alpha: float = 1.5, u_max: float = 2000.0, n: int = 80000) -> float:
    """Least-squares fit of `log|psi(tau)|` on `log tau`; returns `-slope`.

    BRIEF_016's falsifier fit: the model's measured ATM-skew decay exponent,
    compared by the test against the published market band. `taus` IS the
    pinned window -- the short end is `h`-sensitive and is deliberately not
    pinned (recorded in the brief).
    """
    return power_law_fit(
        taus,
        [atm_skew(exponent_family, S, t, r, q, h, alpha, u_max, n) for t in taus],
    )


# ---------------------------------------------------------------------------
# BRIEF_018: the variance-gamma law (the CGMY family's `Y = 0` corner).
#
# The numerical shadow of ImprovedBS/VGLaw.lean. The law is the difference of
# the two Gamma laws `Gamma(C*tau, M)` and `Gamma(C*tau, G)` (BRIEF_018 F2 --
# the Madan-Carr-Chang form, not the normal variance-mean mixture), so its mgf
# on the landed strip `-G < u < M` is
#
#     M(u) = (M/(M-u))^{C tau} (G/(G+u))^{C tau} = exp(tau * kappa_0(u)),
#     kappa_0(u) = C [ log(M/(M-u)) + log(G/(G+u)) ].
#
# Three conventions are pinned here because they are the three places a silent
# error hides (BRIEF_018 F3/F5):
#
#   * WHICH SIDE EACH RATE TEMPERS. `M` sits on the POSITIVE side (`M - u`)
#     and `G` on the negative side (`G + u`), matching `cgmy_exponent`'s
#     `M - iv` / `G + iv` pairing. Reflecting `u` (M33) swaps the mean's sign.
#   * THE CORNER IS A LIMIT, NEVER AN EVALUATION. `cgmyCumulant ... 0 u` is
#     `Gamma(0) * 0` -- Lean's `Real.Gamma 0 = 0` makes that silently the Dirac
#     law, not an error. So `vg_cumulant` is written EXPLICITLY (the log form
#     above), exactly as `cgmy_zeroth_exponent` is explicit on the complex
#     side, and the test's canary pins the Dirac's signature against it.
#   * WHICH WAY THE TILT MOVES THE RATES. The Esscher tilt at `theta` sends
#     `(G, M) -> (G + theta, M - theta)` (the law-level image of
#     `esscher_cgmy_shift`); swapping the two legs (M32) prices a different law.
#
# `gamma_mgf` is the one-line mgf of a single Gamma law (Lean
# `gammaMeasure_mgf`); everything else composes it. No published literal lives
# here (BRIEF_016's rule): the Case-4 numbers stay in `tests/`.
# ---------------------------------------------------------------------------


def gamma_mgf(a: float, r: float, u: float) -> float:
    """`(r/(r-u))^a` -- the mgf of `Gamma(a, r)` at `u` (Lean `gammaMeasure_mgf`).

    Valid for `u < r`; the test pins the underlying Gamma integral by
    quadrature at one shape and the rate scaling exactly.
    """
    if not u < r:
        raise ValueError("Gamma mgf needs u < r")
    return (r / (r - u)) ** a


def vg_cumulant(C: float, G: float, M: float, u: float) -> float:
    """`kappa_0(u) = C [log(M/(M-u)) + log(G/(G+u))]` -- the `Y = 0` real
    cumulant (Lean `vgCumulant`), the difference of the two Gamma cumulants.

    The strip `-G < u < M` is enforced: both log arguments must be positive.
    At `u = 1` this is `-omega`, the VG parameterization's own martingale
    correction (BRIEF_018 F3 -- the bridge between the two normalizations).
    """
    if not -G < u < M:
        raise ValueError("vg_cumulant needs -G < u < M")
    return C * (math.log(M / (M - u)) + math.log(G / (G + u)))


def vg_mgf(C: float, G: float, M: float, tau: float, u: float) -> float:
    """`exp(tau * kappa_0(u))` -- the mgf of `vgLaw` (Lean `vgLaw_mgf`).

    The `tau` is load-bearing: the law's shape is `C*tau`, and dropping it
    (mutant M31) prices the `tau = 1` law at every maturity.
    """
    return math.exp(tau * vg_cumulant(C, G, M, u))


def vg_drift_map(C: float, G: float, M: float, theta: float) -> float:
    """`g(theta) = kappa_0(theta+1) - kappa_0(theta)` -- the drift the tilt
    at `theta` delivers (Lean `vgDriftMap`), the `Y = 0` value of
    `esscher_drift_map`. Antisymmetric about `(M-G-1)/2`, strictly increasing
    on `[-G, M-1]`, and UNBOUNDED at both edges (BRIEF_018 F4): there is no
    out-of-range case at the corner.
    """
    return vg_cumulant(C, G, M, theta + 1.0) - vg_cumulant(C, G, M, theta)


def vg_tilted_cumulant(C: float, G: float, M: float, theta: float, u: float) -> float:
    """`kappa_0` at the SHIFTED rates `(G+theta, M-theta)` -- the tilted law
    is the family member at those rates (Lean `vg_tilt_cumulant_shift`).

    The identity `kappa(u+theta) - kappa(theta) = kappa_{(G+theta,M-theta)}(u)`
    is what the test asserts; swapping the two legs (mutant M32) breaks it.
    """
    return vg_cumulant(C, G + theta, M - theta, u)


def vg_esscher_solve(C: float, G: float, M: float, target: float,
                     iters: int = 200):
    """Bisection on `g(theta) = target` over the admissible interval
    `(-G, M-1)` -- the numerical drift solve at the corner.

    Unlike `esscher_solve`, the edge values are `-inf`/`+inf` (F4), so the
    bracket is inset by `1e-12` of the width before the sign check: for every
    finite target the inset bracket straddles it. Returns `None` only when the
    interval itself is EMPTY (`G + M <= 1`); there is no `esscher_no_solution`
    twin at `Y = 0`.
    """
    lo, hi = -G, M - 1.0
    if not lo < hi:
        return None
    inset = 1e-12 * (hi - lo)
    lo, hi = lo + inset, hi - inset
    flo = vg_drift_map(C, G, M, lo) - target
    fhi = vg_drift_map(C, G, M, hi) - target
    if flo * fhi > 0.0:
        return None
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        fm = vg_drift_map(C, G, M, mid) - target
        if flo * fm <= 0.0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return 0.5 * (lo + hi)


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


# ---------------------------------------------------------------------------
# BRIEF_019: the compound-Poisson mixture and the truncated CGMY jump law.
#
# The Lean module lands `cpLaw` -- the Poisson mixture of additive convolution
# powers, `charFun_cpLaw = cexp (lam (phi - 1))` -- and the truncated CGMY jump
# law, whose marginal's characteristic function is `cexp (tau * A_eps)` with
#
#     A_eps(v) = int_{|x| >= eps} (e^{i v x} - 1) nu_eps(dx)
#
# written as a Bochner integral (absolutely convergent BECAUSE of the
# truncation).  The two sides the rows below compare are deliberately different
# objects:
#
#   mixture : the *truncated tsum* `sum_{n <= N} p_n phi(t)^n`, powers
#             accumulated multiplicatively.  The weights are built in log space
#             because the rate reaches 20656 in the witnesses: `exp(-lam)`
#             underflows and `lam^n` overflows before `n!` cancels either.
#             Every mixture row therefore also carries the Poisson tail bound
#             of the terms it drops; a residual under that bound is evidence.
#   closed  : `cexp (lam (phi(t) - 1))`, and at the CGMY law `cexp (tau A_eps)`
#             with the `-1` of the integrand carrying the mass `lambda_eps`.
#
# The scaling rows are the ones that make the truncation SYMMETRIC (`{|x| >=
# eps}`, the module's R4 clause): the mass grows like `2C/Y eps^{-Y}`, the
# truncation error `|A_eps - psi_Y|` decays like `eps^{2-Y}`, while the
# one-sided truncation loses the `i v x` cancellation and, for `Y >= 1`,
# diverges like `eps^{1-Y}` (the canary row).
# ---------------------------------------------------------------------------


def cgmy_levy_density(C: float, G: float, M: float, Y: float, x: float) -> float:
    """The oracle's `cgmyLevyDensity C G M Y`: `C e^{-rate |x|} |x|^{-1-Y}`.

    One even-in-`|x|` function with the tempering rate `M` on `x > 0` and `G`
    on `x < 0`, split in Lean by `cgmyLevyDensity_pos_of_pos` /
    `_neg_of_neg`.  Written from the definition rather than from either
    theorem, so the two halves of the test do not share an algebra.
    """
    rate = M if x > 0.0 else G
    return C * math.exp(-rate * abs(x)) * abs(x) ** (-1.0 - Y)


def poisson_tail(lam: float, n_max: int) -> float:
    """Upper bound on `sum_{n > n_max} e^{-lam} lam^n / n!` (Chernoff).

    For any `t > 0`, `P(X > n_max) <= exp(lam (e^t - 1) - (n_max+1) t)`; the
    minimiser `t = log((n_max+1)/lam)` (valid when `n_max + 1 > lam`) gives
    `exp(-(n_max+1) log((n_max+1)/lam) + (n_max+1) - lam)`.  Below the mode the
    bound is vacuous and the function returns 1.
    """
    if n_max + 1 <= lam:
        return 1.0
    r = (n_max + 1) / lam
    return math.exp(-(n_max + 1) * math.log(r) + (n_max + 1) - lam)


def poisson_weights(lam: float, n_max: int = None):
    """`(weights, tail)`: Poisson weights `e^{-lam} lam^n / n!`, `n <= n_max`.

    Log space: `log w_n = -lam + n log lam - log n!` accumulated by the
    recursion `log w_{n+1} = log w_n + log lam - log (n+1)`, exponentiated
    relative to the mode and normalised by their own sum.  That renormalisation
    is deliberate -- the returned weights sum to 1 while `tail` (the true
    omitted mass, bounded by `poisson_tail`) is what a truncated tsum is
    missing.  `n_max` defaults to twelve standard deviations above the mean.
    """
    if n_max is None:
        n_max = int(math.ceil(lam + 12.0 * math.sqrt(lam) + 12.0))
    logs = [-lam]
    for n in range(1, n_max + 1):
        logs.append(logs[-1] + math.log(lam) - math.log(n))
    top = max(logs)
    ws = [math.exp(l - top) for l in logs]
    total = math.fsum(ws)
    return [w / total for w in ws], poisson_tail(lam, n_max)


def cp_law_cf_mixture(lam: float, jump_cf, t: float, n_max: int = None):
    """`(value, tail)`: the truncated mixture `sum_{n <= n_max} p_n phi(t)^n`.

    `phi(t)^n` is accumulated by one multiplication per term rather than by
    `** n`, which is what keeps the small-`n` terms of a 20k-term sum from
    being rounded away.  This is the *only* place the mixture is formed.
    """
    w, tail = poisson_weights(lam, n_max)
    phi = jump_cf(t)
    acc = 0.0 + 0.0j
    power = 1.0 + 0.0j
    for pn in w:
        acc += pn * power
        power *= phi
    return acc, tail


def cp_law_cf_closed(lam: float, jump_cf, t: float) -> complex:
    """`cexp (lam (phi(t) - 1))` -- the closed form `charFun_cpLaw` proves.

    Nothing here knows about a tsum, which is the point: `charFun_map_cast_poissonMeasure`
    is this identity at `rho = delta_1`, and the test checks the two sides
    against each other rather than against a shared expansion.
    """
    return cmath.exp(lam * (jump_cf(t) - 1.0))


def _cgmy_truncated_leg(
    rate: float,
    Y: float,
    eps: float,
    v: float,
    minus_one: bool = True,
    x_max: float = 60.0,
    panels: int = 30,
    n_panel: int = 200,
) -> complex:
    """`int_eps^{x_max} (e^{ivx} [- 1]) e^{-rate x} x^{-1-Y} dx`, graded Simpson.

    Dyadic panels `[eps 2^k, eps 2^{k+1}]` up to 1 plus one Simpson pass on
    `[1, x_max]`: the `x^{-1-Y}` growth at `eps` is what a uniform mesh cannot
    see.  The `-1` goes through `_expm1_complex`, so the innermost panels keep
    the `~ i v x` behaviour instead of cancelling it away.
    """
    def f(x: float) -> complex:
        z = 1j * v * x
        weight = _expm1_complex(z) if minus_one else cmath.exp(z)
        return weight * math.exp(-rate * x) * x ** (-1.0 - Y)

    total = 0.0 + 0.0j
    edges = [eps * 2.0 ** k for k in range(panels + 1) if eps * 2.0 ** k < 1.0]
    edges.append(1.0)
    for a, b in zip(edges, edges[1:]):
        total += _simpson(f, a, b, n_panel)
    total += _simpson(f, 1.0, x_max, 4000)
    return total


def _cgmy_truncated_sum(
    C: float,
    G: float,
    M: float,
    Y: float,
    eps: float,
    v: float,
    minus_one: bool = True,
    one_sided: bool = False,
    **quad,
) -> complex:
    """Both legs of the truncated integral (the symmetric truncation), summed.

    `one_sided=True` drops the mirror leg -- the route `[CPoisson]` R4 forbids
    and the canary row measures; it is a keyword rather than a second function
    so that a mutant can turn it on inside the same quadrature.
    """
    pos = _cgmy_truncated_leg(M, Y, eps, v, minus_one, **quad)
    if one_sided:
        return C * pos
    neg = _cgmy_truncated_leg(G, Y, eps, -v, minus_one, **quad)
    return C * (pos + neg)


def cgmy_jump_mass(C: float, G: float, M: float, Y: float, eps: float, **quad) -> float:
    """`lambda_eps = int_{|x| >= eps} cgmyLevyDensity dx`, both legs.

    The truncation is what makes this finite (`int_{|x|<eps}` diverges like
    `eps^{-Y}`) and its growth `2C/Y eps^{-Y}` is why the `eps -> 0` step is a
    conditional-convergence argument (BRIEF_019 F3).
    """
    pos = _cgmy_truncated_leg(M, Y, eps, 0.0, False, **quad)
    neg = _cgmy_truncated_leg(G, Y, eps, 0.0, False, **quad)
    return C * (pos.real + neg.real)


def cgmy_truncated_exponent(
    C: float, G: float, M: float, Y: float, eps: float, v: float, **quad
) -> complex:
    """`A_eps(v) = int_{|x| >= eps} (e^{ivx} - 1) nu_eps(dx)` -- the Lean def.

    Bochner-integrable exactly because the set excludes `0`: `|e^{ivx} - 1| <= 2`
    and the density's mass there is finite.
    """
    return _cgmy_truncated_sum(C, G, M, Y, eps, v, True, False, **quad)


def cgmy_jump_cf(C: float, G: float, M: float, Y: float, eps: float, t: float, **quad) -> complex:
    """`phi(t)` of the normalised jump law `nu_eps / lambda_eps`.

    `e^{itx} = (e^{itx} - 1) + 1` term by term, so the numerator is `A_eps(t) +
    lambda_eps` and the division *is* the normalisation (`cgmyJumpLaw`); the
    mutant that drops the division is the "jump law not normalised" row.
    """
    lam = cgmy_jump_mass(C, G, M, Y, eps, **quad)
    return (cgmy_truncated_exponent(C, G, M, Y, eps, t, **quad) + lam) / lam


def cgmy_law_cf(C: float, G: float, M: float, Y: float, eps: float, tau: float, v: float, **quad) -> complex:
    """The marginal's CF at rate `tau * lambda_eps`: `cexp (tau * A_eps(v))`.

    `charFun_cgmyCpLaw`'s right-hand side; its left-hand side is
    `cp_law_cf_mixture (tau * lambda_eps) (cgmy_jump_cf ...)`, so the row is the
    cancellation `lambda_eps * (phi - 1) = A_eps` seen through a 20k-term sum.
    """
    return cmath.exp(tau * cgmy_truncated_exponent(C, G, M, Y, eps, v, **quad))


# ---------------------------------------------------------------------------
# BRIEF_020: the CGMY law -- the `eps -> 0` limit of the truncated exponent.
#
# BRIEF_019 landed the truncated family and its CF; its F3 recorded that
# `eps -> 0` is a CONDITIONAL-convergence statement -- `lambda_eps` grows like
# `2C/Y eps^{-Y}`, so no dominated-convergence theorem applies to the unsplit
# integral `A_eps(v) = int_{|x| >= eps} (e^{ivx} - 1) nu_eps(dx)`.
#
# BRIEF_020 §1 makes it unconditional with an IDENTITY that holds at every
# `eps > 0` (ledger correction C25 -- the near-zero `i v x` pieces *pair*, they
# do not cancel):
#
#     A_eps(v) = B_eps(v) + i v d_eps,
#     B_eps(v) = int_{|x| >= eps} (e^{ivx} - 1 - i v x 1_{|x| <= 1}) nu_eps(dx),
#     d_eps    = C int_eps^1 x^{-Y} (e^{-M x} - e^{-G x}) dx,
#
# and each piece is now dominated on all of `R \ {0}`: the compensated
# integrand is `O(x^{1-Y})` at 0 (integrable for every `Y < 2`) and `<= 2` far
# out, while the PAIRED drift integrand is `O(x^{1-Y})` because
# `e^{-Mx} - e^{-Gx} = O(x)`. The limit
#
#     L(v) = B_0(v) + i v d_0
#
# is the Levy-Khintchine exponent with the unit-ball compensator, finite on
# all of `0 < Y < 2` INCLUDING `Y = 1` (the pole at `Y = 1` belongs to the
# closed form `Gamma(-Y)`, not to the law), and it is the exponent of the law
# `cgmyLaw` that §2 constructs as the `limUnder` of the compound-Poisson
# marginals along `eps_n = 2^{-n}`.
#
# The drift is load-bearing and it is NOT zero: `d_0 = -0.115465 / -0.346002 /
# -1.641132` at `Y = 1/2, 1, 3/2` for `(C, G, M) = (0.5, 5, 10)`. The
# *unpaired* leg `C int_eps^1 x^{-Y} e^{-Mx} dx` alone is `122.5` at
# `eps = 2^{-14}`, `Y = 3/2`, and grows like `eps^{1-Y}` -- which is why
# `[CGMYLaw]` R2 forbids writing either leg on its own and why mutant M39 below
# is a divergence canary rather than a rounding canary.
#
# HOW THE LIMITS ARE QUADRATURED. A cutoff at `inner` leaves an un-tailed piece
# of size `inner^{2-Y}` (compensated) or `inner^{1-Y}` (uncompensated), and at
# `inner = 1e-12` -- the floor the landed `cgmy_levy_integral_one_sided` uses --
# that piece is `~1e-6`, four decades above anything this brief resolves. So
# every limit here is a dyadic-panel integral down to `2^-60` PLUS the analytic
# `int_0^{inner}` of the same integrand, taken from its own power series
# (`_cgmy_ball_tail`, `_cgmy_uncompensated_tail`, `_gamma_series_tail`). The
# series and the panels are different objects -- one is a local expansion, the
# other a mesh -- so their sum is a genuine route, not a self-comparison.
#
# `n_panel = 400` per dyadic panel is the floor these rows need and no more:
# the panel error goes like `n^{-4}` (measured `1.6e-11 / 9.7e-13 / 6.0e-14` at
# `n = 200 / 400 / 800` for the `x^{-1/2}` Gamma integrand), so 400 lands every
# row an order of magnitude inside the issue-time route-check's own residuals.
# ---------------------------------------------------------------------------

# The inner cutoff of every `eps = 0` limit row. `2^-60` keeps the first
# neglected series term below `1e-50` for every `Y` in `(0, 2)`.
CGMY_LIMIT_INNER = 2.0 ** -60


def _simpson_far(f, x_max: float = 60.0, x_lo: float = 1.0, n_panel: int = 200):
    """Graded Simpson on the far field `[x_lo, x_max]`: `[1,2],[2,4],[4,8],...`

    One uniform pass over `[1, 60]` is the trap here. The tempered integrand is
    smooth but its derivatives grow like `rate^k`, so a single mesh of step
    `59/4000` leaves a FIXED residual of a few `1e-11` that no amount of
    near-zero panel refinement removes (measured: `2.96e-11` at the real-rate
    Gamma anchor with 200, 800 and 1600 points per near panel). Doubling panels
    cut the step where the integrand is largest and dropped the same residual
    below `1e-14`, which is where the rest of this brief's rows live.
    """
    total = 0.0
    edges = [x_lo]
    while edges[-1] * 2.0 < x_max:
        edges.append(edges[-1] * 2.0)
    edges.append(x_max)
    for a, b in zip(edges, edges[1:]):
        total += _simpson(f, a, b, n_panel)
    return total


def _cgmy_ball_tail(rate: float, Y: float, v: float, delta: float) -> complex:
    """`int_0^delta (e^{ivx} - 1 - i v x) e^{-rate x} x^{-1-Y} dx`, from the series.

    Expanding both factors, the compensated integrand is

        -(v^2/2) x^{1-Y} + ((v^2 rate)/2 - i v^3/6) x^{2-Y} + O(x^{3-Y}),

    so the omitted piece is `O(delta^{2-Y})` and the two terms below leave a
    residual of `O(delta^{4-Y})` -- at `delta = 2^-60` that is `1e-54`, i.e.
    nothing. This is the analytic half of every `eps = 0` row; the dyadic
    panels are the other half and they never see `x < delta`.
    """
    c2 = -0.5 * v * v
    c3 = 0.5 * v * v * rate - 1j * (v ** 3) / 6.0
    return (c2 * delta ** (2.0 - Y) / (2.0 - Y)
            + c3 * delta ** (3.0 - Y) / (3.0 - Y))


def _cgmy_uncompensated_tail(rate: float, Y: float, v: float, delta: float) -> complex:
    """`int_0^delta (e^{ivx} - 1) e^{-rate x} x^{-1-Y} dx`, from the series.

    The uncompensated integrand is `i v x^{-Y} + (-i v rate - v^2/2) x^{1-Y} +
    ...`, so the omitted piece is `O(delta^{1-Y})`: integrable for `0 < Y < 1`
    (the range the uncompensated one-sided form is valid on) and *divergent*
    for `Y >= 1`, which is exactly the obstruction BRIEF_019 F3 named.
    """
    c1 = 1j * v
    c2 = -1j * v * rate - 0.5 * v * v
    return (c1 * delta ** (1.0 - Y) / (1.0 - Y)
            + c2 * delta ** (2.0 - Y) / (2.0 - Y))


def _cgmy_one_sided_leg(
    rate: float,
    Y: float,
    inner: float,
    v: float,
    mode: str = "ball",
    x_max: float = 60.0,
    n_panel: int = 400,
    to_zero: bool = False,
) -> complex:
    """One tempering leg of a CGMY exponent integral, graded Simpson + series tail.

    `int_inner^{x_max} w(x) e^{-rate x} x^{-1-Y} dx`, plus -- when `to_zero`,
    i.e. when the leg stands for the IMPROPER integral from `0` and `inner` is
    only its innermost panel edge -- the analytic `int_0^{inner}` of the same
    integrand. A leg that genuinely starts at a truncation `eps > 0` must pass
    `to_zero=False`: adding the tail there would quietly turn `B_eps` into `B_0`
    and make the whole `eps -> 0` limit vacuous. `w` is

      * `"ball"`: `e^{ivx} - 1 - i v x` on `x <= 1` and `e^{ivx} - 1` beyond --
        the UNIT-BALL compensator of the Levy-Khintchine form `L`;
      * `"full"`: `e^{ivx} - 1 - i v x` everywhere -- the FULLY compensated
        form, which BRIEF_011's `cgmy_exponent_one_sided_compensated` closes;
      * `"none"`: `e^{ivx} - 1` everywhere -- the uncompensated form
        `cgmy_exponent_one_sided` closes, convergent only for `0 < Y < 1`.

    Dyadic panels `[inner 2^k, inner 2^{k+1}]` up to 1 resolve the `x^{-1-Y}`
    growth at the cutoff that a uniform mesh cannot see; one Simpson pass
    covers `[1, x_max]`. The small-`x` weight goes through
    `_expm1_minus_z_complex` / `_expm1_complex`, so the innermost panels keep
    their `x^2` (resp. `x`) behaviour instead of cancelling it away.
    """
    if not 0.0 < inner < 1.0:
        raise ValueError("_cgmy_one_sided_leg needs 0 < inner < 1")
    if mode not in ("ball", "full", "none"):
        raise ValueError(f"unknown compensation mode {mode!r}")

    def weight(x: float, compensated: bool) -> complex:
        z = 1j * v * x
        if compensated:
            return _expm1_minus_z_complex(z)
        return _expm1_complex(z)

    def near(x: float) -> complex:
        return (weight(x, mode != "none") * math.exp(-rate * x) * x ** (-1.0 - Y))

    def far(x: float) -> complex:
        return (weight(x, mode == "full") * math.exp(-rate * x) * x ** (-1.0 - Y))

    total = 0.0 + 0.0j
    edges = [inner * 2.0 ** k for k in range(200) if inner * 2.0 ** k < 1.0]
    edges.append(1.0)
    for a, b in zip(edges, edges[1:]):
        total += _simpson(near, a, b, n_panel)
    total += _simpson_far(far, x_max, n_panel=n_panel)
    if to_zero:
        if mode == "none":
            total += _cgmy_uncompensated_tail(rate, Y, v, inner)
        else:
            total += _cgmy_ball_tail(rate, Y, v, inner)
    return total


def cgmy_compensated_exponent(
    C: float, G: float, M: float, Y: float, eps: float, v: float, **quad
) -> complex:
    """`B_eps(v) = int_{|x| >= eps} (e^{ivx} - 1 - i v x 1_{|x| <= 1}) nu_eps(dx)`.

    The Lean `cgmyLKExponent`'s first term (its `eps = 0` value `B_0` is the
    integral over all of `R \\ {0}`). `eps = 0` means the LIMIT: the panels run
    down to `CGMY_LIMIT_INNER` and `_cgmy_ball_tail` supplies `int_0^{inner}`,
    so `B_0` is not a cutoff value wearing a limit's clothes. The two legs are
    mirrored (`v -> -v`, rate `G`), which is the substitution `x |-> -x` on the
    negative half-line -- the same reflection the Lean proof takes through
    `integral_comp_neg_Ioi`.
    """
    if eps < 0.0 or eps > 1.0:
        raise ValueError("cgmy_compensated_exponent is stated for 0 <= eps <= 1")
    to_zero = eps <= 0.0
    inner = CGMY_LIMIT_INNER if to_zero else eps
    pos = _cgmy_one_sided_leg(M, Y, inner, v, "ball", to_zero=to_zero, **quad)
    neg = _cgmy_one_sided_leg(G, Y, inner, -v, "ball", to_zero=to_zero, **quad)
    return C * (pos + neg)


def cgmy_paired_drift(
    C: float, G: float, M: float, Y: float, eps: float, n_panel: int = 400
) -> float:
    """`d_eps = C int_eps^1 x^{-Y} (e^{-M x} - e^{-G x}) dx` -- the PAIRED drift.

    The `eps -> 0` limit `d_0` is the drift of the Levy-Khintchine form `L`,
    and it is nonzero (`-1.641132` at `Y = 3/2`, `(C,G,M) = (0.5,5,10)`). Both
    legs sit inside ONE integrand on purpose: each leg on its own diverges like
    `eps^{1-Y}` at `0` for `Y >= 1` (mutant M39 measures `122.5` at
    `eps = 2^{-14}`, `Y = 3/2`), and only the difference is `O(x^{1-Y})`.

    `expm1` on both legs is what keeps the difference honest at the innermost
    panel: `exp(-M x) - exp(-G x)` computed directly loses every digit there,
    while `expm1(-M x) - expm1(-G x)` cancels the `1`s exactly. For `eps = 0`
    the analytic `int_0^{inner}` is `(G-M) inner^{2-Y}/(2-Y) +
    (M^2-G^2) inner^{3-Y}/(2(3-Y))` from the same expansion.
    """
    if eps < 0.0 or eps > 1.0:
        raise ValueError("cgmy_paired_drift is stated for 0 <= eps <= 1")

    def f(x: float) -> float:
        return (math.expm1(-M * x) - math.expm1(-G * x)) * x ** (-Y)

    if eps <= 0.0:
        inner = CGMY_LIMIT_INNER
        total = ((G - M) * inner ** (2.0 - Y) / (2.0 - Y)
                 + 0.5 * (M * M - G * G) * inner ** (3.0 - Y) / (3.0 - Y))
    else:
        inner, total = eps, 0.0
    edges = [inner * 2.0 ** k for k in range(200) if inner * 2.0 ** k < 1.0]
    edges.append(1.0)
    for a, b in zip(edges, edges[1:]):
        total += _simpson(f, a, b, n_panel)
    return C * total


def cgmy_far_drift(C: float, G: float, M: float, Y: float, x_max: float = 60.0) -> float:
    """`d_far = C int_{|x| > 1} x nu(dx) = C int_1^inf x^{-Y}(e^{-Mx} - e^{-Gx}) dx`.

    The far-field half of the drift. `d_0 + d_far` is the WHOLE drift
    `C int_0^inf x^{-Y}(e^{-Mx} - e^{-Gx}) dx`, which `cgmy_drift_identity_closed`
    evaluates as `m^inf` -- so the split at 1 is a route to `m^inf` that shares
    nothing with the `Gamma` closed form, and the row that compares them is the
    real-rate statement of BRIEF_020 §3's `cgmyDrift_identity`.

    Plain `exp` rather than `expm1` here, unlike `cgmy_paired_drift`: on
    `x >= 1` the two exponentials are nowhere near each other, so there is
    no small-argument cancellation to protect -- and keeping the two
    integrands textually distinct is what lets the mutation harness target
    the paired one (M39, M42).
    """
    def f(x: float) -> float:
        return (math.exp(-M * x) - math.exp(-G * x)) * x ** (-Y)

    return C * _simpson_far(f, x_max, n_panel=400)


def cgmy_lk_exponent(
    C: float, G: float, M: float, Y: float, v: float, n_panel: int = 400, **quad
) -> complex:
    """`L(v) = B_0(v) + i v d_0` -- the `eps -> 0` limit of `A_eps(v)`.

    The Lean `cgmyLKExponent C G M Y v`: the exponent of the law `cgmyLaw`, by
    quadrature and with no `Gamma` anywhere in it. That is what makes the row
    `|L - psi_Y|` a real check of `cgmyLKExponent_eq_cgmyExponent`: the closed
    side is a difference of `Gamma(-Y)` values with a pole at `Y = 1`, while
    this side is finite there.
    """
    b_zero = cgmy_compensated_exponent(C, G, M, Y, 0.0, v, n_panel=n_panel, **quad)
    d_zero = cgmy_paired_drift(C, G, M, Y, 0.0, n_panel=n_panel)
    return b_zero + 1j * v * d_zero


def cgmy_one_sided_exponent_integral(a: float, Y: float, v: float, **quad) -> complex:
    """`int_0^inf (e^{ivx} - 1) e^{-a x} x^{-1-Y} dx` -- the UNCOMPENSATED leg.

    `cgmy_exponent_one_sided(1, a, Y, v)`'s integral, convergent exactly for
    `0 < Y < 1` (the `i v x^{-Y}` behaviour at 0). The landed
    `cgmy_levy_integral_one_sided` computes the same integral but stops at
    `inner = 1e-12` with no analytic tail, which leaves `i v inner^{1-Y}/(1-Y)`
    -- `~1e-6` at `Y = 1/2` -- unaccounted for, i.e. four decades above what
    this brief resolves; hence the separate route here.
    """
    if not 0.0 < Y < 1.0:
        raise ValueError("the uncompensated one-sided integral needs 0 < Y < 1")
    inner = quad.pop("inner", CGMY_LIMIT_INNER)
    return _cgmy_one_sided_leg(a, Y, inner, v, "none", to_zero=True, **quad)


def cgmy_one_sided_compensated_integral(a: float, Y: float, v: float, **quad) -> complex:
    """`int_0^inf (e^{ivx} - 1 - i v x) e^{-a x} x^{-1-Y} dx` -- the FULLY compensated leg.

    `cgmy_exponent_one_sided_compensated(1, a, Y, v)`'s integral, convergent on
    all of `0 < Y < 2` (the integrand is `O(x^{1-Y})` at 0). The two one-sided
    forms are the statements BRIEF_011's oracle already pins and `test_cgmy_contour`
    already measures; §3 of BRIEF_020 turns them into theorems by one and two
    integrations by parts from G1.
    """
    if not 0.0 < Y < 2.0:
        raise ValueError("the compensated one-sided integral needs 0 < Y < 2")
    inner = quad.pop("inner", CGMY_LIMIT_INNER)
    return _cgmy_one_sided_leg(a, Y, inner, v, "full", to_zero=True, **quad)


def _gamma_series_tail(s: float, z: complex, delta: float) -> complex:
    """`int_0^delta x^{s-1} e^{-z x} dx`, from `e^{-zx}`'s own power series.

    Term by term, `sum_k (-z)^k delta^{s+k} / (k! (s+k))`; two terms leave
    `O(delta^{s+2})`, which at `delta = 2^-60` is below `1e-50` for `s >= 1/2`.
    """
    return (delta ** s / s - z * delta ** (s + 1.0) / (s + 1.0))


def gamma_integral_complex_rate(
    s: float, z: complex, x_max: float = 60.0, n_panel: int = 400, **quad
) -> complex:
    """G1's left side: `int_0^inf x^{s-1} e^{-z x} dx` for `0 < s`, `0 < Re z`.

    The complex-rate Gamma integral. mathlib at the pinned tag ships the
    REAL-rate version `integral_cpow_mul_exp_neg_mul_Ioi`, and `CGMYLaw.lean`'s
    G1 (`integral_cpow_mul_cexp_neg_mul_Ioi`) extends it to `Re z > 0` by the
    identity theorem -- differentiability in `z` under the integral, analyticity
    of both sides on the half-plane, agreement on the positive reals where the
    shipped lemma applies. This quadrature is the numeric shadow: the right side
    is `Gamma(s) z^{-s}`, and the residual at `z = M - i v` is the same as at
    the real anchor `z = M` (`2.9e-11`), i.e. the quadrature's, not the
    identity's.
    """
    if not s > 0.0:
        raise ValueError("gamma_integral_complex_rate needs 0 < s")
    if not z.real > 0.0:
        raise ValueError("gamma_integral_complex_rate needs 0 < Re z")
    inner = quad.pop("inner", CGMY_LIMIT_INNER)

    def f(x: float) -> complex:
        return x ** (s - 1.0) * cmath.exp(-z * x)

    total = _gamma_series_tail(s, z, inner)  # the improper integral starts at 0
    edges = [inner * 2.0 ** k for k in range(200) if inner * 2.0 ** k < 1.0]
    edges.append(1.0)
    for a, b in zip(edges, edges[1:]):
        total += _simpson(f, a, b, n_panel)
    total += _simpson_far(f, x_max, n_panel=n_panel)
    return total


def cgmy_drift_identity_closed(C: float, G: float, M: float, Y: float) -> float:
    """`m^inf = C Gamma(1-Y) (M^{Y-1} - G^{Y-1})` -- the closed form of the drift.

    The real-rate, Frullani-type statement of BRIEF_020 §3: one integration by
    parts turns `int_0^inf x^{-Y}(e^{-Mx} - e^{-Gx}) dx` into a difference of
    two `Gamma(1-Y)` integrals. It is what the tree's uncompensated
    `cgmy_exponent` differs from the fully compensated Levy-Khintchine form by
    (`i v m^inf`), and it is finite on all of `0 < Y < 2, Y != 1`:
    `-0.116083169` at `Y = 1/2`, `-1.641663919` at `Y = 3/2`.
    """
    if Y == 1.0:
        raise ValueError("cgmy_drift_identity_closed has a pole at Y = 1")
    return C * math.gamma(1.0 - Y) * (M ** (Y - 1.0) - G ** (Y - 1.0))


def cgmy_lk_exponent_via_one_sided(C: float, G: float, M: float, Y: float, v: float) -> complex:
    """`L(v)` assembled from the two one-sided FULLY compensated closed forms.

        L(v) = [one-sided compensated at (M, v)] + [one-sided compensated at (G, -v)]
               + i v m^inf

    The bracket is `cgmyExponent - i v m^inf` (the extra `i v Y a^{Y-1}` of each
    compensated leg is `-i v Gamma(1-Y) a^{Y-1}` after `Gamma(1-Y) = -Y Gamma(-Y)`),
    so this equals the tree's `cgmy_exponent` -- and the point of writing it out
    is that the drift term `i v m^inf` is then VISIBLE: dropping it (mutant M41)
    moves `L` by `|v m^inf| = 1.641664` at `(Y, v) = (3/2, 1)`, and replacing
    `Gamma(1-Y)` by `Gamma(-Y)` in it (mutant M43) by `2.736107`.

    This side is closed-form, so the load-bearing comparison is not this
    function against `cgmy_exponent` (algebraically the same expression) but
    `cgmy_lk_exponent` -- quadrature -- against either of them.
    """
    compensated = (cgmy_exponent_one_sided_compensated(C, M, Y, complex(v))
                   + cgmy_exponent_one_sided_compensated(C, G, Y, complex(-v)))
    return compensated + 1j * v * cgmy_drift_identity_closed(C, G, M, Y)
