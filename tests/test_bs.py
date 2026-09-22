"""
Sanity tests for the BS numeric oracle. These are NOT the artifact (the Lean
formalization is): they exist to make sure the formula we intend to formalize
is the formula we actually wrote, and that it numerically satisfies the
properties the formal theorems claim (parity, PDE identity, boundaries).

Run:  python3 -m pytest tests/   (or:  python3 tests/test_bs.py)

NON-TAUTOLOGY RULE
------------------
A test is only evidence if it can fail. Each identity below is therefore
checked between two *independently derived* expressions:

  T1  d1 - d2 = s*sqrt(tau)      d2 comes from its own explicit formula
  T2  put-call parity            the put comes from its own closed form,
                                 using Phi(-x), not from the call
  T6(3a) closed form = e^{-r tau} E[payoff]
                                 the expectation is a quadrature against
                                 norm_pdf; no norm_cdf, no d1/d2 in the route
  BRIEF_009 parity/bounds        checked at hand-built NON-lognormal discrete
                                 laws, so no Gaussian route can vouch for the
                                 model-free skeleton; the drift hypothesis is
                                 proved load-bearing by a wrong-drift canary

`tests/test_mutants.py` enforces this rule mechanically: it seeds bugs that
violate each identity and asserts the *targeted* test goes red. If a future
refactor re-derives the put from parity (or d2 from d1), that suite fails --
so the vacuity cannot silently come back.
"""

import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from experiments.black_scholes import (
    _d1d2,
    bs_call,
    bs_call_by_expectation,
    bs_call_by_fourier_inversion,
    bs_call_by_fourier_inversion_complex,
    bs_price,
    bs_pde_residual,
    bs_put,
    bs_put_by_expectation,
    bs_put_by_parity,
    carr_madan_by_law,
    cgmy_base_reals,
    cgmy_char_factor,
    cgmy_contour_re,
    cgmy_decay_threshold,
    cgmy_exponent,
    cgmy_exponent_by_pieces,
    cgmy_exponent_one_sided_compensated,
    cgmy_gamma_neg,
    cgmy_levy_integral_one_sided,
    cgmy_pricing_contour_v,
    cgmy_tempered_constant,
    cgmy_tempered_correction,
    cgmy_tempered_rate,
    forward_by_expectation,
    model_free_forward,
    model_free_prices,
    norm_cdf,
    norm_pdf,
)

# Textbook reference case: S=K=100, r=5%, q=0, sigma=20%, T-t=1yr
S, K, R, Q, SGM, TAU = 100.0, 100.0, 0.05, 0.0, 0.20, 1.0

# A grid spanning moneyness / tenor / vol / rates / dividend yield, used by
# the identity tests so a single lucky calibration cannot hide a wrong formula.
GRID = [
    (100.0, 100.0, 1.00, 0.05, 0.00, 0.20),
    (100.0, 120.0, 0.50, 0.03, 0.01, 0.35),
    (80.0, 90.0, 2.00, 0.01, 0.00, 0.60),
    (100.0, 60.0, 0.25, 0.08, 0.02, 0.15),
    (50.0, 100.0, 3.00, 0.00, 0.05, 0.90),
    (200.0, 150.0, 1.50, -0.02, 0.00, 0.05),
]


def test_textbook_call():
    c = bs_price(S, K, TAU, 0.0, R, SGM)
    assert abs(c - 10.4506) < 1e-3, f"call {c} off textbook"


def test_textbook_put():
    p = bs_price(S, K, TAU, 0.0, R, SGM, option="put")
    assert abs(p - 5.5735) < 1e-3, f"put {p} off textbook"


def test_d1_minus_d2():
    """T1: d1 - d2 = sigma*sqrt(tau), against an INDEPENDENT d2.

    The oracle computes d2 from its own explicit formula, so this compares
    two distinct expressions rather than unfolding a definition. The
    explicit form is restated here a third time, inline, so that a mistake
    shared by the oracle and this file would still have to survive the
    textbook-value tests above.
    """
    for (s_, k_, tau_, r_, q_, sg_) in GRID:
        d1, d2 = _d1d2(s_, k_, tau_, r_, q_, sg_)
        d2_explicit = (math.log(s_ / k_) + (r_ - q_ - 0.5 * sg_ * sg_) * tau_) / (
            sg_ * math.sqrt(tau_)
        )
        assert abs(d2 - d2_explicit) < 1e-12, f"d2 {d2} != explicit {d2_explicit}"
        assert abs((d1 - d2) - sg_ * math.sqrt(tau_)) < 1e-12, "T1 violated"


def test_put_call_parity():
    """T2: P = C - S e^{-q tau} + K e^{-r tau}, with an INDEPENDENT put.

    `bs_put` prices the put through its own closed form using Phi(-d1),
    Phi(-d2); `bs_put_by_parity` derives it from the call. Agreeing to
    ~1e-15 IS the numerical content of Phi(x) + Phi(-x) = 1. This test can
    fail -- test_mutants.py demonstrates it does, when Phi loses odd
    symmetry.
    """
    for (s_, k_, tau_, r_, q_, sg_) in GRID:
        lhs = bs_put(s_, k_, tau_, r_, q_, sg_)
        rhs = bs_put_by_parity(s_, k_, tau_, r_, q_, sg_)
        assert abs(lhs - rhs) < 1e-11 * max(1.0, abs(rhs)), f"parity {lhs} vs {rhs}"


def test_put_call_parity_via_public_api():
    """The frozen public API must expose the independent put, not the parity one."""
    c = bs_price(S, K, TAU, 0.0, R, SGM)
    p = bs_price(S, K, TAU, 0.0, R, SGM, option="put")
    lhs = c - p
    rhs = S * math.exp(-Q * TAU) - K * math.exp(-R * TAU)
    assert abs(lhs - rhs) < 1e-11, f"parity {lhs} vs {rhs}"


def test_public_api_argument_order():
    """Pin the boundary translation: bs_price(S,K,T,t,r,s,q) -> helpers(S,K,tau,r,q,s).

    The public signature puts `s` before `q`; the internal helpers and the
    Lean definitions put `q` before `sigma`. Swapping them at the boundary
    would silently misprice every dividend-paying option, so the translation
    is asserted explicitly with q != r.
    """
    s_, k_, tau_, r_, q_, sg_ = 100.0, 110.0, 0.75, 0.04, 0.03, 0.28
    assert bs_price(s_, k_, tau_, 0.0, r_, sg_, q_, "call") == bs_call(s_, k_, tau_, r_, q_, sg_)
    assert bs_price(s_, k_, tau_, 0.0, r_, sg_, q_, "put") == bs_put(s_, k_, tau_, r_, q_, sg_)
    # and the swap would actually be wrong (guards against a vacuous test)
    assert bs_call(s_, k_, tau_, r_, q_, sg_) != bs_call(s_, k_, tau_, q_, r_, sg_)


def test_delta_identity_numerically():
    """T3: S e^{-q tau} phi(d1) == K e^{-r tau} phi(d2).

    Requires sigma > 0 and tau > 0. In Lean the statement additionally needs
    (hS : 0 < S) (hK : 0 < K) (hsigma : sigma ~= 0) (htau : 0 < tau): with
    mathlib's `a / 0 = 0` convention, sigma = 0 collapses d1 = d2 = 0 and the
    identity becomes S e^{-q tau} phi(0) = K e^{-r tau} phi(0), which is false
    for S ~= K. The grid here stays strictly inside the hypotheses.
    """
    for (s_, k_, tau_, r_, q_, sg_) in GRID:
        d1, d2 = _d1d2(s_, k_, tau_, r_, q_, sg_)
        lhs = s_ * math.exp(-q_ * tau_) * norm_pdf(d1)
        rhs = k_ * math.exp(-r_ * tau_) * norm_pdf(d2)
        assert abs(lhs - rhs) < 1e-11 * max(1.0, abs(rhs)), "T3 delta identity violated"


def test_value_bounds():
    """T4 (numerical shadow): max(S e^{-q tau} - K e^{-r tau}, 0) <= C <= S e^{-q tau}."""
    for (s_, k_, tau_, r_, q_, sg_) in GRID:
        c = bs_call(s_, k_, tau_, r_, q_, sg_)
        lower = max(s_ * math.exp(-q_ * tau_) - k_ * math.exp(-r_ * tau_), 0.0)
        upper = s_ * math.exp(-q_ * tau_)
        assert lower - 1e-11 <= c <= upper + 1e-11, f"bounds violated: {lower} <= {c} <= {upper}"
        p = bs_put(s_, k_, tau_, r_, q_, sg_)
        plower = max(k_ * math.exp(-r_ * tau_) - s_ * math.exp(-q_ * tau_), 0.0)
        pupper = k_ * math.exp(-r_ * tau_)
        assert plower - 1e-11 <= p <= pupper + 1e-11, f"put bounds violated: {p}"


def test_pde_residual_vanishes():
    """T5 (numerical shadow): the closed form solves the BSM diffusion equation."""
    res = bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "call", h=1e-3)
    assert abs(res) < 1e-4, f"PDE residual {res} not ~0"
    res_p = bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "put", h=1e-3)
    assert abs(res_p) < 1e-4, f"put PDE residual {res_p} not ~0"


def test_pde_residual_is_second_order():
    """Central differences must shrink the residual as O(h^2) inside the window.

    This replaces the old `r2 <= r1 + 1e-4`, which was satisfied even when the
    residual got WORSE and so could not fail for any reason that mattered.
    Measured ratios on the textbook case are ~100x per decade of h down to
    h=1e-3; the assertions below ask for >=50x and >=10x, leaving margin for
    round-off while still discriminating a mis-derived formula (which does not
    converge at all -- see mutants M4/M8 in test_mutants.py).

    h below 1e-3 is round-off dominated and the residual DIVERGES; see the
    step-size window documented in experiments/black_scholes.py. Do not
    "improve" this test by shrinking h.
    """
    r1 = abs(bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "call", h=1e-1))
    r2 = abs(bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "call", h=1e-2))
    r3 = abs(bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "call", h=1e-3))
    assert r1 > 0.0 and r2 > 0.0 and r3 > 0.0, "residuals hit exact zero: window is wrong"
    assert r1 / r2 >= 50.0, f"not O(h^2) from 1e-1 to 1e-2: {r1:.3e} -> {r2:.3e}"
    assert r2 / r3 >= 10.0, f"not O(h^2) from 1e-2 to 1e-3: {r2:.3e} -> {r3:.3e}"


def test_degenerate_spot_zero():
    assert bs_price(0.0, K, TAU, 0.0, R, SGM) == 0.0
    assert bs_price(0.0, K, TAU, 0.0, R, SGM, option="put") == K * math.exp(-R * TAU)


def test_invalid_inputs_raise():
    for kwargs in (
        dict(S=S, K=K, T=TAU, t=TAU, r=R, s=SGM),  # tau=0
        dict(S=S, K=K, T=TAU, t=0.0, r=R, s=0.0),  # sigma=0
        dict(S=S, K=K, T=TAU, t=0.0, r=R, s=SGM, option="american"),  # bad option
    ):
        try:
            bs_price(**kwargs)
            raise AssertionError(f"expected ValueError for {kwargs}")
        except ValueError:
            pass


def test_phi_and_Phi_are_consistent():
    """phi must be the derivative of Phi -- the analytic hinge for T3 and T5.

    Checked by central difference over the grid, so a Phi whose derivative is
    not phi (e.g. a wrong sqrt(2) scaling) is caught independently of pricing.
    """
    h = 1e-5
    for x in (-2.5, -1.0, -0.25, 0.0, 0.25, 1.0, 2.5):
        dPhi = (norm_cdf(x + h) - norm_cdf(x - h)) / (2.0 * h)
        assert abs(dPhi - norm_pdf(x)) < 1e-7, f"Phi'({x}) = {dPhi} != phi({x}) = {norm_pdf(x)}"


def test_risk_neutral_expectation():
    """T6(3a) (numerical shadow): the closed form IS the discounted expectation.

    With Z ~ N(0,1), m = (r - q - sigma^2/2) tau and s = sigma sqrt(tau):

        bs_call = e^{-r tau} * E[(S e^{m + s Z} - K)^+]      (Lean: bsCall_eq_riskNeutral_expectation)
        bs_put  = e^{-r tau} * E[(K - S e^{m + s Z})^+]      (Lean: bsPut_eq_riskNeutral_expectation)
        E[S e^{m + s Z}] = S e^{(r-q) tau}                    (Lean: integral_spot_mul_phi_eq_forward)

    The expectations come from `bs_call_by_expectation` & co.: quadrature of the
    payoff against `norm_pdf`, with no `norm_cdf` and no `_d1d2` in the route,
    so the comparison is between two independently derived numbers. Mutant M11
    (tests/test_mutants.py) flips the sign of sigma^2/2 in the drift and is
    killed by this test alone. The last assertion is the sign fact behind the
    Lean hypothesis `0 < sigma`: at -sigma the closed form is -bs_put(sigma),
    while the expectation does not change.
    """
    for (s_, k_, tau_, r_, q_, sg_) in GRID:
        c, ce = bs_call(s_, k_, tau_, r_, q_, sg_), bs_call_by_expectation(s_, k_, tau_, r_, q_, sg_)
        assert abs(ce - c) < 1e-9 * max(1.0, c), f"call != expectation: {c} vs {ce}"
        p, pe = bs_put(s_, k_, tau_, r_, q_, sg_), bs_put_by_expectation(s_, k_, tau_, r_, q_, sg_)
        assert abs(pe - p) < 1e-9 * max(1.0, p), f"put != expectation: {p} vs {pe}"
        fwd = forward_by_expectation(s_, k_, tau_, r_, q_, sg_)
        assert abs(fwd - s_ * math.exp((r_ - q_) * tau_)) < 1e-9 * s_, f"drift condition fails: {fwd}"
    s_, k_, tau_, r_, q_, sg_ = GRID[0]
    assert abs(bs_call(s_, k_, tau_, r_, q_, -sg_) + bs_put(s_, k_, tau_, r_, q_, sg_)) < 1e-12


def test_fourier_inversion():
    """T6(3b) (numerical shadow): Carr–Madan Fourier inversion equals the closed form.

    The call price is computed by inverting the damped Fourier transform
    `carrMadanKernel(gbmCharFactor, alpha)` along `v = u - i(alpha + 1)`:
        C = e^{-r tau} S e^{-alpha k} / pi * int_0^infty Re(e^{-i u k} kernel(u)) du
    landing on `bs_call_by_expectation` and `bs_call`.

    Real-valuedness: `bs_call_by_fourier_inversion_complex` computes the two-sided
    integral on [-u_max, u_max]; its imaginary part vanishes to machine precision
    because the integrand's imaginary part is an odd function of u.
    """
    for (s_, k_, tau_, r_, q_, sg_) in GRID:
        c = bs_call(s_, k_, tau_, r_, q_, sg_)
        cf = bs_call_by_fourier_inversion(s_, k_, tau_, r_, q_, sg_)
        assert abs(cf - c) < 1e-10 * max(1.0, c), f"call != fourier inversion: {c} vs {cf}"
        ce = bs_call_by_expectation(s_, k_, tau_, r_, q_, sg_)
        assert abs(cf - ce) < 1e-10 * max(1.0, c), f"fourier inversion != expectation: {cf} vs {ce}"
        c_cplx = bs_call_by_fourier_inversion_complex(s_, k_, tau_, r_, q_, sg_)
        assert abs(c_cplx.real - c) < 1e-10 * max(1.0, c), f"cplx real != closed form: {c_cplx.real} vs {c}"
        assert abs(c_cplx.imag) < 1e-13 * max(1.0, c), f"imaginary part not zero: {c_cplx.imag}"

    # alpha <= 0 must be rejected
    try:
        bs_call_by_fourier_inversion(100.0, 100.0, 1.0, 0.05, 0.0, 0.20, alpha=-0.5)
        raise AssertionError("expected ValueError for alpha <= 0")
    except ValueError:
        pass


def test_model_free_skeleton():
    """BRIEF_009 (numerical shadow): parity and bounds at laws that are NOT lognormal.

    This is the model-free skeleton (Lean `ImprovedBS/Skeleton.lean`), checked
    at hand-built discrete laws -- a skewed 3-point law, a 32-point uniform
    discretization, a wrong-drift law, and a degenerate one-point law -- so
    nothing here can lean on the Gaussian routes:

        call - put = e^{-r tau} (E[S_T] - K)              (model_free_parity_gap)
        E[S_T] = S e^{(r-q) tau}  =>  call - put = S e^{-q tau} - K e^{-r tau}
                                                  (model_free_put_call_parity)
        0 <= S_T, 0 <= K, drift  =>  bounds      (model_free_call_bounds/_put_)

    The drift hypothesis is proved load-bearing, not decorative (the `sigma <
    0` discipline of test_risk_neutral_expectation, one layer up): at the
    wrong-drift law the forward form of parity FAILS while the unfixed gap
    identity still holds -- which is exactly the seam between Lean's
    `model_free_parity_gap` and `model_free_put_call_parity`. The degenerate
    law pins the bound constants: the call's lower edge binds exactly in both
    regimes (K < F and K > F), so a slack bound could not pass as the bound.
    Mutants M13 (put payoff corrupted to the call payoff) and M14 (mean
    corrupted to the second moment) are killed by this test alone.
    """
    S, K, r, q, tau = 100.0, 100.0, 0.05, 0.02, 1.0
    disc = math.exp(-r * tau)
    target = S * math.exp((r - q) * tau)          # the forward S e^{(r-q) tau}
    fwd_spread = S * math.exp(-q * tau) - K * math.exp(-r * tau)
    lo_c = max(S * math.exp(-q * tau) - K * math.exp(-r * tau), 0.0)
    hi_c = S * math.exp(-q * tau)
    lo_p = max(K * math.exp(-r * tau) - S * math.exp(-q * tau), 0.0)
    hi_p = K * math.exp(-r * tau)

    def scaled_law(probs, raw):
        # rescale so the law's mean IS the forward (the drift condition)
        scale = target / model_free_forward(probs, raw)
        return [x * scale for x in raw]

    probs_a = [0.25, 0.5, 0.25]
    law_a = (probs_a, scaled_law(probs_a, [60.0, 100.0, 150.0]))   # skewed, correct drift
    probs_b = [1.0 / 32.0] * 32
    raw_b = [40.0 + i * (220.0 - 40.0) / 31.0 for i in range(32)]
    law_b = (probs_b, scaled_law(probs_b, raw_b))                  # uniform-ish, correct drift
    law_c = ([0.25, 0.5, 0.25], [50.0, 90.0, 200.0])               # mean 107.5 != forward
    law_d = ([1.0], [target])                                      # degenerate at the forward

    for tag, (probs, spots) in [("a", law_a), ("b", law_b), ("c", law_c), ("d", law_d)]:
        call, put = model_free_prices(probs, spots, K, r, tau)
        mean = model_free_forward(probs, spots)
        # (1) the unfixed gap identity: true for every law, drift or no drift
        assert abs((call - put) - disc * (mean - K)) < 1e-12, (
            f"[{tag}] gap identity fails: call-put={call - put} vs e^(-r tau)(E[S_T]-K)={disc * (mean - K)}"
        )

    for tag, (probs, spots) in [("a", law_a), ("b", law_b), ("d", law_d)]:
        call, put = model_free_prices(probs, spots, K, r, tau)
        mean = model_free_forward(probs, spots)
        assert abs(mean - target) < 1e-12, f"[{tag}] law not at the forward: {mean} vs {target}"
        # (2) forward parity under the drift condition
        assert abs((call - put) - fwd_spread) < 1e-12, (
            f"[{tag}] forward parity fails: {call - put} vs {fwd_spread}"
        )
        # (4) the no-arb bounds (q != 0 on purpose, so a missing e^{-q tau} dies)
        assert lo_c - 1e-12 <= call <= hi_c + 1e-12, f"[{tag}] call bounds fail: {call} not in [{lo_c}, {hi_c}]"
        assert lo_p - 1e-12 <= put <= hi_p + 1e-12, f"[{tag}] put bounds fail: {put} not in [{lo_p}, {hi_p}]"

    # (3) the drift canary: at the wrong-drift law the forward form FAILS while
    # the unfixed gap identity (asserted above) still holds. This assertion is
    # the proof that the drift hypothesis is load-bearing -- delete the
    # hypothesis from the Lean statement and this is the test that notices.
    call, put = model_free_prices(*law_c, K, r, tau)
    mean_c = model_free_forward(*law_c)
    assert abs(mean_c - target) > 1.0, f"law_c unexpectedly at the forward: {mean_c}"
    assert abs((call - put) - fwd_spread) > 1e-6, (
        f"forward parity held at a wrong-drift law (mean={mean_c}, target={target}): "
        f"the drift hypothesis is NOT load-bearing and the Lean statement is over-claimed"
    )

    # (5) the degenerate law pins the bound constants: values are the
    # discounted intrinsic and the call's lower edge binds exactly in both
    # regimes, so the bound constants are the right ones, not slack.
    for k_ in (100.0, 110.0):                    # K < F and K > F
        call, put = model_free_prices(*law_d, k_, r, tau)
        f_ = target
        assert abs(call - disc * max(f_ - k_, 0.0)) < 1e-12, f"degenerate call wrong at K={k_}: {call}"
        assert abs(put - disc * max(k_ - f_, 0.0)) < 1e-12, f"degenerate put wrong at K={k_}: {put}"
        lo_c_ = max(S * math.exp(-q * tau) - k_ * math.exp(-r * tau), 0.0)
        lo_p_ = max(k_ * math.exp(-r * tau) - S * math.exp(-q * tau), 0.0)
        assert abs(call - lo_c_) < 1e-12, f"call lower edge does not bind at K={k_}: {call} vs {lo_c_}"
        assert abs(put - lo_p_) < 1e-12, f"put lower edge does not bind at K={k_}: {put} vs {lo_p_}"


def test_carr_madan_free_law():
    """BRIEF_010 (numerical shadow): Carr–Madan inversion at an ARBITRARY law.

    `carr_madan_by_law` inverts `φ(v) = Σ p_j e^{i v log(s_j/S)}` along the
    pricing contour `v = u - i(α+1)` (Lean `cmPriceIntegral (contourCharFun μ)`)
    and must agree with `model_free_prices` -- the discounted expectation,
    which at a discrete law is a sum with no quadrature in it -- at three
    multi-atom laws plus the degenerate one-atom law. The imaginary part of
    the two-sided integral must vanish (Lean `carrMadan_im_eq_zero`, via the
    Hermitian symmetry `cmPriceIntegrand_reflect`).

    Why the tolerance is `1e-4` and not the GBM route's `2e-11`: a discrete
    law's characteristic function does not decay (`|φ| ↛ 0`), so the error is
    truncation at `u_max`, not quadrature -- measured `1.3e-05`--`2.1e-05`
    relative at `u_max=1200, n=30000` for the three laws below, and the
    bound is set an order of magnitude above the measurement. Mutant M16
    (the `-(α+1)` shift off by one, rel `3.75e-01`) is killed by this test
    alone.
    """
    S, K, r, tau, alpha = 100.0, 110.0, 0.05, 1.0, 1.2
    k = math.log(K / S)
    laws = [
        ("skewed", [0.5, 0.3, 0.2], [80.0, 105.0, 160.0]),
        ("left-heavy", [0.6, 0.3, 0.1], [70.0, 100.0, 150.0]),
        ("symmetric", [0.25, 0.5, 0.25], [80.0, 100.0, 120.0]),
        ("degenerate", [1.0], [120.0]),
    ]
    for tag, probs, spots in laws:
        val = carr_madan_by_law(probs, spots, S, r, tau, alpha, k, 1200.0, 30000)
        call, _ = model_free_prices(probs, spots, K, r, tau)
        assert abs(val.real - call) < 1e-4 * max(1.0, abs(call)), (
            f"[{tag}] free-law inversion != expectation: {val.real} vs {call}"
        )
        assert abs(val.imag) < 1e-8 * max(1.0, abs(call)), (
            f"[{tag}] imaginary part not zero: {val.imag}"
        )

    # alpha <= 0 must be rejected, as in the GBM route
    for bad in (-0.5, 0.0):
        try:
            carr_madan_by_law([1.0], [120.0], S, r, tau, bad, k, 1200.0, 30000)
            raise AssertionError(f"expected ValueError for alpha={bad}")
        except ValueError:
            pass


# ---------------------------------------------------------------------------
# BRIEF_011: the CGMY exponent, its contour decay, and the moment strip.
# ---------------------------------------------------------------------------


def test_cgmy_contour():
    """BRIEF_011 (numerical shadow of `ImprovedBS/CGMY.lean`).

    Every assertion names the Lean declaration it shadows. The CGMY exponent
    is `psi(v) = C Gamma(-Y) [(M - iv)^Y - M^Y + (G + iv)^Y - G^Y]`; the
    pricing contour is `v = u - i(alpha+1)` (correction C12/C14), on which
    `M - iv = (M - (alpha+1)) - iu` and `G + iv = (G + alpha+1) + iu`, so the
    branch condition is `alpha + 1 < M` and NOTHING about `G` -- `G` only
    constrains the old line `v = u + i(alpha)`.

    The decay constants checked here are the ones the Lean defs use, term for
    term: `r = 2C|Gamma(-Y) cos(pi Y/2)|` (`cgmyTemperedRate`),
    `c' = 2^{Y-1} Y (M+G) |C Gamma(-Y)|` (`cgmyTemperedCorrection`),
    `K0 = C|Gamma(-Y)|(M^Y + G^Y)` (`cgmyTemperedConstant`) and
    `cgmyDecayThreshold = max(M+G, max(4c'/r, max(1, (4K0/r)^{1/Y})))`.
    """
    # --- the closed form itself: `cgmyExponent` vs its pieces (exact identity)
    for C, G, M, Y in ((1.0, 5.0, 10.0, 0.7), (0.5, 0.5, 2.0, 1.3), (2.0, 1.0, 4.0, 1.9)):
        for v in (2.0 + 0j, 1j, -3.0 + 0.5j, 0.0 + 0j):
            a = cgmy_exponent(C, G, M, Y, v)
            b = cgmy_exponent_by_pieces(C, G, M, Y, v)
            assert abs(a - b) < 1e-12 * max(1.0, abs(a)), (C, G, M, Y, v, a, b)

    # --- `cgmyCharFactor_add` / `cgmyCharFactor_zero`: affine in tau
    C, G, M, Y, alpha = 1.0, 5.0, 10.0, 0.7, 1.2
    t1, t2, v = 0.4, 0.9, cgmy_pricing_contour_v(alpha, 2.5)
    f1 = cgmy_char_factor(C, G, M, Y, t1, v)
    f2 = cgmy_char_factor(C, G, M, Y, t2, v)
    f12 = cgmy_char_factor(C, G, M, Y, t1 + t2, v)
    assert abs(f12 - f1 * f2) < 1e-14 * max(1.0, abs(f12))
    assert abs(cgmy_char_factor(C, G, M, Y, 0.0, v) - 1.0) < 1e-15

    # --- the Levy-integral route check (the identity that is NOT machine-checked)
    # `cgmy_exponent_one_sided_compensated` is the closed form of the compensated
    # one-sided integral; `cgmy_levy_integral_one_sided(..., compensated=True)`
    # is the quadrature. Compensated = the `int (1 ^ x^2) nu < inf` measure.
    for a, Y in ((5.0, 0.4), (5.0, 0.9), (5.0, 1.25)):
        for w in (0.5 + 0j, 2.0 + 1.0j):
            quad = cgmy_levy_integral_one_sided(a, Y, -w, x_max=80.0, panels=35,
                                                n_panel=200, compensated=True)
            closed = cgmy_exponent_one_sided_compensated(1.0, a, Y, -w)
            assert abs(quad - closed) < 1e-3 * max(1.0, abs(closed)), (a, Y, w, quad, closed)

    # --- `cgmy_tempered_prod_neg`: the sign on (0,2) \ {1}
    for Y in (0.1, 0.4, 0.75, 0.99, 1.01, 1.3, 1.7, 1.99):
        assert cgmy_gamma_neg(Y) * math.cos(math.pi * Y / 2.0) < 0.0, Y

    # --- `cgmy_cpow_re_ge_of_lt_one` / `cgmy_cpow_re_le_of_one_le`
    worst = 0.0
    for Y in (1.0, 1.2, 1.5, 1.8, 1.95):
        for y in (0.05, 0.5, 1.0, 3.0, 17.0, 250.0):
            for i in range(0, 41):
                xx = y * i / 40.0
                lhs = ((xx + 1j * y) ** Y).real
                rhs = (y ** Y * math.cos(math.pi * Y / 2.0)
                       + 2.0 ** (Y - 1.0) * Y * xx * y ** (Y - 1.0))
                worst = max(worst, lhs - rhs)
    assert worst <= 0.0, worst
    worst = 0.0
    for Y in (0.2, 0.5, 0.9, 0.99):
        for y in (0.05, 0.5, 3.0, 40.0):
            for xx in (0.0, 1e-6, 0.01, 0.5, 3.0, 9.0, 100.0):
                worst = max(worst, y ** Y * math.cos(math.pi * Y / 2.0)
                            - ((xx + 1j * y) ** Y).real)
    assert worst <= 0.0, worst

    # --- `cgmyExponent_contour_re_le` and `cgmyExponent_contour_re_le_half`
    grid = ((1.0, 5.0, 10.0, 0.7, 1.2), (0.5, 0.5, 3.0, 1.3, 0.5),
            (1.0, 0.05, 2.0, 1.7, 0.9), (2.0, 1.0, 10.0, 0.4, 2.0))
    for C, G, M, Y, alpha in grid:
        r = cgmy_tempered_rate(C, Y)
        corr = cgmy_tempered_correction(C, G, M, Y)
        k0 = cgmy_tempered_constant(C, G, M, Y)
        thr = cgmy_decay_threshold(C, G, M, Y)
        assert r > 0.0 and corr >= 0.0 and k0 >= 0.0
        for u in (M + G, 1.5 * (M + G), 40.0, 500.0, 5000.0):
            re = cgmy_exponent(C, G, M, Y, cgmy_pricing_contour_v(alpha, u)).real
            assert re <= -r * u ** Y + corr * u ** (Y - 1.0) + k0 + 1e-9, (C, G, M, Y, alpha, u)
        for u in (thr, 1.7 * thr, 12.0 * thr):
            re = cgmy_exponent(C, G, M, Y, cgmy_pricing_contour_v(alpha, u)).real
            assert re <= -(r / 2.0) * u ** Y + 1e-9, (C, G, M, Y, alpha, u)
        # sharpness: the true rate is r, approached from below
        re = cgmy_exponent(C, G, M, Y, cgmy_pricing_contour_v(alpha, 5000.0)).real
        ratio = -re / (r * 5000.0 ** Y)
        assert 0.8 < ratio < 1.02, (C, G, M, Y, alpha, ratio)

    # --- C14: the two lines. Pricing-line base reals are >= 0 under alpha+1 < M;
    # the old line's `G + iv` base is `G - alpha`, negative once alpha >= G.
    for G, M, alpha in ((0.5, 10.0, 1.5), (2.0, 3.0, 1.5), (0.05, 1.6, 0.5)):
        assert alpha + 1.0 < M
        lft, rgt = cgmy_base_reals(G, M, alpha, 2.0, "pricing")
        assert abs(lft - (M - (alpha + 1.0))) < 1e-15
        assert abs(rgt - (G + alpha + 1.0)) < 1e-15
        assert lft >= 0.0 and rgt >= 0.0
        old_rgt = cgmy_base_reals(G, M, alpha, 2.0, "old")[1]
        assert abs(old_rgt - (G - alpha)) < 1e-15
    # the C14 witness: G binds only the old line
    assert cgmy_base_reals(0.5, 10.0, 1.5, 2.0, "old")[1] < 0.0
    assert cgmy_base_reals(0.5, 10.0, 1.5, 2.0, "pricing")[1] > 0.0

    # --- the numeraire condition (`cgmy_numeraire_strip`): `u = 1` needs `1 < M`
    # `cgmyExponent_strip` at `v = -i u` is real and equals the closed form.
    for u in (0.5, 1.0):
        z = cgmy_exponent(1.0, 5.0, 10.0, 0.7, -1j * u)
        assert abs(z.imag) < 1e-14 * max(1.0, abs(z.real)), u


if __name__ == "__main__":
    import traceback

    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    fails = 0
    for fn in fns:
        try:
            fn()
            print(f"  ok  {fn.__name__}")
        except Exception:
            fails += 1
            print(f"FAIL  {fn.__name__}")
            traceback.print_exc()
    print(f"\n{len(fns)-fails}/{len(fns)} passed")
    sys.exit(1 if fails else 0)
