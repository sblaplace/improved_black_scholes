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
  BRIEF_012 non-uniqueness       two martingale laws on the SAME spots that
                                 satisfy every BRIEF_009 clause and price the
                                 call at 1/4 and 1/8; exact rationals, so the
                                 disagreement is a claim, not a rounding

`tests/test_mutants.py` enforces this rule mechanically: it seeds bugs that
violate each identity and asserts the *targeted* test goes red. If a future
refactor re-derives the put from parity (or d2 from d1), that suite fails --
so the vacuity cannot silently come back.
"""

import cmath
import math
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from experiments.black_scholes import (
    _d1d2,
    atm_skew,
    bs_call,
    bs_call_by_expectation,
    bs_call_by_fourier_inversion,
    bs_call_by_fourier_inversion_complex,
    bs_price,
    bs_pde_residual,
    bs_put,
    bs_put_by_expectation,
    bs_put_by_parity,
    carr_madan_by_exponent,
    carr_madan_by_law,
    cgmy_compensated_exponent,
    cgmy_drift_identity_closed,
    cgmy_far_drift,
    cgmy_lk_exponent,
    cgmy_lk_exponent_via_one_sided,
    cgmy_one_sided_compensated_integral,
    cgmy_one_sided_exponent_integral,
    cgmy_paired_drift,
    gamma_integral_complex_rate,
    cgmy_zeroth_corner_map,
    cgmy_zeroth_exponent,
    cgmy_zeroth_forward_exponent,
    corner_forward_exponent,
    implied_vol_bs,
    power_law_exponent,
    power_law_fit,
    vg_exponent,
    cgmy_base_reals,
    cgmy_char_factor,
    cgmy_contour_re,
    cgmy_cumulant,
    cgmy_decay_threshold,
    cgmy_exponent,
    cgmy_exponent_by_pieces,
    cgmy_exponent_one_sided_compensated,
    cgmy_gamma_neg,
    cgmy_exponent_one_sided,
    cgmy_levy_density,
    cgmy_jump_mass,
    cgmy_jump_cf,
    cgmy_law_cf,
    cgmy_truncated_exponent,
    cp_law_cf_mixture,
    cp_law_cf_closed,
    poisson_weights,
    poisson_tail,
    _simpson,
    _cgmy_truncated_leg,
    _cgmy_truncated_sum,
    cgmy_levy_integral_one_sided,
    cgmy_pricing_contour_v,
    cgmy_tempered_constant,
    cgmy_tempered_correction,
    cgmy_tempered_rate,
    corner_forward_exponent,
    corner_scale,
    pareto_pdf,
    pareto_tail,
    esscher_drift_bound,
    esscher_drift_map,
    esscher_exponent,
    esscher_solve,
    esscher_theta_zero,
    forward_by_expectation,
    gamma_mgf,
    model_free_forward,
    model_free_prices,
    vg_cumulant,
    vg_drift_map,
    vg_esscher_solve,
    vg_mgf,
    vg_tilted_cumulant,
    norm_cdf,
    norm_pdf,
    NONUNIQ_SPOTS,
    NONUNIQ_WEIGHTS_A,
    NONUNIQ_WEIGHTS_B,
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


def test_nonuniqueness_witness():
    """BRIEF_012 (numerical shadow): the static skeleton does not select the measure.

    The Lean side (`ImprovedBS/NonUniqueness.lean`,
    `static_skeleton_does_not_select_measure`) exhibits two probability laws on
    the SAME three spots (1/2, 1, 2) at S = K = tau = 1, r = q = 0,

        A = (1/2, 1/4, 1/4)      B = (1/4, 5/8, 1/8),

    both with the forward as mean, both satisfying BRIEF_009's parity and
    bounds VERBATIM (the Lean proofs instantiate `model_free_put_call_parity`
    and `model_free_call_bounds`; the `[NONUNIQ]` lint checks the citation),
    mutually absolutely continuous -- and pricing the call at 1/4 versus 1/8.
    This test is that table, run through `model_free_prices` /
    `model_free_forward` and nothing else, in exact `Fraction` arithmetic so
    that "1/4 != 1/8" is a claim and not a rounding artefact. (The constants are
    data in the oracle module, not oracle code: the witness must be
    expressible inside the model-free layer or it is not about that layer.)

    Beyond the two points it checks the whole martingale segment (Lean
    `martingale_set_param` / `martingale_set_call_eq`): on these spots
    `sum = 1` and `E[S_T] = 1` force `p = (p1, 1 - 3 p1/2, p1/2)`, nonneg
    exactly for `p1 in [0, 2/3]`, and the call is EXACTLY `p1/2` -- so every
    price in `[0, 1/3]` is a martingale price, while the skeleton's bounds
    only say `0 <= call <= 1`. The forward, a linear payoff, is constant on the
    segment: the martingale condition pins the law on `1` and on `S_T` and on
    nothing else. Two canaries prove the drift clause is load-bearing:
    BRIEF_012's own `(1/4, 5/8, 3/8)` (mass 5/4, mean 3/2, traded parity off
    by 1/4) and a normalized one `(1/4, 1/2, 1/4)` (mass 1, mean 9/8) at which
    the unfixed gap identity of `model_free_parity_gap` still holds and the
    bounds still hold while traded parity fails -- BRIEF_009's seam again.

    Mutants M17 (B's `p3 : 1/8 -> 3/8`, the brief's canary: B stops being a
    probability law with the forward as mean, and traded parity at B fails by
    1/4), M18 (call payoff corrupted to the LINEAR payoff `s - K`: at both
    laws the "call" collapses to `E[S_T] - K = 0`, so `call(A) != call(B)` dies
    without any probability being touched) and M19 (B replaced by A: every
    clause but the price disagreement survives) are each killed by this test.
    The brief's literal M18 -- the call payoff evaluated with the put's
    `max(K - s, 0)` -- is BLIND at this witness, because at K = F with r = 0
    the call and the put coincide (1/4 = 1/4, 1/8 = 1/8): it is M13's cousin
    and only `test_model_free_skeleton` (K != F) can see it, which is why the
    committed M18 is the linear payoff instead.
    """
    S, K, r, q, tau = 1, Fraction(1), 0.0, 0.0, 1.0
    spots = NONUNIQ_SPOTS
    disc = math.exp(-r * tau)                                    # 1.0
    fwd = S * math.exp((r - q) * tau)                            # 1.0, the forward
    traded_spread = S * math.exp(-q * tau) - K * math.exp(-r * tau)   # S e^{-q tau} - K e^{-r tau} = 0
    lo_c, hi_c = max(traded_spread, 0.0), S * math.exp(-q * tau)      # the BRIEF_009 call bounds
    assert spots == (Fraction(1, 2), Fraction(1), Fraction(2)), f"witness spots moved: {spots}"

    def segment(p1):
        # (★): the unique three-point law on these spots with mass 1 and mean 1
        return (p1, 1 - Fraction(3, 2) * p1, p1 / 2)

    expected = {"A": (NONUNIQ_WEIGHTS_A, Fraction(1, 4)), "B": (NONUNIQ_WEIGHTS_B, Fraction(1, 8))}
    prices = {}
    for tag, (probs, price) in expected.items():
        # (1) a probability law with the forward as mean -- exactly
        assert sum(probs) == 1, f"[{tag}] not a probability law: mass {sum(probs)}"
        assert all(p > 0 for p in probs), f"[{tag}] must charge every spot (A ~ B): {probs}"
        mean = model_free_forward(probs, spots)
        assert mean == fwd, f"[{tag}] drift fails: E[S_T] = {mean} != {fwd}"
        # (2) the skeleton's clauses: gap identity, traded parity, bounds
        call, put = model_free_prices(probs, spots, K, r, tau)
        assert call - put == disc * (mean - K), f"[{tag}] gap identity fails: {call - put}"
        assert call - put == traded_spread, f"[{tag}] traded parity fails: {call - put} vs {traded_spread}"
        assert lo_c <= call <= hi_c, f"[{tag}] call bounds fail: {call} not in [{lo_c}, {hi_c}]"
        assert 0.0 <= put <= K * math.exp(-r * tau), f"[{tag}] put bounds fail: {put}"
        # (3) the price, at its exact dyadic value (float agrees bit-for-bit)
        assert call == float(price), f"[{tag}] call = {call}, expected {price}"
        assert put == float(price), f"[{tag}] put = {put}, expected {price}"
        # (4) the law sits on the segment (martingale_set_param): p3 = p1/2, p2 = 1 - 3 p1/2
        assert probs == segment(probs[0]), f"[{tag}] not on the martingale segment: {probs}"
        prices[tag] = call

    # (5) the point: same spots, same drift, same skeleton -- different prices
    assert NONUNIQ_WEIGHTS_A != NONUNIQ_WEIGHTS_B, "the two witness laws coincide"
    assert prices["A"] != prices["B"], (
        f"call(A) = {prices['A']} == call(B) = {prices['B']}: the skeleton selected the price "
        f"and `static_skeleton_does_not_select_measure` is over-claimed"
    )
    assert prices["A"] - prices["B"] == 0.125, f"price gap {prices['A'] - prices['B']} != 1/8"

    # (6) the segment (★), swept exactly: p1 in {0, 1/24, ..., 2/3}, 17 points
    calls = []
    for k in range(17):
        p1 = Fraction(k, 24)
        probs = segment(p1)
        assert sum(probs) == 1 and all(p >= 0 for p in probs), f"(★) leaves the simplex at p1={p1}: {probs}"
        assert model_free_forward(probs, spots) == 1, f"(★) drift fails at p1={p1}"
        call, put = model_free_prices(probs, spots, K, r, tau)
        assert call == float(p1 / 2), f"(★) call at p1={p1} is {call}, not p1/2 = {p1 / 2}"
        assert call - put == traded_spread, f"(★) parity fails at p1={p1}"
        calls.append(call)
    assert calls[0] == 0.0 and calls[-1] == float(Fraction(1, 3)), f"(★) price range is not [0, 1/3]: {calls}"
    assert calls == sorted(calls) and len(set(calls)) == 17, "(★) call is not strictly increasing in p1"
    assert segment(Fraction(17, 24))[1] == Fraction(-1, 16), "(★) should first leave the simplex at p1 = 17/24"
    assert segment(Fraction(1, 2)) == NONUNIQ_WEIGHTS_A and segment(Fraction(1, 4)) == NONUNIQ_WEIGHTS_B
    # the skeleton's bounds [lo_c, hi_c] = [0, 1] do not come close to pinning it
    assert hi_c - lo_c > calls[-1] - calls[0] > 0.3

    # (7) the drift canaries: the drift clause is load-bearing, not decorative.
    # BRIEF_012's own canary -- B with p3 moved from 1/8 to 3/8 (the M17 seed).
    canary = (Fraction(1, 4), Fraction(5, 8), Fraction(3, 8))
    call, put = model_free_prices(canary, spots, K, r, tau)
    assert sum(canary) == Fraction(5, 4) and model_free_forward(canary, spots) == Fraction(3, 2)
    assert call - put == 0.25, f"canary parity gap {call - put} != 1/4 (BRIEF_012 route check)"
    assert call - put != traded_spread, "traded parity held at the wrong-drift canary"
    # A NORMALIZED wrong-drift law: mass 1, mean 9/8. The unfixed gap identity
    # (model_free_parity_gap) and the bounds still hold; traded parity fails.
    canary = (Fraction(1, 4), Fraction(1, 2), Fraction(1, 4))
    mean = model_free_forward(canary, spots)
    call, put = model_free_prices(canary, spots, K, r, tau)
    assert sum(canary) == 1 and mean == Fraction(9, 8)
    assert call - put == disc * (mean - K), f"gap identity fails at the normalized canary: {call - put}"
    assert lo_c <= call <= hi_c and 0.0 <= put <= K * math.exp(-r * tau)
    assert call - put == 0.125 and call - put != traded_spread, (
        f"traded parity held at a normalized wrong-drift law (mean={mean}): "
        f"the drift hypothesis is NOT load-bearing and the Lean statement is over-claimed"
    )


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


# BRIEF_013 witness sets (the brief's numeric contract, tau = 1 throughout):
# (label, C, G, M, Y, target r-q, expected theta*, expected range half-width H).
ESSCHER_SETS = [
    ("A", 1.0, 5.0, 10.0, 0.7, 0.05, 2.381041, 2.932381),
    ("B", 1.0, 2.0, 8.0, 1.5, 0.05, 2.531499, 8.561606),
    ("C", 0.5, 0.05, 1.0, 0.3, 0.05, -0.021865, 0.848811),
    ("D", 1.0, 0.5, 3.0, 1.9, 0.05, 0.752775, 22.837027),
]


def test_esscher_drift():
    """BRIEF_013 (numerical shadow of `ImprovedBS/Esscher.lean`).

    Every assertion names the Lean declaration it shadows. The Esscher tilt
    is the shift psi^theta(v) = psi(v - i theta) - psi(-i theta), which for
    CGMY stays inside the family -- `(G, M) |-> (G+theta, M-theta)`
    (`esscher_cgmy_shift`); the drift g(theta) = kappa(theta+1) - kappa(theta)
    is antisymmetric about theta0 = (M-G-1)/2 (`esscherDriftMap_reflect`),
    strictly monotone on the admissible interval
    (`esscherDriftMap_strictMono`), and the strip decides solvability of the
    martingale equation g(theta) = r - q: exactly one theta when
    `|r-q| < H` (`esscher_exists_unique_of_mem_range`), none at and beyond
    (`esscher_no_solution_of_outside_range`), with
    `H = |C Gamma(-Y)| |(G+M)^Y - (G+M-1)^Y - 1|` (`esscherDriftBound`).
    The witness sets are the brief's numeric contract; the solver is the
    bisection of `esscher_solve` (200 steps), so residuals sit at ~1e-13 and
    the 1e-12 tolerances carry a 10x margin.
    """
    # --- family closure `esscher_cgmy_shift`: the shift equals the exponent
    # at shifted rates, for EVERY v (term algebra, no branch hypothesis)
    grid = [(1.0, 5.0, 10.0, 0.7), (1.0, 2.0, 8.0, 1.5), (0.5, 0.05, 1.0, 0.3),
            (1.0, 0.5, 3.0, 1.9), (0.5, 3.0, 1.0, 1.7), (1.0, 1.0, 2.0, 0.99)]
    worst = 0.0
    for C, G, M, Y in grid:
        for frac in (0.05, 0.25, 0.5, 0.75, 0.95):
            theta = -G + frac * (M - 1.0 + G)
            for v in (2.0 + 0j, 1j, -3.0 + 0.5j, 0.0 + 0j,
                      0.3 + 0.2j, -1.5 + 0.4j, -0.8j):
                a = esscher_exponent(C, G, M, Y, theta, v)
                b = cgmy_exponent(C, G + theta, M - theta, Y, v)
                worst = max(worst, abs(a - b) / max(1.0, abs(b)))
    assert worst <= 1e-10, worst

    for label, C, G, M, Y, target, theta_exp, H_exp in ESSCHER_SETS:
        H = esscher_drift_bound(C, G, M, Y)
        th0 = esscher_theta_zero(G, M)
        width = M - 1.0 + G
        # `esscherDriftBound_pos`, and the brief's H values
        assert H > 0.0, label
        assert abs(H - H_exp) < 1e-4, (label, H)
        # `esscher_theta_zero_unique`: theta0 is admissible, and its drift is 0
        assert -G < th0 < M - 1.0, label
        assert abs(esscher_drift_map(C, G, M, Y, th0)) < 1e-12, label
        # `esscherDriftMap_bound_eq`: the edge values are exactly ±H
        assert abs(esscher_drift_map(C, G, M, Y, M - 1.0) - H) < 1e-12, label
        assert abs(esscher_drift_map(C, G, M, Y, -G) + H) < 1e-12, label
        # `esscherDriftMap_reflect`: antisymmetry about theta0
        for f in (0.05, 0.15, 0.3):
            t = f * width
            s = (esscher_drift_map(C, G, M, Y, th0 + t)
                 + esscher_drift_map(C, G, M, Y, th0 - t))
            assert abs(s) < 1e-11, (label, t, s)
        # `esscherDriftMap_strictMono`: a strict-monotonicity sweep
        prev = None
        for i in range(401):
            theta = -G + (i + 0.5) / 401.0 * width
            g = esscher_drift_map(C, G, M, Y, theta)
            if prev is not None:
                assert g > prev, (label, i, prev, g)
            prev = g
        # `esscher_exists_unique_of_mem_range`: the witness solve
        th = esscher_solve(C, G, M, Y, target)
        assert th is not None, label
        assert -G < th < M - 1.0, label
        assert abs(th - theta_exp) < 1e-4, (label, th)
        assert abs(esscher_drift_map(C, G, M, Y, th) - target) <= 1e-12, label
        # `esscherExponent_neg_I_eq`: the COMPLEX route at v = -i is real and
        # equals the delivered drift; both bases are positive reals there
        z = esscher_exponent(C, G, M, Y, th, -1j)
        assert abs(z.imag) < 1e-12, (label, z.imag)
        assert abs(z.real - target) <= 1e-12, label
        assert M - th - 1.0 > 0.0 and G + th + 1.0 > 0.0, label
        z2 = cgmy_exponent(C, G + th, M - th, Y, -1j)
        assert abs(z2 - z) < 1e-12, label
        # `esscher_drift_factor`: exp(tau psi^theta(-i)) = exp(tau (r-q)), tau = 1
        fac = cgmy_char_factor(C, G + th, M - th, Y, 1.0, -1j)
        assert abs(fac - cmath.exp(target)) < 1e-12, label
        # `esscher_tilted_numeraire`: the numeraire sits in the TILTED strip
        assert 1.0 < M - th, label
        # `esscher_correction_invariant`: c' carries G + M, which the tilt fixes
        c0 = cgmy_tempered_correction(C, G, M, Y)
        c1 = cgmy_tempered_correction(C, G + th, M - th, Y)
        assert abs(c1 - c0) < 1e-13 * max(1.0, c0), label

    # --- consumption in `esscher_cmPriceKernel_integrable`, set A at alpha=1.5:
    # the tilted contour is legal, and the decay bound holds past the shifted
    # threshold -- r and c' tilt-invariant, K0 at the shifted rates
    _, C, G, M, Y, target, _, _ = ESSCHER_SETS[0]
    th = esscher_solve(C, G, M, Y, target)
    alpha = 1.5
    assert alpha + 1.0 < M - th
    r = cgmy_tempered_rate(C, Y)
    cp = cgmy_tempered_correction(C, G, M, Y)
    K0 = cgmy_tempered_constant(C, G + th, M - th, Y)
    u0 = cgmy_decay_threshold(C, G + th, M - th, Y)
    for u in (u0, 1.7 * u0, 12.0 * u0, 2000.0):
        re_psi = cgmy_contour_re(C, G + th, M - th, Y, alpha, u)
        bound = -r * u ** Y + cp * u ** (Y - 1.0) + K0
        assert re_psi <= bound + 1e-9, (u, re_psi, bound)
        f = cgmy_char_factor(C, G + th, M - th, Y, 1.0,
                             cgmy_pricing_contour_v(alpha, u))
        assert abs(f) <= math.exp(-0.5 * r * u ** Y) + 1e-12, u

    # --- `esscher_no_solution_of_outside_range`: set A, target beyond H
    H_A = esscher_drift_bound(C, G, M, Y)
    assert 3.0324 > H_A
    assert esscher_solve(C, G, M, Y, 3.0324) is None

    # --- empty admissible interval: G + M <= 1 makes (-G, M-1) empty
    assert not (-0.3 < 0.5 - 1.0)
    assert esscher_solve(1.0, 0.3, 0.5, 0.7, 0.05) is None

    # --- strong tilt: set A at target 0.4 -- the tilted contour condition
    # `alpha + 1 < M - theta` binds at alpha = M - theta - 1 = 4.1729
    th4 = esscher_solve(C, G, M, Y, 0.4)
    assert th4 is not None
    assert abs(th4 - 4.8271) < 1e-3, th4
    assert abs((M - th4) - 5.1729) < 1e-3, M - th4
    assert abs((M - th4 - 1.0) - 4.1729) < 1e-3


# (G, M, sigma, r, q, alpha, tau) for BRIEF_014. Every case satisfies the
# corner's hypotheses: 0 < G, 1 < M, 0 < sigma, 0 < alpha, alpha + 1 < M, and
# 1 < G + M (the shifted rates satisfy alpha + 1 < M' too -- checked inside).
CORNER_CASES = (
    (3.0, 3.0, 0.20, 0.05, 0.02, 0.30, 0.8),
    (0.5, 1.8, 0.65, -0.01, 0.02, 0.20, 1.2),
    (5.0, 8.0, 0.37, 0.05, 0.00, 0.40, 2.0),
)
# Y approaches 2 from BELOW. Nothing here evaluates the pole.
CORNER_EPSILONS = (0.1, 0.01, 0.001, 0.0001)


def _corner_uncorrected(sigma: float, G: float, M: float, v: complex) -> complex:
    """`−(σ²/2)v² + i(σ²/2)(G−M)v` -- expanded from `B₂(v) = −2v² + 2i(G−M)v`.

    The bracket at `Y = 2`, by hand: NOT a CGMY evaluation, so the comparison
    has two independent sides.
    """
    half = sigma * sigma / 2.0
    return 1j * half * (G - M) * v - half * v * v


def _corner_gbm(sigma: float, carry: float, v: complex) -> complex:
    """The risk-neutral GBM log exponent `i(carry − σ²/2)v − (σ²/2)v²`.

    Independent of the CGMY oracle: it is the polynomial the corner is
    supposed to land on, written down from the model, not from `cgmy_exponent`.
    """
    half = sigma * sigma / 2.0
    return 1j * (carry - half) * v - half * v * v


def _corner_rel(actual: complex, expected: complex) -> float:
    return abs(actual - expected) / (1.0 + abs(expected))


def test_gbm_corner():
    """BRIEF_014 (numerical shadow of `ImprovedBS/Corner.lean`).

    The corner is a ONE-SIDED limit at a scale, and this test is built so
    that all three ways of getting it wrong are loud:

      * the bare corner (`Y -> 2` at fixed `C`) DIVERGES, because `Γ(−Y)` has
        a pole there (ledger C17) -- asserted below as a canary, and the
        reason `corner_scale` exists at all;
      * the scale must be `(σ²/2)(2−Y)` (`cgmyCornerC`, oracle
        `corner_scale`): doubling it gives twice the variance (mutant M22);
      * the forward normalization must subtract the cumulant
        (`cornerForwardExponent`, oracle `corner_forward_exponent`): without
        it the tempering asymmetry `G − M` survives the limit (mutant M23).

    What is asserted, per Lean declaration:

      `cgmyCornerGamma_eq` / `cgmyCornerGamma_tendsto`
          the stable recurrence `ε Γ(−Y) = Γ(3−Y)/(Y(Y−1))` agrees with the
          oracle's own reflection-form `Γ(−Y)` (no `sin(πY)` in the stable
          route), and `C_Y Γ(−Y) → σ²/4` at the measured rate;
      `cgmyCornerExponent_tendsto` / `cornerForwardExponent_tendsto` /
      `cornerForwardFactor_tendsto`
          the raw, normalized and factorized routes converge to their
          independently expanded targets, with the error shrinking in `ε`;
      `cornerForward_numeraire` / `cornerForwardFactor_numeraire`
          `Ψ_Y(−i) = r − q` and `exp(τ Ψ_Y(−i)) = exp(τ(r−q))` EXACTLY at
          every `Y` (tolerance-free up to Float round-off);
      `cornerEsscherZero_numeraire` / `cornerEsscherZero_exponent` /
      `cornerEsscherZero_tendsto`
          `θ₀ = (M−G−1)/2` solves the Esscher equation exactly at every `Y`,
          the tilted exponent vanishes at `v = −i`, the shift equals the
          exponent at the shifted rates, and the tilted route converges to
          the ZERO-CARRY GBM exponent with no drift correction at all;
      `cornerEsscherBound_tendsto`
          `H → (σ²/2)(G+M−1)`.

    Measured, not assumed: the residuals shrink ~O(ε) on this grid (worst
    1.0e-4 at ε = 1e-4, from the range route), which a wrong scale or a
    missing drift correction cannot do -- those sit at O(1)·|v|.
    """
    results = []
    for eps in CORNER_EPSILONS:
        Y = 2.0 - eps
        worst = dict(coefficient=0.0, uncorrected=0.0, kappa1=0.0, gbm=0.0,
                     factor=0.0, esscher_zero=0.0, esscher_range=0.0, closure=0.0)
        for G, M, sigma, r, q, alpha, tau in CORNER_CASES:
            assert G > 0.0 and M > 1.0 and sigma > 0.0 and alpha > 0.0
            assert alpha + 1.0 < M and G + M > 1.0
            C = corner_scale(sigma, Y)          # `cgmyCornerC`, the scale under test
            half = sigma * sigma / 2.0
            carry = r - q

            # --- `cgmyCornerGamma_eq`: reflection form vs the two recurrences,
            # evaluated WITHOUT sin(pi Y) on the stable side.
            prefactor = C * cgmy_gamma_neg(Y)
            stable_prefactor = half * math.gamma(3.0 - Y) / (Y * (Y - 1.0))
            worst["coefficient"] = max(worst["coefficient"],
                                       _corner_rel(prefactor, stable_prefactor))

            # --- `cgmyCornerCumulant_one_tendsto`: the REAL cumulant route
            kappa1 = cgmy_cumulant(C, G, M, Y, 1.0)
            worst["kappa1"] = max(worst["kappa1"],
                                  _corner_rel(kappa1, half * (G - M + 1.0)))
            # `cgmy_numeraire_strip` / `cgmyExponent_strip`: u = 1 needs 1 < M
            assert abs(cgmy_exponent(C, G, M, Y, -1j) - kappa1) < 1e-10

            # --- route B: theta0 is EXACTLY the zero-drift parameter at every Y
            theta0 = esscher_theta_zero(G, M)
            assert -G < theta0 < M - 1.0
            assert abs(esscher_drift_map(C, G, M, Y, theta0)) < 1e-10
            tilted_G, tilted_M = G + theta0, M - theta0
            assert tilted_G > 0.0 and tilted_M > 1.0
            worst["esscher_range"] = max(
                worst["esscher_range"],
                _corner_rel(esscher_drift_bound(C, G, M, Y), half * (G + M - 1.0)))

            points = (0j, 1 + 0j, -2 + 0j, 1.25 - 0.8j, -1j,
                      cgmy_pricing_contour_v(alpha, 1.1))
            for v in points:
                assert -M < v.imag < G and -tilted_M < v.imag < tilted_G
                raw = cgmy_exponent(C, G, M, Y, v)
                worst["uncorrected"] = max(worst["uncorrected"],
                                           _corner_rel(raw, _corner_uncorrected(sigma, G, M, v)))
                # route A: the forward normalization, from the oracle so that
                # a dropped `-kappa(1)` (M23) is reachable from this test.
                normalized = corner_forward_exponent(C, G, M, Y, r, q, v)
                target = _corner_gbm(sigma, carry, v)
                worst["gbm"] = max(worst["gbm"], _corner_rel(normalized, target))
                worst["factor"] = max(worst["factor"],
                                      _corner_rel(cmath.exp(tau * normalized),
                                                  cmath.exp(tau * target)))
                # route B: no drift correction, carry 0
                esscher = esscher_exponent(C, G, M, Y, theta0, v)
                worst["esscher_zero"] = max(
                    worst["esscher_zero"],
                    _corner_rel(esscher, _corner_gbm(sigma, 0.0, v)))
                worst["closure"] = max(
                    worst["closure"],
                    _corner_rel(esscher, cgmy_exponent(C, tilted_G, tilted_M, Y, v)))

            # --- `cornerForward_numeraire` / `cornerForwardFactor_numeraire`:
            # exact at every Y, on the ORIGINAL (unshifted) exponent.
            norm_num = corner_forward_exponent(C, G, M, Y, r, q, -1j)
            assert abs(norm_num - carry) < 1e-10, (eps, norm_num)
            assert abs(cmath.exp(tau * norm_num) - math.exp(tau * carry)) < 1e-10
            # --- `cornerEsscherZero_exponent` / `_numeraire`: exact at every Y
            assert abs(esscher_exponent(C, G, M, Y, theta0, -1j)) < 1e-10
            assert abs(cgmy_char_factor(C, tilted_G, tilted_M, Y, tau, -1j) - 1.0) < 1e-10
        results.append(worst)

    # Convergence has a measurable rate on this grid; a wrong scale or a
    # missing drift correction sits at O(1) and does not shrink.
    for key in ("uncorrected", "kappa1", "gbm", "factor", "esscher_zero",
                "esscher_range"):
        assert results[-1][key] < 0.15 * results[-2][key], (key, results[-1][key])
    assert results[-1]["uncorrected"] < 1e-3, results[-1]["uncorrected"]
    assert results[-1]["gbm"] < 1e-3, results[-1]["gbm"]
    assert results[-1]["esscher_zero"] < 1e-3, results[-1]["esscher_zero"]
    # `cgmyCornerGamma_eq` is an identity, and the shift is term algebra.
    assert max(row["coefficient"] for row in results) < 1e-9
    assert max(row["closure"] for row in results) < 1e-9

    # --- the pole is not a value. `Y = 2` must stay outside the domain.
    try:
        cgmy_exponent(0.1, 3.0, 3.0, 2.0, 1 + 0j)
    except ValueError:
        pass
    else:
        raise AssertionError("the oracle evaluated Gamma(-2) at its pole")

    # --- CANARY 1: at FIXED C the bare corner diverges (ledger C17). With
    # G = M the bracket tends to -2, so Re psi(1) ~ -C/(2-Y).
    fixed_C = 0.35
    wide = cgmy_exponent(fixed_C, 3.0, 3.0, 1.9, 1 + 0j).real
    near = cgmy_exponent(fixed_C, 3.0, 3.0, 1.999, 1 + 0j).real
    assert near < 20 * wide < 0.0, (wide, near)
    assert abs(0.001 * near + fixed_C) < 1e-3, near

    # --- CANARY 2: sending G, M to sigma^2/2 at fixed Y is NOT the corner.
    # With G = M the real part of any Gaussian exponent scales like v^2, so
    # the ratio at frequencies 2 and 1 would be exactly 4, whatever the drift.
    rate = 1.5 ** 2 / 2.0                      # 1.125 > 1: the numeraire fits
    at_one = cgmy_exponent(0.2, rate, rate, 1.5, 1 + 0j).real
    at_two = cgmy_exponent(0.2, rate, rate, 1.5, 2 + 0j).real
    assert abs(at_two / at_one - 4.0) > 0.2, at_two / at_one

    # --- CANARY 3: the two seeded cheats, measured. Doubling the scale
    # doubles the variance; omitting -kappa(1) leaves G - M in the drift.
    G = M = 3.0
    sigma, carry, v, eps = 0.75, 0.03, 2 + 0j, 0.0001
    Y = 2.0 - eps
    C = corner_scale(sigma, Y)
    target = _corner_gbm(sigma, carry, v)
    correct = corner_forward_exponent(C, G, M, Y, carry, 0.0, v)
    doubled = corner_forward_exponent(2.0 * C, G, M, Y, carry, 0.0, v)
    uncorrected = cgmy_exponent(C, G, M, Y, v) + 1j * carry * v
    assert abs(correct - target) < 1e-3, abs(correct - target)
    assert abs(doubled - target) > 0.8, abs(doubled - target)
    assert abs(uncorrected - target) > 0.4, abs(uncorrected - target)



def _log_quad(f, a: float, b: float, n: int = 40000) -> float:
    """Trapezoid rule in `u = log x` on `[a, b]`, `a > 0` -- resolves power tails."""
    la, lb = math.log(a), math.log(b)
    h = (lb - la) / n
    total = 0.0
    for i in range(n + 1):
        x = math.exp(la + i * h)
        w = 0.5 if i in (0, n) else 1.0
        total += w * f(x) * x
    return total * h


def test_pareto_witness():
    """BRIEF_015 (numerical shadow of `ImprovedBS/ParetoWitness.lean`).

    Asserted, per Lean declaration:

      upstream `lintegral_paretoPDF_eq_one`
          the density integrates to 1 (quadrature to 1e6 t + the analytic tail);
      `paretoMeasure_Ici`
          a quadrature of `pareto_pdf` over `[x, inf)` equals the independent
          closed form `pareto_tail` -- to relative 1e-5, at `t != 1` included;
      `pareto_tail_lower_bound`
          `htail` at `c = t^r, alpha = r, x0 = t` holds WITH EQUALITY. Equality,
          not `>=`: at `t = 2` the constant swap `t^r -> t^(-r)` still satisfies
          the inequality (gap +0.875), so only equality kills mutant M25;
      `pareto_exp_moment_infinite` (via Levy.lean)
          the lower-bound sequence `e^x (t/x)^r` at `x = 2^k` and the partial
          moments `int_t^R e^x pdf` are unbounded, including at `r = 3` (F3);
      `dirac_tail_hypothesis_fails` / `dirac_exp_integrable` (the species)
          exponential and Gaussian laws have finite `E[e^X]` and FAIL `htail`.
    """
    grid = [(t, r) for t in (0.5, 1.0, 2.0) for r in (0.5, 1.0, 1.5, 3.0)]
    for t, r in grid:
        B = t * 1e6
        mass = _log_quad(lambda x: pareto_pdf(t, r, x), t, B) + pareto_tail(t, r, B)
        assert abs(mass - 1.0) < 1e-6, (t, r, mass)
        for k in (0, 2, 5):
            x = 1.37 * t * 2 ** k
            q = _log_quad(lambda y: pareto_pdf(t, r, y), x, x * 1e6, 20000) + pareto_tail(t, r, x * 1e6)
            closed = pareto_tail(t, r, x)
            assert abs(q - closed) / closed < 1e-5, (t, r, x, q, closed)
            # htail with equality at c = t^r, alpha = r, x0 = t
            assert abs(pareto_tail(t, r, x) - t ** r * x ** (-r)) < 1e-12
        assert pareto_tail(t, r, t) == 1.0 or abs(pareto_tail(t, r, t) - 1.0) < 1e-12
    # equality at t != 1 is what the weak mutant cannot fake
    for t in (0.5, 2.0):
        for x in (t, 3 * t, 10 * t):
            assert abs(pareto_tail(t, 1.5, x) - t ** 1.5 * x ** (-1.5)) < 1e-12

    # divergence: the Levy.lean lower bound and the partial moments
    for t, r in ((1.0, 0.5), (1.0, 3.0)):
        lb = [math.exp(2 ** k) * pareto_tail(t, r, 2 ** k) for k in range(3, 7)]
        assert all(b > a for a, b in zip(lb, lb[1:])) and lb[-1] > 1e20, lb
    partial = [_log_quad(lambda x: math.exp(x) * pareto_pdf(1.0, 1.5, x), 1.0, R, 20000)
               for R in (10.0, 20.0, 40.0)]
    assert partial[0] < partial[1] < partial[2] and partial[2] > 1e12, partial

    # canaries: finite exponential moment AND htail fails
    for lam in (2.0, 5.0):
        assert abs(_log_quad(lambda x: math.exp(x) * lam * math.exp(-lam * x), 1e-9, 60.0)
                   - lam / (lam - 1.0)) < 1e-3
        assert math.exp(-lam * 100.0) < 1e-6 * 100.0 ** (-3.0)
    gauss_tail = 0.5 * math.erfc(20.0 / math.sqrt(2.0))
    assert gauss_tail < 1e-60 * 20.0 ** (-10.0)




# ---------------------------------------------------------------------------
# BRIEF_016: the EXTERNAL anchor (published constants, quoted, not computed)
# and the term-structure falsifier.
#
# Carr, P. and Madan, D. B. (1999), "Option valuation using the fast Fourier
# transform", Journal of Computational Finance 2(4), 61-73, DOI
# 10.21314/JCF.1999.043, Section 5 (the sentence introducing Figure 2) and that
# figure's error table. Case 4: S0 = 100, r = 0.05, q = 0.03, sigma = 0.25,
# nu = 2.0, theta = -0.10, t = 0.25.
#
# The three VALUES below are the prices the paper reports (agreed by VGP /
# VGFIC / TV to four decimals). They are quoted from the paper, not recomputed
# here -- nothing in this file derives them -- and they are the PUT (OTM, or
# call-time-value) column: the K = 77 call is ~ 23.84, so 0.6356 cannot be a
# call. The paper ALSO prints its own failing VGPS (Pi1/Pi2) route at the same
# three strikes, which makes a free negative control: those three numbers must
# stay rejected.
#
# The market side of the falsifier (F5): El Amrani and Guyon, "Does the term
# structure of the at-the-money skew really follow a power law?" (Risk, Cutting
# Edge; two years of SPX / SX5E / DAX) gives alpha = 0.43 / 0.44 / 0.45 above
# three to four weeks and 0.19 / 0.04 / 0.08 below (the short end does not blow
# up); Gatheral, Jaisson and Rosenbaum, Quantitative Finance 18(6) (2018),
# state the same law as alpha in (0.3, 0.5) with an SPX fit of tau^(-0.44). The
# market band below is the intersection of those citations, pinned as a
# literal so widening it is a visible diff.
#
# The model side's asymptotic rate is tau^(-1), NOT tau^(-1/2) (ledger C19:
# Figueroa-Lopez, Forde and Jacquier, "The large-time smile and skew for
# exponential Levy models", Proposition 4.1). The measured exponents below are
# what the test pins, and the two bands are DISJOINT -- that is the RED.
# ---------------------------------------------------------------------------

CARR_MADAN_1999_CASE4_PARAMS = dict(
    sigma=0.25, nu=2.0, theta=-0.10, tau=0.25, S=100.0, r=0.05, q=0.03
)
# Section 5, the sentence introducing Figure 2: the OTM/put column.
CARR_MADAN_1999_CASE4 = ((77.0, 0.6356), (78.0, 0.6787), (79.0, 0.7244))
# The same paper's wrong VGPS row at the same strikes (the free mutant).
CARR_MADAN_1999_VGPS_WRONG = (0.2425, 0.2299, 1.5386)

MODEL_SKEW_EXPONENT_BAND = (0.90, 1.15)   # measured; the family's rate is 1 (C19)
MARKET_SKEW_EXPONENT_BAND = (0.30, 0.50)  # El Amrani-Guyon / Gatheral et al.
VG_SKEW_EXPONENT = 1.0857                 # measured at the pinned window/settings
CGMY_SKEW_EXPONENT = 0.9682
SKEW_EXPONENT_TOL = 0.02
SKEW_WINDOW = (0.25, 0.5, 1.0, 2.0, 5.0)  # the pinned window starts at 0.25: the
                                          # short end is h-sensitive (BRIEF_016 §2)
ANCHOR_ALPHA = 1.5
ANCHOR_U_MAX = 2000.0
ANCHOR_N = 80000
ANCHOR_H = 0.005
ANCHOR_QUAD_GRID = (
    (1000.0, 40000), (1000.0, 80000),
    (2000.0, 40000), (2000.0, 80000),
    (4000.0, 40000), (4000.0, 80000),
)


def test_term_structure_anchor():
    """BRIEF_016: the published anchor (A1-A5) and the term-structure falsifier (F1-F4).

    Anchors the oracle to the one genuinely external table it has -- Carr-Madan
    (1999) Case 4, which is this tree's own method AND the `Y = 0` (variance-
    gamma) corner of its CGMY family -- and pins the measured ATM-skew decay
    exponents that make the dynamic half of the T6 direction a documented
    failure. What is asserted:

      A1  the model's PUTS reproduce the three published literals to 5e-5 by
          BOTH parameterizations (VG `(sigma, nu, theta)` and the CGMY `Y = 0`
          corner `(C, G, M)`), so the F3 map is load-bearing;
      A2  the CALLS at the same strikes do NOT (the call is ~ 23.84 against a
        ~ 0.64 literal), so a call/put convention slip cannot pass;
      A3  the paper's own WRONG VGPS row stays rejected by >= 0.3;
      A4  parity at the anchor's numbers: the model call inverted to a BS
          implied vol and repriced by the oracle's own `bs_put` agrees with the
          parity put to 1e-9 (the bisection floor);
      A5  `nu -> 0` recovers GBM at the measured rate `err/nu -> 2.31`;
      F1  the measured skew exponents are within 0.02 of their pinned literals
          and inside the model band;
      F2  the model band and the market band are DISJOINT (0.90 > 0.50) -- the
          RED in machine-checkable form;
      F3  `|psi|*tau` stays inside [0.04, 0.35] on the window (the `1/tau`
          law), while `|psi|*sqrt(tau)` falls by more than a factor of 2 on the
          CGMY witness set -- the `tau^(-1/2)` reading is not what the family
          does;
      F4  the fitted exponent moves by <= 0.002 across the pinned quadrature
          grid, so the RED is not a quadrature artifact;
      canary  the same measurement run on the CLOSED-FORM instance with a
          prescribed `tau^(-1/2)` skew returns 0.5, and the flat instance
          returns 0 -- the machinery can see a different power law, and it does
          not hallucinate one. (The closed form is NOT the falsifier's target;
          the CF-priced family is -- and mutants M26-M29 live here.)
    """
    P = CARR_MADAN_1999_CASE4_PARAMS
    sigma, nu, theta, tau = P["sigma"], P["nu"], P["theta"], P["tau"]
    S, r, q = P["S"], P["r"], P["q"]
    C, G, M = cgmy_zeroth_corner_map(sigma, nu, theta)

    # --- the F3 map: one place, and its content is the two cumulants
    assert abs(C - 1.0 / nu) < 1e-15, C
    assert abs(C * (1.0 / M - 1.0 / G) - theta) < 1e-12, (C, G, M)
    assert abs(C * (1.0 / M ** 2 + 1.0 / G ** 2) - (sigma ** 2 + nu * theta ** 2)) < 1e-12
    assert 1.0 < M, f"the numeraire condition 1 < M fails: M = {M}"

    def vg_route(t):
        return lambda v: vg_exponent(sigma, nu, theta, t, r, q, v)

    def corner_route(t):
        return lambda v: t * cgmy_zeroth_forward_exponent(C, G, M, r, q, v)

    # the two parameterizations are the SAME law: exponents agree pointwise...
    for v in (0.0, 1.0, -1.5, 2.0, complex(1.0, -2.5), complex(-0.5, 1.0)):
        a = vg_exponent(sigma, nu, theta, tau, r, q, v)
        b = tau * cgmy_zeroth_forward_exponent(C, G, M, r, q, v)
        assert abs(a - b) <= 1e-12 * max(1.0, abs(a)), (v, a, b)
    # ...and the risk-neutral normalization is exact: psi(-i) = (r - q) tau
    assert abs(vg_exponent(sigma, nu, theta, tau, r, q, -1j) - (r - q) * tau) < 1e-12
    # kappa_0(1) = psi_0(-i) is real (it equals -omega of the VG parameterization)
    assert abs(cgmy_zeroth_exponent(C, G, M, -1j).imag) < 1e-15

    # --- A1/A2/A3/A4: the published literals, both routes, plus the controls
    for route_name, route in (("vg", vg_route), ("corner", corner_route)):
        for (K, published), vgps_wrong in zip(CARR_MADAN_1999_CASE4, CARR_MADAN_1999_VGPS_WRONG):
            call = carr_madan_by_exponent(
                route(tau), S, K, tau, r, q, ANCHOR_ALPHA, ANCHOR_U_MAX, ANCHOR_N
            )
            put = call - S * math.exp(-q * tau) + K * math.exp(-r * tau)
            assert abs(put - published) <= 5e-5, (route_name, K, put, published)
            assert abs(call - published) > 1.0, (route_name, K, call, published)   # A2
            assert abs(put - vgps_wrong) >= 0.3, (route_name, K, put, vgps_wrong)  # A3
            iv = implied_vol_bs(call, S, K, tau, r, q)
            assert abs(bs_put(S, K, tau, r, q, iv) - put) < 1e-9, (route_name, K)  # A4

    # --- A5: nu -> 0 is GBM, at the measured rate err/nu -> 2.31
    gbm = bs_call(S, 100.0, tau, r, q, sigma)
    errors, rates = [], []
    for nu_small in (0.2, 0.05, 0.01, 0.002, 0.0004):
        call = carr_madan_by_exponent(
            lambda v, nu_=nu_small: vg_exponent(sigma, nu_, theta, tau, r, q, v),
            S, 100.0, tau, r, q, ANCHOR_ALPHA, ANCHOR_U_MAX, ANCHOR_N,
        )
        errors.append(abs(call - gbm))
        rates.append(errors[-1] / nu_small)
    assert all(b < a for a, b in zip(errors, errors[1:])), errors
    assert rates[-1] > rates[0] + 0.2, rates
    assert abs(rates[-1] - 2.31) < 0.05, rates

    # --- F1/F2/F3: the two witness sets, the window, the disjoint bands
    def cgmy_route(t):
        return lambda v: t * corner_forward_exponent(1.0, 5.0, 10.0, 0.7, 0.0, 0.0, v)

    witnesses = (
        ("VG case 4", vg_route, r, q, VG_SKEW_EXPONENT),
        ("CGMY(1,5,10,.7)", cgmy_route, 0.0, 0.0, CGMY_SKEW_EXPONENT),
    )
    skews_by_set = {}
    for name, family, rr, qq, literal in witnesses:
        skews = [atm_skew(family, S, t, rr, qq, ANCHOR_H, ANCHOR_ALPHA, ANCHOR_U_MAX, ANCHOR_N)
                 for t in SKEW_WINDOW]
        skews_by_set[name] = skews
        assert all(s < 0.0 for s in skews), (name, skews)
        fit = power_law_fit(SKEW_WINDOW, skews)
        assert MODEL_SKEW_EXPONENT_BAND[0] <= fit <= MODEL_SKEW_EXPONENT_BAND[1], (name, fit)
        assert abs(fit - literal) <= SKEW_EXPONENT_TOL, (name, fit, literal)
        scaled = [abs(s) * t for s, t in zip(skews, SKEW_WINDOW)]
        assert all(0.04 <= x <= 0.35 for x in scaled), (name, scaled)

    assert MODEL_SKEW_EXPONENT_BAND[0] > MARKET_SKEW_EXPONENT_BAND[1], "the bands must be disjoint"
    assert MODEL_SKEW_EXPONENT_BAND[0] - MARKET_SKEW_EXPONENT_BAND[1] >= 0.4

    half = [abs(s) * math.sqrt(t) for s, t in zip(skews_by_set["CGMY(1,5,10,.7)"], SKEW_WINDOW)]
    assert all(b < a for a, b in zip(half, half[1:])), half
    assert half[0] / half[-1] > 2.0, half

    # --- F4: the exponent is quadrature-independent on the pinned grid
    fits = [power_law_exponent(vg_route, S, r, q, SKEW_WINDOW, ANCHOR_H, ANCHOR_ALPHA, um, n)
            for um, n in ANCHOR_QUAD_GRID]
    assert max(fits) - min(fits) <= 0.002, (ANCHOR_QUAD_GRID, fits)

    # --- canary: the measurement can see a DIFFERENT power law
    canary_sigma, canary_c = 0.30, -0.6

    def prescribed_skew(t):
        F = S * math.exp((r - q) * t)

        def iv(k):
            return canary_sigma * (1.0 + canary_c * k * t ** -0.5)

        vols = []
        for k in (-ANCHOR_H, ANCHOR_H):
            K = F * math.exp(k)
            vols.append(implied_vol_bs(bs_call(S, K, t, r, q, iv(k)), S, K, t, r, q))
        return (vols[1] - vols[0]) / (2.0 * ANCHOR_H)

    canary_fit = power_law_fit(SKEW_WINDOW, [prescribed_skew(t) for t in SKEW_WINDOW])
    assert abs(canary_fit - 0.5) < 0.01, canary_fit

    def flat_route(t):
        return lambda v: 1j * (r - q - 0.5 * sigma ** 2) * t * v - 0.5 * sigma ** 2 * t * v * v

    flat = [atm_skew(flat_route, S, t, r, q) for t in SKEW_WINDOW]
    assert max(abs(x) for x in flat) < 1e-6, flat


# BRIEF_018 witness sets (the brief's numeric contract; tau = 0.25, S = K = 100,
# r = 0.05, q = 0.03 throughout):
# (label, C, G, M, theta*, kappa0(1), mgf(1), tilted call, tilted put).
# Witness A is the anchor's own F3 map of (sigma, nu, theta) = (0.25, 2.0, -0.10);
# the test derives it through `cgmy_zeroth_corner_map` and pins the mapped triple.
VG_SETS = [
    ("A", 0.5, 2.708131845707604, 5.908131845707604, 1.463508761,
     -0.0644164359214842, 0.9840248688965743, 2.749188832359, 2.254163399833),
    ("B", 0.5, 5.0, 10.0, 3.095836730,
     -0.03848052056806412, 0.9904259952806018, 1.705678682076, 1.210653249550),
]
VG_TAU, VG_R, VG_Q, VG_S, VG_K = 0.25, 0.05, 0.03, 100.0, 100.0


def _gamma_integral_quad(a: float, n: int = 20000) -> float:
    """`Gamma(a) = (1/a) int_0^inf exp(-z^(1/a)) dz` by Simpson -- the
    `z = x^a` substitution, which removes the `x^(a-1)` singularity at the
    origin for `a < 1`. The independent route for `gammaMeasure_mgf`'s
    Gamma integral (the rate scaling is exact algebra, asserted alongside)."""
    zmax = 40.0 ** a
    h = zmax / n
    tot = 1.0 + math.exp(-(zmax ** (1.0 / a)))
    for i in range(1, n):
        tot += math.exp(-((i * h) ** (1.0 / a))) * (4 if i % 2 else 2)
    return tot * h / 3.0 / a


def test_vg_law():
    """BRIEF_018 (numerical shadow of `ImprovedBS/VGLaw.lean`).

    Every assertion names the Lean declaration it shadows. The variance-gamma
    law is the difference of the two Gamma laws `Gamma(C*tau, M)` and
    `Gamma(C*tau, G)` (`vgLaw`), so its mgf on the landed strip `-G < u < M`
    is `exp(tau * kappa_0(u))` with `kappa_0(u) = C[log(M/(M-u)) +
    log(G/(G+u))]` (`vgLaw_mgf`, via the two-Gamma factorization); the corner
    `psi_Y -> psi_0` is a LIMIT (`vg_corner`), never an evaluation (Lean's
    `Real.Gamma 0 = 0` makes a raw `Y = 0` evaluation silently the Dirac law
    -- the canary below pins its signature); the Esscher tilt at the law level
    is the family member at the shifted rates (`vg_tilt_cumulant_shift`); and
    at the drift solution the tilted law is a martingale law
    (`vg_drift_identity`, item 3) whose Carr-Madan price sits inside the
    model-free bounds (`vg_modelFree_*`, item 5) -- the first non-Gaussian law
    in the tree that discharges BRIEF_009's hypotheses by construction.
    """
    tau, r, q, S, K = VG_TAU, VG_R, VG_Q, VG_S, VG_K

    # --- the Gamma rung (`gammaMeasure_mgf`): quadrature at the singular
    # shape a = 0.125 against `math.gamma`, plus the exact rate scaling
    g = _gamma_integral_quad(0.125)
    assert abs(g - math.gamma(0.125)) / math.gamma(0.125) <= 1e-9, g
    assert abs(gamma_mgf(2.5, 3.0, 1.0) - (3.0 / 2.0) ** 2.5) < 1e-15
    try:
        gamma_mgf(1.0, 2.0, 2.0)
        raise AssertionError("gamma_mgf must refuse u >= r")
    except ValueError:
        pass

    # --- witness A is the anchor's Case-4 triple through the F3 map, and
    # `kappa_0(1) = -omega` is the bridge to the VG parameterization (F3)
    C_A, G_A, M_A = cgmy_zeroth_corner_map(0.25, 2.0, -0.10)
    _, C_exp, G_exp, M_exp = VG_SETS[0][:4]
    for got, exp in ((C_A, C_exp), (G_A, G_exp), (M_A, M_exp)):
        assert abs(got - exp) < 1e-12, (got, exp)
    omega = math.log(1.0 - (-0.10) * 2.0 - 0.5 * 0.25 * 0.25 * 2.0) / 2.0
    assert abs(vg_cumulant(C_A, G_A, M_A, 1.0) + omega) < 1e-12, omega

    for label, C, G, M, th_exp, k1_exp, m1_exp, call_exp, put_exp in VG_SETS:
        # `vgCumulant` pinned, and real on the strip by construction
        k1 = vg_cumulant(C, G, M, 1.0)
        assert abs(k1 - k1_exp) < 1e-12, (label, k1)
        # the two-Gamma factorization (`integral_prod_mul`): the law's mgf is
        # the product of the Gamma mgfs at `u` and `-u`
        for u in (-G + 0.05, -0.5, 0.0, 0.5, 1.0, (M - 1.0) / 2.0, M - 0.05):
            lhs = vg_mgf(C, G, M, tau, u)
            rhs = gamma_mgf(C * tau, M, u) * gamma_mgf(C * tau, G, -u)
            assert abs(lhs - rhs) < 1e-14 * max(1.0, rhs), (label, u, lhs, rhs)
        # the bridge to the complex corner (`vgCumulant_eq_corner_re` at u = 1):
        # `exp(tau * psi_0(-i))` is real and equals the mgf at 1
        bridge = cmath.exp(tau * cgmy_zeroth_exponent(C, G, M, -1j))
        m1 = vg_mgf(C, G, M, tau, 1.0)
        assert abs(bridge.imag) < 1e-14, (label, bridge)
        assert abs(bridge.real - m1) < 1e-14, (label, bridge, m1)
        assert abs(m1 - m1_exp) < 1e-12, (label, m1)
        # theta0 is admissible with drift 0 (the Y = 0 reflection fixed point)
        th0 = esscher_theta_zero(G, M)
        assert -G < th0 < M - 1.0, label
        assert abs(vg_drift_map(C, G, M, th0)) < 1e-12, label
        # the drift solve: theta*, its residual, and the derived numeraire
        th = vg_esscher_solve(C, G, M, r - q)
        assert th is not None, label
        assert -G < th < M - 1.0, label
        assert abs(th - th_exp) < 1e-6, (label, th)
        assert abs(vg_drift_map(C, G, M, th) - (r - q)) <= 1e-12, label
        assert 1.0 < M - th, label
        # `vg_drift_identity` (item 3): the tilted mgf at 1 is `exp(tau (r-q))`,
        # both via the shifted cumulant and via the mgf ratio
        target = math.exp(tau * (r - q))
        tilted = math.exp(tau * vg_tilted_cumulant(C, G, M, th, 1.0))
        assert abs(tilted - target) <= 1e-12, (label, tilted, target)
        ratio = vg_mgf(C, G, M, tau, 1.0 + th) / vg_mgf(C, G, M, tau, th)
        assert abs(ratio - target) <= 1e-12, (label, ratio, target)
        # `vg_tilt_cumulant_shift`: the shift identity on a (theta, u) grid,
        # and the closure at the solution
        for theta in (th0, 0.0, th):
            for u in (-0.5, 0.25, 1.0):
                a = vg_tilted_cumulant(C, G, M, theta, u)
                b = vg_cumulant(C, G, M, u + theta) - vg_cumulant(C, G, M, theta)
                assert abs(a - b) <= 1e-12, (label, theta, u, a, b)
        assert abs(vg_drift_map(C, G, M, th)
                   - vg_tilted_cumulant(C, G, M, th, 1.0)) <= 1e-12, label
        # item 5: the Carr-Madan call at the TILTED law (pinned grid), inside
        # the model-free bounds, with the put through parity inside its own
        lower = S * math.exp(-q * tau) - K * math.exp(-r * tau)
        upper = S * math.exp(-q * tau)
        putcap = K * math.exp(-r * tau)
        assert abs(lower - 0.49502543252569353) < 1e-9, lower
        assert abs(upper - 99.25280548191384) < 1e-9, upper
        assert abs(putcap - 98.75778004938815) < 1e-9, putcap
        expf = lambda v, C=C, G=G, M=M, th=th: (  # noqa: E731
            tau * cgmy_zeroth_exponent(C, G + th, M - th, v))
        call = carr_madan_by_exponent(expf, S, K, tau, r, q,
                                      alpha=1.5, u_max=2000.0, n=80000)
        assert abs(call - call_exp) < 1e-6, (label, call)
        assert lower < call < upper, (label, call)
        # not the silent Dirac: a raw Y = 0 evaluation (exponent identically 0)
        # prices the discounted intrinsic 0.0 here, an O(1) miss
        assert abs(call - 0.0) > 1.0, (label, call)
        put = call - lower
        assert abs(put - put_exp) < 1e-6, (label, put)
        assert 0.0 <= put <= putcap, (label, put)

    # --- `vg_corner`: |psi_Y - psi_0|/Y stays finite as Y -> 0, i.e. O(Y)
    for C, G, M, v, lo, hi, first, last in (
            (0.5, 5.0, 10.0, 1.0, 0.07, 0.14, 0.1343, 0.0764),
            (0.5, 5.0, 10.0, 3.0, 0.24, 0.46, 0.4480, 0.2527),
            (1.0, 3.0, 6.0, 1.0, 0.16, 0.29, 0.2796, 0.1734),
            (1.0, 3.0, 6.0, 3.0, 0.65, 1.10, 1.0808, 0.6659)):
        psi0 = cgmy_zeroth_exponent(C, G, M, complex(v))
        prev, Y = None, 0.5
        for _ in range(7):
            ratio = abs(cgmy_exponent(C, G, M, Y, complex(v)) - psi0) / Y
            assert lo < ratio < hi, (C, G, M, v, Y, ratio)
            if prev is not None:
                assert ratio < prev, (C, G, M, v, Y, ratio, prev)
            prev = ratio
            Y /= 2.0
        assert abs(abs(cgmy_exponent(C, G, M, 0.5, complex(v)) - psi0) / 0.5
                   - first) < 1e-3, (C, G, M, v)
        assert abs(abs(cgmy_exponent(C, G, M, 1.0 / 128.0, complex(v)) - psi0)
                   * 128.0 - last) < 1e-3, (C, G, M, v)

    # --- the published-factor identity (F2): the law's mgf IS the no-drift VG
    # factor `(1 - theta nu u - sigma^2 nu u^2/2)^(-tau/nu)` at witness A
    C, G, M = C_A, G_A, M_A
    worst = 0.0
    for i in range(11):
        u = -G + 0.05 + (M + G - 0.1) * i / 10.0
        pub = (1.0 - (-0.10) * 2.0 * u - 0.5 * 0.25 * 0.25 * 2.0 * u * u) ** (-tau / 2.0)
        got = vg_mgf(C, G, M, tau, u)
        worst = max(worst, abs(got - pub) / abs(pub))
    assert worst <= 1e-12, worst

    # --- the strip is enforced, and the solve has no solution only when the
    # interval itself is empty (no `esscher_no_solution` twin at Y = 0: F4)
    try:
        vg_cumulant(0.5, 5.0, 10.0, 10.0)
        raise AssertionError("vg_cumulant must refuse u = M")
    except ValueError:
        pass
    assert vg_esscher_solve(1.0, 0.3, 0.5, 0.05) is None

    # --- canary (R1): the sigma -> 0 GBM call is the FORWARD intrinsic, pinned
    # as an equality -- the raw-Y=0 Dirac prices the discounted intrinsic
    # instead (0.0 at S = K), so a Y = 0 evaluation cannot pass it
    fwd = S * math.exp(-q * tau) - K * math.exp(-r * tau)
    assert abs(bs_call(S, K, tau, r, q, 1e-12) - fwd) < 1e-9
    assert abs(bs_call(S, K, tau, r, q, 1e-12) - 0.49502543252569353) < 1e-9
    fwd90 = S * math.exp(-q * tau) - 90.0 * math.exp(-r * tau)
    assert abs(bs_call(S, 90.0, tau, r, q, 1e-12) - fwd90) < 1e-9
    assert abs(bs_call(S, 90.0, tau, r, q, 1e-12) - 10.370803437464502) < 1e-9


def test_compound_poisson():
    """BRIEF_019 (numerical shadow of `ImprovedBS/CompoundPoisson.lean`).

    Two constructions, each checked against a side that is NOT a re-derivation
    of it:

      * the Poisson mixture `sum_n p_n rho^{*n}` -- powers accumulated one
        multiplication at a time -- against `cexp (lam (phi(t) - 1))`, the shape
        `charFun_cpLaw` proves. At `lam = 0.5, 2.5` the closed side IS mathlib's
        shipped `charFun_map_cast_poissonMeasure` (`exp (lam (e^{it} - 1))`), so
        that row checks the machinery against a shipped object;
      * the truncated CGMY jump law on `{|x| >= eps}` (`cgmyJumpLaw`): its mass
        against the density integral (an independent log-substituted mesh) and
        against the `2C/Y eps^{-Y}` asymptote, its exponent against the landed
        `cgmy_exponent` at the rates F3 predicts, and the marginal
        `cexp (tau A_eps)` against the mixture (`charFun_cgmyCpLaw`).

    The truncation is the whole story. `lambda_eps` grows like `eps^{-Y}`, so
    `eps -> 0` is a CONDITIONAL-convergence statement and NOT dominated
    convergence (F3); the symmetric truncation has error `eps^{2-Y}` while the
    one-sided half-line moves `eps^{1-Y}` -- decaying for `Y < 1`, DIVERGENT for
    `Y > 1`. The canary below asserts that divergence: it is a different family
    (F2), not an approximation error, and it is why `{|x| >= eps}` is the only
    truncation the module may write (lint R4). `A_eps` is Bochner-integrable
    because it lives on the truncated set -- it is a plain `∫`, not an improper
    integral.

    `A_eps` is the cutoff of `psi_Y` in the same sense that BRIEF_018's `vgLaw`
    is the `Y -> 0` corner: the corner row checks `|A_eps - psi_0| / Y`
    (`psi_0` = `cgmy_zeroth_exponent`, tied to `vg_exponent` in
    `test_vg_law`); the F6 row checks that "compensate everywhere" is a
    *translated* law -- a different target -- and not a choice of notation.

    The last block MEASURES the five cheat classes (mutants M34-M38 in
    `tests/test_mutants.py`), so "this test kills them" is a number and not an
    adjective. Metric: the log-scale separation of the corrupted witness from
    its route-check value (the exponent displacement, since every CF here is
    `exp` of an exponent).
    """
    C, G, M, tau = 0.5, 5.0, 10.0, 0.25
    delta1_cf = lambda t: cmath.exp(1j * t)

    def sym_err(Y, eps, v):
        """`|A_eps - psi_Y|`: the symmetric truncation error (F3's rate)."""
        return abs(cgmy_truncated_exponent(C, G, M, Y, eps, v)
                   - cgmy_exponent(C, G, M, Y, complex(v)))

    def one_err(Y, eps, v):
        """The FORBIDDEN one-sided error, against the one-sided closed form."""
        return abs(C * _cgmy_truncated_leg(M, Y, eps, v, True)
                   - cgmy_exponent_one_sided(C, M, Y, complex(v)))

    def slope3(Y, v, f):
        """Log-log slope of `f` against `eps` over {1e-4, 1e-3, 1e-2}.

        Evenly spaced in `log eps`, so the three-point least-squares slope is
        the mean of the two decade slopes -- the route-check's definition.
        """
        return (math.log(abs(f(Y, 1e-2, v))) - math.log(abs(f(Y, 1e-4, v)))) / (2.0 * math.log(10.0))

    def mass_by_density(Y, eps, n=4000):
        """`int_{|x| >= eps} cgmyLevyDensity C G M Y x dx`: third route.

        `u = log(x/eps)` turns the `x^{-1-Y}` growth at the cutoff into the
        smooth `eps^{-Y} e^{-Y u}`, so this mesh shares no structure with the
        dyadic panels of `_cgmy_truncated_leg`. Both legs go through the
        module's own `cgmy_levy_density`, so a rate/sign change there is caught
        here (the two legs are summed in quadrature, not in the density).
        """
        total = 0.0
        u_max = math.log(60.0 / eps)
        for sign in (1.0, -1.0):
            def f(u, sign=sign):
                x = sign * eps * math.exp(u)
                return cgmy_levy_density(C, G, M, Y, x) * eps * math.exp(u)
            total += _simpson(f, 0.0, u_max, n)
        return total

    # --- the weights: log space (the rate reaches 20656, where `exp(-lam)`
    # underflows and `lam^n` overflows before `n!` cancels either), against the
    # closed form `e^{-lam} lam^n / n!` at a rate where both are representable,
    # and the omitted mass against its Chernoff bound.
    for lam in (0.5, 2.5, 5164.028168615301, 20656.112674461205):
        w, tail = poisson_weights(lam)
        total = math.fsum(w)
        assert abs(total - 1.0) <= 1e-12, (lam, total)
        assert 1.0 - total <= tail + 1e-12, (lam, tail)
        assert max(w) > 0.0 and min(w) >= 0.0, lam
    w30, _ = poisson_weights(30.0)
    worst = max(abs(q - math.exp(-30.0 + n * math.log(30.0) - math.lgamma(n + 1.0)))
                for n, q in enumerate(w30))
    assert worst <= 1e-13, worst

    # --- `charFun_cpLaw` at `rho = delta_1`.
    worst = 0.0
    for lam in (0.5, 2.5):
        for t in (0.3, 1.7, -2.2):
            mix, tail = cp_law_cf_mixture(lam, delta1_cf, t)
            closed = cp_law_cf_closed(lam, delta1_cf, t)
            worst = max(worst, abs(mix - closed))
            assert abs(mix - closed) <= max(1e-13, tail), (lam, t, mix, closed, tail)
    assert worst <= 3.5e-16, worst

    # --- `charFun_cgmyCpLaw`: the same identity at the truncated jump law,
    # with rates that reach 2e4 terms. The closed side is `cexp (lam (phi-1))`
    # with `lam = lambda_eps`; the residual is floating-point summation, and it
    # does not degrade with the rate.
    worst, at = 0.0, None
    for Y in (0.7, 1.5):
        for eps in (1e-2, 1e-3):
            lam = cgmy_jump_mass(C, G, M, Y, eps)
            jcf = (lambda t, Y=Y, eps=eps: cgmy_jump_cf(C, G, M, Y, eps, t))
            for v in (0.5, 2.0):
                mix, tail = cp_law_cf_mixture(lam, jcf, v)
                closed = cp_law_cf_closed(lam, jcf, v)
                if abs(mix - closed) > worst:
                    worst, at = abs(mix - closed), (Y, eps, v, lam)
                assert abs(mix - closed) <= 1e-13, (Y, eps, v)
    assert worst <= 1e-13 and at[3] > 2e4, (worst, at)

    # --- the mass row: `lambda_eps -> infinity` like `2C/Y eps^{-Y}`, asserted
    # against the closed form (so a later "simplification" cannot restore a
    # DCT-shaped proof of the `eps -> 0` step), and against the density route.
    for Y, slope, lam4 in ((0.5, 0.546475, 190.58166067128686),
                           (1.5, 1.507914, 665216.6196349466)):
        l3 = cgmy_jump_mass(C, G, M, Y, 1e-3)
        l4 = cgmy_jump_mass(C, G, M, Y, 1e-4)
        assert abs((math.log(l4) - math.log(l3)) / math.log(10.0) - slope) <= 1e-6, (Y, l3, l4)
        assert abs(l4 - lam4) <= 1e-3, (Y, l4)
        asym = 2.0 * C / Y * (1e-4) ** (-Y)
        assert 0.95 <= l4 / asym <= 1.0, (Y, l4 / asym)
        assert l4 >= 3.0 * l3, (Y, l3, l4)         # the mass grows with every decade of cutoff
        by_density = mass_by_density(Y, 1e-3)
        assert abs(by_density - l3) <= 1e-8 * l3, (Y, by_density, l3)

    # --- the truncation error: `|A_eps - psi_Y| ~ eps^{2-Y}` (symmetric: the
    # only truncation R4 allows).
    for Y, want in ((0.5, 1.4904), (1.5, 0.4947)):
        for v in (0.5, 2.0):
            got = slope3(Y, v, sym_err)
            assert abs(got - want) <= 1e-4, (Y, v, got)

    # --- the canary: the ONE-SIDED truncation is a different family. For
    # `Y = 1/2` the error still decays (slope 1 - Y); for `Y = 3/2` it GROWS
    # like `eps^{-1/2}` -- that divergence is the row, not a value mismatch.
    for v in (0.5, 2.0):
        got = slope3(0.5, v, one_err)
        assert abs(got - 0.4929) <= 1e-4, (0.5, v, got)
        got = slope3(1.5, v, one_err)
        assert abs(got + 0.4798) <= 1e-4, (1.5, v, got)
        assert got < 0.0, (1.5, v, got)

    # --- F6: "compensate everywhere" is a TRANSLATED law, not a convention.
    for Y, m_inf in ((0.5, -0.116083169), (1.5, -1.641663919)):
        m = C * cgmy_gamma_neg(Y) * Y * (G ** (Y - 1.0) - M ** (Y - 1.0))
        assert abs(m - m_inf) <= 1e-9, (Y, m)
        for v in (0.5, 1.0, 2.0):
            w = complex(v)
            lhs = cgmy_exponent(C, G, M, Y, w) - 1j * w * m
            rhs = (cgmy_exponent_one_sided_compensated(C, M, Y, w)
                   + cgmy_exponent_one_sided_compensated(C, G, Y, -w))
            assert abs(lhs - rhs) <= 1.2e-15 * max(1.0, abs(lhs)), (Y, v, lhs, rhs)
    Y, eps = 1.5, 1e-3
    m = C * cgmy_gamma_neg(Y) * Y * (G ** (Y - 1.0) - M ** (Y - 1.0))
    for v in (1.0, 2.0):
        A = cgmy_truncated_exponent(C, G, M, Y, eps, v)
        shifted = cmath.exp(tau * (A - 1j * v * m))
        translated = cmath.exp(-1j * v * tau * m) * cmath.exp(tau * A)
        assert abs(shifted - translated) <= 1e-15 * max(1.0, abs(translated))
        assert abs(shifted - cmath.exp(tau * A)) >= 0.1, (v, shifted)

    # --- the corner: `psi_0` is BRIEF_018's `vgLaw` exponent, and the cutoff
    # error against it is `O(1)` in `Y` after the `1/Y` scaling of the corner.
    for v, want in ((0.5, 0.037511), (2.0, 0.158055)):
        A = cgmy_truncated_exponent(C, G, M, 1e-3, 1e-4, v)
        psi0 = cgmy_zeroth_exponent(C, G, M, complex(v))
        got = abs(A - psi0) / 1e-3
        assert abs(got - want) <= 1e-5, (v, got)

    # --- the mutant witness, (Y, eps, v) = (1.5, 1e-3, 1).
    Y, eps, v = 1.5, 1e-3, 1.0
    lam = cgmy_jump_mass(C, G, M, Y, eps)
    rate = tau * lam
    A = cgmy_truncated_exponent(C, G, M, Y, eps, v)
    assert abs(lam - 20656.112674461205) <= 1e-6, lam
    assert abs(A - (-0.306170169269563 - 1.4797187232987774j)) <= 1e-9, A
    truth = cmath.exp(tau * A)                 # the marginal's exponent is tau*A, NOT rate*A
    assert abs(truth - (0.8636509648070771 - 0.3349085281853914j)) <= 1e-12, truth
    mix, _ = cp_law_cf_mixture(rate, lambda t: cgmy_jump_cf(C, G, M, Y, eps, t), v)
    assert abs(mix - truth) <= 1e-11, (mix, truth)

    # the jump law IS a probability law, the integrand vanishes at `v = 0`, and
    # BOTH legs of the density are present: three structural rows that no
    # quadrature can satisfy by accident.
    assert abs(cgmy_jump_cf(C, G, M, Y, eps, 0.0) - 1.0) <= 1e-13
    assert abs(cgmy_truncated_exponent(C, G, M, Y, eps, 0.0)) <= 1e-15
    leg_pos = C * _cgmy_truncated_leg(M, Y, eps, v, True)
    leg_neg = C * _cgmy_truncated_leg(G, Y, eps, -v, True)
    assert abs(A - (leg_pos + leg_neg)) <= 1e-15 * max(1.0, abs(A))

    # --- the cheat classes, measured (log-scale separations).
    # M36: the `-1` of the integrand is dropped; the mass the `-1` cancels
    # comes back and displaces the exponent by exactly `lambda_eps`.
    A_plus_mass = _cgmy_truncated_sum(C, G, M, Y, eps, v, False, False)
    sep_m36 = tau * abs(A_plus_mass - A)
    assert abs(sep_m36 - 5164.028168615301) <= 1e-6, sep_m36

    # M37: the tempering legs are swapped; the exponent moves against a scale
    # of `|tau A|`.
    A_sw = C * (_cgmy_truncated_leg(G, Y, eps, v, True)
                + _cgmy_truncated_leg(M, Y, eps, -v, True))
    sep_m37 = abs(tau * (A_sw - A))
    assert abs(sep_m37 - 0.7398593616493887) <= 1e-6, sep_m37
    assert abs(abs(tau * A) - 0.377765442489741) <= 1e-9

    # M38: the forbidden one-sided truncation: the error against the ONE-SIDED
    # closed form is the canary's `eps^{1-Y}` divergence, `tau`-scaled.
    A_one = C * _cgmy_truncated_leg(M, Y, eps, v, True)
    sep_m38 = tau * abs(A_one - cgmy_exponent_one_sided(C, M, Y, complex(v)))
    assert abs(sep_m38 - 7.984621002490288) <= 1e-4, sep_m38

    # M35: the jump law is not normalised, so its CF at 0 is the mass
    # `lambda_eps` instead of 1 and the marginal reads `exp (rate (lam - 1))`.
    sep_m35 = abs(rate * (mass_by_density(Y, eps) - 1.0))
    assert abs(sep_m35 - 106663583.68) <= 0.1, sep_m35

    # M34: the `1/n!` is dropped from the log-space weight recursion; the
    # weights stop being Poisson weights and the mixture stops being
    # `exp (rate (phi - 1))`.
    def no_factorial_weights(lam):
        n_max = int(math.ceil(lam + 12.0 * math.sqrt(lam) + 12.0))
        logs = [-lam]
        for n in range(1, n_max + 1):
            logs.append(logs[-1] + math.log(lam))       # <- no `- log n`
        top = max(logs)
        ws = [math.exp(l - top) for l in logs]
        total = math.fsum(ws)
        return [q / total for q in ws]

    acc, power = 0.0 + 0.0j, 1.0 + 0.0j
    phi = cgmy_jump_cf(C, G, M, Y, eps, v)
    for q in no_factorial_weights(rate):
        acc += q * power
        power *= phi
    sep_m34 = abs(cmath.log(acc) - tau * A)
    assert 1e-3 <= sep_m34 <= 0.2, sep_m34
    acc1, power = 0.0 + 0.0j, 1.0 + 0.0j
    for q in no_factorial_weights(2.5):
        acc1 += q * power
        power *= delta1_cf(0.3)
    assert abs(acc1 - cp_law_cf_closed(2.5, delta1_cf, 0.3)) >= 0.5


def test_cgmy_law():
    """BRIEF_020 (numerical shadow of `ImprovedBS/CGMYLaw.lean`).

    Stage 2b takes the `eps -> 0` limit of BRIEF_019's truncated exponent and
    lands it as the exponent of a law. Three routes meet here, and every row
    below compares two that are NOT re-derivations of each other:

      * `cgmy_truncated_exponent` -- the LANDED `A_eps`, an integral of
        `e^{ivx} - 1` over `{|x| >= eps}` (BRIEF_019's route);
      * `cgmy_compensated_exponent` + `cgmy_paired_drift` -- the Levy-Khintchine
        split `B_eps + i v d_eps`, quadratured from its own integrands, with the
        `eps = 0` limit supplied by dyadic panels down to `2^-60` PLUS the
        analytic `int_0^{inner}` of the same integrand;
      * `cgmy_exponent` / `cgmy_drift_identity_closed` / `gamma_integral_complex_rate`
        -- the closed forms: a difference of `Gamma(-Y)` values, the Frullani-type
        drift `C Gamma(1-Y)(M^{Y-1} - G^{Y-1})`, and the complex-rate Gamma
        integral G1 `int_0^inf x^{s-1} e^{-zx} dx = Gamma(s) z^{-s}`.

    The rows, in the order the Lean module proves them:

      1. THE DECOMPOSITION (F1, correction C25). `A_eps = B_eps + i v d_eps` is
         an IDENTITY at every `eps > 0`, not a limit. Checked twice: on the unit
         ball with both routes on the same dyadic mesh -- where the identity
         holds node by node, so the residual is rounding (`8.2e-15`) -- and over
         the whole line with independent meshes, which is what proves it is not
         a mesh artifact (`5.2e-10`, the two routes' far-field difference).
      2. THE TWO LIMITS (F1). `B_eps -> B_0` and `d_eps -> d_0` along
         `eps_n = 2^-n`, both at the rate `eps^{2-Y}`: deep-end slopes
         `1.4996 / 0.9997 / 0.4998` at `Y = 1/2, 1, 3/2`. The drift is NOT zero
         (`d_0 = -0.115465 / -0.346002 / -1.641132`) -- that is C25.
      3. THE IDENTIFICATION (F5). `L = B_0 + i v d_0` against the landed closed
         form `psi_Y`, and against the same closed form reassembled from the two
         one-sided compensated legs plus `i v m^inf`.
      4. `Y = 1` IS NOT A POLE OF THE LAW (F2). `L` is finite there and the
         closed form approaches it from both sides at `O(delta)`: the pole is
         the FORMULA's, so the law's range is all of `0 < Y < 2`.
      5. G1 (F4). The complex-rate Gamma integral at `z = M - i v`, `G + i v`
         and the real anchor `z = M`, where mathlib's shipped lemma lives.
      6. THE IBP CHAINS (F5). The one-sided uncompensated and fully compensated
         integrals against BRIEF_011's pinned closed forms.
      7. THE DRIFT IDENTITY (F5, real rate). `d_0 + d_far = m^inf`, three ways:
         the split at 1 by quadrature, the `Gamma(1-Y)` closed form, and (for
         `Y < 1`, where each leg converges on its own) two G1 integrals.
      8. THE CF LADDER (F8). `Re A_eps < 0` all along the ladder and
         `|e^{tau A_eps} - e^{tau L}| <= tau |A_eps - L|` -- the CF convergence
         is no slower than the exponent's, which is why `Tendsto.cexp` suffices
         in the Lean proof and no second estimate is needed.
      9. THE TIGHTNESS PROXY (F3). mathlib's own bound
         `(R/2) int_{-2/R}^{2/R} (1 - Re phi_n(t)) dt`: monotone in `n`,
         converging to the limit law's value, decreasing in `R`. That is
         tightness, measured.
     10. THE `Y -> 0` END (F7). `|L - psi_0| / Y` against BRIEF_018's `vgLaw`
         corner `cgmy_zeroth_exponent`.
     11. THE FIVE CHEAT CLASSES, measured (mutants M39-M43). The one that
         matters is M39: the UNPAIRED drift leg `C int_eps^1 x^{-Y} e^{-Mx} dx`
         does not converge at all -- `122.47` at `eps = 2^-14` and growing like
         `eps^{1-Y}` (deep-end slope `-0.5011`) -- while the paired integrand
         sits at `-1.6021`, within `0.04` of `d_0`. Only the difference is
         integrable at 0 for `Y >= 1`; that is lint clause `[CGMYLaw]` R2.

    Metric for row 11: the displacement of the corrupted exponent from its
    route-check value, since every CF here is `exp` of an exponent.
    """
    C, G, M, tau = 0.5, 5.0, 10.0, 0.25
    NP = 400  # Simpson points per dyadic panel; the error goes like n^{-4}

    # --- 1. the decomposition, an identity at every eps (F1 / C25).
    # Ball-restricted with a SHARED mesh: the integrand identity
    # `e^{ivx} - 1 = (e^{ivx} - 1 - ivx) + ivx` holds at every quadrature node,
    # so the two routes' panel errors cancel and what is left is rounding.
    worst_ball, worst_full, at = 0.0, 0.0, None
    for Y in (0.5, 1.0, 1.5):
        for v in (0.5, 2.0):
            for eps in (1e-1, 1e-2, 1e-3):
                A = cgmy_truncated_exponent(C, G, M, Y, eps, v, x_max=1.0, n_panel=NP)
                B = cgmy_compensated_exponent(C, G, M, Y, eps, v, x_max=1.0, n_panel=NP)
                d = cgmy_paired_drift(C, G, M, Y, eps, n_panel=NP)
                r = abs(A - (B + 1j * v * d))
                if r > worst_ball:
                    worst_ball, at = r, (Y, v, eps, abs(A))
                assert r <= 1e-13, (Y, v, eps, r)
                # ... and with INDEPENDENT meshes over the whole line, where the
                # only disagreement left is the two routes' far-field meshes.
                A2 = cgmy_truncated_exponent(C, G, M, Y, eps, v, n_panel=200)
                B2 = cgmy_compensated_exponent(C, G, M, Y, eps, v, n_panel=NP)
                d2 = cgmy_paired_drift(C, G, M, Y, eps, n_panel=200)
                worst_full = max(worst_full, abs(A2 - (B2 + 1j * v * d2)))
    assert worst_ball <= 5e-14, (worst_ball, at)   # ~15 ulp of |A| ~ 3.2
    assert worst_full <= 2e-9, worst_full

    # --- 2. the two limits, and the rate `eps^{2-Y}` (F1).
    def deep_slope(f, n_lo=12, n_hi=14):
        """Log-log slope of `f(2^-n)` over the last two rungs: the asymptotic rate."""
        a, b = f(2.0 ** -n_lo), f(2.0 ** -n_hi)
        return (math.log(abs(b)) - math.log(abs(a))) / ((n_lo - n_hi) * math.log(2.0))

    d0_ref = {0.5: -0.115465, 1.0: -0.346002, 1.5: -1.641132}
    for Y in (0.5, 1.0, 1.5):
        v0 = 0.5
        b0 = cgmy_compensated_exponent(C, G, M, Y, 0.0, v0, n_panel=NP)
        d0 = cgmy_paired_drift(C, G, M, Y, 0.0, n_panel=NP)
        # the drift is finite, nonzero and negative -- C25's correction.
        assert abs(d0 - d0_ref[Y]) <= 2e-6, (Y, d0)
        assert d0 < -0.1, (Y, d0)
        for tag, f in (("B", lambda e, Y=Y, v0=v0: cgmy_compensated_exponent(
                            C, G, M, Y, e, v0, n_panel=NP) - b0),
                       ("d", lambda e, Y=Y: cgmy_paired_drift(
                            C, G, M, Y, e, n_panel=NP) - d0)):
            slope = deep_slope(f)
            assert abs(slope - (2.0 - Y)) <= 5e-3, (tag, Y, slope)

    # --- 3. the identification L = psi_Y, two closed-form routes (F5).
    worst_ident = 0.0
    for Y in (0.5, 1.5):
        for v in (0.5, 2.0):
            L = cgmy_lk_exponent(C, G, M, Y, v, n_panel=NP)
            psi = cgmy_exponent(C, G, M, Y, complex(v))
            worst_ident = max(worst_ident, abs(L - psi))
            assert abs(L - psi) <= 2e-11, (Y, v, abs(L - psi))
            assembled = cgmy_lk_exponent_via_one_sided(C, G, M, Y, v)
            # the same closed form reassembled from its one-sided pieces plus the
            # far-field drift: algebraically identical, so this pins that the
            # drift term is the one that closes the identification.
            assert abs(assembled - psi) <= 1e-12, (Y, v, abs(assembled - psi))
            assert abs(assembled - L) <= 2e-11, (Y, v, abs(assembled - L))
    assert worst_ident <= 7e-12, worst_ident

    # --- 4. Y = 1: the pole is the formula's, not the law's (F2).
    for v in (0.5, 2.0):
        L1 = cgmy_lk_exponent(C, G, M, 1.0, v, n_panel=NP)
        assert abs(L1) < 1.0 and math.isfinite(L1.real) and math.isfinite(L1.imag), L1
        err = {}
        for delta in (1e-3, 1e-4):
            for sgn in (1.0, -1.0):
                err[(delta, sgn)] = abs(
                    cgmy_exponent(C, G, M, 1.0 + sgn * delta, complex(v)) - L1)
        for sgn in (1.0, -1.0):
            # O(delta) and not O(1) or O(delta^2): a decade in delta buys a
            # decade in the residual, from BOTH sides of the pole. `Gamma(-Y)`
            # has a simple pole at Y = 1 whose residue the bracket cancels, and
            # what is left is the law's honest integral.
            ratio = err[(1e-3, sgn)] / err[(1e-4, sgn)]
            assert 9.0 <= ratio <= 11.0, (v, sgn, ratio)
    L1_half = cgmy_lk_exponent(C, G, M, 1.0, 0.5, n_panel=NP)
    assert abs(L1_half - complex(-0.018727, -0.172975)) <= 2e-6, L1_half

    # --- 5. G1, the complex-rate Gamma integral (F4).
    worst_g1 = 0.0
    for s in (0.5, 1.5):
        for v in (0.5, 2.0):
            for z in (M - 1j * v, G + 1j * v, complex(M)):
                q = gamma_integral_complex_rate(s, z, n_panel=NP)
                closed = math.gamma(s) * z ** (-s)
                worst_g1 = max(worst_g1, abs(q - closed))
                assert abs(q - closed) <= 5e-12, (s, z, abs(q - closed))
    # the residual is the quadrature's, not the identity's: the real anchor
    # (where mathlib's shipped real-rate lemma lives) is no better.
    real_anchor = abs(gamma_integral_complex_rate(0.5, complex(M), n_panel=NP)
                      - math.gamma(0.5) * M ** -0.5)
    assert worst_g1 <= 5e-12 and real_anchor <= 2e-12, (worst_g1, real_anchor)

    # --- 6. the IBP chains from G1 (F5): the two one-sided closed forms.
    for v in (0.5, 2.0):
        unc = cgmy_one_sided_exponent_integral(M, 0.5, v, n_panel=NP)
        assert abs(unc - cgmy_exponent_one_sided(1.0, M, 0.5, complex(v))) <= 5e-12, v
        comp = cgmy_one_sided_compensated_integral(M, 1.5, v, n_panel=NP)
        assert abs(comp - cgmy_exponent_one_sided_compensated(
            1.0, M, 1.5, complex(v))) <= 5e-12, v

    # --- 7. the drift identity, three routes (F5, real rate).
    minf_ref = {0.5: -0.116083169, 1.5: -1.641663919}
    for Y in (0.5, 1.5):
        whole = cgmy_paired_drift(C, G, M, Y, 0.0, n_panel=NP) + cgmy_far_drift(C, G, M, Y)
        minf = cgmy_drift_identity_closed(C, G, M, Y)
        assert abs(minf - minf_ref[Y]) <= 2e-9, (Y, minf)
        assert abs(whole - minf) <= 1e-11, (Y, whole, minf)
        if Y < 1.0:
            # each leg converges on its own here, so G1 gives a third route.
            via_g1 = C * (gamma_integral_complex_rate(1.0 - Y, complex(M), n_panel=NP)
                          - gamma_integral_complex_rate(1.0 - Y, complex(G), n_panel=NP))
            assert abs(via_g1.real - minf) <= 1e-11, (Y, via_g1, minf)

    # --- 8. the CF ladder: exp is 1-Lipschitz on the left half-plane (F8).
    ladder = {}
    for Y in (0.5, 1.5):
        v = 1.0
        L = cgmy_lk_exponent(C, G, M, Y, v, n_panel=200)
        max_re, worst_ratio = -1e9, 0.0
        for n in range(1, 15):
            A = cgmy_truncated_exponent(C, G, M, Y, 2.0 ** -n, v, n_panel=200)
            max_re = max(max_re, A.real)          # must stay < 0 (F8)
            gap = abs(A - L)
            ratio = abs(cmath.exp(tau * A) - cmath.exp(tau * L)) / (tau * gap)
            worst_ratio = max(worst_ratio, ratio)
            if n == 14:
                ladder[Y] = gap
        assert max_re < 0.0, (Y, max_re)
        assert worst_ratio <= 1.0, (Y, worst_ratio)   # no slower than the exponent
    assert abs(ladder[0.5] - 8.1e-7) <= 4e-7, ladder       # eps^{2-Y} at Y = 1/2
    assert abs(ladder[1.5] - 3.98e-2) <= 2e-2, ladder      # the Y -> 2 degeneration

    # --- 9. the tightness proxy: monotone in n, finite at the limit (F3).
    # mathlib's own estimate, `sup_n mu_n(|X| > R) <= (R/2) int (1 - Re phi_n)`,
    # with `Re phi_n(t) = exp(tau Re A) cos(tau Im A)` -- dropping the cosine is
    # the wrong bound and changes the numbers by up to a factor of 2.
    grid = [j / 40.0 for j in range(41)]      # shared nodes for R = 2 and R = 5

    def re_phi(Y, n, t):
        A = (cgmy_lk_exponent(C, G, M, Y, t, n_panel=100) if n is None else
             cgmy_truncated_exponent(C, G, M, Y, 2.0 ** -n, t, n_panel=100))
        return math.exp(tau * A.real) * math.cos(tau * A.imag)

    def tightness_proxy(Y, n, R):
        k = int(round((2.0 / R) * 40))
        vals = [1.0 - re_phi(Y, n, t) for t in grid[: k + 1]]
        acc = vals[0] + vals[-1]
        for i in range(1, k):
            acc += (4 if i % 2 else 2) * vals[i]
        return (R / 2.0) * 2.0 * acc * (1.0 / 40.0) / 3.0

    limit_ref = {(0.5, 2.0): 0.00471, (0.5, 5.0): 0.00076,
                 (1.5, 2.0): 0.10771, (1.5, 5.0): 0.01788}
    for Y in (0.5, 1.5):
        cache = {}
        for n in (1, 3, 6, 9, 12):
            cache[n] = {R: tightness_proxy(Y, n, R) for R in (2.0, 5.0)}
        lim = {R: tightness_proxy(Y, None, R) for R in (2.0, 5.0)}
        for R in (2.0, 5.0):
            seq = [cache[n][R] for n in (1, 3, 6, 9, 12)]
            # monotone in n and approaching the limit law's value from below.
            # The approach is only `eps_n^{2-Y}`, so at Y = 3/2 the n = 12 rung
            # is still 7% short -- which is the rate row 2 measured, seen again.
            assert all(a <= b + 1e-9 for a, b in zip(seq, seq[1:])), (Y, R, seq)
            assert seq[-1] <= lim[R] + 1e-9, (Y, R, seq[-1], lim[R])
            assert abs(seq[-1] - lim[R]) <= 0.1 * lim[R], (Y, R, seq[-1], lim[R])
            assert abs(seq[0] - lim[R]) > abs(seq[-1] - lim[R]), (Y, R, seq, lim[R])
            assert abs(lim[R] - limit_ref[(Y, R)]) <= 5e-5, (Y, R, lim[R])
        assert lim[5.0] < lim[2.0], (Y, lim)   # decreasing in R: that IS tightness

    # --- 10. the Y -> 0 end against BRIEF_018's vgLaw corner (F7).
    for v, ref in ((0.5, 0.037518), (2.0, 0.158082)):
        prev = None
        for Y in (1e-2, 1e-3):
            ratio = abs(cgmy_lk_exponent(C, G, M, Y, v, n_panel=NP)
                        - cgmy_zeroth_exponent(C, G, M, complex(v))) / Y
            if prev is not None:
                assert abs(ratio - prev) < 0.2 * prev, (v, Y, ratio, prev)  # settling
            prev = ratio
        assert abs(prev - ref) <= 2e-5, (v, prev, ref)

    # --- 11. the five cheat classes, measured (M39-M43).
    Y, v = 1.5, 1.0
    L = cgmy_lk_exponent(C, G, M, Y, v, n_panel=NP)
    psi = cgmy_exponent(C, G, M, Y, complex(v))
    assert abs(L - psi) <= 2e-11, abs(L - psi)          # the reference residual
    d0 = cgmy_paired_drift(C, G, M, Y, 0.0, n_panel=NP)
    minf = cgmy_drift_identity_closed(C, G, M, Y)
    seps = {
        "M39 unpaired drift leg": None,                  # measured below: it DIVERGES
        "M40 drift dropped": abs(v * d0),
        "M41 missing m^inf": abs(v * minf),
        "M42 flipped drift sign": abs(2.0 * v * d0),
        "M43 Gamma(1-Y) -> Gamma(-Y)": abs(
            v * C * (math.gamma(1.0 - Y) - math.gamma(-Y)) * (M ** (Y - 1.0) - G ** (Y - 1.0))),
    }
    for name in ("M40 drift dropped", "M41 missing m^inf",
                 "M42 flipped drift sign", "M43 Gamma(1-Y) -> Gamma(-Y)"):
        assert seps[name] >= 1.0, (name, seps[name])
    assert abs(seps["M40 drift dropped"] - 1.641132) <= 2e-6, seps
    assert abs(seps["M43 Gamma(1-Y) -> Gamma(-Y)"] - 2.736107) <= 2e-6, seps

    def unpaired_drift_leg(eps):
        """`C int_eps^1 x^{-Y} e^{-M x} dx` -- the M leg of the drift ALONE."""
        f = lambda x: math.exp(-M * x) * x ** (-Y)
        edges = [eps * 2.0 ** k for k in range(200) if eps * 2.0 ** k < 1.0]
        edges.append(1.0)
        return C * sum(_simpson(f, a, b, 200) for a, b in zip(edges, edges[1:]))

    leg14 = unpaired_drift_leg(2.0 ** -14)
    assert leg14 > 100.0, leg14                          # 122.47, and growing
    slope14 = (math.log(unpaired_drift_leg(1e-6)) - math.log(unpaired_drift_leg(1e-8))) \
        / (2.0 * math.log(10.0))     # log-log slope in eps: -0.5011, i.e. 1 - Y
    assert abs(slope14 - (1.0 - Y)) <= 2e-2, slope14      # eps^{1-Y}: DIVERGENT
    # ... while the paired integrand converges to the same d_0 the rows above use.
    assert abs(cgmy_paired_drift(C, G, M, Y, 2.0 ** -14, n_panel=200) - d0) <= 0.05


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
