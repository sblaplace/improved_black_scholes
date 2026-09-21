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
    bs_price,
    bs_pde_residual,
    bs_put,
    bs_put_by_expectation,
    bs_put_by_parity,
    forward_by_expectation,
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
