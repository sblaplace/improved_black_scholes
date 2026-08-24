"""
Sanity tests for the BS numeric oracle. These are NOT the artifact (the Lean
formalization is): they exist to make sure the formula we intend to formalize
is the formula we actually wrote, and that it numerically satisfies the
properties the formal theorems claim (parity, PDE identity, boundaries).

Run:  python3 -m pytest tests/   (or:  python3 tests/test_bs.py)
"""

import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from experiments.black_scholes import bs_price, bs_pde_residual, norm_cdf, norm_pdf

# Textbook reference case: S=K=100, r=5%, q=0, sigma=20%, T-t=1yr
S, K, R, Q, SGM, TAU = 100.0, 100.0, 0.05, 0.0, 0.20, 1.0


def test_textbook_call():
    c = bs_price(S, K, TAU, 0.0, R, SGM)
    assert abs(c - 10.4506) < 1e-3, f"call {c} off textbook"


def test_textbook_put():
    p = bs_price(S, K, TAU, 0.0, R, SGM, option="put")
    assert abs(p - 5.5735) < 1e-3, f"put {p} off textbook"


def test_put_call_parity():
    c = bs_price(S, K, TAU, 0.0, R, SGM)
    p = bs_price(S, K, TAU, 0.0, R, SGM, option="put")
    lhs = c - p
    rhs = S * math.exp(-Q * TAU) - K * math.exp(-R * TAU)
    assert abs(lhs - rhs) < 1e-9, f"parity {lhs} vs {rhs}"


def test_pde_residual_vanishes():
    # the closed form must solve the BSM heat equation to ~0
    res = bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "call", h=1e-3)
    assert abs(res) < 1e-3, f"PDE residual {res} not ~0"


def test_pde_residual_refines_with_h():
    r1 = abs(bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "call", h=1e-2))
    r2 = abs(bs_pde_residual(S, K, TAU, 0.0, R, SGM, Q, "call", h=1e-3))
    assert r2 <= r1 + 1e-4  # dying off with h (central diff)


def test_value_bounds():
    c = bs_price(S, K, TAU, 0.0, R, SGM)
    lower = max(S * math.exp(-Q * TAU) - K * math.exp(-R * TAU), 0.0)
    upper = S * math.exp(-Q * TAU)
    assert lower - 1e-9 <= c <= upper + 1e-9


def test_d1_minus_d2():
    from experiments.black_scholes import _d1d2

    d1, d2 = _d1d2(S, K, TAU, R, SGM, Q)
    assert abs((d1 - d2) - SGM * math.sqrt(TAU)) < 1e-12


def test_delta_identity_numerically():
    # S e^{-q tau} phi(d1) == K e^{-r tau} phi(d2)   (the formal T3 hinge)
    from experiments.black_scholes import _d1d2

    d1, d2 = _d1d2(S, K, TAU, R, SGM, Q)
    lhs = S * math.exp(-Q * TAU) * norm_pdf(d1)
    rhs = K * math.exp(-R * TAU) * norm_pdf(d2)
    assert abs(lhs - rhs) < 1e-12


def test_degenerate_spot_zero():
    assert bs_price(0.0, K, TAU, 0.0, R, SGM) == 0.0
    assert bs_price(0.0, K, TAU, 0.0, R, SGM, option="put") == K * math.exp(-R * TAU)


def test_invalid_inputs_raise():
    for kwargs in (
        dict(S=S, K=K, T=TAU, t=TAU, r=R, s=SGM),  # tau=0
        dict(S=S, K=K, T=TAU, t=0.0, r=R, s=0.0),  # sigma=0
    ):
        try:
            bs_price(**kwargs)
            raise AssertionError("expected ValueError")
        except ValueError:
            pass


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