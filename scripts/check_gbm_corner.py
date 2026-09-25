"""Reproducible, dependency-free pre-brief route-check for BRIEF_014.

This is *not* a Lean proof or a CGMY law construction. It evaluates the existing
CGMY and Esscher oracle routes against a polynomial GBM exponent obtained by
expanding the bracket at Y = 2. In particular, it does not extend the oracle's
accepted domain to the pole at Y = 2 or pretend a fixed-C limit exists.

Run from the repository root: python3 scripts/check_gbm_corner.py
"""

from __future__ import annotations

import cmath
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from experiments.black_scholes import (  # noqa: E402
    cgmy_cumulant,
    cgmy_exponent,
    cgmy_gamma_neg,
    cgmy_pricing_contour_v,
    esscher_drift_bound,
    esscher_drift_map,
    esscher_exponent,
    esscher_theta_zero,
)

# (G, M, sigma, r, q, alpha, tau); alpha + 1 < M and G + M > 1 in every case.
CASES = (
    (3.0, 3.0, 0.20, 0.05, 0.02, 0.30, 0.8),
    (0.5, 1.8, 0.65, -0.01, 0.02, 0.20, 1.2),
    (5.0, 8.0, 0.37, 0.05, 0.00, 0.40, 2.0),
)
EPSILONS = (0.1, 0.01, 0.001, 0.0001)  # approach Y = 2 *from below*


def _relative_error(actual: complex | float, expected: complex | float) -> float:
    return abs(actual - expected) / (1.0 + abs(expected))


def _uncorrected_limit(sigma: float, G: float, M: float, v: complex) -> complex:
    """From B_2(v) = 2i(G-M)v - 2v^2, not from cgmy_exponent."""
    half_var = sigma * sigma / 2.0
    return 1j * half_var * (G - M) * v - half_var * v * v


def _gbm_limit(sigma: float, carry: float, v: complex) -> complex:
    """The GBM risk-neutral log exponent, independently of the CGMY oracle."""
    half_var = sigma * sigma / 2.0
    return 1j * (carry - half_var) * v - half_var * v * v


def check() -> None:
    """Check recurrence, pointwise limits, factor at -i, and false-limit canaries."""
    results: list[dict[str, float]] = []
    for eps in EPSILONS:
        Y = 2.0 - eps
        errors = dict(coefficient=0.0, uncorrected=0.0, kappa1=0.0,
                      gbm=0.0, factor=0.0, esscher_zero=0.0,
                      esscher_range=0.0, closure=0.0)
        for G, M, sigma, r, q, alpha, tau in CASES:
            assert G > 0.0 and M > 1.0 and sigma > 0.0 and alpha > 0.0
            assert alpha + 1.0 < M and G + M > 1.0
            C = (sigma * sigma / 2.0) * eps
            half_var = sigma * sigma / 2.0
            carry = r - q

            # Independent reflection (existing oracle) vs two Gamma recurrences
            # evaluated without sin(pi Y): (2-Y)Gamma(-Y)=Gamma(3-Y)/(Y(Y-1)).
            prefactor = C * cgmy_gamma_neg(Y)
            stable_prefactor = half_var * math.gamma(3.0 - Y) / (Y * (Y - 1.0))
            errors["coefficient"] = max(errors["coefficient"],
                                        _relative_error(prefactor, stable_prefactor))

            # Real cumulant at u=1, separately from the complex exponent route.
            kappa1 = cgmy_cumulant(C, G, M, Y, 1.0)
            errors["kappa1"] = max(errors["kappa1"],
                                    _relative_error(kappa1, half_var * (G - M + 1.0)))
            at_numeraire = cgmy_exponent(C, G, M, Y, -1j)
            assert abs(at_numeraire - kappa1) < 1e-10

            # theta0 is *exactly* the zero-carry Esscher parameter at every Y,
            # not a limiting solution substituted for an unsolved equation.
            theta0 = esscher_theta_zero(G, M)
            assert abs(esscher_drift_map(C, G, M, Y, theta0)) < 1e-10
            range_limit = half_var * (G + M - 1.0)
            errors["esscher_range"] = max(
                errors["esscher_range"],
                _relative_error(esscher_drift_bound(C, G, M, Y), range_limit),
            )
            tilted_G, tilted_M = G + theta0, M - theta0
            assert tilted_G > 0 and tilted_M > alpha + 1.0

            points = (0j, 1 + 0j, -2 + 0j, 1.25 - 0.8j, -1j,
                      cgmy_pricing_contour_v(alpha, 1.1))
            for v in points:
                assert -M < v.imag < G and -tilted_M < v.imag < tilted_G
                raw = cgmy_exponent(C, G, M, Y, v)
                uncorrected_target = _uncorrected_limit(sigma, G, M, v)
                errors["uncorrected"] = max(errors["uncorrected"],
                                             _relative_error(raw, uncorrected_target))

                # Algebraic forward normalization. This is *not* an Esscher tilt;
                # no claim of a constructed tilted measure is being made.
                normalized = raw + 1j * (carry - kappa1) * v
                gbm_target = _gbm_limit(sigma, carry, v)
                errors["gbm"] = max(errors["gbm"],
                                    _relative_error(normalized, gbm_target))
                factor = cmath.exp(tau * normalized)
                gbm_factor = cmath.exp(tau * gbm_target)
                errors["factor"] = max(errors["factor"],
                                       _relative_error(factor, gbm_factor))

                # This *is* the BRIEF_013 selection, at r-q=0. Its exact
                # zero-drift identity and the family-closure theorem hold at
                # every Y, and the GBM limit has log drift -sigma^2/2.
                esscher = esscher_exponent(C, G, M, Y, theta0, v)
                zero_carry_target = _gbm_limit(sigma, 0.0, v)
                errors["esscher_zero"] = max(errors["esscher_zero"],
                                              _relative_error(esscher, zero_carry_target))
                shifted = cgmy_exponent(C, tilted_G, tilted_M, Y, v)
                errors["closure"] = max(errors["closure"],
                                        _relative_error(esscher, shifted))

            normalized_numeraire = at_numeraire + (carry - kappa1)
            assert abs(normalized_numeraire - carry) < 1e-10
            assert abs(cmath.exp(tau * normalized_numeraire)
                       - math.exp(tau * carry)) < 1e-10
            assert abs(esscher_exponent(C, G, M, Y, theta0, -1j)) < 1e-10
        results.append(errors)
        print(f"epsilon={eps:.4g} " + " ".join(f"{key}={value:.3e}"
              for key, value in errors.items()))

    # Convergence has a measurable rate on the fixed grid; numerical errors
    # are not mistaken for a proof of convergence at every complex v.
    for key in ("uncorrected", "kappa1", "gbm", "factor", "esscher_zero",
                "esscher_range"):
        assert results[-1][key] < 0.15 * results[-2][key], key
    assert results[-1]["uncorrected"] < 1e-3
    assert results[-1]["gbm"] < 1e-3
    assert results[-1]["esscher_zero"] < 1e-3
    assert max(row["coefficient"] for row in results) < 1e-9
    assert max(row["closure"] for row in results) < 1e-9
    try:
        cgmy_exponent(0.1, 3.0, 3.0, 2.0, 1 + 0j)
    except ValueError:
        pass  # Y = 2 is outside the oracle's domain, not a value to compare.
    else:
        raise AssertionError("the oracle evaluated Gamma(-2) at its pole")

    # Negative controls. At fixed C the pole survives: Re psi(1) ~ -C/eps for
    # G=M, so the bare "Y -> 2" statement in the old docs was false. Sending
    # G,M to sigma^2/2 at fixed Y remains non-Gaussian. Doubling C doubles
    # the variance, and omitting the forward correction misses the GBM drift.
    fixed_C = 0.35
    wide = cgmy_exponent(fixed_C, 3.0, 3.0, 1.9, 1 + 0j).real
    near = cgmy_exponent(fixed_C, 3.0, 3.0, 1.999, 1 + 0j).real
    assert near < 20 * wide < 0 and abs(0.001 * near + fixed_C) < 1e-3

    # Sending G,M to sigma^2/2 at fixed noninteger Y retains complex powers.
    # With G=M the real part of any Gaussian exponent scales like v^2; the
    # ratio at frequencies 2 and 1 would be exactly 4, whatever the drift.
    alleged_corner_rate = 1.5 ** 2 / 2.0  # 1.125 > 1, so even the numeraire fits.
    at_one = cgmy_exponent(0.2, alleged_corner_rate, alleged_corner_rate,
                           1.5, 1 + 0j).real
    at_two = cgmy_exponent(0.2, alleged_corner_rate, alleged_corner_rate,
                           1.5, 2 + 0j).real
    rate_only_ratio = at_two / at_one
    assert abs(rate_only_ratio - 4.0) > 0.2

    G = M = 3.0
    sigma, carry, v, eps = 0.75, 0.03, 2 + 0j, 0.0001
    Y = 2.0 - eps
    C = sigma * sigma / 2.0 * eps
    raw = cgmy_exponent(C, G, M, Y, v)
    kappa1 = cgmy_cumulant(C, G, M, Y, 1.0)
    target = _gbm_limit(sigma, carry, v)
    correct = raw + 1j * (carry - kappa1) * v
    doubled = cgmy_exponent(2 * C, G, M, Y, v) + 1j * (
        carry - cgmy_cumulant(2 * C, G, M, Y, 1.0)) * v
    uncorrected_drift = raw + 1j * carry * v
    assert abs(correct - target) < 1e-3
    assert abs(doubled - target) > 0.8
    assert abs(uncorrected_drift - target) > 0.4
    print(f"canaries: fixed_C_Re(1)={wide:.3f}->{near:.3f}; "
          f"GM_only_ratio={rate_only_ratio:.3f} (Gaussian=4); "
          f"double_C_error={abs(doubled-target):.3f}; "
          f"missing_drift_error={abs(uncorrected_drift-target):.3f}")
    print("GBM corner pre-brief route-check: OK (numeric only; no Lean theorem)")


if __name__ == "__main__":
    check()
