"""
Mutation harness: proves the oracle tests are *falsifiers*, not decoration.

The repo's claim is that `experiments/` is a "sanity handrail" and that a
numeric residual is "an independent numerical falsifier of the formula".
That is an empirical claim about the test suite, so it gets tested.

How it works
------------
Each mutant is a single textual substitution into the oracle source that
introduces a specific mathematical error. The mutant is written to a temp
tree together with an unmodified copy of `tests/test_bs.py`, the suite is run
in a subprocess, and we assert that the test(s) which *should* catch that
error actually go red.

Two properties this buys:

1. **Detection.** Every seeded bug is caught (39/39 as of this commit).
2. **Non-vacuity.** Two of the mutants exist specifically to catch tests that
   compare a quantity against itself:

     * M7 breaks Phi's odd symmetry, i.e. Phi(x) + Phi(-x) != 1. This is
       *exactly* the identity put-call parity depends on. If the put were
       derived from the call via parity -- as it was before -- the parity test
       could not fail, and M7 SURVIVES it. It is now killed by
       `test_put_call_parity`.
     * M8a/M8b corrupt the independent `d2` expression. If `d2` were defined
       as `d1 - s*sqrt(tau)`, there would be no such expression to corrupt and
       the anchor would not exist -- so the harness fails loudly on the
       missing anchor. That anchor assertion *is* the structural guard.

   The anchors are therefore load-bearing. If you refactor the oracle, update
   the anchors; do not delete them, and do not relax a target to a test that
   only fails for an unrelated reason.

Run:  python3 tests/test_mutants.py    (stdlib only, ~2s)
"""

from __future__ import annotations

import math
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
ORACLE = os.path.join(ROOT, "experiments", "black_scholes.py")
SUITE = os.path.join(ROOT, "tests", "test_bs.py")

# Scratch notes for the __main__ runner. pytest warns when a test function
# returns a value, so the tests record here instead of returning.
LAST_NOTE: dict = {}

# (name, anchor, replacement, tests that MUST fail)
MUTANTS = [
    (
        "M1 d1 drift sign flip: (r-q+s^2/2) -> (r-q-s^2/2)",
        "(log_m + (r - q + 0.5 * s * s) * tau) / den",
        "(log_m + (r - q - 0.5 * s * s) * tau) / den",
        ["test_textbook_call", "test_d1_minus_d2"],
    ),
    (
        "M2 call spot leg uses Phi(d2) instead of Phi(d1)",
        "S * math.exp(-q * tau) * norm_cdf(d1)",
        "S * math.exp(-q * tau) * norm_cdf(d2)",
        ["test_textbook_call", "test_value_bounds"],
    ),
    (
        "M3 put closed form: sign flip on the S e^{-q tau} Phi(-d1) leg",
        "norm_cdf(-d2) - S * math.exp(-q * tau) * norm_cdf(-d1)",
        "norm_cdf(-d2) + S * math.exp(-q * tau) * norm_cdf(-d1)",
        ["test_put_call_parity", "test_textbook_put"],
    ),
    (
        "M4 PDE diffusion coefficient: s^2/2 -> s^2",
        "0.5 * s * s * S * S * V_SS",
        "s * s * S * S * V_SS",
        ["test_pde_residual_vanishes"],
    ),
    (
        "M5 Phi argument scaling: erf(x/sqrt 2) -> erf(x/2)",
        "math.erf(x / math.sqrt(2.0))",
        "math.erf(x / 2.0)",
        ["test_textbook_call", "test_phi_and_Phi_are_consistent"],
    ),
    (
        "M6 strike leg discounted at q instead of r",
        "K * math.exp(-r * tau) * norm_cdf(d2)",
        "K * math.exp(-q * tau) * norm_cdf(d2)",
        ["test_textbook_call", "test_put_call_parity"],
    ),
    (
        "M7 VACUITY CANARY: Phi loses odd symmetry, Phi(x)+Phi(-x) != 1",
        "return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))",
        "return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0))) + 1e-3 * math.exp(-x * x)",
        # The whole point: parity MUST fail. It cannot, if bs_put is derived
        # from bs_call via parity.
        ["test_put_call_parity"],
    ),
    (
        "M8a VACUITY CANARY: independent d2 loses sqrt(tau)",
        "(log_m + (r - q - 0.5 * s * s) * tau) / den",
        "(log_m + (r - q - 0.5 * s * s) * tau) / (s * tau)",
        ["test_d1_minus_d2"],
    ),
    (
        "M8b VACUITY CANARY: independent d2 sign flip, collapsing d2 to d1",
        "(r - q - 0.5 * s * s)",
        "(r - q + 0.5 * s * s)",
        ["test_d1_minus_d2"],
    ),
    (
        "M9 phi normalisation: 1/sqrt(2 pi) -> 1/sqrt(pi)",
        "math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)",
        "math.exp(-0.5 * x * x) / math.sqrt(math.pi)",
        # T3 is homogeneous in phi, so the delta identity CANNOT catch a
        # common scale error; only the Phi' == phi check can.
        ["test_phi_and_Phi_are_consistent"],
    ),
    (
        "M10 parity helper: sign flip on the K e^{-r tau} leg",
        "return bs_call(S, K, tau, r, q, s) - S * math.exp(-q * tau) + K * math.exp(-r * tau)",
        "return bs_call(S, K, tau, r, q, s) - S * math.exp(-q * tau) - K * math.exp(-r * tau)",
        ["test_put_call_parity"],
    ),
    (
        "M11 risk-neutral drift sign flip in the expectation route: (r-q-s^2/2) -> (r-q+s^2/2)",
        "return (r - q - s * s / 2.0) * tau",
        "return (r - q + s * s / 2.0) * tau",
        # Only the expectation test can see this: the closed forms do not use
        # the drift helper, so parity, bounds, PDE and the textbook values all
        # stay green while E[S_T] drifts to S e^{(r-q+s^2) tau}.
        ["test_risk_neutral_expectation"],
    ),
    (
        "M12 Carr-Madan damping denominator mid coefficient: (2*alpha+1) -> (2*alpha-1)",
        "(2.0 * alpha + 1.0) * u",
        "(2.0 * alpha - 1.0) * u",
        # Only the Fourier inversion test can see this: the closed forms and expectation
        # routes do not use the Carr-Madan denominator.
        ["test_fourier_inversion"],
    ),
    (
        "M13 model-free put payoff corrupted to the call payoff",
        "p * max(K - s, 0.0)",
        "p * max(s - K, 0.0)",
        # Only the model-free skeleton test uses the discrete-law helpers: with
        # the put payoff corrupted, put == call and every gap identity dies.
        ["test_model_free_skeleton"],
    ),
    (
        "M14 model-free mean corrupted to the second moment (drift bug, M11's twin)",
        "sum(p * s for p, s in zip(probs, spots))",
        "sum(p * s * s for p, s in zip(probs, spots))",
        # Only the model-free skeleton test uses `model_free_forward`: the gap
        # identity's right-hand side moves and parity dies at every law.
        ["test_model_free_skeleton"],
    ),
    (
        "M15 CONTOUR CANARY: pricing contour swapped to u + i*alpha in bs_call_by_fourier_inversion",
        "v = complex(u, -(alpha + 1.0))",
        "v = complex(u, alpha)",
        # Only the Fourier inversion test uses this contour: on `u + iα` the
        # formula returns 1.82 against 7.11 (rel 7.44e-01, ledger C12) while
        # the closed form, the expectation and the free-law route do not move.
        # The anchor hits the first occurrence (the half-line route); the
        # complex twin keeps the pricing line, so the test's `cf` leg dies.
        ["test_fourier_inversion"],
    ),
    (
        "M16 free-law contour shift off by one: -(alpha+1) -> -alpha in carr_madan_by_law",
        "v = complex(u, -(alpha+1.0))",
        "v = complex(u, -alpha)",
        # Only the free-law test uses `carr_madan_by_law`: the shift off by one
        # moves the skewed-law price by rel 3.75e-01 against the test's 1e-4
        # tolerance, while the GBM Fourier route (spaced `-(alpha + 1.0)`)
        # does not match this anchor and stays green.
        ["test_carr_madan_free_law"],
    ),
    (
        "M17 NONUNIQ DRIFT CANARY: witness B's p3 moved 1/8 -> 3/8 (BRIEF_012's canary)",
        "NONUNIQ_WEIGHTS_B = (Fraction(1, 4), Fraction(5, 8), Fraction(1, 8))",
        "NONUNIQ_WEIGHTS_B = (Fraction(1, 4), Fraction(5, 8), Fraction(3, 8))",
        # Only the witness test reads the witness constants. B now has mass 5/4
        # and mean 3/2, and traded parity at B is off by exactly 1/4 (call 3/8,
        # put 1/8) -- the drift clause of `static_skeleton_does_not_select_measure`
        # is load-bearing, and the test that shadows it notices.
        ["test_nonuniqueness_witness"],
    ),
    (
        "M18 NONUNIQ payoff corrupted: call payoff (s-K)+ replaced by the LINEAR payoff s-K",
        "p * max(s - K, 0.0)",
        "p * (s - K)",
        # No probability is touched, yet call(A) = call(B) = E[S_T] - K = 0 at
        # both witness laws: the disagreement 1/4 != 1/8 was a fact about the
        # CONVEX payoff, and the linear one is pinned by the drift on the whole
        # martingale segment. The witness test dies on `call(A) = 1/4`; the
        # skeleton and free-law tests die too (both price against the same
        # payoff line), which is expected. BRIEF_012's literal M18
        # (call priced with the put's `max(K - s, 0)`) is blind at this witness
        # because K = F and r = 0 make call = put at both laws; that mutant is
        # M13's twin and only test_model_free_skeleton could see it.
        ["test_nonuniqueness_witness"],
    ),
    (
        "M19 NONUNIQ witness collapsed: B's weights replaced by A's (one law, two names)",
        "NONUNIQ_WEIGHTS_B = (Fraction(1, 4), Fraction(5, 8), Fraction(1, 8))",
        "NONUNIQ_WEIGHTS_B = (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4))",
        # The oracle twin of the lint's N1: B is a probability law with the
        # forward as mean, parity and bounds hold, B sits on the segment -- and
        # every clause of the headline is satisfied except the one that IS the
        # theorem, `call(A) != call(B)`. Only the witness test can see it.
        ["test_nonuniqueness_witness"],
    ),
    (
        "M20 ESSCHER shift sign flip: psi(v + i theta) - psi(i theta) for the tilt",
        "cgmy_exponent(C, G, M, Y, v - 1j * theta) - cgmy_exponent(C, G, M, Y, -1j * theta)",
        "cgmy_exponent(C, G, M, Y, v + 1j * theta) - cgmy_exponent(C, G, M, Y, 1j * theta)",
        # The wrong-sign shift still defines a perfectly valid function; what
        # it is not is the family closure. The closure assertion
        # `esscher_exponent == cgmy_exponent at (G+theta, M-theta)` breaks by
        # O(1) (route-check residual at issue: 2.251), while the real-drift
        # machinery (`cgmy_cumulant`, `esscher_solve`) never touches the
        # complex route and stays green -- so only the Esscher test can see
        # it, and it must.
        ["test_esscher_drift"],
    ),
    (
        "M21 ESSCHER range half-width with the inner absolute value dropped",
        "abs(C * cgmy_gamma_neg(Y)) * abs(s ** Y - (s - 1.0) ** Y - 1.0)",
        "abs(C * cgmy_gamma_neg(Y)) * (s ** Y - (s - 1.0) ** Y - 1.0)",
        # The bracket `s^Y - (s-1)^Y - 1` has the sign of `Y - 1` (MVT), so
        # dropping the abs makes H NEGATIVE for every set with `Y < 1` (sets A
        # and C) while leaving the `Y > 1` sets untouched -- one mutant, both
        # regimes, in opposite directions. The `H > 0` and edge-value
        # assertions of the Esscher test are its falsifiers; a test that only
        # exercised `Y > 1` sets would let it survive, which is why the
        # committed contract carries both.
        ["test_esscher_drift"],
    ),
    (
        "M22 CORNER scale doubled: `cgmyCornerC` as sigma^2 (2 - Y), not (sigma^2/2)(2 - Y)",
        "return (sigma * sigma / 2.0) * (2.0 - Y)",
        "return sigma * sigma * (2.0 - Y)",
        # The doubled scale still cancels the pole -- `C_Y Gamma(-Y) -> sigma^2/2`
        # is finite -- so nothing diverges and nothing looks broken. What it
        # delivers is TWICE the intended variance: the limit exponent is
        # `-sigma^2 v^2 + i sigma^2 (G-M) v` instead of the half-variance one,
        # and the drift correction `kappa(1)` is out by a factor of two as
        # well. The canary measures it at 1.257 against a tolerance of 1e-3.
        ["test_gbm_corner"],
    ),
    (
        "M23 CORNER drift correction dropped: Psi_Y = psi_Y + i (r - q) v",
        "return cgmy_exponent(C, G, M, Y, v) + 1j * (r - q - cgmy_cumulant(C, G, M, Y, 1.0)) * v",
        "return cgmy_exponent(C, G, M, Y, v) + 1j * (r - q) * v",
        # Route A's whole content is the `-kappa_Y(1)`: without it the
        # tempering asymmetry `G - M` survives the limit and the exponent is
        # NOT the risk-neutral GBM exponent at any carry. It is a *small*
        # error (0.563 at the canary point, O(sigma^2) in general) -- far below
        # what a loose tolerance would notice, and it does not shrink with
        # epsilon, which is why the test asserts the shrinkage and not just a
        # final residual. This is the mutant the brief's "seed mutants for at
        # least doubled scaling and missing drift correction" asks for.
        ["test_gbm_corner"],
    ),
    (
        "M24 PARETO density exponent -(r+1) -> -r: not a probability density",
        "return r * t ** r * x ** (-(r + 1.0))",
        "return r * t ** r * x ** (-r)",
        # One power too slow: the mass is ~3 at (1, 1.5) and infinite for
        # r <= 1, so the upstream normalization assertion goes red at once.
        ["test_pareto_witness"],
    ),
    (
        "M25 PARETO tail constant t^r -> t^(-r): the weak mutant",
        "return t ** r * x ** (-r)",
        "return t ** (-r) * x ** (-r)",
        # At t = 2 this still satisfies htail as an INEQUALITY (gap +0.875 at
        # x = t) -- found by BRIEF_015's route-check. Only the equality
        # assertions at t != 1 kill it, which is why the test carries them.
        ["test_pareto_witness"],
    ),
    (
        "M26 BRIEF_016 corner map: C = 1/nu -> nu (the Y = 0 corner is scaled by the mixing variance)",
        "C = 1.0 / nu",
        "C = nu",
        # The corner route is the tree's parameterization of the SAME published
        # law the VG route prices; a wrong `C` scales the whole corner exponent
        # by `nu^2 = 4`, and every anchor price moves by O(1). The VG route does
        # not read the map, so only the anchor test can see this.
        ["test_term_structure_anchor"],
    ),
    (
        "M27 BRIEF_016 VG exponent: -(tau / nu) log(.) -> -tau log(.)",
        "return 1j * (r - q + omega) * tau * v - (tau / nu) * cmath.log(w)",
        "return 1j * (r - q + omega) * tau * v - tau * cmath.log(w)",
        # The `tau/nu` scaling is the law's parameterization (nu is the mixing
        # variance, not a unit of time); dropping it moves the published anchor
        # prices by O(1) and both witness exponents.
        ["test_term_structure_anchor"],
    ),
    (
        "M28 BRIEF_016 martingale correction sign: 1 - theta nu - sigma^2 nu/2 -> 1 + ...",
        "m1 = 1.0 - theta * nu - 0.5 * sigma * sigma * nu",
        "m1 = 1.0 + theta * nu + 0.5 * sigma * sigma * nu",
        # `omega` is what makes `E[S_T] = S e^{(r-q) tau}`; the sign flip is not
        # a crash (m1 stays positive at Case 4: 0.8625) -- it is a different,
        # non-martingale law, so the normalization identity psi(-i) = (r-q)tau
        # and the anchor prices both go red.
        ["test_term_structure_anchor"],
    ),
    (
        "M29 BRIEF_016 corner map: theta -> -theta (G and M swapped)",
        "return C, (s + theta) / (sigma * sigma), (s - theta) / (sigma * sigma)",
        "return C, (s - theta) / (sigma * sigma), (s + theta) / (sigma * sigma)",
        # Swapping the tempering rates is the sign error of the corner's
        # asymmetry: the first cumulant flips (C(1/M - 1/G) = -theta) and the
        # corner-route anchor prices move by O(1), while the VG route is
        # untouched -- BRIEF_016's F3 is exactly the statement that the two
        # routes are the same law.
        ["test_term_structure_anchor"],
    ),
    (
        "M30 BRIEF_018 corner sign flip in cgmy_zeroth_exponent: C * (...) -> -C * (...)",
        "return C * (cmath.log(M / (M - 1j * v)) + cmath.log(G / (G + 1j * v)))",
        "return -C * (cmath.log(M / (M - 1j * v)) + cmath.log(G / (G + 1j * v)))",
        # The complex corner target negated: the bridge `exp(tau * psi_0(-i))`
        # moves 0.984025 -> 1.016234 against the real-side mgf, and every
        # corner ratio `|psi_Y - psi_0|/Y` explodes. The anchor test dies too
        # (its corner-route prices move by O(1)) -- recorded, not avoided:
        # BRIEF_018's primitive reconciliation says the corner target is ONE
        # function shared by both tests.
        ["test_vg_law", "test_term_structure_anchor"],
    ),
    (
        "M31 BRIEF_018 mgf drops tau: exp(tau * kappa) -> exp(kappa)",
        "return math.exp(tau * vg_cumulant(C, G, M, u))",
        "return math.exp(vg_cumulant(C, G, M, u))",
        # The law's shape is `C*tau`; dropping `tau` prices the `tau = 1` law
        # at every maturity. The mgf at `u = 1` moves 0.984025 -> 0.937614 and
        # the two-Gamma factorization breaks -- only the VG test reads `vg_mgf`.
        ["test_vg_law"],
    ),
    (
        "M32 BRIEF_018 tilt legs swapped: (G+theta, M-theta) -> (M+theta, G-theta)",
        "return vg_cumulant(C, G + theta, M - theta, u)",
        "return vg_cumulant(C, M + theta, G - theta, u)",
        # The tilted law is the family member at the shifted rates; swapping
        # the legs prices a different law. The tilted mgf at 1 moves
        # 1.0050125 -> 1.2061790 and the shift identity breaks on its grid --
        # only the VG test reads `vg_tilted_cumulant`. (The brief's M32 row
        # quotes 0.984025 -> 0.946021; the from-value is the UNTILTED mgf(1)
        # and the to-value is the theta -> -theta variant -- measured
        # 0.9460212974415997 exactly -- while the as-prosed leg-swap measures
        # 1.2061789609599316. Ledger C21 records the slip; the kill is O(1)
        # either way.)
        ["test_vg_law"],
    ),
    (
        "M33 BRIEF_018 cumulant reflected: u -> -u (the mean changes sign)",
        "return C * (math.log(M / (M - u)) + math.log(G / (G + u)))",
        "return C * (math.log(M / (M + u)) + math.log(G / (G - u)))",
        # `M` tempers the positive side and `G` the negative side; reflecting
        # `u` swaps the mean's sign (`1/M - 1/G -> 1/G - 1/M`). The `kappa_0(1)`
        # pin moves -0.064416 -> +0.152245 (O(1)), and in the unguarded scratch
        # world the solved theta crosses theta0 to -1.736491239, where the
        # TRUE drift is -0.283720 instead of 0.02. Only the VG test reads
        # `vg_cumulant`.
        ["test_vg_law"],
    ),
    (
        "M34 Poisson weights: the 1/n! factor is dropped from the log-space recursion",
        "logs.append(logs[-1] + math.log(lam) - math.log(n))",
        "logs.append(logs[-1] + math.log(lam))",
        ["test_compound_poisson"],
    ),
    (
        "M35 jump law not normalised: the truncated measure itself is handed to cpLaw",
        "return (cgmy_truncated_exponent(C, G, M, Y, eps, t, **quad) + lam) / lam",
        "return cgmy_truncated_exponent(C, G, M, Y, eps, t, **quad) + lam",
        ["test_compound_poisson"],
    ),
    (
        "M36 truncated exponent drops the -1 of the integrand (the cancelled mass comes back)",
        "weight = _expm1_complex(z) if minus_one else cmath.exp(z)",
        "weight = cmath.exp(z)",
        ["test_compound_poisson"],
    ),
    (
        "M37 tempering legs swapped: the positive leg is tempered by G",
        "pos = _cgmy_truncated_leg(M, Y, eps, v, minus_one, **quad)",
        "pos = _cgmy_truncated_leg(G, Y, eps, v, minus_one, **quad)",
        ["test_compound_poisson"],
    ),
    (
        "M38 one-sided truncation: the mirror leg of the density is dropped",
        "neg = _cgmy_truncated_leg(G, Y, eps, -v, minus_one, **quad)",
        "neg = 0.0j",
        ["test_compound_poisson"],
    ),
    # BRIEF_020: the CGMY law. M39 is the one that is not a rounding cheat --
    # the UNPAIRED drift leg does not converge at all (122.47 at eps = 2^-14,
    # growing like eps^{1-Y}), so the limit exponent stops existing. M40-M43
    # move it by a named amount: the drift is load-bearing (ledger C25).
    (
        "M39 drift not paired: only the M leg survives, and it DIVERGES as eps -> 0",
        "        return (math.expm1(-M * x) - math.expm1(-G * x)) * x ** (-Y)",
        "        return math.expm1(-M * x) * x ** (-Y)",
        ["test_cgmy_law"],
    ),
    (
        "M40 drift dropped from the limit exponent: L := B_0 with no i v d_0",
        "    return b_zero + 1j * v * d_zero",
        "    return b_zero + 0.0j",
        ["test_cgmy_law"],
    ),
    (
        "M41 the far-field drift m^inf is missing from the one-sided assembly",
        "    return compensated + 1j * v * cgmy_drift_identity_closed(C, G, M, Y)",
        "    return compensated + 0.0j",
        ["test_cgmy_law"],
    ),
    (
        "M42 drift sign flipped: the paired integrand is negated",
        "        return (math.expm1(-M * x) - math.expm1(-G * x)) * x ** (-Y)",
        "        return (math.expm1(-G * x) - math.expm1(-M * x)) * x ** (-Y)",
        ["test_cgmy_law"],
    ),
    (
        "M43 Gamma(1-Y) -> Gamma(-Y) in the closed form of the drift m^inf",
        "    return C * math.gamma(1.0 - Y) * (M ** (Y - 1.0) - G ** (Y - 1.0))",
        "    return C * math.gamma(-Y) * (M ** (Y - 1.0) - G ** (Y - 1.0))",
        ["test_cgmy_law"],
    ),
]


def _run_suite(workdir: str, oracle_src: str, suite_src: str):
    """Run tests/test_bs.py against a given oracle source; return failing test names."""
    shutil.rmtree(workdir, ignore_errors=True)
    os.makedirs(os.path.join(workdir, "experiments"))
    os.makedirs(os.path.join(workdir, "tests"))
    with open(os.path.join(workdir, "experiments", "__init__.py"), "w") as f:
        f.write("")
    with open(os.path.join(workdir, "experiments", "black_scholes.py"), "w") as f:
        f.write(oracle_src)
    with open(os.path.join(workdir, "tests", "test_bs.py"), "w") as f:
        f.write(suite_src)
    proc = subprocess.run(
        [sys.executable, "tests/test_bs.py"], cwd=workdir, capture_output=True, text=True
    )
    failed = sorted(
        line.split()[1] for line in proc.stdout.splitlines() if line.startswith("FAIL")
    )
    passed = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else ""
    return failed, proc.returncode, passed


def test_baseline_is_green():
    """Guard: the harness is only meaningful if the unmutated suite passes."""
    oracle = open(ORACLE).read()
    suite = open(SUITE).read()
    with tempfile.TemporaryDirectory() as tmp:
        failed, rc, passed = _run_suite(os.path.join(tmp, "base"), oracle, suite)
    assert rc == 0 and not failed, f"unmutated oracle fails its own suite: {failed}"
    # recorded for the __main__ report; pytest warns if a test function returns
    LAST_NOTE["test_baseline_is_green"] = passed


def test_anchors_exist():
    """Guard: every mutation anchor must be present in the oracle source.

    A missing anchor means the oracle was refactored and the mutant silently
    became a no-op -- which would make the detection result below vacuous.
    This is what stops M8a/M8b from passing after someone re-defines
    `d2 := d1 - s*sqrt(tau)`.
    """
    oracle = open(ORACLE).read()
    missing = [name for name, anchor, _, _ in MUTANTS if anchor not in oracle]
    assert not missing, (
        "mutation anchors no longer present in experiments/black_scholes.py -- "
        "update them, do not delete them: " + "; ".join(missing)
    )


def test_every_mutant_is_killed_by_its_target():
    """The detection claim itself: each bug is caught by the test meant to catch it."""
    oracle = open(ORACLE).read()
    suite = open(SUITE).read()
    survivors, wrong_killer = [], []
    with tempfile.TemporaryDirectory() as tmp:
        for i, (name, anchor, replacement, targets) in enumerate(MUTANTS):
            assert anchor in oracle, f"anchor missing for {name}"
            mutated = oracle.replace(anchor, replacement, 1)
            assert mutated != oracle, f"mutation was a no-op for {name}"
            failed, _, _ = _run_suite(os.path.join(tmp, f"m{i:02d}"), mutated, suite)
            if not failed:
                survivors.append(name)
                continue
            missed = [t for t in targets if t not in failed]
            if missed:
                wrong_killer.append(f"{name}: expected {missed} to fail, got {failed}")
    assert not survivors, "MUTANTS SURVIVED (test suite has a hole):\n  " + "\n  ".join(survivors)
    assert not wrong_killer, (
        "mutants killed by the WRONG test (the targeted test is vacuous):\n  "
        + "\n  ".join(wrong_killer)
    )


def test_parity_is_not_tautological_at_runtime():
    """Semantic vacuity detector, independent of source text.

    Perturb Phi by an EVEN function so that Phi(x) + Phi(-x) != 1 while every
    other property (monotonicity, limits, CDF shape) survives. If the put were
    derived from the call via parity, `bs_put` and `bs_put_by_parity` would
    still agree *identically* -- the relation would hold by construction. With
    independent derivations they must diverge. If this ever stops failing, the
    parity test has become a tautology again.
    """
    import experiments.black_scholes as bs

    original = bs.norm_cdf
    broken = lambda x: original(x) + 1e-3 * math.exp(-x * x)  # even perturbation
    try:
        bs.norm_cdf = broken
        args = (100.0, 100.0, 1.0, 0.05, 0.0, 0.20)  # (S, K, tau, r, q, sigma)
        indep = bs.bs_put(*args)
        via_parity = bs.bs_put_by_parity(*args)
    finally:
        bs.norm_cdf = original
    assert abs(indep - via_parity) > 1e-5, (
        "put-call parity held under a symmetry-breaking Phi: bs_put is being "
        f"derived from bs_call, so test_put_call_parity is a tautology "
        f"(indep={indep}, via_parity={via_parity})"
    )


if __name__ == "__main__":
    import traceback

    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    fails = 0
    for fn in fns:
        try:
            LAST_NOTE.clear()
            fn()
            note = LAST_NOTE.get(fn.__name__, "")
            print(f"  ok  {fn.__name__}" + (f"   [{note}]" if note else ""))
        except Exception:
            fails += 1
            print(f"FAIL  {fn.__name__}")
            traceback.print_exc()
    print(f"\n{len(fns)-fails}/{len(fns)} passed  ({len(MUTANTS)} mutants seeded)")
    sys.exit(1 if fails else 0)
