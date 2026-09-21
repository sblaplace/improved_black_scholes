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

1. **Detection.** Every seeded bug is caught (15/15 as of this commit).
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
