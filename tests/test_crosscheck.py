#!/usr/bin/env python3
"""
Oracle ↔ Lean pointwise cross-verifier (BRIEF_002, docs/04 guard 3).

Reads the golden parameter grid (tests/golden_grid.json), evaluates the seven
core quantities (d1, d2, call, put, parity, and BOTH sides of the delta
identity) via the Python oracle (experiments/black_scholes.py) and compares
against the Lean Float evaluations emitted by ImprovedBS/Crosscheck.lean.

This is a **cross-verifier, not a proof.** It detects drift between the two
independent trees.

Line format (fixed, greppable; one line per grid point, 14 tokens):

    CK S K tau r q sigma d1 d2 call put putByParity deltaLhs deltaRhs

`deltaLhs` is `S e^{-qτ} φ(d1)` and `deltaRhs` is `K e^{-rτ} φ(d2)` — the two
sides of T3, evaluated independently in each tree. The comparator checks each
side against the oracle's matching side AND the two sides against each other:
a stream that carries only the LHS cross-verifies nothing about T3 (that was
the defect recorded in benchmarks/LEDGER.md C6 item 4).

Usage:
    # 1. Piped from Lean in CI:
    lake env lean ImprovedBS/Crosscheck.lean | python3 tests/test_crosscheck.py

    # 2. Reading a pre-captured output log:
    python3 tests/test_crosscheck.py --lean-output lean_crosscheck.log

    # 3. Running Lean directly (when lake is installed):
    python3 tests/test_crosscheck.py --run-lean

    # 4. Standalone / unit-test mode (validates grid & oracle self-consistency):
    python3 tests/test_crosscheck.py

Input-source discipline (C6 item 4, second defect): an explicit request is
always honored or fails loudly. `--run-lean` NEVER falls back to the unit
tests — previously `not sys.stdin.isatty()` claimed the input first, so
`echo -n | python3 tests/test_crosscheck.py --run-lean` printed
"4/4 crosscheck unit test(s) passed" with exit code 0 without cross-verifying
anything. `--run-lean` and `--lean-output` together are a contradiction, not
a silent precedence.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from experiments.black_scholes import (
    _d1d2,
    bs_call,
    bs_put,
    bs_put_by_parity,
    norm_pdf,
)

GRID_PATH = os.path.join(ROOT, "tests", "golden_grid.json")
CROSSCHECK_LEAN_PATH = os.path.join(ROOT, "ImprovedBS", "Crosscheck.lean")

# Tolerances justified per BRIEF_002 scope item 5:
# Float in Lean is IEEE-754 double precision (64-bit), same as CPython float.
# Measured worst-case disagreement on the grid is ~1e-14 on prices and ~1e-15
# on d1/d2. Applying a safety factor of 100x gives committed tolerances of 1e-12.
# The delta identity's two sides agree within the oracle itself to <= 7.2e-15
# over the grid (measured, Python vs Python), so the same 1e-12 carries the
# Lean-internal identity check with the same order of headroom.
TOL_PRICE = 1e-12
TOL_ARG = 1e-12
TOL_DELTA = 1e-12

# Number of whitespace-separated fields in a `CK` line: the literal "CK", the
# six parameters, and the seven evaluated quantities.
CK_TOKEN_COUNT = 14

CK_FIELDS = ("d1", "d2", "call", "put", "parity", "delta_lhs", "delta_rhs")


def load_grid() -> list[dict[str, float]]:
    with open(GRID_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def compute_oracle(pt: dict[str, float]) -> dict[str, float]:
    S, K, tau = pt["S"], pt["K"], pt["tau"]
    r, q, sigma = pt["r"], pt["q"], pt["sigma"]
    d1, d2 = _d1d2(S, K, tau, r, q, sigma)
    call = bs_call(S, K, tau, r, q, sigma)
    put = bs_put(S, K, tau, r, q, sigma)
    parity = bs_put_by_parity(S, K, tau, r, q, sigma)
    delta_lhs = S * math.exp(-q * tau) * norm_pdf(d1)
    delta_rhs = K * math.exp(-r * tau) * norm_pdf(d2)
    return {
        "S": S,
        "K": K,
        "tau": tau,
        "r": r,
        "q": q,
        "sigma": sigma,
        "d1": d1,
        "d2": d2,
        "call": call,
        "put": put,
        "parity": parity,
        "delta_lhs": delta_lhs,
        "delta_rhs": delta_rhs,
    }


def parse_lean_lines(lines: list[str]) -> list[dict[str, float]]:
    parsed = []
    for line in lines:
        line = line.strip()
        if not line.startswith("CK "):
            continue
        parts = line.split()
        if len(parts) != CK_TOKEN_COUNT:
            raise ValueError(
                f"Malformed CK line ({len(parts)} tokens, expected {CK_TOKEN_COUNT}): '{line}'\n"
                "The Lean twin must emit BOTH sides of the delta identity; a "
                "13-token line is the pre-C6-item-4 format and is rejected."
            )
        record = {
            "S": float(parts[1]),
            "K": float(parts[2]),
            "tau": float(parts[3]),
            "r": float(parts[4]),
            "q": float(parts[5]),
            "sigma": float(parts[6]),
        }
        for idx, field in enumerate(CK_FIELDS):
            record[field] = float(parts[7 + idx])
        parsed.append(record)
    return parsed


def crosscheck(
    lean_records: list[dict[str, float]],
    grid: list[dict[str, float]],
    tol_price: float = TOL_PRICE,
    tol_arg: float = TOL_ARG,
    tol_delta: float = TOL_DELTA,
) -> tuple[bool, list[str], dict[str, float]]:
    """Compare Lean records against Oracle computations. Returns (ok, errors, max_diffs)."""
    if len(lean_records) != len(grid):
        return (
            False,
            [f"Record count mismatch: Lean emitted {len(lean_records)} lines, grid has {len(grid)} points"],
            {},
        )

    errors = []
    max_diffs = {
        "d1": 0.0,
        "d2": 0.0,
        "call": 0.0,
        "put": 0.0,
        "parity": 0.0,
        "delta_lhs": 0.0,
        "delta_rhs": 0.0,
        "internal_parity": 0.0,
        "internal_delta": 0.0,
    }

    for idx, (lean, pt) in enumerate(zip(lean_records, grid)):
        orc = compute_oracle(pt)

        # Coordinate check
        for param in ("S", "K", "tau", "r", "q", "sigma"):
            if abs(lean[param] - pt[param]) > 1e-9:
                errors.append(
                    f"Point {idx}: parameter {param} mismatch (Lean: {lean[param]}, grid: {pt[param]})"
                )

        diffs = {field: abs(lean[field] - orc[field]) for field in CK_FIELDS}
        diffs["internal_parity"] = abs(lean["put"] - lean["parity"])
        diffs["internal_delta"] = abs(lean["delta_lhs"] - lean["delta_rhs"])
        for field, diff in diffs.items():
            max_diffs[field] = max(max_diffs[field], diff)

        pt_str = f"(S={pt['S']}, K={pt['K']}, tau={pt['tau']}, r={pt['r']}, q={pt['q']}, sigma={pt['sigma']})"

        if diffs["d1"] > tol_arg:
            errors.append(f"{pt_str} d1 divergence: Lean={lean['d1']}, Oracle={orc['d1']}, diff={diffs['d1']:.3e} > {tol_arg}")
        if diffs["d2"] > tol_arg:
            errors.append(f"{pt_str} d2 divergence: Lean={lean['d2']}, Oracle={orc['d2']}, diff={diffs['d2']:.3e} > {tol_arg}")
        if diffs["call"] > tol_price:
            errors.append(f"{pt_str} call divergence: Lean={lean['call']}, Oracle={orc['call']}, diff={diffs['call']:.3e} > {tol_price}")
        if diffs["put"] > tol_price:
            errors.append(f"{pt_str} put divergence: Lean={lean['put']}, Oracle={orc['put']}, diff={diffs['put']:.3e} > {tol_price}")
        if diffs["parity"] > tol_price:
            errors.append(f"{pt_str} parity divergence: Lean={lean['parity']}, Oracle={orc['parity']}, diff={diffs['parity']:.3e} > {tol_price}")
        if diffs["delta_lhs"] > tol_delta:
            errors.append(f"{pt_str} delta-lhs divergence: Lean={lean['delta_lhs']}, Oracle={orc['delta_lhs']}, diff={diffs['delta_lhs']:.3e} > {tol_delta}")
        if diffs["delta_rhs"] > tol_delta:
            errors.append(f"{pt_str} delta-rhs divergence: Lean={lean['delta_rhs']}, Oracle={orc['delta_rhs']}, diff={diffs['delta_rhs']:.3e} > {tol_delta}")
        if diffs["internal_parity"] > tol_price:
            errors.append(f"{pt_str} Lean internal parity violated: |bsPut - bsPutByParity| = {diffs['internal_parity']:.3e} > {tol_price}")
        # T3 itself, inside the Lean tree: the two independently evaluated sides
        # of `S e^{-qτ} φ(d1) = K e^{-rτ} φ(d2)` must agree. (See the module
        # docstring for why this cannot see an LHS-printed-twice stream at this
        # tolerance; THAT cheat is structural and belongs to [CROSSCHECK SYNC].)
        if diffs["internal_delta"] > tol_delta:
            errors.append(
                f"{pt_str} Lean internal delta identity violated: "
                f"|deltaLhs - deltaRhs| = {diffs['internal_delta']:.3e} > {tol_delta}"
            )

    return (len(errors) == 0, errors, max_diffs)


def test_golden_grid_schema_and_domain():
    grid = load_grid()
    assert len(grid) >= 20, f"Grid too small: {len(grid)}"
    moneyness = set()
    tenors = set()
    vols = set()
    has_nonzero_q = False
    has_negative_r = False
    for pt in grid:
        assert pt["S"] > 0, f"S must be > 0: {pt}"
        assert pt["K"] > 0, f"K must be > 0: {pt}"
        assert pt["tau"] > 0, f"tau must be > 0: {pt}"
        assert pt["sigma"] > 0, f"sigma must be > 0: {pt}"
        m = round(pt["S"] / pt["K"], 2)
        moneyness.add(m)
        tenors.add(round(pt["tau"], 4))
        vols.add(round(pt["sigma"], 2))
        if pt["q"] > 0:
            has_nonzero_q = True
        if pt["r"] < 0:
            has_negative_r = True

    for required_m in {0.5, 0.8, 1.0, 1.2, 2.0}:
        assert required_m in moneyness, f"Missing moneyness {required_m} in {moneyness}"
    for required_v in {0.05, 0.2, 0.6}:
        assert required_v in vols, f"Missing vol {required_v} in {vols}"
    assert has_nonzero_q, "Missing non-zero q in grid"
    assert has_negative_r, "Missing negative r in grid"


def test_crosscheck_generator_consistency():
    sys.path.insert(0, os.path.join(ROOT, "scripts"))
    import gen_grid
    pts = gen_grid.load_and_validate_grid()
    assert gen_grid.check_crosscheck_file(pts), "Embedded Lean grid out of sync with golden_grid.json"


def test_oracle_grid_self_consistency():
    grid = load_grid()
    for pt in grid:
        orc = compute_oracle(pt)
        assert orc["d1"] > orc["d2"], f"Point {pt}: d1 <= d2"
        # Numerical put-call parity check in oracle
        assert abs(orc["put"] - orc["parity"]) < 1e-13, f"Point {pt}: parity violated in oracle"
        # Numerical T3 in the oracle's own tree (measured max 7.2e-15; see the
        # tolerance note at the top of this file).
        assert abs(orc["delta_lhs"] - orc["delta_rhs"]) < 1e-12, (
            f"Point {pt}: delta identity violated inside the oracle "
            f"(|lhs - rhs| = {abs(orc['delta_lhs'] - orc['delta_rhs']):.3e})"
        )


def test_crosscheck_mutant_detection():
    """Verify that crosscheck() actually rejects perturbed calculations (non-vacuity)."""
    grid = load_grid()
    base_records = [compute_oracle(pt) for pt in grid]

    # Baseline must pass
    ok, errs, _ = crosscheck(base_records, grid)
    assert ok, f"Baseline crosscheck failed: {errs}"

    # Mutant 1: d2 perturbed by +sigma*sqrt(tau)
    m1_records = [r.copy() for r in base_records]
    m1_records[0]["d2"] += 0.05
    ok1, errs1, _ = crosscheck(m1_records, grid)
    assert not ok1 and any("d2 divergence" in e for e in errs1), "Failed to catch d2 mutation"

    # Mutant 2: call perturbed
    m2_records = [r.copy() for r in base_records]
    m2_records[0]["call"] += 0.01
    ok2, errs2, _ = crosscheck(m2_records, grid)
    assert not ok2 and any("call divergence" in e for e in errs2), "Failed to catch call mutation"

    # Mutant 3: put perturbed
    m3_records = [r.copy() for r in base_records]
    m3_records[0]["put"] += 0.01
    ok3, errs3, _ = crosscheck(m3_records, grid)
    assert not ok3 and any("put divergence" in e for e in errs3), "Failed to catch put mutation"

    # Mutant 4: parity perturbed
    m4_records = [r.copy() for r in base_records]
    m4_records[0]["parity"] += 0.01
    ok4, errs4, _ = crosscheck(m4_records, grid)
    assert not ok4 and any("parity divergence" in e for e in errs4), "Failed to catch parity mutation"

    # Mutant 5: delta-identity RHS perturbed. This is the C6 item 4 regression
    # class: before the fix, the comparator never SAW an RHS at all.
    m5_records = [r.copy() for r in base_records]
    m5_records[0]["delta_rhs"] += 0.01
    ok5, errs5, _ = crosscheck(m5_records, grid)
    assert not ok5 and any("delta-rhs divergence" in e for e in errs5), (
        "Failed to catch delta-identity RHS mutation -- T3's right-hand side is "
        "silent again"
    )

    # Mutant 6: delta-identity LHS perturbed.
    m6_records = [r.copy() for r in base_records]
    m6_records[0]["delta_lhs"] += 0.01
    ok6, errs6, _ = crosscheck(m6_records, grid)
    assert not ok6 and any("delta-lhs divergence" in e for e in errs6), "Failed to catch delta-identity LHS mutation"

    # Mutant 7: RHS computed from the LHS's formula (phi(d1) instead of
    # phi(d2)) at a single point -- a formula-level corruption, not a value
    # blip. Must be caught via BOTH the cross-tree comparison and the
    # Lean-internal identity. The corruption is applied at the grid point of
    # LARGEST delta RHS: at the deep-OTM points the identity's two sides are
    # ~1e-30, below any absolute tolerance, so no absolute-tolerance comparator
    # could ever see the swap there (a fact worth stating, not discovering).
    idx = max(range(len(grid)), key=lambda i: base_records[i]["delta_rhs"])
    pt_big = grid[idx]
    m7_records = [r.copy() for r in base_records]
    m7_records[idx]["delta_rhs"] = (
        pt_big["K"] * math.exp(-pt_big["r"] * pt_big["tau"]) * norm_pdf(base_records[idx]["d1"])
    )
    ok7, errs7, _ = crosscheck(m7_records, grid)
    assert not ok7 and any("delta-rhs divergence" in e for e in errs7), "Failed to catch formula-level RHS mutation"
    assert any("internal delta identity" in e for e in errs7), "Failed to catch formula-level RHS mutation internally"


def test_parse_rejects_old_and_malformed_ck_lines():
    """The pre-fix 13-token format (no delta RHS column) must be REJECTED, loudly.

    C6 item 4: the comparator used to accept a stream with no RHS column, so a
    twin that stopped emitting the RHS would degrade the check silently.
    """
    # Well-formed 14-token line parses:
    good = "CK 100.0 100.0 1.0 0.05 0.0 0.2 0.2350319 -0.2349681 10.45 5.57 5.57 37.52 37.52"
    rec = parse_lean_lines([good])
    assert len(rec) == 1 and rec[0]["delta_rhs"] == 37.52
    # 13-token line (the old LHS-only format) raises:
    old = "CK 100.0 100.0 1.0 0.05 0.0 0.2 0.2350319 -0.2349681 10.45 5.57 5.57 37.52"
    try:
        parse_lean_lines([old])
    except ValueError:
        pass
    else:
        raise AssertionError("13-token CK line was accepted")
    # Garbage token count also raises:
    try:
        parse_lean_lines(["CK 1 2 3"])
    except ValueError:
        pass
    else:
        raise AssertionError("garbage CK line was accepted")


def test_run_lean_flag_is_honored():
    """C6 item 4, second defect: `--run-lean` must never silently self-skip.

    Reproduces the recorded failure `echo -n | python3 tests/test_crosscheck.py
    --run-lean` in an environment scrubbed of `lake`: the flag names an input
    source explicitly, so when that source is unavailable the run must be a
    loud FAIL -- never the "4/4 unit tests passed" self-test fallback.
    """
    env = dict(os.environ)
    env["PATH"] = ""  # no lake, anywhere
    proc = subprocess.run(
        [sys.executable, os.path.join(ROOT, "tests", "test_crosscheck.py"), "--run-lean"],
        input="",                       # stdin NOT a tty -- the exact recorded trigger
        capture_output=True,
        text=True,
        env=env,
    )
    assert proc.returncode != 0, (
        f"--run-lean with no lake and a non-tty stdin exited 0 (the sinkhole returns):\n"
        f"stdout:\n{proc.stdout}"
    )
    assert "lake" in proc.stderr.lower(), f"error did not name the missing tool:\n{proc.stderr}"
    assert "unit test(s) passed" not in proc.stdout, (
        "--run-lean fell back to the self-test suite -- silent acceptance"
    )

    # Conflict between two named input sources is an error, not a precedence rule.
    proc2 = subprocess.run(
        [sys.executable, os.path.join(ROOT, "tests", "test_crosscheck.py"),
         "--run-lean", "--lean-output", "whatever.log"],
        input="",
        capture_output=True,
        text=True,
        env=env,
    )
    assert proc2.returncode != 0 and "conflict" in proc2.stderr.lower(), (
        "--run-lean + --lean-output must be rejected as contradictory"
    )


def run_lean_crosscheck() -> tuple[list[str], str | None]:
    """Invoke `lake env lean ImprovedBS/Crosscheck.lean`.

    Returns (output lines, None) on success, or ([], error message) on any
    failure -- including `lake` simply not existing, which is an ordinary,
    expected situation in a toolchain-free sandbox and must be a clean error,
    never a traceback or a silent fallback.
    """
    exe = shutil.which("lake")
    if exe is None:
        return [], (
            "FAIL: `lake` not found on PATH, so the requested Lean run cannot be "
            "honored.\nOptions: install the toolchain, use `--lean-output FILE` with "
            "captured output, or pipe `lake env lean ...` output on stdin.\n"
            "(Run without `--run-lean` for the standalone self-test suite.)"
        )
    cmd = [exe, "env", "lean", CROSSCHECK_LEAN_PATH]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True)
    except OSError as e:
        return [], f"FAIL: could not execute '{' '.join(cmd)}': {e}"
    if proc.returncode != 0:
        return [], (
            "FAIL: 'lake env lean' returned non-zero exit code:\n" + proc.stderr
        )
    return proc.stdout.splitlines(), None


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Oracle ↔ Lean pointwise cross-verifier",
        epilog="Input sources, in the order they take effect: --run-lean (explicit; "
               "errors if lake is unavailable), --lean-output FILE, piped stdin, "
               "then -- if a tty and lake exists -- an automatic Lean run, else the "
               "standalone self-test suite. An explicit source is honored or fails "
               "loudly; it never degrades into the self-test suite.",
    )
    parser.add_argument("--lean-output", type=str, help="Path to file containing Lean stdout")
    parser.add_argument("--run-lean", action="store_true", help="Invoke 'lake env lean ImprovedBS/Crosscheck.lean'")
    args = parser.parse_args()

    if args.run_lean and args.lean_output:
        print(
            "FAIL: conflicting input sources: --run-lean and --lean-output name "
            "different ones. Pick one.",
            file=sys.stderr,
        )
        return 1

    grid = load_grid()

    raw_lines: list[str] = []

    if args.run_lean:
        # Explicit first: `not sys.stdin.isatty()` used to claim the input
        # before this branch, so a piped (e.g. CI) invocation of --run-lean
        # silently self-skipped into the unit tests (ledger C6 item 4).
        raw_lines, err = run_lean_crosscheck()
        if err is not None:
            print(err, file=sys.stderr)
            return 1
    elif args.lean_output:
        with open(args.lean_output, "r", encoding="utf-8") as f:
            raw_lines = f.readlines()
    elif not sys.stdin.isatty():
        raw_lines = sys.stdin.readlines()
    elif shutil.which("lake") is not None:
        raw_lines, err = run_lean_crosscheck()
        if err is not None:
            print(err, file=sys.stderr)
            return 1

    if raw_lines:
        try:
            lean_records = parse_lean_lines(raw_lines)
        except ValueError as e:
            print(f"FAIL: {e}", file=sys.stderr)
            return 1
        if not lean_records:
            print("FAIL: no 'CK' lines found in Lean output.", file=sys.stderr)
            return 1

        ok, errors, max_diffs = crosscheck(lean_records, grid)
        if not ok:
            print(f"FAIL: {len(errors)} cross-verification error(s) detected:\n", file=sys.stderr)
            for err_line in errors[:20]:
                print(f"  * {err_line}", file=sys.stderr)
            if len(errors) > 20:
                print(f"  ... and {len(errors) - 20} more errors", file=sys.stderr)
            return 1

        print(f"OK: {len(lean_records)}/{len(grid)} grid points cross-verified successfully.")
        print(
            f"Worst-case differences vs Oracle:\n"
            f"  d1:              {max_diffs['d1']:.3e}  (tol: {TOL_ARG})\n"
            f"  d2:              {max_diffs['d2']:.3e}  (tol: {TOL_ARG})\n"
            f"  bsCall:          {max_diffs['call']:.3e}  (tol: {TOL_PRICE})\n"
            f"  bsPut:           {max_diffs['put']:.3e}  (tol: {TOL_PRICE})\n"
            f"  parity:          {max_diffs['parity']:.3e}  (tol: {TOL_PRICE})\n"
            f"  delta (lhs):     {max_diffs['delta_lhs']:.3e}  (tol: {TOL_DELTA})\n"
            f"  delta (rhs):     {max_diffs['delta_rhs']:.3e}  (tol: {TOL_DELTA})\n"
            f"  internal parity: {max_diffs['internal_parity']:.3e}\n"
            f"  internal delta:  {max_diffs['internal_delta']:.3e}  (T3: |lhs - rhs| inside the Lean stream)"
        )
        return 0

    # Standalone mode without toolchain: run unit tests
    fns = [
        test_golden_grid_schema_and_domain,
        test_crosscheck_generator_consistency,
        test_oracle_grid_self_consistency,
        test_crosscheck_mutant_detection,
        test_parse_rejects_old_and_malformed_ck_lines,
        test_run_lean_flag_is_honored,
    ]
    fails = 0
    for fn in fns:
        try:
            fn()
            print(f"  ok  {fn.__name__}")
        except Exception as e:
            fails += 1
            print(f"FAIL  {fn.__name__}: {e}")
    print(f"\n{len(fns)-fails}/{len(fns)} crosscheck unit test(s) passed.")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
