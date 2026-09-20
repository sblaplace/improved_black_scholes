#!/usr/bin/env python3
"""
Oracle ↔ Lean pointwise cross-verifier (BRIEF_002, docs/04 guard 3).

Reads the golden parameter grid (tests/golden_grid.json), evaluates the six
core quantities (d1, d2, call, put, parity, delta identity) via the Python
oracle (experiments/black_scholes.py) and compares against the Lean Float
evaluations emitted by ImprovedBS/Crosscheck.lean.

This is a **cross-verifier, not a proof.** It detects drift between the two
independent trees.

Usage:
    # 1. Piped from Lean in CI:
    lake env lean ImprovedBS/Crosscheck.lean | python3 tests/test_crosscheck.py

    # 2. Reading a pre-captured output log:
    python3 tests/test_crosscheck.py --lean-output lean_crosscheck.log

    # 3. Running Lean directly (when lake is installed):
    python3 tests/test_crosscheck.py --run-lean

    # 4. Standalone / unit-test mode (validates grid & oracle self-consistency):
    python3 tests/test_crosscheck.py
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
TOL_PRICE = 1e-12
TOL_ARG = 1e-12
TOL_DELTA = 1e-12


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
    delta = S * math.exp(-q * tau) * norm_pdf(d1)
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
        "delta": delta,
    }


def parse_lean_lines(lines: list[str]) -> list[dict[str, float]]:
    parsed = []
    for line in lines:
        line = line.strip()
        if not line.startswith("CK "):
            continue
        parts = line.split()
        if len(parts) != 13:
            raise ValueError(f"Malformed CK line ({len(parts)} tokens, expected 13): '{line}'")
        parsed.append({
            "S": float(parts[1]),
            "K": float(parts[2]),
            "tau": float(parts[3]),
            "r": float(parts[4]),
            "q": float(parts[5]),
            "sigma": float(parts[6]),
            "d1": float(parts[7]),
            "d2": float(parts[8]),
            "call": float(parts[9]),
            "put": float(parts[10]),
            "parity": float(parts[11]),
            "delta": float(parts[12]),
        })
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
        "delta": 0.0,
        "internal_parity": 0.0,
    }

    for idx, (lean, pt) in enumerate(zip(lean_records, grid)):
        orc = compute_oracle(pt)

        # Coordinate check
        for param in ("S", "K", "tau", "r", "q", "sigma"):
            if abs(lean[param] - pt[param]) > 1e-9:
                errors.append(
                    f"Point {idx}: parameter {param} mismatch (Lean: {lean[param]}, grid: {pt[param]})"
                )

        diff_d1 = abs(lean["d1"] - orc["d1"])
        diff_d2 = abs(lean["d2"] - orc["d2"])
        diff_call = abs(lean["call"] - orc["call"])
        diff_put = abs(lean["put"] - orc["put"])
        diff_parity = abs(lean["parity"] - orc["parity"])
        diff_delta = abs(lean["delta"] - orc["delta"])
        diff_internal_parity = abs(lean["put"] - lean["parity"])

        max_diffs["d1"] = max(max_diffs["d1"], diff_d1)
        max_diffs["d2"] = max(max_diffs["d2"], diff_d2)
        max_diffs["call"] = max(max_diffs["call"], diff_call)
        max_diffs["put"] = max(max_diffs["put"], diff_put)
        max_diffs["parity"] = max(max_diffs["parity"], diff_parity)
        max_diffs["delta"] = max(max_diffs["delta"], diff_delta)
        max_diffs["internal_parity"] = max(max_diffs["internal_parity"], diff_internal_parity)

        pt_str = f"(S={pt['S']}, K={pt['K']}, tau={pt['tau']}, r={pt['r']}, q={pt['q']}, sigma={pt['sigma']})"

        if diff_d1 > tol_arg:
            errors.append(f"{pt_str} d1 divergence: Lean={lean['d1']}, Oracle={orc['d1']}, diff={diff_d1:.3e} > {tol_arg}")
        if diff_d2 > tol_arg:
            errors.append(f"{pt_str} d2 divergence: Lean={lean['d2']}, Oracle={orc['d2']}, diff={diff_d2:.3e} > {tol_arg}")
        if diff_call > tol_price:
            errors.append(f"{pt_str} call divergence: Lean={lean['call']}, Oracle={orc['call']}, diff={diff_call:.3e} > {tol_price}")
        if diff_put > tol_price:
            errors.append(f"{pt_str} put divergence: Lean={lean['put']}, Oracle={orc['put']}, diff={diff_put:.3e} > {tol_price}")
        if diff_parity > tol_price:
            errors.append(f"{pt_str} parity divergence: Lean={lean['parity']}, Oracle={orc['parity']}, diff={diff_parity:.3e} > {tol_price}")
        if diff_delta > tol_delta:
            errors.append(f"{pt_str} delta divergence: Lean={lean['delta']}, Oracle={orc['delta']}, diff={diff_delta:.3e} > {tol_delta}")
        if diff_internal_parity > tol_price:
            errors.append(f"{pt_str} Lean internal parity violated: |bsPut - bsPutByParity| = {diff_internal_parity:.3e} > {tol_price}")

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


def main() -> int:
    parser = argparse.ArgumentParser(description="Oracle ↔ Lean pointwise cross-verifier")
    parser.add_argument("--lean-output", type=str, help="Path to file containing Lean stdout")
    parser.add_argument("--run-lean", action="store_true", help="Invoke 'lake env lean ImprovedBS/Crosscheck.lean'")
    args = parser.parse_args()

    grid = load_grid()

    raw_lines: list[str] = []

    if args.lean_output:
        with open(args.lean_output, "r", encoding="utf-8") as f:
            raw_lines = f.readlines()
    elif not sys.stdin.isatty():
        raw_lines = sys.stdin.readlines()
    elif args.run_lean or shutil.which("lake") is not None:
        cmd = ["lake", "env", "lean", CROSSCHECK_LEAN_PATH]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        if proc.returncode != 0:
            print("FAIL: 'lake env lean' returned non-zero exit code:", file=sys.stderr)
            print(proc.stderr, file=sys.stderr)
            return 1
        raw_lines = proc.stdout.splitlines()

    if raw_lines:
        lean_records = parse_lean_lines(raw_lines)
        if not lean_records:
            print("FAIL: no 'CK' lines found in Lean output.", file=sys.stderr)
            return 1

        ok, errors, max_diffs = crosscheck(lean_records, grid)
        if not ok:
            print(f"FAIL: {len(errors)} cross-verification error(s) detected:\n", file=sys.stderr)
            for err in errors[:20]:
                print(f"  * {err}", file=sys.stderr)
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
            f"  delta:           {max_diffs['delta']:.3e}  (tol: {TOL_DELTA})\n"
            f"  internal parity: {max_diffs['internal_parity']:.3e}"
        )
        return 0

    # Standalone mode without toolchain: run unit tests
    fns = [
        test_golden_grid_schema_and_domain,
        test_crosscheck_generator_consistency,
        test_oracle_grid_self_consistency,
        test_crosscheck_mutant_detection,
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
