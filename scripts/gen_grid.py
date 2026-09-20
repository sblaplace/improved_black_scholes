#!/usr/bin/env python3
"""
Generate or check the embedded golden grid in ImprovedBS/Crosscheck.lean from
tests/golden_grid.json.

Ensures tests/golden_grid.json remains the single source of truth for the
cross-verification parameter points.

Usage:
    python3 scripts/gen_grid.py             # format Lean grid definition to stdout
    python3 scripts/gen_grid.py --update    # update ImprovedBS/Crosscheck.lean in-place
    python3 scripts/gen_grid.py --check     # verify ImprovedBS/Crosscheck.lean matches JSON
"""

from __future__ import annotations

import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GRID_PATH = os.path.join(ROOT, "tests", "golden_grid.json")
CROSSCHECK_PATH = os.path.join(ROOT, "ImprovedBS", "Crosscheck.lean")


def load_and_validate_grid() -> list[dict[str, float]]:
    if not os.path.exists(GRID_PATH):
        raise FileNotFoundError(f"Missing {GRID_PATH}")
    with open(GRID_PATH, "r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, list) or not data:
        raise ValueError("Grid JSON must be a non-empty list of points")
    required_keys = {"S", "K", "tau", "r", "q", "sigma"}
    for idx, pt in enumerate(data):
        if not isinstance(pt, dict):
            raise ValueError(f"Point {idx} is not a dict: {pt}")
        missing = required_keys - set(pt.keys())
        if missing:
            raise ValueError(f"Point {idx} missing keys: {missing}")
        if pt["S"] <= 0:
            raise ValueError(f"Point {idx} has S <= 0: {pt}")
        if pt["K"] <= 0:
            raise ValueError(f"Point {idx} has K <= 0: {pt}")
        if pt["tau"] <= 0:
            raise ValueError(f"Point {idx} has tau <= 0: {pt}")
        if pt["sigma"] <= 0:
            raise ValueError(f"Point {idx} has sigma <= 0: {pt}")
    return data


def format_lean_float(x: float) -> str:
    s = f"{x}"
    if "." not in s and "e" not in s:
        s += ".0"
    return s


def render_lean_grid(points: list[dict[str, float]]) -> str:
    lines = [
        "def goldenGrid : List GridPoint := [",
    ]
    for pt in points:
        S = format_lean_float(pt["S"])
        K = format_lean_float(pt["K"])
        tau = format_lean_float(pt["tau"])
        r = format_lean_float(pt["r"])
        q = format_lean_float(pt["q"])
        sigma = format_lean_float(pt["sigma"])
        lines.append(f"  ⟨{S}, {K}, {tau}, {r}, {q}, {sigma}⟩,")
    lines.append("]")
    return "\n".join(lines)


def update_crosscheck_file(points: list[dict[str, float]]) -> None:
    rendered = render_lean_grid(points)
    if not os.path.exists(CROSSCHECK_PATH):
        raise FileNotFoundError(f"{CROSSCHECK_PATH} does not exist yet")
    content = open(CROSSCHECK_PATH, "r", encoding="utf-8").read()
    start_tag = "-- BEGIN GENERATED GOLDEN GRID"
    end_tag = "-- END GENERATED GOLDEN GRID"
    if start_tag not in content or end_tag not in content:
        raise ValueError(
            f"{CROSSCHECK_PATH} does not contain '{start_tag}' and '{end_tag}' markers"
        )
    prefix = content.split(start_tag)[0]
    suffix = content.split(end_tag)[1]
    new_content = f"{prefix}{start_tag}\n{rendered}\n{end_tag}{suffix}"
    with open(CROSSCHECK_PATH, "w", encoding="utf-8") as f:
        f.write(new_content)
    print(f"Updated {CROSSCHECK_PATH} with {len(points)} grid points.")


def check_crosscheck_file(points: list[dict[str, float]]) -> bool:
    if not os.path.exists(CROSSCHECK_PATH):
        print(f"FAIL: {CROSSCHECK_PATH} does not exist", file=sys.stderr)
        return False
    content = open(CROSSCHECK_PATH, "r", encoding="utf-8").read()
    start_tag = "-- BEGIN GENERATED GOLDEN GRID"
    end_tag = "-- END GENERATED GOLDEN GRID"
    if start_tag not in content or end_tag not in content:
        print(
            f"FAIL: {CROSSCHECK_PATH} missing generator markers", file=sys.stderr
        )
        return False
    actual_section = content.split(start_tag)[1].split(end_tag)[0].strip()
    expected_section = render_lean_grid(points).strip()
    if actual_section != expected_section:
        print(
            f"FAIL: {CROSSCHECK_PATH} grid differs from {GRID_PATH}. Run 'python3 scripts/gen_grid.py --update'",
            file=sys.stderr,
        )
        return False
    return True


def main() -> int:
    try:
        points = load_and_validate_grid()
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1

    if "--update" in sys.argv:
        try:
            update_crosscheck_file(points)
            return 0
        except Exception as e:
            print(f"ERROR: {e}", file=sys.stderr)
            return 1
    elif "--check" in sys.argv:
        ok = check_crosscheck_file(points)
        if ok:
            print(f"OK: {CROSSCHECK_PATH} matches {GRID_PATH} ({len(points)} points).")
            return 0
        return 1
    else:
        print(render_lean_grid(points))
        return 0


if __name__ == "__main__":
    sys.exit(main())
