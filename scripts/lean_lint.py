#!/usr/bin/env python3
"""
Lint for the Lean tree. **Needs no Lean toolchain**, so it runs in CI on any
runner and in any sandbox -- including ones where elan cannot be installed.

This exists because the repo's grading rule ("a `sorry` anywhere in the parity
/ d1-d2 node is an automatic reject", BRIEF_001) is a *syntactic* rule, and
syntactic rules should be checked syntactically. `lake build` is the authority
on whether a proof is correct; this script is the authority on whether the tree
is honestly labelled. Both lanes run in .github/workflows/lean.yml.

Checks
------
1. NAMESPACE      no `.lean` file under a top-level `Lean/` directory (that
                  makes the module `Lean.core.*` and squats the elaborator's
                  own namespace).
2. REQUIRED       every theorem in the committed stack must still be declared.
                  Stops the easiest way to make a lint pass: delete the theorem.
3. PROTECTED      zero `sorry`/`admit`/`native_decide` in the T1/T2 node, which
                  is the BRIEF_001 deliverable. Automatic reject.
4. RATCHET        repo-wide, the set of declarations containing a deferred-proof
                  marker must be a subset of the committed baseline, and the
                  total count must not exceed it. You may discharge a `sorry`;
                  you may not add one, and you may not move one from a deferred
                  node into a protected one.
5. AXIOMS         no new top-level `axiom` command outside the allowlist. An
                  `axiom` is a `sorry` that survives `lake build` silently.
6. INDEPENDENCE   the anti-vacuity guard, mirroring tests/test_mutants.py:
                  `d2` must not be defined in terms of `d1`, and `bsPut` must
                  not be defined in terms of `bsCall`. If either is, then T1 and
                  T2 are true by construction and a green build certifies
                  nothing. This is the check that would have caught the original
                  version of this file.
7. ORACLE SYNC    the Lean `def`s and the Python oracle must use the same
                  arithmetic: both `d1`/`d2` from independent explicit formulas,
                  both puts from an independent closed form. Guards against the
                  two trees drifting into proving different mathematics.

Exit status is non-zero on any failure, with every failure printed.

Usage:  python3 scripts/lean_lint.py                    # from the repo root
        python3 scripts/lean_lint.py --explain          # print the baseline and stop
        python3 scripts/lean_lint.py --write-baseline   # re-record the ratchet

`--write-baseline` is a deliberate, reviewable act: it records the CURRENT
deferred-proof markers as the new ceiling. Use it when landing a brief whose
scope explicitly defers nodes (e.g. T5), never to make a failing lint pass.
The diff of .github/lean_lint_baseline.json is the audit trail.
"""

from __future__ import annotations

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE_PATH = os.path.join(ROOT, ".github", "lean_lint_baseline.json")
ORACLE_PATH = os.path.join(ROOT, "experiments", "black_scholes.py")

# Declarations that must exist in the tree (name -> file).
REQUIRED = {
    "Phi": "ImprovedBS/Core.lean",
    "phi": "ImprovedBS/Core.lean",
    "d1": "ImprovedBS/Core.lean",
    "d2": "ImprovedBS/Core.lean",
    "bsCall": "ImprovedBS/Core.lean",
    "bsPut": "ImprovedBS/Core.lean",
    "Phi_add_Phi_neg": "ImprovedBS/Core.lean",
    "Phi_neg": "ImprovedBS/Core.lean",
    "t1_d1_minus_d2": "ImprovedBS/Core.lean",
    "t2_put_call_parity": "ImprovedBS/Core.lean",
    "t2_put_call_parity_spread": "ImprovedBS/Core.lean",
    "t3_delta_identity": "ImprovedBS/Core.lean",
    "t4_call_bounds": "ImprovedBS/Core.lean",
    "t4_put_bounds": "ImprovedBS/Core.lean",
}

# The T1/T2 node: zero deferred-proof markers allowed, per BRIEF_001.
PROTECTED = {
    "Phi_add_Phi_neg",
    "Phi_neg",
    "t1_d1_minus_d2",
    "t2_put_call_parity",
    "t2_put_call_parity_spread",
}

# A `sorry` that survives `lake build` is an axiom. Allow none by default.
AXIOM_ALLOWLIST: set[str] = set()

MARKERS = ("sorry", "admit", "native_decide")

DECL_RE = re.compile(
    r"^(theorem|lemma|def|instance|example|axiom|structure|class|abbrev)\s+"
    r"(?:\{[^}]*\}\s*)?([A-Za-z_][\w.']*)",
    re.MULTILINE,
)


def strip_comments(src: str) -> str:
    """Blank out Lean comments, preserving offsets so line numbers stay correct.

    Handles nested block comments (`/- ... -/`) and line comments (`--`).
    Doc-strings (`/-!`, `/--`) are comments too and get blanked; declarations
    are re-found in the stripped text, so nothing is lost.
    """
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth > 0:
            if out[i] != "\n":
                out[i] = " "
            i += 1
        else:
            i += 1
    return "".join(out)


def declarations(clean: str) -> list[tuple[str, str, int, str]]:
    """Return [(kind, name, line, body)] for every top-level declaration."""
    hits = list(DECL_RE.finditer(clean))
    result = []
    for idx, m in enumerate(hits):
        end = hits[idx + 1].start() if idx + 1 < len(hits) else len(clean)
        body = clean[m.start() : end]
        line = clean[: m.start()].count("\n") + 1
        result.append((m.group(1), m.group(2), line, body))
    return result


def lean_files() -> list[str]:
    found = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [
            d
            for d in dirnames
            if d not in {".git", ".lake", "node_modules", "__pycache__"} and not d.startswith(".")
        ]
        for f in filenames:
            if f.endswith(".lean"):
                found.append(os.path.relpath(os.path.join(dirpath, f), ROOT))
    return sorted(found)


def main() -> int:
    explain = "--explain" in sys.argv
    failures: list[str] = []
    notes: list[str] = []

    files = lean_files()
    if not files:
        print("FATAL: no .lean files found under", ROOT)
        return 2

    baseline = {"deferred": {}, "axioms": []}
    if os.path.exists(BASELINE_PATH):
        baseline = json.load(open(BASELINE_PATH))
    else:
        failures.append(f"[BASELINE] {os.path.relpath(BASELINE_PATH, ROOT)} is missing")

    decls_by_file: dict[str, list] = {}
    for rel in files:
        src = open(os.path.join(ROOT, rel), encoding="utf-8").read()
        clean = strip_comments(src)
        decls_by_file[rel] = declarations(clean)

        # 1. namespace squatting
        if rel.split(os.sep)[0] == "Lean":
            failures.append(
                f"[NAMESPACE] {rel}: a .lean file under a top-level Lean/ directory makes the "
                f"module Lean.* and squats the elaborator's namespace. Use ImprovedBS/."
            )

    all_decls = {name: (rel, kind, line, body)
                 for rel, ds in decls_by_file.items() for kind, name, line, body in ds}

    if explain:
        print("baseline:", json.dumps(baseline, indent=2))
        print("declarations found:")
        for rel, ds in decls_by_file.items():
            for kind, name, line, _ in ds:
                print(f"  {rel}:{line:<5} {kind} {name}")
        return 0

    # 2. required declarations still present
    for name, rel in REQUIRED.items():
        if name not in all_decls:
            failures.append(
                f"[REQUIRED] `{name}` is not declared anywhere (expected in {rel}). "
                f"Deleting a theorem is not a way to make this lint pass."
            )
        elif rel not in all_decls[name][0]:
            notes.append(f"[REQUIRED] `{name}` moved: expected {rel}, found {all_decls[name][0]}")

    # 3 + 4. deferred-proof markers
    found_deferred: dict[str, int] = {}
    for name, (rel, kind, line, body) in sorted(all_decls.items()):
        hits = []
        for marker in MARKERS:
            # word-boundary match, so `sorryAx`-free text like `nosorry` is not caught
            hits += [m for m in re.finditer(rf"\b{marker}\b", body)]
        if not hits:
            continue
        found_deferred[name] = len(hits)
        where = ", ".join(
            f"line {line + body[: h.start()].count(chr(10))}" for h in hits[:3]
        )
        if name in PROTECTED:
            failures.append(
                f"[PROTECTED] `{name}` ({rel}:{line}) contains "
                f"{', '.join(sorted({h.group(0) for h in hits}))} at {where}. "
                f"This is the T1/T2 node: an automatic reject per BRIEF_001."
            )

    base_deferred = baseline.get("deferred", {})
    new_names = sorted(set(found_deferred) - set(base_deferred))
    if new_names:
        failures.append(
            "[RATCHET] deferred-proof markers appeared in declarations not in the baseline: "
            + ", ".join(new_names)
            + f". Baseline allows: {sorted(base_deferred) or '(none)'}."
        )
    for name, count in sorted(found_deferred.items()):
        allowed = base_deferred.get(name)
        if allowed is not None and count > allowed:
            failures.append(
                f"[RATCHET] `{name}` has {count} markers, baseline allows {allowed}."
            )
    total_now, total_base = sum(found_deferred.values()), sum(base_deferred.values())
    if total_now > total_base:
        failures.append(f"[RATCHET] total markers {total_now} > baseline {total_base}")
    notes.append(
        f"[RATCHET] deferred markers: {total_now}/{total_base} budget "
        f"in {sorted(found_deferred) or '(no declarations)'}"
    )

    # 5. axioms
    axioms = sorted(
        name for name, (_, kind, _, _) in all_decls.items() if kind == "axiom"
    )
    unexpected = [a for a in axioms if a not in set(baseline.get("axioms", [])) | AXIOM_ALLOWLIST]
    if unexpected:
        failures.append(
            "[AXIOMS] new top-level axiom(s): " + ", ".join(unexpected)
            + ". An axiom is a `sorry` that survives `lake build` silently."
        )

    # 6. independence / anti-vacuity
    core = decls_by_file.get("ImprovedBS/Core.lean", [])
    bodies = {name: body for _, name, _, body in core}

    def def_body(name: str) -> str:
        """The right-hand side of `def name ... := <rhs>`, comments stripped."""
        b = bodies.get(name)
        if b is None:
            failures.append(f"[INDEPENDENCE] `def {name}` not found in ImprovedBS/Core.lean")
            return ""
        return b.split(":=", 1)[1] if ":=" in b else ""

    d2_rhs = def_body("d2")
    if re.search(r"\bd1\b", d2_rhs):
        failures.append(
            "[INDEPENDENCE] `d2` is defined in terms of `d1`. Then "
            "`t1_d1_minus_d2` is true by construction (`unfold d2; ring`) and a "
            "green build certifies nothing. Give d2 its own explicit formula."
        )
    put_rhs = def_body("bsPut")
    if re.search(r"\bbsCall\b", put_rhs):
        failures.append(
            "[INDEPENDENCE] `bsPut` is defined in terms of `bsCall`. Then "
            "`t2_put_call_parity` is true by construction and never exercises "
            "`Phi_add_Phi_neg`, which is the actual content of parity."
        )
    # and the converse: parity must be reachable from the symmetry lemma
    if "Phi_add_Phi_neg" in bodies and "t2_put_call_parity" in bodies:
        if "Phi_add_Phi_neg" not in bodies["t2_put_call_parity"]:
            failures.append(
                "[INDEPENDENCE] `t2_put_call_parity` does not cite "
                "`Phi_add_Phi_neg`. BRIEF_001 requires the symmetry lemma to be "
                "used, not merely to exist."
            )
    else:
        failures.append("[INDEPENDENCE] `Phi_add_Phi_neg` or `t2_put_call_parity` is missing")

    # 7. oracle sync
    if os.path.exists(ORACLE_PATH):
        orc = open(ORACLE_PATH, encoding="utf-8").read()

        def py_body(fn: str) -> str:
            """Body of `def fn(...)`, with `#` comments removed."""
            if f"def {fn}(" not in orc:
                return ""
            chunk = orc.split(f"def {fn}(", 1)[1].split("\ndef ", 1)[0]
            return re.sub(r"#.*", "", chunk)

        if "bs_put_by_parity" in py_body("bs_put"):
            failures.append(
                "[ORACLE SYNC] experiments/black_scholes.py derives `bs_put` from parity, "
                "while ImprovedBS/Core.lean defines `bsPut` independently. The two trees "
                "would then be checking different claims."
            )
        if re.search(r"return\s+d1,\s*d1\s*-", py_body("_d1d2")):
            failures.append(
                "[ORACLE SYNC] the oracle's `_d1d2` returns `d1 - s*sq` as d2, while the "
                "Lean `d2` is independent. Align them (docs/01 is the source of truth)."
            )
        notes.append("[ORACLE SYNC] oracle and Lean tree agree on independent derivations")
    else:
        failures.append(f"[ORACLE SYNC] {ORACLE_PATH} not found")

    if "--write-baseline" in sys.argv:
        protected_hits = sorted(set(found_deferred) & PROTECTED)
        if protected_hits:
            print(
                "REFUSING to write baseline: the protected T1/T2 node still contains "
                "deferred-proof markers: " + ", ".join(protected_hits) + "\n"
                "A baseline must never legitimise a `sorry` in a protected declaration."
            )
            return 1
        payload = {
            "_read_this": (
                "Ratchet ceiling for deferred-proof markers (sorry / admit / native_decide) "
                "in the Lean tree, enforced by scripts/lean_lint.py. A declaration may "
                "appear here only if its brief explicitly defers it. Lower a count when a "
                "proof lands; never raise one to make CI pass. The T1/T2 node "
                "(PROTECTED in lean_lint.py) may never appear here at all."
            ),
            "_generated_by": "python3 scripts/lean_lint.py --write-baseline",
            "deferred": {k: found_deferred[k] for k in sorted(found_deferred)},
            "axioms": axioms,
        }
        os.makedirs(os.path.dirname(BASELINE_PATH), exist_ok=True)
        with open(BASELINE_PATH, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2)
            fh.write("\n")
        print(
            f"wrote {os.path.relpath(BASELINE_PATH, ROOT)}: "
            f"{sum(found_deferred.values())} marker(s) across "
            f"{len(found_deferred)} declaration(s): {sorted(found_deferred)}"
        )
        return 0

    for n in notes:
        print("  note:", n)
    if failures:
        print()
        for f in failures:
            print("FAIL", f)
        print(f"\n{len(failures)} lint failure(s)")
        return 1
    print(f"\nlean lint: OK ({len(files)} .lean file(s), {len(all_decls)} declarations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
