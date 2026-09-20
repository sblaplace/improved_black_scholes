#!/usr/bin/env python3
"""
Statement pins: turn "the protected theorems say what the ledger claims" from a
prose claim into a checked one.

WHY THIS FILE EXISTS
--------------------
`lake build` is the authority on whether a proof is *correct*. Nothing in this
repository was the authority on whether a theorem is still *the theorem* --
including `scripts/lean_lint.py`, which inspects names, markers and definition
RHSes but never a statement. The gap is not hypothetical:

    theorem t4_call_bounds (S K tau r q sigma : ℝ)
        (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) : True := by
      trivial

passes `lake build`, passes `#print axioms` (no `sorryAx`: `True` is genuinely
provable, which is what makes it a *sound* way to say nothing), passes
`scripts/lean_lint.py`, and leaves the oracle suite at 13/13 because the oracle
has no idea what a Lean statement is. A landed node could be hollowed out
without a single lane going red. That is precisely the failure mode README calls
"a green check that could not have been red", and this file closes it.

THE RULE
--------
For every declaration in `lean_lint.REQUIRED | lean_lint.PROTECTED`:

  * a `theorem`/`lemma` is pinned by its **statement** -- the text from the
    declaration keyword through the first `:=`, comments stripped and whitespace
    collapsed. Proofs may be rewritten freely; a statement may not. This is
    deliberate: a better tactic is not a change to the claim, and forcing a
    golden-file diff for one would train people to regenerate without reading.
  * a `def` is pinned by its **whole body**, because a definition *is* the
    specification. Editing `Phi := (1 + erf (x / sqrt 2)) / 2` into anything
    else changes what every theorem in the tree is about, which is exactly the
    kind of change that must show up as a diff in `tests/golden_statements.json`.

The artifact is a committed file, so weakening a claim is always a reviewable
diff -- the same idiom as `lean_lint.py --write-baseline`, where the baseline may
move only by an act that shows up in the patch.

TWO LAYERS
----------
1. **Source-level pins** (`pins`) need no toolchain, so `scripts/lean_lint.py`
   enforces them in the `lint` job, on any runner, in any sandbox. This is the
   layer that catches the `: True` hollowing above.
2. **Elaborated pins** (`elab`) are the `#check` type and the `#print axioms`
   output per constant, produced by `lake env lean`. They catch what a text
   comparison cannot: a statement that *reads* the same but elaborates
   differently (a notation change, a shadow, an unintended coercion). These can
   only be produced where a toolchain exists, so the `build` job regenerates and
   diffs them; the `lint` job never runs them.

`--write` refreshes layer 1 and never touches the `elab` block, so a local
author without a toolchain cannot accidentally drop the elaborated pins.

Run:  python3 scripts/pin_statements.py --check       # layer 1, no toolchain
      python3 scripts/pin_statements.py --write       # regenerate layer 1
      python3 scripts/pin_statements.py --elab-check  # layer 2 diff (needs lake)
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(SCRIPTS)
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)

import lean_lint as LL  # noqa: E402  (module-level defs only; importing is side-effect free)

GOLDEN_PATH = os.path.join(ROOT, "tests", "golden_statements.json")
LEAN_NAMESPACE = "BSM"

# Kinds whose *statement* (everything before the first `:=`) is the contract.
STATEMENT_KINDS = ("theorem", "lemma", "example")

# A fixed path for the generated audit file: `#check` output embeds the file name
# in message prefixes on some runners, and pinning text that varies per machine
# would make the diff meaningless.
AUDIT_PATH = "/tmp/bsm_pin_audit.lean"

_MSG_PREFIX = re.compile(
    r"^[^\s:]*\.lean(?::\d+){0,3}:\s*(?:information|warning|error):\s*", re.MULTILINE
)


def normalize(text: str) -> str:
    """Collapse whitespace and drop `file:line:col: information:` message prefixes.

    Writer and checker both run this, so even if a prefix survives on some
    runner it survives identically on both sides of the comparison.
    """
    text = _MSG_PREFIX.sub("", text)
    return " ".join(text.split())


def _trim_body(body: str) -> str:
    """Cut a declaration body where it stops being the declaration.

    `lean_lint.declarations()` delimits a body at the *next* declaration, so the
    last declaration in a file would otherwise swallow `end BSM` and any
    `#eval`/`#print` after it. Those are not part of the claim.
    """
    out = []
    for line in body.split("\n"):
        s = line.strip()
        if s.startswith("end ") or s.startswith("section ") or s.startswith("#"):
            break
        out.append(line)
    return "\n".join(out)


def pin_text(kind: str, body: str) -> str:
    """The pinned text: statement for theorems, whole body for definitions.

    Splitting on the *first* `:=` is safe for this tree's statements -- nothing in
    a `∀`-telescope or a `→`-chain contains `:=`, and `=>` (as in
    `fun x => ...`) is a different token.
    """
    body = _trim_body(body)
    if kind in STATEMENT_KINDS:
        body = body.split(":=", 1)[0]
    return normalize(body)


def pinned_names() -> list[str]:
    """Everything the pins must cover: the required stack and the protected node.

    A theorem added to `PROTECTED` when a brief lands is automatically in scope,
    so the pin list cannot be dodged by forgetting to add it here.
    """
    return sorted(set(LL.REQUIRED) | set(LL.PROTECTED))


def extract() -> tuple[dict, list[str]]:
    """Recompute the pins from the current Lean sources. Returns (pins, errors)."""
    names = pinned_names()
    want_files = sorted({LL.REQUIRED.get(n, "ImprovedBS/Core.lean") for n in names})
    pins: dict[str, dict] = {}
    errors: list[str] = []

    for rel in want_files:
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            errors.append(f"[PINS] pinned file {rel} not found")
            continue
        decls = LL.declarations(LL.strip_comments(open(path, encoding="utf-8").read()))
        # Duplicate detection. `name -> body` dicts are last-wins, so a trivial
        # second `theorem t4_call_bounds ... : True` smuggled in below the real
        # one would silently become "the" declaration for some checks. Two
        # declarations of one pinned name is a red, never a preference.
        seen: set[str] = set()
        for kind, name, _line, body in decls:
            short = name.split(".")[-1]
            if short not in names:
                continue
            if short in seen:
                errors.append(
                    f"[PINS] `{short}` is declared more than once in {rel}; a duplicate "
                    "shadow is not a way to keep a pin green while hollowing the claim."
                )
                continue
            seen.add(short)
            pins[f"{LEAN_NAMESPACE}.{short}"] = {
                "kind": kind,
                "file": rel,
                "pin": pin_text(kind, body),
            }

    missing = [n for n in names if f"{LEAN_NAMESPACE}.{n}" not in pins]
    if missing:
        errors.append(
            "[PINS] no pinned text could be extracted for: " + ", ".join(missing)
            + ". A protected declaration that cannot be read is not a protected "
            "declaration -- find it, do not drop it from REQUIRED/PROTECTED."
        )
    return pins, errors


def load_golden() -> dict:
    if not os.path.exists(GOLDEN_PATH):
        return {}
    with open(GOLDEN_PATH, encoding="utf-8") as fh:
        return json.load(fh)


def save_golden(pins: dict, elab: dict) -> None:
    payload = {
        "_read_this": (
            "Pinned claims for the protected Lean stack. A theorem is pinned by its "
            "STATEMENT (through the first `:=`), a definition by its BODY; whitespace is "
            "collapsed and comments stripped, so a reformatted proof is free and a "
            "reworded claim is not. `pins` is enforced by scripts/lean_lint.py with no "
            "toolchain. `elab` holds the #check type and #print axioms output and is "
            "enforced by the lake-build job, which can run a toolchain. Weakening, "
            "renaming away, or deleting an entry here is not a way to pass CI: the key "
            "set is derived from REQUIRED|PROTECTED in lean_lint.py. Regenerate with "
            "`python3 scripts/pin_statements.py --write`; the diff is the audit trail, "
            "and it must be read before it is committed."
        ),
        "_generated_by": "python3 scripts/pin_statements.py --write",
        "namespace": LEAN_NAMESPACE,
        "pins": pins,
        "elab": elab,
    }
    with open(GOLDEN_PATH, "w", encoding="utf-8") as fh:
        # ensure_ascii=False: this file IS the review artifact, and an unreadable
        # diff of \u211d escapes is a diff nobody reads. Unicode statements stay unicode.
        json.dump(payload, fh, indent=2, sort_keys=True, ensure_ascii=False)
        fh.write("\n")


def check() -> list[str]:
    """Layer 1: source text vs committed pins. No toolchain needed."""
    pins, errors = extract()
    if not os.path.exists(GOLDEN_PATH):
        return errors + [
            f"[PINS] {os.path.relpath(GOLDEN_PATH, ROOT)} is missing. Generate it with "
            "`python3 scripts/pin_statements.py --write` and commit it. The lint refuses "
            "to invent its own baseline."
        ]
    gpins = load_golden().get("pins", {})
    if not gpins:
        return errors + [
            "[PINS] committed pins are empty -- that is not a baseline, it is a bypass. "
            "Run `python3 scripts/pin_statements.py --write`."
        ]
    for key in sorted(gpins):
        if key not in pins:
            errors.append(
                f"[PINS] `{key}` is pinned in the golden file but absent from the tree. "
                "Deleting a theorem is not a way to make this lint pass."
            )
    for key, got in sorted(pins.items()):
        if key not in gpins:
            errors.append(
                f"[PINS] `{key}` has no committed pin. Add it with "
                "`python3 scripts/pin_statements.py --write`."
            )
            continue
        want = gpins[key]
        if want.get("kind") != got["kind"]:
            errors.append(
                f"[PINS] `{key}` changed kind: pinned `{want.get('kind')}`, source has "
                f"`{got['kind']}`. Turning a theorem into a definition (or an `example`) "
                "drops it out of the checked stack; that must be a reviewed diff."
            )
        if normalize(want.get("pin", "")) != got["pin"]:
            errors.append(
                f"[PINS] `{key}` no longer matches its pinned statement.\n"
                f"       pinned: {want.get('pin')}\n"
                f"       source: {got['pin']}\n"
                "       If the claim genuinely changed, regenerate and review the diff. "
                "If the proof improved and the claim did not, this failure means the "
                "statement text moved -- check for a weakened hypothesis."
            )
    return errors


# ---------------------------------------------------------------- elaboration

def audit_source(qualified: list[str]) -> str:
    """The Lean file whose output *is* the elaborated pin.

    `@@END@@` sentinels let the reader join wrapped lines without guessing where
    one declaration's output ends, because `#check` breaks long types across
    lines. `#eval IO.println` is the same mechanism `ImprovedBS/Crosscheck.lean`
    already relies on, so it needs no new Lean API surface -- an important
    property while the tree is authored without a toolchain.
    """
    lines = ["import ImprovedBS", ""]
    for q in qualified:
        lines += [
            f"#check @{q}",
            '#eval IO.println "@@END@@"',
            f"#print axioms {q}",
            '#eval IO.println "@@END@@"',
            "",
        ]
    return "\n".join(lines)


def elaborate(pins: dict) -> dict:
    """Run the audit through `lake env lean`; return {name: {type, axioms}}.

    Parsing is by line *prefix*, not by line count: a chunk belonging to `q`
    starts at `BSM.q :` (the `#check` echo) and the axiom line is the one that
    says `depends on axioms` / `does not depend on any axioms`. Anything that
    fails to parse raises rather than pinning a partial result -- a half-pin is
    worse than a red build, because it looks like a checked claim.
    """
    qualified = sorted(pins)
    if shutil.which("lake") is None:
        raise RuntimeError(
            "no `lake` on PATH. Elaborated pins are CI-only; layer 1 (`--check`) is "
            "the one that runs everywhere."
        )
    with open(AUDIT_PATH, "w", encoding="utf-8") as fh:
        fh.write(audit_source(qualified))
    proc = subprocess.run(
        ["lake", "env", "lean", AUDIT_PATH], cwd=ROOT, capture_output=True, text=True
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout + proc.stderr)
        raise RuntimeError(
            f"`lake env lean {AUDIT_PATH}` failed; refusing to pin nothing."
        )
    if "sorryAx" in proc.stdout:
        raise RuntimeError("[PINS][ELAB] sorryAx in the audit output -- refusing to pin it.")
    # The generated file emits, per constant: #check, sentinel, #print axioms,
    # sentinel. So stdout splits into 2N blocks in exactly `qualified` order --
    # no guessing which line belongs to which declaration, and no dependence on
    # how Lean chooses to wrap a long type.
    blocks = [[ln for ln in b.splitlines() if ln.strip()] for b in proc.stdout.split("@@END@@")]
    if len(blocks) < 2 * len(qualified):
        raise RuntimeError(
            f"[PINS][ELAB] expected {2 * len(qualified)} @@END@@-delimited blocks, got "
            f"{len(blocks)}. The audit file or the sentinel mechanism changed; fix the "
            "parser rather than pinning a partial result."
        )

    def block_text(block: list[str], q: str) -> str:
        """Drop leading noise lines (a stray warning before our echo), keep the rest.

        Lean's own output for both commands starts with the constant name, so the
        first such line is the start of the payload and everything after it is
        either the same message wrapped or the message.
        """
        start = next((i for i, ln in enumerate(block) if ln.startswith(f"{q} ")), None)
        if start is None:
            return ""
        return normalize(" ".join(block[start:]))

    out: dict[str, dict] = {}
    for i, q in enumerate(qualified):
        ty = block_text(blocks[2 * i], q)
        ax = block_text(blocks[2 * i + 1], q)
        if not ty or not ax:
            raise RuntimeError(
                f"[PINS][ELAB] could not recover both a type and an axiom line for `{q}` "
                f"(type={ty!r}, axioms={ax!r}). The `#check`/`#print axioms` output format "
                "is an assumption; repair the parser explicitly rather than committing a "
                "half-pin."
            )
        out[q] = {"type": ty, "axioms": ax}
    return out


def elab_check() -> tuple[list[str], dict]:
    """Layer 2, run where a toolchain exists (the `lake build` job)."""
    fresh = elaborate(load_pins_or_die())
    gel = load_golden().get("elab", {})
    if not gel:
        return (
            [
                "[PINS][ELAB] no elaborated pins are committed -- this is the bootstrap "
                "state. The `elab` object printed below is what CI just elaborated; commit "
                "it (or run `python3 scripts/pin_statements.py --elab-write` where a "
                "toolchain exists) and push. The build job stays red until then on "
                "purpose: a pin that was never produced is not a passing pin."
            ],
            fresh,
        )
    failures: list[str] = []
    for q, entry in sorted(fresh.items()):
        if q not in gel:
            failures.append(f"[PINS][ELAB] `{q}` is not elaboration-pinned.")
            continue
        for field in ("type", "axioms"):
            if normalize(gel[q].get(field, "")) != entry[field]:
                failures.append(
                    f"[PINS][ELAB] `{q}` {field} differs.\n"
                    f"       committed:  {gel[q].get(field, '')}\n"
                    f"       elaborated: {entry[field]}"
                )
    for q in sorted(set(gel) - set(fresh)):
        failures.append(
            f"[PINS][ELAB] `{q}` is pinned but no longer elaborated by the tree."
        )
    return failures, fresh


def load_pins_or_die() -> dict:
    pins, errors = extract()
    if errors:
        raise RuntimeError("[PINS][ELAB] cannot pin an unreadable tree:\n  " + "\n".join(errors))
    return pins


def main(argv: list[str]) -> int:
    if "--write" in argv:
        pins, errors = extract()
        if errors:
            print("\n".join(errors), file=sys.stderr)
            return 1
        save_golden(pins, load_golden().get("elab", {}))
        print(f"wrote {os.path.relpath(GOLDEN_PATH, ROOT)}: {len(pins)} pinned declaration(s)")
        return 0
    if "--elab-write" in argv:
        pins = load_pins_or_die()
        try:
            elab = elaborate(pins)
        except RuntimeError as e:
            print(f"FAIL [PINS][ELAB] {e}", file=sys.stderr)
            return 1
        save_golden(pins, elab)
        print(f"wrote {os.path.relpath(GOLDEN_PATH, ROOT)}: {len(pins)} pins, "
              f"{len(elab)} elaborated")
        return 0
    if "--elab-check" in argv:
        try:
            failures, fresh = elab_check()
        except RuntimeError as e:
            # No toolchain, an audit run that failed, or output we could not pair:
            # all three are "this layer did not run", never "this layer passed".
            print(f"FAIL [PINS][ELAB] {e}", file=sys.stderr)
            return 1
        if failures:
            for f in failures:
                print("FAIL", f)
            print("\n" + json.dumps({"elab": fresh}, indent=2, sort_keys=True))
            print(
                "\nThe block above is paste-ready because CI logs are readable from a "
                "sandbox via `gh api` and Actions artifacts are not -- the same reason "
                "the axioms audit is published to the PR."
            )
            return 1
        print("OK: elaborated types and axioms match the committed pins.")
        return 0
    failures = check()
    if failures:
        for f in failures:
            print("FAIL", f)
        print(f"\n{len(failures)} pin failure(s)")
        return 1
    pins, _ = extract()
    print(f"OK: {len(pins)} pinned declaration(s) match the tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
