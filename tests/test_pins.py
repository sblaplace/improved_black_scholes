#!/usr/bin/env python3
"""
Tests for the statement pins: `scripts/pin_statements.py`.

Why a test file for a *generator*? Because the pins have two layers and only one
of them can be exercised where this repository gets authored. The source layer
(`pins`) needs no toolchain and its mutants live in `tests/test_lint.py`
(P1–P7). The elaborated layer (`elab`) can only be produced by `lake env lean`,
which runs in CI -- and the first CI run of the pins found a real bug in it: the
parser assumed `#print axioms` echoes the constant bare, like `#check` does, but
Lean quotes it. Run 35519747870 failed with

    could not recover both a type and an axiom line for `BSM.Phi`
    (type='BSM.Phi : ℝ → ℝ', axioms='')

which is the designed behaviour (refuse rather than half-pin), and the designed
fix is not "patch CI and pray" -- it is to make the *protocol* testable without a
toolchain by parsing recorded output. So the samples below are the actual shapes
`lake env lean` emits, and they are what `parse_audit` is checked against.

Three properties matter and all three are tested here:
  * both output shapes parse (quoted and bare), long types included;
  * a truncated or shifted audit run raises instead of pinning something partial;
  * the generator and the parser agree on the sentinel protocol, so neither can
    drift alone.

Run:  python3 tests/test_pins.py      (stdlib only, no Lean toolchain)
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import pin_statements as P  # noqa: E402

GOLDEN = os.path.join(ROOT, "tests", "golden_statements.json")
LAST_NOTE: dict = {}

# ------------------------------------------------------------------ recorded CI

# Faithful to run 35519747870: `#check` prints `Name : type` bare and wraps long
# types across lines; `#print axioms` prints `'Name' depends on axioms: [...]`
# WITH quotes, and `does not depend on any axioms.` for axiom-free constants.
SAMPLE = "\n".join(
    [
        "BSM.Phi : ℝ → ℝ",
        P.SENTINEL,
        "'BSM.Phi' depends on axioms: [propext, Classical.choice, Quot.sound]",
        P.SENTINEL,
        "BSM.exp_neg_sq_even : ∀ (t : ℝ), Real.exp (-((-t) ^ 2)) = Real.exp (-(t ^ 2))",
        P.SENTINEL,
        "'BSM.exp_neg_sq_even' does not depend on any axioms.",
        P.SENTINEL,
        "BSM.t4_call_bounds : ∀ (S K tau r q sigma : ℝ), 0 < S → 0 < K →",
        "  0 < tau → 0 < sigma → max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0 ≤",
        "  BSM.bsCall S K tau r q sigma ∧ BSM.bsCall S K tau r q sigma ≤ S * Real.exp (-q * tau)",
        P.SENTINEL,
        "'BSM.t4_call_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]",
        P.SENTINEL,
        "",
    ]
)
# Blocks are paired with the name list *by position*, and `elaborate` emits in
# sorted order -- so a sample that is out of sorted order is a broken sample, not
# a broken parser. Recorded shapes from run 35519747870: `#check` bare, `#print
# axioms` quoted, long types wrapped.
QUALIFIED = ["BSM.Phi", "BSM.exp_neg_sq_even", "BSM.t4_call_bounds"]  # sorted order


def test_parse_audit_replays_recorded_ci_output():
    """Both message shapes, plus a type wrapped over three lines, from the recorded run."""
    got = P.parse_audit(SAMPLE, QUALIFIED)
    assert got["BSM.Phi"]["type"] == "BSM.Phi : ℝ → ℝ"
    assert got["BSM.Phi"]["axioms"] == (
        "'BSM.Phi' depends on axioms: [propext, Classical.choice, Quot.sound]"
    )
    # The wrapped type must be rejoined, not truncated at the first newline --
    # otherwise the pin depends on how Lean happens to break a line.
    assert got["BSM.t4_call_bounds"]["type"].startswith("BSM.t4_call_bounds : ∀ (S K tau")
    assert "max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0 ≤" in (
        got["BSM.t4_call_bounds"]["type"]
    )
    assert got["BSM.t4_call_bounds"]["type"].endswith(
        "BSM.bsCall S K tau r q sigma ≤ S * Real.exp (-q * tau)"
    )
    # The "no axioms" sentence is a *payload*, not an absence: pinning it is what
    # makes an axiom-free proof of a node that should need mathlib go red.
    assert got["BSM.exp_neg_sq_even"]["axioms"] == (
        "'BSM.exp_neg_sq_even' does not depend on any axioms."
    )
    LAST_NOTE["test_parse_audit_replays_recorded_ci_output"] = f"{len(got)} constants parsed"


def test_parse_audit_accepts_the_bare_axioms_form_too():
    """Do not encode one Lean version's formatting choice into the contract.

    The pinned value is the *message text*, so a format change shows up as a diff
    the writer can regenerate -- but the parser must still find the block, or every
    future toolchain bump becomes an unexplained red in the build job.
    """
    bare = "\n".join(
        ["BSM.Phi : ℝ → ℝ", P.SENTINEL, "BSM.Phi depends on axioms: [propext]", P.SENTINEL, ""]
    )
    got = P.parse_audit(bare, ["BSM.Phi"])
    assert got["BSM.Phi"]["axioms"] == "BSM.Phi depends on axioms: [propext]"


def test_parse_audit_refuses_a_half_output():
    """A missing axioms block is an error, never a pin with an empty field.

    This is the failure mode the CI run actually produced. Had the parser stored
    `axioms: ""` for the constants it could not read, the artifact would have
    claimed elaboration coverage it did not have -- strictly worse than a red job.
    """
    # Right *number* of blocks, one of them empty: the count guard cannot save us
    # here, only the payload check can.
    s_ = P.SENTINEL
    truncated = "\n".join(
        [f"BSM.Phi : ℝ → ℝ\n{s_}", f"{s_}", f"BSM.Phi2 : ℕ\n{s_}",
         f"'BSM.Phi2' depends on axioms: []\n{s_}", ""]
    )
    try:
        P.parse_audit(truncated, ["BSM.Phi", "BSM.Phi2"])
    except RuntimeError as e:
        assert "could not recover" in str(e), e
    else:
        raise AssertionError("parse_audit accepted a truncated audit run")


def test_parse_audit_replays_the_at_echo_shape():
    """`#check @q` echoes the `@` when the constant has binders.

    Recorded verbatim -- raw block echoed by the (then) self-diagnosing parse
    error -- from run 35535082152, where `BSM.carrMadanKernel_integrable` was
    the first pinned constant with a binder telescope and Lean printed
    `@name : ∀ {φ ...},` with the break after the comma, not after the name.
    The other 44 pins parsed bare because `#check @` on a telescope-free
    constant drops the `@`. The pin drops it too: it is audit_source's own
    invocation echoing back, and the audit must pin ONE shape regardless of
    whether the constant happens to carry binders.
    """
    at_echo = "\n".join(
        [
            "@BSM.carrMadanKernel_integrable : ∀ {φ : ℂ → ℂ} {α : ℝ},",
            "0 < α →",
            "(Continuous fun u => φ (↑u + ↑α * Complex.I)) →",
            "∀ {c D Y : ℝ},",
            "0 < c →",
            "0 ≤ D →",
            "0 < Y →",
            "∀ {u₀ : ℝ},",
            "(∀ (u : ℝ), u₀ ≤ |u| → ‖φ (↑u + ↑α * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y)) →",
            "MeasureTheory.Integrable (BSM.carrMadanKernel φ α) MeasureTheory.volume",
            P.SENTINEL,
            "'BSM.carrMadanKernel_integrable' depends on axioms: [propext]",
            P.SENTINEL,
            "",
        ]
    )
    got = P.parse_audit(at_echo, ["BSM.carrMadanKernel_integrable"])
    assert got["BSM.carrMadanKernel_integrable"]["type"] == (
        "BSM.carrMadanKernel_integrable : ∀ {φ : ℂ → ℂ} {α : ℝ}, 0 < α → "
        "(Continuous fun u => φ (↑u + ↑α * Complex.I)) → ∀ {c D Y : ℝ}, "
        "0 < c → 0 ≤ D → 0 < Y → ∀ {u₀ : ℝ}, (∀ (u : ℝ), u₀ ≤ |u| → "
        "‖φ (↑u + ↑α * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y)) → "
        "MeasureTheory.Integrable (BSM.carrMadanKernel φ α) MeasureTheory.volume"
    )
    assert got["BSM.carrMadanKernel_integrable"]["axioms"] == (
        "'BSM.carrMadanKernel_integrable' depends on axioms: [propext]"
    )


def test_parse_audit_accepts_a_name_broken_from_its_colon():
    """Defensive tolerance: name alone on a line, separator on the next.

    Not yet observed -- run 35533637758's refusal was misattributed to this
    shape before the raw-block dump (then unprinted) revealed the `@`-echo
    above. Kept because it cannot fire spuriously: the line must equal the
    qualified name exactly, and `normalize` rejoins it into the same pinned
    text the never-broken printer would emit.
    """
    wrapped = "\n".join(
        [
            "BSM.carrMadanKernel_integrable",
            "    {φ : ℂ → ℂ} {α : ℝ} (hα : 0 < α) :",
            "    Integrable (BSM.carrMadanKernel φ α) MeasureTheory.volume",
            P.SENTINEL,
            "'BSM.carrMadanKernel_integrable' depends on axioms: [propext]",
            P.SENTINEL,
            "",
        ]
    )
    got = P.parse_audit(wrapped, ["BSM.carrMadanKernel_integrable"])
    assert got["BSM.carrMadanKernel_integrable"]["type"] == (
        "BSM.carrMadanKernel_integrable {φ : ℂ → ℂ} {α : ℝ} (hα : 0 < α) : "
        "Integrable (BSM.carrMadanKernel φ α) MeasureTheory.volume"
    )
    assert got["BSM.carrMadanKernel_integrable"]["axioms"] == (
        "'BSM.carrMadanKernel_integrable' depends on axioms: [propext]"
    )


def test_parse_audit_refuses_a_shifted_stream():
    """Sentinel count must match the emission count, or blocks belong to the wrong name."""
    try:
        P.parse_audit("BSM.Phi : ℝ → ℝ\n" + P.SENTINEL + "\n", ["BSM.Phi", "BSM.Phi2"])
    except RuntimeError as e:
        assert "delimited blocks" in str(e)
    else:
        raise AssertionError("parse_audit accepted a short block list")


def test_generator_and_parser_agree_on_the_protocol():
    """`audit_source` and `parse_audit` must not drift apart alone.

    Neither is checkable without a toolchain end-to-end, so the contract between
    them -- one `#check`, one `#print axioms`, two sentinels per constant, in
    sorted order -- is asserted structurally. If a future edit adds a third
    command per constant, the sentinel arithmetic here goes red in a sandbox
    instead of in someone's CI.
    """
    src = P.audit_source(QUALIFIED)
    assert src.count(P.SENTINEL) == 2 * len(QUALIFIED)
    for q in QUALIFIED:
        assert f"#check @{q}" in src, q
        assert f"#print axioms {q}" in src, q
    assert src.startswith("import ImprovedBS"), "the audit must see the built library"
    # ...and the emitted order is the order the parser assumes.
    assert QUALIFIED == sorted(QUALIFIED)


def test_pins_match_the_tree():
    """Layer 1 in this repo, right now: the committed artifact and the sources agree.

    Redundant with `scripts/lean_lint.py`, and deliberately so -- `pytest tests/`
    must be able to say this without invoking the lint, since the lint is the thing
    under test elsewhere.
    """
    failures = P.check()
    assert not failures, "statement pins drifted:\n" + "\n".join(failures)
    with open(GOLDEN, encoding="utf-8") as fh:
        n = len(json.load(fh)["pins"])
    LAST_NOTE["test_pins_match_the_tree"] = f"{n} declarations pinned, all matching"


def test_pinned_t4_still_mentions_the_price():
    """A minimal semantic read of the artifact itself, independent of the tree.

    Not a lint rule -- keyword-matching a Lean statement in CI would be brittle and
    would make `docs/01` a second source of truth. It is a test, and it exists
    because the *only* local defence against "hollow the statement and regenerate
    the pins" is a human reading a diff: if that diff ever stops containing the
    price at all, this fails and forces the question. The layer that makes it
    impossible is CI's `elab` block (see docs/04 guard 4).
    """
    with open(GOLDEN, encoding="utf-8") as fh:
        pins = json.load(fh)["pins"]
    stmt = pins["BSM.t4_call_bounds"]["pin"]
    assert "bsCall" in stmt and "max" in stmt and "True" not in stmt, stmt
    assert "0 < S" in stmt and "0 < sigma" in stmt, (
        "T4's hypotheses are part of the claim: they are what made the earlier "
        "version of T3 false. " + stmt
    )


def test_elab_layer_is_red_without_a_toolchain():
    """CI-only must mean *red here*, not *skipped here*.

    A check that is silent when its inputs are missing is how a lane ends up
    advertising coverage it does not have. With `lake` present this test only
    requires the step to run and report; without it, exit status must be 1.
    """
    proc = subprocess.run(
        [sys.executable, "scripts/pin_statements.py", "--elab-check"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    out = proc.stdout + proc.stderr
    if shutil.which("lake") is None:
        assert proc.returncode == 1, f"expected a red, got {proc.returncode}\n{out}"
        assert "no `lake` on PATH" in out, out
        LAST_NOTE["test_elab_layer_is_red_without_a_toolchain"] = "red by design, no lake"
    else:
        assert proc.returncode in (0, 1), f"unexpected crash: {out}"
        assert "PINS" in out or "pins" in out, out
        LAST_NOTE["test_elab_layer_is_red_without_a_toolchain"] = "lake present, ran"


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
    print(f"\n{len(fns)-fails}/{len(fns)} passed")
    sys.exit(1 if fails else 0)
