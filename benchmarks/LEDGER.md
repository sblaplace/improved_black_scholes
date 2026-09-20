# Ledger

Every PR landed against a brief gets a row here. The deliverable is the
verified theorem stack; this table is the record of how it was reached —
including the approaches that failed the grader.

Verdict discipline:
- Only CI-graded verdicts count. A row is `PENDING` until the harness says
  GREEN/RED. No human "looks good".
- A brief whose proof is asserted but not checker-backed (a stray `sorry`)
  is RED, by definition of the grader (see BRIEF_001).
- Separate *incident* (harness broke, runner lost) from *verdict* (the
  approach failed the grader). A RED verdict is a result, not a bug report.

| # | brief | contributor | PR | verdict |
|---|-------|-------------|----|---------|
| 1 | BRIEF_001 (T1+T2, Lean lane) | — | — | **PENDING — never built.** Lane scaffolding landed; no `lake build` has ever executed. See correction C1. |
| 2 | BRIEF_002 (oracle ↔ Lean cross-verifier) | — | — | OPEN — not started |
| 3 | BRIEF_003 (T3 delta identity + T4 bounds) | — | — | OPEN — not started, blocked on #1 |
| 4 | BRIEF_004 (α-stable moment obstruction) | — | — | OPEN — not started, independent of #1–#3 |

## Corrections and co-recorded changes to the ask

Briefs are committed in-repo up front, so a correction is recorded here rather
than edited silently into the original text.

### C1 — BRIEF_001, corrected before any PR existed

**Date:** 2026-09-20. **Trigger:** an audit of the tree, not a contributor's
PR. Full detail is in the correction record at the top of
`briefs/BRIEF_001_parity_and_lean_lane.md`.

Four defects made the brief as issued either unachievable or — worse —
*achievable without meaning anything*:

1. **T1 and T2 were tautologies.** `d2 := d1 − σ√τ` and
   `bsPut := bsCall − S e^{−qτ} + K e^{−rτ}` made both theorems true by
   construction (`unfold; ring`). T2 in particular never touched
   `Φ(x) + Φ(−x) = 1`, which the brief's own scope item 3 required be cited. A
   contributor could have shipped a green build certifying nothing and been
   graded GREEN. The same circularity was mirrored in the oracle: the put was
   *computed* via parity, so `test_put_call_parity` could not fail. Demonstrated
   by mutation: a Φ perturbed to lose odd symmetry passed that test.
2. **`t3_delta_identity` was false as stated** — missing `σ ≠ 0` and `0 < τ`.
   At σ = 0, Lean's `a / 0 = 0` collapses it to `S e^{−qτ} φ(0) = K e^{−rτ} φ(0)`;
   S=2, K=1, r=q=0 gives 0.797885 ≠ 0.398942. A contributor would have hit a
   red build caused by the statement and spent their budget on the wrong problem.
3. **The Lean lane could not start.** Invalid `lakefile.toml` (mathlib
   requirement commented out; `[lake] binary` / `precompiled` are not Lake
   keys), no `lean-toolchain`, no `lake-manifest.json`, no root module, no
   `lean.yml`. `Lean/core/bsm_theorems.lean` also made the module
   `Lean.core.*`, squatting the elaborator's namespace.
4. **The acceptance bar was unenforceable in the named venue.** The brief
   budgeted ≤60 minutes of sandbox compute against a bar of "`lake build`
   green". Sandboxes without a route to `elan.lean-lang.org` and the Mathlib
   olean cache cannot install a toolchain at any budget.

**Changes landed with this correction:**

- `d2`, `bsPut` given independent explicit closed forms in both trees; values
  unchanged to 3.6e-15 across a 6-point grid, so the frozen numeric contract
  holds. Oracle tests 10 → 13.
- `tests/test_mutants.py` added: 11 seeded bugs, each required to be killed by
  its targeted test, including two *vacuity canaries* (M7 breaks Φ's odd
  symmetry, M8a/M8b corrupt the independent `d2`). Baseline before the fix: M7
  and M8 survived their targeted tests.
- `test_pde_residual_refines_with_h` (`r2 <= r1 + 1e-4`, satisfiable even when
  the residual got worse) replaced by `test_pde_residual_is_second_order`,
  asserting the measured O(h²) shrink inside a documented h-window. Measured:
  100× per decade from h=1e-2 to 1e-3, then divergence below 1e-3 as round-off
  dominates — the window is a fact about finite differences, recorded in
  `experiments/black_scholes.py` so nobody "improves" the test by shrinking h.
- Lean tree moved to `ImprovedBS/`; pinned to mathlib v4.34.0 /
  Lean v4.34.0 across `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`.
- `.github/workflows/lean.yml` added: a toolchain-free `lint` job and a
  `build` job (`leanprover/lean-action@v1`) that tees `lake build` to an
  artifact and audits `#print axioms` for `sorryAx`.
- `scripts/lean_lint.py` added. No toolchain required. Enforces: no `sorry` in
  the protected T1/T2 node; a ratchet on total deferred markers; no new axioms;
  every stack theorem still declared; and the independence guard (`d2` not from
  `d1`, `bsPut` not from `bsCall`, T2 citing `Phi_add_Phi_neg`). Verified to
  catch all 8 seeded regressions of those properties.
- T3 hypotheses corrected; T4 stated for the first time (it had no Lean
  declaration despite being listed "stated" in two tables); T5's proof route
  recorded (via T3, in `x = log S` coordinates); T6 restated around the
  tempered-stable repair.
- `docs/01` §2a, §4, §5 and `docs/04` rewritten to state the independence rule
  and the domain hypotheses; `docs/02` and `docs/03` repaired (duplicate `## 4.`
  heading, a D4 with no D3, and several unparseable sentences); `docs/03` §D1
  rewritten around the exponential-moment obstruction, which is now BRIEF_004.
- BRIEF_002, BRIEF_003, BRIEF_004 authored.

**Honest status of what landed:** the Lean definitions, the `Phi_add_Phi_neg`,
T1, T2 and T2′ proof scripts, and all Lean-side scaffolding were written and
reviewed by hand in an environment with **no Lean toolchain and no route to
install one**. They have never been compiled. They are best-effort, not
verified, and row 1 is PENDING precisely because of that. The Python half —
oracle, tests, mutation harness, lint — has been executed and is green.

### C2 — `docs/04` status table, corrected

The table previously read "T1 done, T2+T3 done in-code" in one cell while the
adjacent rows and the `.lean` file both said `stated` / `sorry`. Nothing was
done. Status in that table is now derived from `scripts/lean_lint.py` output
rather than typed, so the two cannot disagree.
