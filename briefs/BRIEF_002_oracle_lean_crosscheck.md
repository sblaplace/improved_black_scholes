# BRIEF_002 — Oracle ↔ Lean pointwise cross-verifier

- **Status:** OPEN
- **Prerequisite PRs:** BRIEF_001 merged and green (this brief edits the same
  Lean file, and needs a working `lake build` to produce its Lean-side output)
- **Skills:** Lean 4 `#eval` / `Float`; a little Python. No new mathematics.
- **Budget:** ≤ 90 minutes. Both halves are locally checkable except the
  Lean-side `#eval`, which needs the CI toolchain.

## Goal

Today the numeric oracle and the Lean tree agree because a human read both and
thought they matched. That is the weakest link in the repository: two
hand-written sources expressing the same mathematics, with no mechanical
coupling. `docs/04` calls this out explicitly and lists it as the missing
guard.

Build guard (3) from `docs/04` §"Oracle ↔ formal correspondence": evaluate
`d1`, `d2`, `bsCall`, `bsPut`, parity and the delta identity at a fixed grid of
points **in both trees**, and fail CI if they disagree.

**This is a cross-verifier, not a proof.** It cannot show the Lean definitions
are correct — only that the two trees have not drifted into stating different
mathematics. Be explicit about that in the PR description; the repo's whole
ethos is not overclaiming.

## Scope (numbered)

1. **Golden grid.** Add `tests/golden_grid.json`: a list of parameter points
   `(S, K, tau, r, q, sigma)` covering moneyness in {0.5, 0.8, 1.0, 1.2, 2.0},
   tenor in {1/12, 0.25, 1, 3}, vol in {0.05, 0.2, 0.6}, non-zero `q`, and at
   least one negative `r`. Every point must satisfy the domain of `docs/01` §4
   (S>0, K>0, τ>0, σ>0). Commit the *inputs only* — not the outputs.
2. **Oracle side.** `tests/test_crosscheck.py` reads the grid, computes the six
   quantities per point via `experiments/black_scholes.py`, and compares against
   the Lean side.
3. **Lean side.** A module (suggest `ImprovedBS/Crosscheck.lean`) with a
   `#eval` that reads no files and prints one line per grid point in a
   fixed, greppable format, e.g.
   `CK 100.0 100.0 1.0 0.05 0.0 0.2 0.3729709466 0.6270290533 …`.
   Embed the grid in the Lean source (generated from the JSON by a small
   `scripts/gen_grid.py`, so there is one source of truth) rather than doing
   file IO inside `#eval`.
4. **CI wiring.** Add a step to the `build` job of `.github/workflows/lean.yml`
   that runs `lake env lean ImprovedBS/Crosscheck.lean`, captures stdout, and
   diffs it against the Python side. Non-zero exit on any mismatch, with the
   offending points printed.
5. **Tolerance.** Decide and justify it. `Float` in Lean is IEEE double, same as
   Python, so the two should agree to within a few ulp on each intermediate —
   but `Real.erf` in Lean and `math.erf` in CPython are *different
   implementations*, so exact bit agreement is not available. Start from an
   absolute tolerance of 1e-12 on prices and 1e-12 on `d1`/`d2`, measure the
   actual worst-case disagreement on the grid, and set the committed tolerance
   to the measured worst case times a safety factor of ~100. Record the
   measurement in the PR: an unjustified tolerance is how a cross-check becomes
   decoration.
6. **Ledger row** in `benchmarks/LEDGER.md`.

## Done looks like (acceptance — machine-graded)

- Deliberately perturbing one Lean definition (e.g. `d2`'s `−σ²/2` → `+σ²/2`)
  makes the new CI step fail, and the failure message names the points that
  diverged. Demonstrate this in the PR with a temporary commit or a log paste —
  a cross-check that has never been seen to fail is not a cross-check. This is
  the same standard `tests/test_mutants.py` holds the oracle to.
- `scripts/lean_lint.py` still green, baseline unchanged. Note the lint's
  `[ORACLE SYNC]` check is structural; extend it if the new module makes a
  stronger structural claim worth enforcing.
- `tests/test_bs.py` 13/13 and `tests/test_mutants.py` 4/4 unchanged.
- No new third-party Python deps.

## Explicitly out of scope

- Proving anything. This is a contradiction detector.
- T3–T6, and any change to theorem statements or definitions.
- Replacing the oracle with Lean-generated numbers. The oracle stays
  dependency-free and auditable; that is its value.
- Property-based / randomized grids. A fixed committed grid is reproducible and
  reviewable; randomness makes a red build un-diagnosable.

## Why this is worth a brief

The failure it prevents is the worst kind for this repository: both trees
green, both internally consistent, and quietly about different mathematics. The
`[ORACLE SYNC]` lint catches the *shape* of that drift (is `d2` independent in
both?), not the *content* (do they compute the same number?). Only pointwise
evaluation catches the second.
