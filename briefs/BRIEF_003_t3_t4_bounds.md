# BRIEF_003 — The delta identity (T3) and the no-arbitrage bounds (T4)

- **Status:** OPEN
- **Prerequisite PRs:** BRIEF_001 merged and green. BRIEF_002 is helpful but
  not required.
- **Skills:** Lean 4 + mathlib real analysis (`Real.exp`/`Real.log` algebra,
  `Real.sqrt`, `positivity`, `nlinarith`). This is the first brief with genuine
  proof-engineering content rather than scaffolding.
- **Budget:** ≤ 3 hours. T3 is the work; T4 is mostly a mathlib-availability
  question.

## Goal

Discharge the two `sorry`s that `BRIEF_001` leaves in the warm-up tier, and
lower `.github/lean_lint_baseline.json` from 3 markers to 0. That is the first
time the repository will have a fully proved T1–T4 stack, which is the
prerequisite for T5 (proved *through* T3 — see `docs/04`).

Both statements are already in `ImprovedBS/Core.lean` with their hypotheses
corrected and their proof routes recorded in doc-comments. Read those comments
first; they are not decoration, they are the prior contributor's analysis.

## Scope (numbered)

### T3 — `t3_delta_identity`

    S * e^{−qτ} * φ(d1) = K * e^{−rτ} * φ(d2)

Hypotheses (already stated, do not weaken them): `0 < S`, `0 < K`, `0 < tau`,
`sigma ≠ 0`.

1. Prove `d1² − d2² = 2·ln(S/K) + 2·(r−q)·τ`. Route: factor as
   `(d1 − d2)(d1 + d2)`, substitute T1, clear the denominator with `field_simp`,
   and use `Real.mul_self_sqrt (le_of_lt htau)`. **Reuse
   `t1_d1_minus_d2`** — do not re-derive the difference. The spine in `docs/04`
   means something: a proof of T3 that does not mention T1 has duplicated work
   and will drift from it.
2. Conclude `φ(d1) = (K/S)·e^{−(r−q)τ}·φ(d2)` via `Real.exp_add` /
   `Real.exp_sub` and `Real.exp_log` on `0 < K/S` (`div_pos hK hS`).
3. Multiply through by `S·e^{−qτ}` and `ring`.

### T4 — `t4_call_bounds`, `t4_put_bounds`

    max (S e^{−qτ} − K e^{−rτ}) 0 ≤ bsCall ≤ S e^{−qτ}

4. **Establish `0 ≤ Phi x` and `Phi x ≤ 1` first**, as named lemmas
   (`Phi_nonneg`, `Phi_le_one`). *Before writing any proof, check what mathlib
   v4.34.0 actually provides about `Real.erf` bounds* — search for
   `Real.abs_erf_le_one`, `Real.erf_le_one`, or fall back to the integral
   definition. If mathlib has nothing, this becomes the real content of the
   brief and you should say so in the PR rather than proving it by
   `positivity` on a goal it cannot see. **A negative result here is a valid
   outcome**: "T4 requires an erf bound mathlib does not have, here is the
   minimal lemma and its proof from the integral definition" is a better PR
   than a `sorry` dressed up as progress.
5. Upper bound: drop the non-negative `K e^{−rτ} Φ(d2)` term.
6. Lower bound: needs `Φ` monotone (`Phi_monotone`, from `Real.erf_strictMono`
   if it exists, else from `Φ' = φ > 0` — which is itself a useful lemma for
   T5) plus `d2 ≤ d1`, which is T1 with `0 ≤ σ√τ`.
7. `t4_put_bounds` should be a **corollary** of `t4_call_bounds` and
   `t2_put_call_parity`, not an independent analytic argument. If your proof
   does not mention parity, it is doing T4 twice.

### Housekeeping

8. Lower the ratchet: run `python3 scripts/lean_lint.py --write-baseline` and
   commit the result. It must show `"deferred": {}`. The lint refuses to write
   a baseline that still contains a protected node, so this cannot be abused —
   but check the diff before committing.
9. The `#print axioms` audit in `.github/workflows/lean.yml` must be extended to
   cover `t3_delta_identity`, `t4_call_bounds`, `t4_put_bounds`, and any new
   helper lemma. Add the new lemma names to `REQUIRED` and to the audit list.
10. Ledger row.

## Done looks like (acceptance — machine-graded)

- `lake build` green; `#print axioms` shows no `sorryAx` for any of T1–T4 and
  the new helpers.
- `.github/lean_lint_baseline.json` has an empty `deferred` map.
- `scripts/lean_lint.py` green with the enlarged `REQUIRED` set.
- `tests/test_bs.py` 13/13 and `tests/test_mutants.py` 4/4 unchanged — the
  numeric shadows (`test_delta_identity_numerically`, `test_value_bounds`)
  already pass on a 6-point grid, so a Lean proof that contradicts them means
  the *Lean* side is wrong.
- No statement weakened. In particular: do not add hypotheses to make a proof
  go through, and do not remove them. If a hypothesis looks unnecessary, that
  is a separate finding — report it, don't act on it. (The history here is
  instructive: T3 shipped *missing* hypotheses and was false. The opposite
  error is more benign but still a silent change to the contract.)

## Explicitly out of scope

- **T5.** Do not attempt the PDE identity, even though T3 unlocks it. It needs
  the coordinate decision (`x = Real.log S` vs. `S`) recorded in `docs/04`, and
  that decision belongs in its own brief.
- **T6 / anything Lévy.** See BRIEF_004 for the research tier.
- No changes to `experiments/` or its tests.
- No switching `Phi`/`phi` to mathlib's Gaussian distribution machinery. That
  migration is deferred to T5/T6 deliberately (`docs/04`).
