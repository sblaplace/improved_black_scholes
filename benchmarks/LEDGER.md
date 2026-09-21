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
| 1 | BRIEF_001 (T1+T2, Lean lane) | arena-ai-coding-agent | [#1](https://github.com/sblaplace/improved_black_scholes/pull/1) | **GREEN** @ `638c66e`, run 35509578689 — `lake build` + `#print axioms` audit + `lint` + `oracle` all pass. Reached on the 8th run; see the CI history. |
| 2 | BRIEF_002 (oracle ↔ Lean cross-verifier) | arena-ai-coding-agent | [#3](https://github.com/sblaplace/improved_black_scholes/pull/3) | **GREEN** @ `2a7bacb`, run 35517328856 — 39-point golden grid, docs/04 guard (3) active: `ImprovedBS/Crosscheck.lean` (#eval) cross-verified against `experiments/black_scholes.py` with max price diff 1.6e-14 (tol 1e-12) and 4/4 mutants caught. |
| 3 | BRIEF_003 (T3 delta identity + T4 bounds) | arena-ai-coding-agent | [#2](https://github.com/sblaplace/improved_black_scholes/pull/2) | **GREEN** @ `726325d`, run 35514867674 (first green: run 35514609619 @ `2273461`) — `lake build` + `#print axioms` audit + `lint` + `oracle` all pass; ratchet 3 → 0. Reached on the 1st run; see the CI history and correction C4. |
| — | *(tooling, no brief)* statement pins + the lint's own falsifiers | arena-ai-coding-agent | [#4](https://github.com/sblaplace/improved_black_scholes/pull/4) | **GREEN** @ `341b9f4`, run 35520713909 (tip re-graded green: run 35521215779 @ `0785e90`) — `lake build` + `#print axioms` audit + **Statement pins (elab)** + `lint` + `oracle` all pass. Three-run arc, which is the informative part: run 35519747870 red on an empty `elab` block (by design — a pin that was never produced is not a passing pin) → run 35520154876 red on a parser format bug (`#print axioms` quotes the constant, `#check` does not; the parser refused to half-pin and printed the block instead) → block committed verbatim → run 35520713909 green, the 31 elaborated pairs reproducing identically across two independent checkouts, which is what makes them a pin rather than a transcription. Locally: `test_lint.py` 7/7 (22 cheats killed by named checks, 5 controls green, 1 residual gap asserted open), `test_pins.py` 8/8, `lean_lint` OK (43 decls, 31 pins + 31 elab, cross-layer skew clean), oracle 13/13, mutants 4/4, crosscheck 4/4. No `.lean` file changed; sorry baseline untouched. |
| 4 | BRIEF_004 (α-stable moment obstruction) | arena-ai-coding-agent | [#5](https://github.com/sblaplace/improved_black_scholes/pull/5) | **GREEN** @ `d61c874`, run 35523250105 — `lake build` + `#print axioms` audit + **Statement pins (elab)** + `lint` + `oracle` all pass. Module authored without a toolchain (four-run arc: two one-line build errors, then build+audit green with an empty `elab` block by design, then the block committed verbatim). The seven new constants are on `[propext, Classical.choice, Quot.sound]` only. Statement strengthened: the theorem holds for **every real α**, superseding the `α < 2` acceptance item (correction C7). The documentation commits that record this row re-grade green as well (run 35523462850 @ `28dda5b`). |
| — | *(defect repair, no new brief)* BRIEF_002's two recorded crosscheck defects (C6 item 4) | arena-ai-coding-agent | [#6](https://github.com/sblaplace/improved_black_scholes/pull/6) | **GREEN** @ `7d2b2a3`, run 35526035651 (oracle lane run 35526035655) — `lake build` + `#print axioms` audit + **Statement pins (elab)** + `lint` + `oracle` all pass; the crosscheck step ran the real `#eval` against 14-token `CK` lines (both T3 sides) through the new comparator. Locally, before pushing: crosscheck 6/6 (7 comparator mutants, incl. formula-level RHS corruption at the largest-delta point; 13-token lines rejected; the recorded `--run-lean` repro now a loud FAIL with a scrubbed PATH), `test_lint.py` 7/7 (24 mutants — CC1/CC2 killed by `[CROSSCHECK SYNC]`), oracle 13/13, mutants 4/4, pins 8/8. Sorry baseline untouched; no theorem statement changed. See correction C8. |
| 5 | BRIEF_005 (T6 sub-goal 2: tempered contour absolute convergence) | arena-ai-coding-agent | [#6](https://github.com/sblaplace/improved_black_scholes/pull/6) | **GREEN** @ `386a331`, lean run 35536031936 (oracle lane run 35536031949) — `lake build` + `#print axioms` audit + **Statement pins (elab, all 49)** + `lint` + `oracle` all pass. `ImprovedBS/Fourier.lean` (431 lines) fully elaborates at mathlib v4.34.0: `integrable_exp_neg_abs_rpow`, `cmDenom_u4_le`, `cmDenom_ne_zero`, `carrMadanKernel_integrable`, `carrMadan_price_integrable` and both GBM instances — every new constant on `[propext, Classical.choice, Quot.sound]`, no sorryAx; the CGMY-decay hypothesis appears only as a hypothesis (brief acceptance: no unbacked premise). Eight-run lean arc (seven red, then green), and its shape is the informative part: `d935117` → 35531017611 elaboration errors → round 2 `bedef4e`→`11f47df` (35532227392, 35532974067) → **`2209077` → run 35533637758: build GREEN**, elab-pins step red — then two red runs spent *finding the parse failure's shape*, not fixing assumptions: `3dbaeb2` 35534649501 (wrap hypothesis, wrong), `926637c` 35535082152 (self-diagnosing error dumped the raw block: `#check @q` echoes the `@` when the constant has a binder telescope — first such pin in the tree) → `d379fc5` 35535582258 parses all 49, red by design on the 11 unpinned elab pairs, block printed paste-ready → committed byte-for-byte with identical-merge re-verified → `386a331` green. Sorry baseline: `deferred: {}` added zero entries; no T1–T5 statement changed. |
| 6 | BRIEF_006 (T5: the closed form solves the BSM PDE) | arena-ai-coding-agent | [#8](https://github.com/sblaplace/improved_black_scholes/pull/8) | **GREEN** @ `4fd57de`, lean run 35566569107 (oracle lane run 35566569054) — `lake build` + `#print axioms` audit + **Statement pins (elab, all 60)** + the oracle↔Lean pointwise cross-verifier + `lint` (incl. `[SPINE]`) all pass. The build line is `✔ [8926/8928] Built ImprovedBS.Core`, i.e. the whole T5 section — `hasDerivAt_erf`/`Phi`, `hasDerivAt_d_spot`/`d_tau_quotient_eq`/`hasDerivAt_d_tau`/`d1_tau_sub_d2_tau`, `t5_delta`/`t5_gamma`/`t5_tau`, `t5_bsCall_pde_tau`/`t5_bsCall_pde` — elaborates at mathlib v4.34.0, then `✔ [8927/8928] Built ImprovedBS`; all 50 audited constants sit on `[propext, Classical.choice, Quot.sound]`, never `sorryAx`. The **four-run arc** is the informative part here, and it was all elaboration, no mathematics: 35541544305 (15 errors, all in `Core.lean`) → 35565366768 (3 left) → 35566220133 **build GREEN**, red *by design* on the pins step because the 11 T5 constants had no `elab` entry (the step printed the paste-ready block and published it to the PR) → 35566569107 green with the block committed byte-for-byte and the 49 pre-existing entries diffed field-by-field before pasting (so no T1–T4 elaborated type moved). Root causes, none of them mathematical: (1) `simpa`/`exact` compare an *already-fixed* term type with the goal, and that comparison does not unfold the `Pi`-instance forms or an *unapplied* `def` — hence four redundant `ring`s after `field_simp` (`No goals to be solved`), `simpa only [erf]`/`[Phi]` against a bare `erf`/`Phi` in the goal, `HasDerivAt.sub`'s `(fun x ↦ T) - fun x ↦ x` against the goal's `fun u ↦ T - u`, and the `bsCall` lambda form against `hP.sub hQ`'s `Pi` form; (2) `HasDerivAt.comp` with a lambda-form expected type makes the elaborator try to *invert* the composition (`?m ∘ …`), so the composite is now elaborated with no expected type and bridged by an explicit `funext` equation. Two genuine name/arity bugs hid behind those: `Real.hasDerivAt_sqrt`'s point is `x` with hypothesis `x ≠ 0` (passing `√τ ≠ 0` instantiated it at `√τ`), and the shared factor of the tau-`φ` cancellation sits on the *left*, so the factoring lemma is `← mul_sub`, not `← sub_mul`. Statement pins grew 49 → 60 exactly as predicted by BRIEF_006; no T1–T4 statement, hypothesis or pin changed, and `deferred: {}` is untouched. Landed in `ImprovedBS/Core.lean`: 11 declarations (`hasDerivAt_erf`, `hasDerivAt_Phi`, `hasDerivAt_d_spot`, `d_tau_quotient_eq`, `hasDerivAt_d_tau`, `d1_tau_sub_d2_tau`, `t5_delta`, `t5_gamma`, `t5_tau`, `t5_bsCall_pde_tau`, `t5_bsCall_pde`), all in `REQUIRED` + `PROTECTED`, 11 new statement pins (60 total), a `[SPINE]` route check with its 25th lint mutant, and the `docs/04` spine correction (C9). No `sorry`; baseline untouched at `deferred: {}`; T1–T4 statements unchanged. |
| 7 | BRIEF_007 (T6 sub-goal 3a: the closed form is the risk-neutral expectation) | arena-ai-coding-agent | [#9](https://github.com/sblaplace/improved_black_scholes/pull/9) | **GREEN** @ `f50a256`, lean run 35574194681 (oracle lane run 35574194638) — `lake build` + `#print axioms` audit + **Statement pins (elab, all 81)** + the oracle↔Lean pointwise cross-verifier + `lint` all pass; the build line is `✔ [8927/8929] Built ImprovedBS.RiskNeutral`, and all 71 audited constants (50 previous + the 21 below) sit on `[propext, Classical.choice, Quot.sound]`, never `sorryAx`. Reached on the 4th run; the arc (two build runs, one of them the first push with 20 of 21 declarations already elaborating, then the two-run pin bootstrap that this time also fixed its own channel — C10) is in the CI history below. Scope: new module `ImprovedBS/RiskNeutral.lean`, 21 declarations (`phi_eq_gaussianPDFReal`, `Phi_eq_gaussianReal_Iic`, `integral_gaussianReal_eq_integral_mul_phi`, `integral_phi`, `exp_mul_phi_eq`, `integrable_exp_mul_phi`, `integral_exp_mul_phi`, `integral_phi_Ioi`, `integral_phi_sub_Ioi`, `integral_exp_mul_phi_Ioi`, `sigma_sqrt_tau_mul_d2`, `spot_sub_strike_eq`, `max_spot_sub_strike_mul_phi`, `max_sub_swap_eq`, `integrable_spot_mul_phi`, `integral_spot_mul_phi_eq_forward`, `integrable_max_spot_sub_strike_mul_phi`, `bsCall_eq_riskNeutral_expectation`, `bsPut_eq_riskNeutral_expectation`, `bsCall_eq_gaussianReal_expectation`, `bsCall_eq_lognormal_expectation`), all in `REQUIRED` + `PROTECTED`, statement pins 60 → 81 in both layers with the 60 pre-existing entries byte-identical, audit list extended by 21, `deferred: {}` untouched, T1–T5 and BRIEF_004/005 statements unchanged. Oracle side: `bs_call_by_expectation` / `bs_put_by_expectation` / `forward_by_expectation` (Simpson, no `norm_cdf`/`_d1d2`), `test_risk_neutral_expectation` (closed form vs expectation ≤ 1.6e-12 rel on the 39-point grid, forward ≤ 1.2e-14 rel) and mutant M11 (drift sign), killed by that test alone. Authored without a toolchain; see the CI history for row 7. |
| 8 | BRIEF_008 (T6 sub-goal 3b: Fourier inversion and real-valuedness) | arena-ai-coding-agent | [#10](https://github.com/sblaplace/improved_black_scholes/pull/10) | **GREEN** @ `e974bd7`, lean run 35578278238 (oracle lane run 35578278250) — `lake build` + `#print axioms` audit + **Statement pins (elab, all 94)** + the oracle↔Lean pointwise cross-verifier + `lint` all pass; the build line is `✔ [8928/8930] Built ImprovedBS.Inversion`, and all 82 audited constants (71 previous + the 11 below) sit on `[propext, Classical.choice, Quot.sound]`, never `sorryAx`. Scope: new module `ImprovedBS/Inversion.lean`, 13 declarations (`carrMadanInversion`, `dampedCallPrice`, `carrMadanInversion_integrand_integrable`, `gbm_carrMadanInversion_integrable`, `dampedCallPrice_log_eq`, `undamped_dampedCallPrice`, `fourierInversion_dampedCallPrice`, `fourierInversion_dampedCallPrice_at`, `carrMadan_inversion_eq_lognormal_expectation`, `carrMadan_inversion_eq_bsCall`, `carrMadan_inversion_im_eq_zero`, `carrMadan_inversion_eq_re`, `carrMadan_inversion_re_eq_bsCall`), all in `REQUIRED` + `PROTECTED`, statement pins 81 → 94 in both layers with the 81 pre-existing entries byte-identical, audit list extended by 11, `deferred: {}` untouched, T1–T5 and BRIEF_004/005/007 statements unchanged. Oracle side: `carr_madan_denom`, `bs_call_by_fourier_inversion` (Simpson with adaptive truncation), `bs_call_by_fourier_inversion_complex` (two-sided complex integral verifying imaginary part ≤ 2e-15), `test_fourier_inversion` (closed form vs inversion ≤ 2.02e-11 rel on 39-point grid, expectation vs inversion, imaginary part < 1e-13, α ≤ 0 rejected) and mutant M12, killed by that test alone. Authored without a toolchain; see the CI history for row 8. |
| 9 | BRIEF_009 (the model-free skeleton: parity + bounds at the expectation level) | arena-ai-coding-agent | [#11](https://github.com/sblaplace/improved_black_scholes/pull/11) | **GREEN** @ `8f6c656`, lean run 35589005865 (oracle lane run 35589005799) — `lake build` + `#print axioms` audit + **Statement pins (elab, all 108)** + the oracle↔Lean pointwise cross-verifier + `lint` (incl. `[SKELETON]`) all pass; the build line is `✔ [8928/8931] Built ImprovedBS.Skeleton`, and all 94 audited constants (82 previous + the 12 theorems below; `modelFreeCall`/`modelFreePut` are pins but not audit entries) sit on `[propext, Classical.choice, Quot.sound]`, never `sorryAx`. Scope: new module `ImprovedBS/Skeleton.lean`, 14 declarations (`modelFreeCall`, `modelFreePut`, `integrable_call_payoff`, `integrable_put_payoff`, `model_free_parity_gap`, `model_free_put_call_parity`, `model_free_call_nonneg`, `model_free_call_bounds`, `model_free_put_bounds`, `integrable_gaussianReal_iff`, `lognormal_parity_gap`, `lognormal_call_bounds`, `t2_spread_via_skeleton`, `t4_call_bounds_via_skeleton`), all in `REQUIRED` + `PROTECTED`, statement pins 94 → 108 in both layers with the 94 pre-existing entries byte-identical, audit list extended by 12, `deferred: {}` untouched, T1–T5 and BRIEF_004/005/007/008 statements unchanged. The layer holds at any terminal-spot law with the drift condition (parity unfixed at the expectation level; `lognormal_parity_gap` carries `htau : 0 ≤ tau` and nothing else; the T4′ put half rides parity and must cite it — mutant K1; `t2_spread_via_skeleton`/`t4_call_bounds_via_skeleton` re-derive T2/T4 through the layer and are graded to consume it and not the closed forms — mutant K2). `[SKELETON]` route checks with cheats K1/K2 (27 lint mutants, 5 controls). Oracle side: `model_free_prices`/`model_free_forward`, `test_model_free_skeleton` (gap identity + forward parity at 3 laws + degenerate, drift canary where the gap is not the forward spread, bounds at (a)/(b)/(d), degenerate edge tightness at K=100/110) and mutants M13 (put payoff `max (K−s) 0` flipped to `max (s−K) 0`) / M14 (spot's second moment in the gap), killed by that test alone. Seven-run lean arc, all elaboration and API shape at the tag (not mathematics): 35583242988 (9 errors) → 35584511555 (a same-file batch-edit race lost the block rewrite — see the follow-up commit) → 35584605087 (5: the un-instantiated payoff-integrability statements were *false* at infinite measures and now carry `[IsProbabilityMeasure μ]`; `AEStronglyMeasurable.sup`, not `.max`) → 35586213657 (2: `Integrable.mono` arg order) → 35586918124 (2: the density iff is `g x * (ρ x).toReal` and takes an a.e.-finiteness side goal) → 35588330009 **build GREEN**, elab pins red by design → 35589005865 green with the block merged (`added 14, changed 0, elab now 108`, golden diff pure insertion). Authored without a toolchain; see the CI history for row 9. |

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

## CI history for row 1 (PR #1)

Recorded because a verdict without its history is not reproducible, and because
the failures produced findings that changed the plan and two brief budgets.
Eight runs, one of which was an *incident* rather than a verdict.

| # | head | `lake build` | cause |
|---|---|---|---|
| 1 | `fbbc6d8` | fail 3m49s | `ImprovedBS.lean:21:0: invalid 'import' command` — a module doc-comment is a *command*, so placing it above the `import` makes the import illegal |
| 2 | `e806581` | fail 3m38s | same |
| 3 | `07f5aa8` | fail | `bad import 'Mathlib.Analysis.SpecialFunctions.Erf'`, `bad import 'Mathlib.Data.Real.Pi'` — neither path exists in v4.34.0, and `Real.erf` does not exist at all (correction C3) |
| 4 | `b1084d3` | fail | six × `failed to compile definition, consider marking it as 'noncomputable'`; `integral_comp_neg` applied to explicit args it takes implicitly; T1's `simp` left the fractions uncombined and used `eq_div_iff_mul_eq` where the division is on the left; T2's `linarith` on a goal containing a *product* of atoms |
| 5 | `a47b029` | **INCIDENT** | runner died: `System.IO.IOException: No space left on device`. No verdict — nothing after the cache step ran, including the log publisher |
| 6 | `9d6dd16` | fail | one error: `sub_div` in v4.34.0 is `(a - b) / c = a / c - b / c`, i.e. it *splits* a fraction; combining two fractions needs `← sub_div` |
| 7 | `b96d61a` | **build GREEN**, audit fail | `#print axioms ImprovedBS.t1_d1_minus_d2` — module name is not namespace; with no `namespace` command the theorems were in the root namespace |
| 8 | `638c66e` | **GREEN** 5m32s | all steps pass |

What the runs established, beyond the verdict:

- **The scaffolding was correct from run 1.** `Set up Lean + Mathlib cache`
  succeeded every time: elan installed, the v4.34.0 olean cache fetched, and
  `lakefile.toml` / `lean-toolchain` / `lake-manifest.json` resolved and agreed.
  A build is ~5m30s end to end, not the hours a from-source mathlib build would
  take. So correction C1 item 3 is genuinely fixed.
- **`Real.erf` is not in mathlib v4.34.0** (correction C3). Run 3 forced this
  out and it re-budgets T4 and T5.
- **Two reporting gaps hid real results, and both are now closed.** Run 5 died of
  ENOSPC before any step could report, so the failure was invisible except in a
  check-run annotation. Run 7 had a *green build and a red audit*, and the
  publisher shipped only `lake-build.log`, so the PR comment showed three
  expected `sorry` warnings and nothing else — which reads like success. The job
  now measures disk before spending it, and publishes every log it produces.

  Generalizable: a CI lane that cannot report its own failure is worse than no
  lane, because it produces a red X with no diagnosis and invites a contributor
  to guess. Reporting is part of the grader, not a convenience.

### Machine-checked as of run 8

`lake build` green **and** the `#print axioms` audit green, which is the
distinction this repository cares about — a `sorry` still builds, it just
elaborates to `sorryAx`. Verified free of `sorryAx`:

    BSM.exp_neg_sq_even   BSM.erf_neg   BSM.Phi_add_Phi_neg   BSM.Phi_neg
    BSM.t1_d1_minus_d2    BSM.t2_put_call_parity   BSM.t2_put_call_parity_spread

So T1 and T2 — and the odd-symmetry identity T2 actually rests on — are
machine-checked results, not prose. At that point `BSM.t3_delta_identity`,
`BSM.t4_call_bounds`, `BSM.t4_put_bounds` were still deferred and ratcheted at
3 markers; they landed in PR #2 (row 3, below).

### C3 — `docs/04` claimed a mathlib dependency that does not exist

`docs/04_formal_plan.md` listed "`Real.erf` (already in Mathlib:
`Mathlib.Analysis.SpecialFunctions.Erf`)" and "`Real.hasDerivAt_erf`" as
available dependencies. **Neither exists in v4.34.0.** Verified against the
release tag: no file named `Erf.lean` among the tree's 9112 `.lean` files, and
GitHub code search over `leanprover-community/mathlib4` returns 0 hits for
`Real.erf`, `def erf` and `erf_neg` — against 107 for `Real.sqrt` and 57 for
`Real.pi`, so the search itself was working.

`ImprovedBS/Core.lean` now defines `erf` itself as
`(2 / Real.sqrt Real.pi) * ∫ t in 0..x, Real.exp (-(t^2))` and proves `erf_neg`
by substitution in the interval integral. That supplies exactly the *oddness*
T2 needs.

It does **not** supply what T4 and T5 need, and this changes their budgets:
bounds `0 ≤ Phi ≤ 1` require `|erf x| ≤ 1`, hence the *value* of the Gaussian
integral `∫ x:ℝ, exp (-(x^2)) = sqrt pi` — measure theory
(`Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`), not
interval integrals. T5 likewise needs `HasDerivAt erf`, now derived rather than
imported. Both briefs should be re-budgeted before being handed out; BRIEF_003
already carries the warning in T4's doc-comment.

*(Outcome, PR #2: half right. The Gaussian integral's value was needed and it
was measure theory — but it entered through `Φ(x) = ∫_{(−∞,x]} φ`, not through
`|erf x| ≤ 1`, and the bounds `0 ≤ Φ ≤ 1` were the cheap part. The expensive
part was the T4 *lower* bound, whose recorded route was wrong. See C4.)*

**Generalizable lesson, and the reason this is in the ledger rather than a
commit message:** a mathlib dependency is a claim about a *specific version* and
must be checked against that version. Two plausible-looking import paths,
guessed without a toolchain, cost three red runs. Any brief that adds a mathlib
dependency should require the author to verify the path against the pinned tag —
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.34.0` is
reachable even where the Lean toolchain is not.

## CI history for row 3 (PR #2)

Two runs, both green. Recorded anyway, because the *reason* it was one run
rather than eight is the transferable part.

| # | head | `lake build` | notes |
|---|---|---|---|
| 1 | `2273461` | **GREEN** 3m54s | T3 + T4 + 18 helper lemmas, first push |
| 2 | `726325d` | **GREEN** 3m10s | workflow-only change: post the `#print axioms` output as a PR comment on success, so the audit is quotable without artifact access |

What made the difference from PR #1's eight runs: **every mathlib name was
checked against the pinned tag before pushing**, via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.34.0`, and
that check caught one real error at the desk — `map_add_right_eq_self` is in
namespace `MeasureTheory`, not `MeasureTheory.Measure` (its source file `open`s
`MeasureTheory.Measure`, which is why the sibling `map_neg_eq_self` *looks*
namespaced in mathlib's own proofs). Three stylistic rules also paid for
themselves: fully qualified names and no `open`, so nothing resolves by
accident; `mul_comm`/`mul_assoc` always with explicit arguments, because bare
`mul_comm` will happily rewrite the `2 * π` inside `√(2π)`; and no `field_simp`,
whose closes-or-doesn't behaviour cannot be predicted without a toolchain.

### Machine-checked as of run 35514867674

Quoted from the audit comment the workflow now posts on PR #2 — all 25
declarations in the T1–T4 node depend on exactly
`[propext, Classical.choice, Quot.sound]` and nothing else:

    BSM.exp_neg_sq_even   BSM.erf_neg   BSM.Phi_add_Phi_neg   BSM.Phi_neg
    BSM.t1_d1_minus_d2    BSM.t2_put_call_parity   BSM.t2_put_call_parity_spread
    BSM.phi_neg   BSM.phi_nonneg   BSM.phi_integrable   BSM.phi_add
    BSM.integral_phi_Iic_zero   BSM.Phi_eq_integral_Iic   BSM.Phi_nonneg   BSM.Phi_le_one
    BSM.integral_comp_add_right_Iic   BSM.Phi_le_exp_mul_Phi_add
    BSM.d1_exponent   BSM.d2_exponent   BSM.forward_eq
    BSM.bsCall_nonneg   BSM.bsPut_nonneg
    BSM.t3_delta_identity   BSM.t4_call_bounds   BSM.t4_put_bounds

`.github/lean_lint_baseline.json` now reads `"deferred": {}`. The lint's
`PROTECTED` set covers all of the above, so none of them can go back to `sorry`
without an automatic reject; `REQUIRED` covers them so none can be deleted.

### C4 — BRIEF_003's T4 route was wrong, and its budget was inverted

**Date:** 2026-09-20. **Trigger:** analysis before writing any Lean, confirmed
by the proof that landed. Full detail in the correction record at the top of
`briefs/BRIEF_003_t3_t4_bounds.md` and in the T4 doc-comment in
`ImprovedBS/Core.lean`.

The brief (and the T4 doc-comment it pointed to) said the lower bound
`max(F − D, 0) ≤ bsCall` follows from `0 ≤ Φ ≤ 1` plus monotonicity of `Φ` and
`d2 ≤ d1`. It does not. Monotonicity gives `bsCall ≥ (F − D)·Φ(d1)`, and since
`0 ≤ Φ(d1) ≤ 1` that is *weaker* than both `bsCall ≥ 0` and `bsCall ≥ F − D`
in the regime where each is the binding one. Concretely, S=100, K=120, τ=1,
r=q=0, σ=0.2: `bsCall ≈ 2.15` and `(F − D)·Φ(d1) ≈ −4.17`. A contributor
following the brief would have proved `Phi_monotone` (real work — it needs
`Φ′ = φ` or the integral representation) and then found that `linarith` cannot
close T4 from it, with no explanation in the tree of why.

What the lower bound actually is: the BSM price is the discounted expectation
of a non-negative payoff, so `bsCall ≥ 0`, `bsPut ≥ 0`, and parity turns the
second into `bsCall ≥ F − D`. That is a statement about `Φ` as an *integral*,
and it landed as one inequality, `Phi_le_exp_mul_Phi_add`:
`Φ(x) ≤ e^{a x + a²/2} Φ(x + a)` for `a ≥ 0`, which is the pointwise identity
`e^{a u + a²/2} φ(u + a) = φ(u)` (complete the square) integrated over
`(−∞, x]`. At `x = d2`, `a = σ√τ` it reads `D·Φ(d2) ≤ F·Φ(d1)`; at `x = −d1`
it reads `F·Φ(−d1) ≤ D·Φ(−d2)`. The same pointwise identity, un-integrated, *is*
T3. So the budget line was backwards: T3 is an eight-line corollary of the
tilting identity, and T4 is where the analysis lives — sixteen infrastructure
lemmas plus the two positivity lemmas, ~200 lines with their doc-comments,
including a translation-invariance lemma for half-line integrals
(`integral_comp_add_right_Iic`) that mathlib v4.34.0 has only in reflection form.

**Generalizable:** a recorded proof route is a claim and should be checked the
way a statement is — by trying to break it on a numeric example *before*
formalising. Ten seconds with the oracle (`bsCall(100,120,1,0,0,0.2)` against
`(F − D)·Φ(d1)`) falsified the route; the brief's author had checked the
*statement* numerically (`test_value_bounds`) but not the *route*. The T4
doc-comment now records the failed route and the counterexample next to the
proof, so the next reader does not have to rediscover it.

### C5 — BRIEF_002: Oracle ↔ Lean pointwise cross-verifier (guard 3)

**Date:** 2026-09-20. **Landed:** PR #3, run 35517328856.

**Summary:**
Stands up guard (3) from `docs/04` §"Oracle ↔ formal correspondence":
- **Golden grid:** `tests/golden_grid.json` commits 39 parameter points covering
  moneyness $S/K \in \{0.5, 0.8, 1.0, 1.2, 2.0\}$, tenors $\tau \in \{1/12, 0.25, 1.0, 3.0\}$,
  vols $\sigma \in \{0.05, 0.2, 0.6\}$, non-zero dividend yield $q$, and negative rates $r$.
  Inputs only are committed; single source of truth managed via `scripts/gen_grid.py`.
- **Lean side:** `ImprovedBS/Crosscheck.lean` implements independent closed forms in IEEE-754
  double precision (`Float`) and evaluates them via `#eval runCrosscheck`, emitting greppable
  `CK` records with high-precision Cody (1969) rational Chebyshev approximation for `erf`
  (accuracy $\sim 1.1\times 10^{-16}$).
- **Oracle side:** `tests/test_crosscheck.py` cross-verifies all six quantities
  ($d_1, d_2$, call, put, parity, delta identity) against `experiments/black_scholes.py`.
- **Tolerance:** Double precision matches across all 39 points with worst-case differences:
  $\Delta d_1, \Delta d_2 \le 1.1\times 10^{-16}$, $\Delta \text{call}, \Delta \text{put} \le 1.6\times 10^{-14}$.
  Committed tolerances set to $10^{-12}$ (safety factor $> 50\times$).
- **Anti-vacuity & non-tautology:** 4/4 mutation tests in `test_crosscheck.py` prove that
  deliberately perturbing $d_2$ (e.g. flipping $-\sigma^2/2$ to $+\sigma^2/2$), call, put,
  or parity immediately fails CI with the exact diverging points named. Structural guards
  in `scripts/lean_lint.py` enforce derivation independence and grid synchronization.
- **CI integration:** Wired into `.github/workflows/lean.yml` (`lake env lean ... | python3 tests/test_crosscheck.py`)
  and `.github/workflows/oracle.yml`. Failure logs and divergence reports are automatically
  published back to the PR if triggered.

### C6 — statement pins and the lint's own mutation harness

**Date:** 2026-09-20. **Trigger:** an audit of the *grading lane* — the question
asked was whether the toolchain-free Python had become an unverified pillar under
the Lean assumptions. Four findings, only one of which was about the oracle.

1. **No theorem depends on the Python, and that was worth checking rather than
   asserting.** `ImprovedBS/Core.lean` imports no numeric value, declares no
   `axiom`, and its 25 protected declarations are all `∀ S K tau r q sigma`
   proved from mathlib; deleting `experiments/` and `tests/` leaves T1–T4
   theorems of mathlib. The oracle is load-bearing in a different way: emptying
   those directories turns `scripts/lean_lint.py` red, so the *gate* needs the
   Python even though the *proofs* do not.
   Notably, the thing a numeric oracle would otherwise be trusted to supply —
   that `Φ` is normalized to integrate to 1 — stopped being a Python assumption
   when BRIEF_003 landed: `integral_phi_Iic_zero` derives it from
   `integral_gaussian_Ioi`, and halving `erf`'s `2/√π` prefactor now fails the
   build instead of failing a comparison.
2. **The linter was the unverified pillar.** `lean_lint.py` decides whether the
   tree is honestly labelled and gates `lake build` via `needs:`, and nothing
   tested it. `tests/test_lint.py` now does, with the repo's own discipline
   (21 seeded cheats, each required to be killed by a named check; 5 legitimate
   edits required to stay green; a baseline guard so "all mutants killed" cannot
   be satisfied by an always-red lint).
3. **The vacuity hole the repo's rule had not been applied to.** Replacing a
   landed theorem's statement with `: True := trivial` was, before this change,
   invisible to every lane: it builds, shows no `sorryAx`, keeps its name, and
   the oracle suite stays 13/13. Conversely the parity guard was *too* strict —
   reproving T2 with `simp only [bsPut, bsCall, Phi, erf_neg]`, i.e. odd
   symmetry one step closer to its source, was a lint failure. Both directions
   are now pinned: `[PINS]` (source text, everywhere) + the CI `elab` layer
   (elaborated types), and `ODD_SYMMETRY_WITNESSES` accepting any real witness of
   the symmetry. `tests/test_mutants.py`'s positive-anchor trick was also missing
   from `[ORACLE SYNC]`, whose checks were all prohibitions — a hollowed-out
   oracle satisfied it. `ORACLE_ANCHORS` fixes that, and the mutant
   "M-oracle-3" proves the fix does the work.
4. **Two defects found in the BRIEF_002 lane, deliberately not fixed here** (they
   belong to guard (3), not to this change; recorded so they are not lost):
   `ImprovedBS/Crosscheck.lean` defines `deltaIdentityRhs` and never prints it,
   so the cross-verifier compares *LHS to LHS* and never checks T3's equation
   across trees, while its module header claims both sides do; and
   `tests/test_crosscheck.py --run-lean` is unreachable whenever stdin is not a
   tty (`not sys.stdin.isatty()` claims the input first), so it prints
   `4/4 crosscheck unit test(s) passed` without cross-verifying anything —
   reproducible with `echo -n | python3 tests/test_crosscheck.py --run-lean`.
   The deeper point about that lane, for a future brief: `Crosscheck.lean`
   imports *nothing*, so guard (3) cross-checks the oracle against a hand-written
   `Float` twin rather than against `BSM.*`, and the twin↔formal link is carried
   by prose and by `[CROSSCHECK SYNC]`'s regexes. The chain
   "published textbook values ≡ oracle ≡ Lean" is therefore only as strong as a
   human reading that the twin matches the tree. A `BSM.*`-anchored version of
   that guard (validated bounds on the real definitions via `norm_num`/`interval`
   arithmetic, at a few grid points) is the fix, and it would retire the twin.

5. **The bootstrap and the skew.** `elab` can only be produced by `lake env lean`,
   so the artifact ships with an empty block and the build job prints the block to
   commit — a red first run, by design, because a pin that was never produced is not
   a passing pin. That red found a real bug: `#print axioms` quotes the constant name
   (`'BSM.Phi' depends on axioms: [...]`) where `#check` does not (`BSM.Phi : ℝ → ℝ`),
   and the parser had assumed symmetry between two commands that share no format. The
   parser refused to pin a half-result (type recovered, axioms empty), which is the
   behaviour that made this a fixable log line rather than a corrupt artifact. It is
   now a pure function tested against recorded CI output in `tests/test_pins.py`, so
   the assumption is exercised where it can be iterated on. Committing a real `elab`
   block then enabled a check the empty artifact could not have: `cross_layer_check()`
   compares which spec constants the pinned *statement* mentions against which the
   pinned *type* mentions, catching the stale combination (`--write` preserves `elab`,
   so a toolchain-less author can produce it by accident). The mutant that used to be
   the harness's declared local gap is now killed by it, and the gap entry was
   replaced by the deliberate self-consistent forgery — hollow the claim, re-run
   `--write`, hand-edit `elab` — which no local lane can see and CI sees instantly,
   because CI re-elaborates rather than re-reading. Attribution was checked, not
   assumed: disabling only `cross_layer_check()` leaves exactly one survivor out of
   22 mutants; deleting the whole `[PINS]` block leaves eight.

**Generalizable:** a graded tree needs its *grader* graded. Every lane here had a
falsifier except the one whose verdicts the others were written to satisfy, and
the class of cheat that slips through a name-and-marker check — keep the name,
keep the absence of `sorry`, change what is claimed — is exactly the class that
cannot be caught syntactically, which is why the answer is a pinned artifact plus
an elaboration diff, not a stricter regex.

### C7 — BRIEF_004: the `α < 2` acceptance item was false; the theorem is stated for every real `α`

**Date:** 2026-09-20. **Trigger:** *proving* the brief, not running the grader.
**Found by:** the author, while choosing the half-line levels `x = 2^k`: the
lower bound `e^{2^k} · (2^k)^(−α) → ∞` never consults `α`, which forced the
question of whether `α < 2` was load-bearing at all.

1. **`α < 2` dropped from the statement.** BRIEF_004's acceptance item 4
   demanded the hypothesis be *used*, with the argument: "with `α ≥ 2`-like
   Gaussian tails the exponential moment is finite, so a proof that never uses
   `α < 2` has proved something false". The instinct is right — a proof that
   ignores a hypothesis can be a proof of a false statement — but the argument
   is invalid. A Gaussian tail is not a power law with `α ≥ 2`: `e^{−x²/2}` is
   eventually *below* `c·x^(−α)` for **every** `α`, so it satisfies no such
   hypothesis at any index and cannot be the counterexample the item claims.
   For a genuine power tail the conclusion holds at every index —
   `∫ e^x x^(−3) dx` diverges exactly as `∫ e^x x^(−1) dx` does. The dichotomy
   the obstruction turns on is **polynomial versus exponential decay**, not
   `α < 2` versus `α ≥ 2`.
   The machine-checked form of the correction is the absence of `α < 2` from
   the theorem, and the pins record it: `tests/golden_statements.json` stores
   the statement as it is. The result is strictly stronger, and it *widens* the
   obstruction inside T6 — `α ∈ (0, 2)`, the whole interval the resolution
   cares about, is inside it, so the tempered (CGMY) repair is not an artifact
   of having restricted the index.
2. **`0 < α` dropped as a binder, kept as a statement note.** It too is never
   used in the proof: the divergence is `exp` versus `rpow` and the index does
   not enter the estimate. Its content is a domain fact — for `α ≤ 0` the lower
   bound `μ([x, ∞)) ≥ c·x^(−α)` is *unsatisfiable* for a probability measure,
   since it forces `c ≤ μ([x, ∞))` for all large `x` — so `α > 0` is exactly
   the range in which the hypothesis says anything. Recorded in the module
   doc-comment and `docs/03` §D1 rather than kept as an unused hypothesis.
3. **Not machine-checked, and said so:** the specialization to a symmetric
   α-stable law. mathlib v4.34.0 has no such law, so the tail bound enters as
   the hypothesis; the `c = F(−α)` constant of the Zolotarev `S1` tail stays a
   citation in `docs/03` §D1, per the brief's scope item 3. No definition-free
   fake and no prose posing as a theorem.

**What this says about "use your hypotheses" as an acceptance bar.** It is the
right instinct — it is what kills vacuous proofs — but it cannot be written as
a *syntactic* requirement, because the honest answer to "does this proof need
`α < 2`?" can be "no, and the hypothesis should not have been there". The bar
that survives is the one the repository already uses: pin the statement,
audit the axioms, and record the correction when the *brief's* statement, not
the proof, was the thing that was wrong.

### C8 — BRIEF_002's two recorded crosscheck defects, fixed (C6 item 4 closed)

**Date:** 2026-09-20. **Landed:** PR #6, run 35526035651 (build lane),
35526035655 (oracle lane). **Trigger:** C6 item 4's own escalation — the two
defects it recorded "deliberately not fixed here … recorded so they are not
lost" were next in the queue.

1. **The delta identity's RHS is now actually cross-checked.** `runCrosscheck`
   evaluates *and prints* both sides per grid point (14-token `CK` lines: six
   parameters + `d1 d2 call put parity deltaLhs deltaRhs`); the Python
   comparator checks each side against the oracle's independently computed
   counterpart and the two sides against each other. The interesting part is
   **where the guard had to live.** A twin that prints the LHS *twice* passes
   every numeric comparison: the two sides agree to ≤ 7.2e-15 inside the
   oracle (measured over the grid), an order of magnitude under the 1e-12
   tolerance, so `internal_delta` reads 0 while `delta_rhs`-vs-oracle reads
   ≤ 7.2e-15 — both green. No absolute-tolerance comparator can see that
   cheat at those magnitudes; what sees it is the *source*: `[CROSSCHECK
   SYNC]` in `scripts/lean_lint.py` now requires `runCrosscheck` to reference
   `deltaIdentityLhs` and `deltaIdentityRhs`, and `tests/test_lint.py` seeds
   both halves of the defect class — CC1 (LHS printed twice; numerically
   invisible, structurally dead) and CC2 (definition deleted). The numeric
   half was not given up on: the comparator also gained a *formula-level*
   mutant (RHS recomputed with `φ(d1)` in place of `φ(d2)`), which is caught
   only at the grid's largest-delta point — at deep-OTM points both T3 sides
   are ~1e-30, under *any* absolute tolerance, and that fact is now recorded
   in the test rather than left to a future reader's surprise.
2. **`--run-lean` can no longer self-skip.** `not sys.stdin.isatty()` claimed
   the input before the `--run-lean` branch; the recorded repro
   (`echo -n | python3 tests/test_crosscheck.py --run-lean` → `4/4 crosscheck
   unit test(s) passed`, exit 0) was reproduced before the fix and is,
   after it, a loud `FAIL: \`lake\` not found on PATH …` with exit 1. Input
   sources now take effect in an explicit order (`--run-lean` → `--lean-output`
   → piped stdin → auto-detect → self-tests); a named source is honored or
   errors; `--run-lean --lean-output` together is a contradiction, not a
   precedence rule; missing `lake` names the alternatives. The regression is
   pinned by `test_run_lean_flag_is_honored`, which scrubs PATH and replays
   the repro in a subprocess.

**Generalizable:** a cross-verifier has *two* vacuity classes, not one — value
corruption (a number wrong by more than tolerance) and *formula duplication
within tolerance* (a required column that is a copy of another). The first
class is the comparator's job; the second is provably invisible to any
absolute-tolerance comparator when the duplicated quantity's two sides agree
below tolerance, and it is the structural lint's job. Decide which class a
defect belongs to before assigning the guard — a wrong assignment is a guard
that cannot fire. And the second defect is the small-c interface version of
row-1-run-5's lesson: a mode that can silently degenerate into a weaker check
while inheriting the stronger check's PASS is worse than no mode.

## CI history for row 4 (PR #5)

Four runs, three of them informative, and the whole module was written in a
sandbox with no Lean toolchain — the CI lane was the first thing that ever
compiled it.

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `54a0ff6` | first push of `ImprovedBS/Levy.lean` | build fail, two one-line errors: `add_le_add_right` in v4.34.0 adds on the **left** (`h : x ≤ y` gives `d + x ≤ d + y`), so the term fed to `Real.exp_le_exp.mpr` had the wrong sum for the goal; and `ENNReal.ofReal_coe_nnreal` is stated with an implicit variable, so it is not a function of `r` and `(lemma r).ge` does not elaborate. Everything else in the module — `setLIntegral_mono'`, the half-line bound, `Real.tendsto_exp_div_rpow_atTop`, `Tendsto.const_mul_atTop`, both §2 scaling lemmas — elaborated on the first try. |
| 2 | `edfafc4` | `add_le_add_right` → explicit `hxy := hy` + `linarith`; `(lemma r).ge` → a typed `have` with `ENNReal.ofReal_coe_nnreal.symm` | build fail, one step further: `(r : ℝ≥0)` is scoped notation under `NNReal`, which the module does not open, so it parsed as the *comparison* `ℝ ≥ 0` and the elaborator asked for `LE Type` / `OfNat Type 0`. A notation-scope error, not a mathematical one. |
| 3 | `99db114` | spell `NNReal`/`ENNReal` explicitly in the coe step | **build GREEN + audit GREEN**: all 32 constants (25 existing + 7 new) report `[propext, Classical.choice, Quot.sound]`, none `sorryAx`. Pins RED *by design*: seven declarations with no `elab` block, and the block to commit was printed paste-ready by the failing step. |
| 4 | `d61c874` | commit the printed block verbatim | **GREEN** — `lint` + `lake build` + sorryAx audit + **Statement pins (elab)** + `Oracle ↔ Lean` crosscheck all pass. 38 pins, 38 elaborated pairs. |

**Machine-checked as of run 35523250105.** `BSM.ofReal_mul_tail_le_lintegral_exp_add`,
`BSM.lintegral_exp_add_eq_top_of_tail_lower_bound`,
`BSM.lintegral_exp_eq_top_of_tail_lower_bound`,
`BSM.exp_moment_infinite_add_of_tail_lower_bound`,
`BSM.exp_moment_infinite_of_tail_lower_bound`,
`BSM.spot_not_integrable_of_tail_lower_bound`,
`BSM.no_drift_makes_spot_integrable`. What is *not* machine-checked, and is
declared as such in the module and the PR: the specialization to the symmetric
α-stable law — mathlib v4.34.0 has no such law, so the power tail bound is the
hypothesis and the `c = F(−α)` constant stays a citation in `docs/03` §D1.

**Why this row is worth reading as a grading story.** The interesting part is
not that two proofs had to be fixed; it is that the *statement* was wrong before
the proof existed, and the fix was to prove more than the brief asked
(correction C7). The acceptance item "the hypotheses are used: `0 < α`,
`α < 2` …" would have rejected a correct, stronger theorem, and the sanity
check offered for it was a false statement about Gaussian tails. The sequence
that got the right answer was: prove it, notice the proof never touches `α < 2`,
work out why the demanded hypothesis does not belong, and record the correction
— which is the same sequence that produced C1 and C4. The pins then make the
strengthened statement the *checked* one, so "the brief asked for `α < 2`" can
never quietly re-enter the tree.

### C9 — `docs/04`'s T5 route was reversed by the brief that implemented it

**Date:** 2026-09-20. **Trigger:** writing BRIEF_006, whose first scope item was
to settle the coordinate question that `docs/04` had left open.

`docs/04` §"The dependency spine" carried a paragraph headed **"Change variables
before differentiating"**: formalize T5 in `x = Real.log S`, where the BSM
operator has constant coefficients and the closed form is the convolution of the
payoff with the Gaussian kernel, with uniqueness coming from the heat-kernel
side. BRIEF_006 §1 commits to the opposite: the PDE stated and proved directly in
`(S, τ)`, with `V_S` and `V_SS` as the derivatives of the closed form. The
reasons (also recorded in `docs/04`, where the paragraph now points at this
correction):

1. The graded claim *is* the `(S, t)` PDE. A change of variables proves a
   different theorem — the heat equation for `v(x, τ) = V(e^x, τ)` — and
   recovering the stated identity needs the chain rule back twice, so the `1/S`
   factors the paragraph wanted to avoid arrive anyway, hidden inside a
   substitution lemma.
2. The log-`S` route is not "cheaper", it is *priced elsewhere*: it needs the
   convolution with the Gaussian kernel to be a theorem in the tree, i.e. the
   measure-theoretic side that `docs/04`'s own mathlib table marks as not yet
   available at this tier. In `(S, τ)` the whole analytic bill is one interval
   integral — the derivative of the local `erf`, since mathlib v4.34.0 has no
   `Real.erf` and therefore no `HasDerivAt erf`.
3. The feared cost did not materialize. The `S`-side algebra is two
   `field_simp`/`ring` steps, and the `√2`/`√π` factors cancel as *quotients*
   rather than as squares — no `Real.sq_sqrt` appears anywhere in the T5 node.
   That is a measurable outcome, not an impression: it is what the node's shape
   shows, and the brief records it because the argument for the other route was
   an argument about cost.

The uniqueness half is deferred, not dropped: it belongs to T6 sub-goal 3, where
the kernel and the measure-theoretic integral are the actual objects. A second,
smaller staleness in the same section is corrected too: the closing paragraph
assigned the T5 coordinate decision to "whoever writes BRIEF_005", and
BRIEF_005 was the tempered-contour brief.

**Generalizable lesson, and the reason this is a correction rather than a silent
edit:** a plan document's *route* paragraph is a prediction about a proof that
does not exist yet, and it will sometimes be wrong. The failure mode is not the
wrong prediction, it is a brief that follows it anyway (or leaves both routes
open, which is the same thing with more words). The check that keeps the
*implemented* route honest is new with this brief: `[SPINE]` in
`scripts/lean_lint.py` fails if the T5 node stops citing `t3_delta_identity` and
`hasDerivAt_Phi`, or if `t5_delta` stops consuming T3 — because "T5 was proved
via T3" is a claim about a proof *body*, and nothing in the tree could see a
route change before.

Two mathlib-arity findings from this brief, recorded because they cost guessing
time and generalize past T5:

- **`HasDerivAt.comp`'s point is an explicit argument, and it is invisible in
  the statement.** `Mathlib/Analysis/Calculus/Deriv/Comp.lean:243` is written
  `theorem HasDerivAt.comp (hh₂ : …) (hh : …)`; the `𝕜`-point appears in neither
  binder. It is contributed by a `variable … (x)` line 170 lines earlier (with
  the comment *"For composition lemmas, we put x explicit to help the
  elaborator"*), so every call site in mathlib passes it:
  `(Real.hasDerivAt_exp (f x)).comp x hf`. A source grep of the statement text
  cannot see this; the call sites can.
- **`Real.hasDerivAt_log`'s value is `x⁻¹`, not `1/x`.** The `S`-side chain rule
  needs `inv_div` before the quotients cancel, or the inverse-of-a-quotient
  survives into `field_simp` as a term nobody wrote on purpose.

Both are instances of the rule this ledger already carries from C3 — *a mathlib
dependency is a claim about a specific version, and it has to be checked against
that version* — with one addition: for a lemma, "the version" includes its
*signature*, and a signature is not always visible in the declaration's first
line.

## CI history for row 6 (PR #8)

Four runs, and every failure in them was *elaboration*, not mathematics: the
tree that run 1 rejected and the tree that run 4 accepted differ only in tactic
spellings. The eight lemmas and three derivatives of T5 were never in question.

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `66a9e99` | first push of the T5 section | build fail, **15 errors**, all `ImprovedBS.Core` (the tail of T1–T4 built, and `ImprovedBS.Lean`/`Fourier.lean` were untouched) — `lint` green, so `[SPINE]`, the 11 new pins and the ratchet were already fine in the CI environment. |
| 2 | `6c93d96` | 16 surgical fixes: four `No goals to be solved`, three `simpa`-against-a-bare-`def`, six `HasDerivAt.comp` calls, `← sub_mul` → `← mul_sub`, `Real.hasDerivAt_sqrt`'s point | build fail, **3 errors** — and, importantly, only sites run 1 could not reach (a failing block skips the rest of its declaration). Everything from `d1_tau_sub_d2_tau` on elaborated clean, so the composition bridges all landed. |
| 3 | `2792ce5` | the last three: the fifth `field_simp`-already-closed `ring`, `simpa only [Phi]` on an *unapplied* `Phi`, and `Real.hasDerivAt_sqrt htau.ne'` | **build GREEN** (`✔ [8926/8928] Built ImprovedBS.Core`, `✔ [8927/8928] Built ImprovedBS`), sorryAx audit **GREEN** — and the job red *by design* at the pins step: 11 constants with no `elab` entry. The step printed the paste-ready block, and the workflow's failure publisher put it on PR #8, which is the only reason a toolchain-less sandbox can iterate at all. |
| 4 | `4fd57de` | commit that block byte-for-byte, after diffing its 49 pre-existing entries field-by-field against the committed ones (`added: 11, removed: 0, changed: 0`) | **GREEN** — `lint` + `lake build` + sorryAx audit + **Statement pins (elab, 60)** + the oracle↔Lean pointwise cross-verifier all pass; oracle lane run 35566569054 green. |

**Machine-checked as of run 35566569107.** `BSM.hasDerivAt_erf`,
`BSM.hasDerivAt_Phi`, `BSM.hasDerivAt_d_spot`, `BSM.d_tau_quotient_eq`,
`BSM.hasDerivAt_d_tau`, `BSM.d1_tau_sub_d2_tau`, `BSM.t5_delta`,
`BSM.t5_gamma`, `BSM.t5_tau`, `BSM.t5_bsCall_pde_tau` and
`BSM.t5_bsCall_pde` elaborate at mathlib v4.34.0 and depend only on
`[propext, Classical.choice, Quot.sound]`, never `sorryAx`; their 11 pinned
`elab` types are the statements the ledger claims, so a restatement cannot pass
while the prose still reads right. `deferred: {}` is untouched, no T1–T4
statement or pin moved, and `docs/04`'s spine section carries the corrected
route (C9).

Two findings generalize past T5, and both are the kind that cost a run per
occurrence:

- **A term whose type is already fixed is compared to the goal, not unified
  with it — and that comparison does not unfold `Pi`-instance forms or an
  unapplied `def`.** `simpa using e` elaborates `e` on its own, then compares;
  the same `HasDerivAt` written as a goal is elaborated *against* the expected
  type and unified. So `simpa` cannot see that
  `(fun u ↦ bsCall S K u r q sigma)` and
  `(fun u ↦ …) - fun u ↦ …` are the same function, nor that a goal whose
  function is the bare constant `erf`/`Phi` is the lambda in `e` — `simp only
  [erf]` matches the *applied* equation `erf x = …` and the goal's occurrence is
  not applied. The fix is not a stronger `simp` set: state the unfolding as an
  explicit `funext` equation and `rw` it, in whichever direction the goal needs.
  Four of the 15 errors were the mirror image of this in arithmetic, where
  `field_simp` had already closed the goal and the trailing `ring` was `No goals
  to be solved` — a hard error, and the one error class here that a "harmless
  extra tactic" reading gets exactly backwards.
- **`HasDerivAt.comp` with a lambda-form expected type makes the elaborator
  invert the composition.** Given `HasDerivAt (fun x ↦ Phi (d1 x)) … S`, it
  answers `?m ∘ fun x ↦ d1 x` and then asks `hd1S` for a derivative of
  `∫ …` — the error names a subterm nobody wrote. Elaborating the *same*
  application with no expected type reads `h₂` off `hasDerivAt_Phi`'s own type
  and works; that is what the already-green `hasDerivAt_d_spot` did, which is
  why the pattern was worth copying rather than inventing a `show`.

| 5 | `d8153aa` | the wording commit itself: row 6's verdict, this history section, and the `README`/`docs/04` placeholders | no verdict to decide — docs only, and re-graded anyway: **GREEN** (lean run 35567331284, oracle lane run 35567331328), every step of both jobs, which is what makes the wording citable rather than merely typed |

A third, smaller one belongs with C9's arity notes: **`Real.hasDerivAt_sqrt`'s
hypothesis is `x ≠ 0`, so the proof handed in *is* the point.** Passing
`√tau ≠ 0` instantiates it at `√tau` (derivative `1/(2*√√tau)`), which is
type-correct-looking and silently not the lemma you want.

### C10 — the pins channel truncates, and the pins step did not know it

**Date:** 2026-09-21. **Trigger:** PR #9, run 35573065136 — the first run of
BRIEF_007 whose build was green.

The mechanism the two-run pin arc rests on is: the build job's pins step prints
the freshly elaborated `elab` block, the failure publisher posts the log to the
PR, and a toolchain-less sandbox commits the block verbatim. That publisher posts
the **last 25 000 characters** of each log (`tail -c 25000`, `lean.yml`), which
was ample for 49 and 60 entries. At 81 entries the block is ~30k characters, so
the PR comment began mid-block and the first-sorted new entry,
`BSM.Phi_eq_gaussianReal_Iic`, was cut off. Actions logs and artifacts sit
behind blob storage the sandbox cannot reach (the same fact that made the
publisher necessary, C6), so there was no second copy to read.

Two things were wrong and both are fixed in this PR, not worked around:

1. **The step printed only a block that grows with the tree.** It now also
   prints an `elab_delta` block — the entries that are missing from or differ
   from the committed `elab` — *after* the full block, so whatever the tree's
   size the tail of the log contains exactly what must be committed
   (`elab_delta` in `scripts/pin_statements.py`; run 35573718718 exercised it:
   one entry, printed last, inside the tail).
2. **"Commit verbatim" was a manual paste.** `--elab-merge <file>` now merges a
   CI-printed `elab`/`elab_delta` block into `tests/golden_statements.json`,
   refuses a name the source layer does not pin, and reports every entry it
   overwrites. `tests/test_pins.py` gained two tests: the delta is exactly the
   merge set (identical entries excluded, normalisation respected, bootstrap =
   whole block), and the merge is verbatim, reports overwrites, and refuses
   unpinned names — 12/12.

What was **not** done: hand-typing the missing elaborated type. It was
guessable (`BSM.Phi x = (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal`)
and the guess would have been wrong — Lean prints the measure application as
`((ProbabilityTheory.gaussianReal 0 1) (Set.Iic x)).toReal`. The 20 entries that
were inside the tail were merged from run 35573065136's comment, the 21st from
run 35573718718's delta, and the rule that every `elab` entry in the golden file
was produced by CI holds for all 81.

## CI history for row 7 (PR #9)

Authored without a toolchain; every mathlib name read in the v4.34.0 source
via the GitHub contents API before the first push (ledger C3), and the route
checked numerically first (C4: `bs_call_by_expectation` vs the closed form,
≤ 1.6e-12 relative on the golden grid).

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `31ea20e` | first push of `ImprovedBS/RiskNeutral.lean`, 21 declarations | build fail, **2 errors**, both in the last theorem `bsCall_eq_lognormal_expectation` and both one cause: at the tag `NNReal` is a `def` over `{r // 0 ≤ r}` with a *protected* `NNReal.mk`, and the anonymous constructor `⟨(σ√τ)^2, _⟩` elaborates at the subtype, which is "not type-correct under `HMul ℝ≥0`" — so `NNReal.coe_mul` found no pattern, and `rw [hw]` could not match the `NNReal.mk (c ^ 2) _ * v` that `gaussianReal_map_const_mul` produces. The other **20 declarations elaborated on the first run**, including both main theorems, the Gaussian bridge and the `integral_map` pull-backs. `lint` and `oracle` green. |
| 2 | `5b34b2b` | `hw` restated with `NNReal.mk`, consumed by `congrArg` (defeq) instead of `rw` | **build GREEN** (`✔ [8927/8929] Built ImprovedBS.RiskNeutral (5.2s)`, `✔ [8928/8929] Built ImprovedBS`), sorryAx audit **GREEN** — all 21 new constants on `[propext, Classical.choice, Quot.sound]`. Red *by design* at the pins step (21 constants with no `elab` entry) — and the printed block overflowed the 25k-character PR comment (C10): 20 of the 21 new entries recovered from the tail, one cut off. Four `fun_prop` fallbacks flagged as never executed (warnings, not errors) — `fun_prop` closes all four goals at the tag. |
| 3 | `2b12957` | the 20 recovered entries merged verbatim (60 → 80 `elab`; the 60 pre-existing entries byte-identical); `elab_delta` printed last + `--elab-merge` (C10); fallbacks removed | build **GREEN** with no `RiskNeutral.lean` warnings, audit **GREEN**, pins red *by design* for exactly one constant — and the new `elab_delta` block sat at the end of the tail with that one entry, `((ProbabilityTheory.gaussianReal 0 1) (Set.Iic x)).toReal`, whose parenthesised coercion form is the reason it was not typed by hand. |
| 4 | `f50a256` | the 81st entry merged from run 3's delta (`--elab-merge`, `added 1, changed 0`) | **GREEN** — `lint` + `lake build` + sorryAx audit (71 constants, all `[propext, Classical.choice, Quot.sound]`) + **Statement pins (elab, 81)** + the oracle↔Lean pointwise cross-verifier; oracle lane run 35574194638 green (14/14, 12 mutants 4/4, lint mutants 25, pins tests 12/12). The audit was published to PR #9 by the workflow. |
| 5 | *(this commit)* | the wording: row 7's verdict, this row, and the `README`/`docs/04`/brief status lines | docs only — re-graded anyway, as row 6's wording commit was; the verdict above is run 4's. |

Two things the arc says that are worth keeping:

- **Mathematically nothing was in question after the first push.** 20 of 21
  declarations — both main theorems included — elaborated on run 1; the one
  failure was a *constructor spelling* for `ℝ≥0` (`NNReal.mk`, not `⟨_, _⟩`,
  because the tag's `NNReal` is a `def` with a protected `mk` and the anonymous
  constructor lands at the underlying subtype). That is the cheapest possible
  first-run failure for a 500-line measure-theory file written blind, and the
  reason is the C3 rule: every lemma below was read in the pinned source, with
  its signature, before it was used.
- **The pin bootstrap found a defect in its own channel and fixed it in the same
  PR** (C10). The 25k-character tail was enough for 60 entries and not for 81;
  the fix is a delta printed last plus a merge command, both tested, and no
  elaborated type was typed by hand to get around it.

## CI history for row 8 (PR #10)

Authored without a toolchain; every mathlib name verified in the v4.34.0 source
before pushing (ledger C3), and the route checked numerically first (ledger C4:
`bs_call_by_fourier_inversion` vs closed form ≤ 2.02e-11 rel on the 39-point grid,
imaginary part ≤ 2e-15 on textbook case).

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `23c41ea` (run 35577403029) | first push of `ImprovedBS/Inversion.lean`, 13 declarations | RED (12 of 13 declarations elaborated; type mismatch on line 211 in `carrMadan_inversion_eq_re`) |
| 2 | `aef13fb` (run 35577857638) | `rw [Complex.ofReal_re]` fix | RED by design on pins: `lake build` + `#print axioms` audit **GREEN** (all 11 new theorems on `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`), `elab_delta` (13 entries) printed last and published to PR #10 |
| 3 | `e974bd7` (run 35578278238) | merged 13 `elab_delta` pins via `scripts/pin_statements.py --elab-merge` (all 94 elab pins present) | **GREEN** (`lake build` + `#print axioms` audit + pins + crosscheck + lint all pass) |

### Notes on row 8 (PR #10)

- **12 of 13 declarations elaborated on the very first blind push.** The single
  flaw was an over-coercion in `carrMadan_inversion_eq_re`: `exact (Complex.ofReal_re _).symm`
  expected an equality of reals cast into complexes, whereas `rw [Complex.ofReal_re]`
  simplified the complex cast's real projection directly and resolved the reflexivity.
- **The two-run pin bootstrap worked without a hitch.** Run 2 passed the full Mathlib
  compilation and `#print axioms` audit, failing by design on the missing elab pins
  while emitting the un-truncated `elab_delta` block at the end of the log. Run 3 merged
  the 13 entries byte-for-byte and achieved immediate green across both oracle and lean lanes.
- **T6 is fully completed.** With BRIEF_005 (tempered decay and absolute convergence
  of the Carr–Madan kernel), BRIEF_007 (expectation bridge from closed form to risk-neutral
  and lognormal integrals), and BRIEF_008 (Fourier inversion and real-valuedness landing
  on the lognormal expectation and closed form), all parts of the research-tier T6 program
  are machine-checked in Lean 4 without sorries or non-standard axioms.

### C11 — BRIEF_009 §2's payoff integrability was false at infinite measures

BRIEF_009 §2 states `integrable_call_payoff` and `integrable_put_payoff` at a
bare measure `μ` with `hX : Integrable X μ`. As written that is **false**: a
nonzero constant over an infinite measure is not integrable — take `X ≡ 0`
(integrable everywhere) and `K > 0`; the put payoff is the constant `K`. The
CI arc that reached these proofs made `integrable_const` demand
`IsFiniteMeasure μ`, which is the mathematical content of the failure, not
just API shape. Both statements now carry `[IsProbabilityMeasure μ]` — the
same instance the parity and bounds half of the layer already had, and the
natural setting of a terminal-spot law (the layer's own subject). Exactly 2
of the 108 pins moved (arc 3); the 94 pre-existing pins are byte-identical
throughout, and every call site (`model_free_parity_gap`,
`model_free_put_call_parity`) already had the instance to supply. The brief's
route sketch for item 2 (`Real.abs_add`, `hX.abs.add (integrable_const |K|)`,
its own `?`-flagged guess) also died at the tag — `abs_add` is now
`abs_add_le` — and was replaced by the sharper domination
`‖max (X−K) 0‖ ≤ ‖X−K‖` over `X − K`; item 3's `max_sub_swap_eq` congruence
route survived as specified.

## CI history for row 9 (PR #11)

Seven lean runs, recorded for the reason row 5's history is: every failure was
*API shape at the mathlib v4.34.0 tag*, not mathematics, and the shapes are
worth more than the fixes. The workflow published each failure's error lines to
the PR (`Publish the failure log back to the PR`), which is what made
toolchain-free iteration convergent.

| # | head | `lake build` | cause |
|---|---|---|---|
| 1 | `d8a756a` | fail 3m45s | 9 errors, all in `Skeleton.lean`: `abs_add` unknown at the tag (dropped entirely — the domination bound became `‖max (X−K) 0‖ ≤ ‖X−K‖`, integrable via `Integrable.sub`); `MeasureTheory.integrable_const` takes its constant *explicitly* (5 sites); `aestronglyMeasurable_const` takes *no* explicit argument (2 sites); and `ℝ≥0` is *scoped* notation — `(1 : ℝ≥0)` parses as `ℝ ≥ 0` outside the scope (`failed to synthesize LE Type` / `OfNat Type 0`) and is `(1 : NNReal)` in `RiskNeutral.lean`'s frozen idiom |
| 2 | `1857697` | fail 3m33s | the half-fixed push: a batch of same-file edits clobbered each other (last writer wins) and the block rewrite never landed — 3 errors, all ones the commit message already claimed. Recovered in `2b82f42` after re-applying and verifying against the file |
| 3 | `2b82f42` | fail 3m42s | 5 errors: `integrable_const` needs `IsFiniteMeasure μ`, and the un-instantiated payoff-integrability statements were **false** at infinite measures (a nonzero constant over an infinite measure is not integrable) — `integrable_call_payoff`/`integrable_put_payoff` now carry `[IsProbabilityMeasure μ]` like the rest of the family (2 pins moved, the 94 pre-existing byte-identical); `AEStronglyMeasurable.max` does not exist — the Order-section lattice closure is `AEStronglyMeasurable.sup` (`max` is `sup` on `ℝ`); `integrable_withDensity_iff` wants `Measurable`, not `AEMeasurable` |
| 4 | `d760317` | fail 3m45s | 2 errors: `Integrable.mono`'s arguments are `(Integrable g) (AEStronglyMeasurable f) (ae-bound)` — the bound sat in the measurability slot; `integrable_withDensity_ofReal_iff` does not exist at the tag |
| 5 | `03c503b` | fail 6m33s | 2 errors + a named side goal: `integrable_withDensity_iff`'s pointwise form is `g x * (ρ x).toReal` — *not* the `.toReal • g` of its integral sibling `integral_withDensity_eq_integral_toReal_smul`, which the gaussian file itself uses — and the rule carries `(hflt : ∀ᵐ x, ρ x < ⊤)` that `rw` leaves as `case hflt`, discharged with `gaussianPDF_lt_top` |
| 6 | `bbd7c9f` | fail 4m08s | **build GREEN** (`✔ [8928/8931] Built ImprovedBS.Skeleton`, no error lines; `#print axioms` audit clean) — red *by design* on the pins step, which printed the paste-ready `elab_delta` with all 14 entries on `[propext, Classical.choice, Quot.sound]` |
| 7 | `8f6c656` | **GREEN** 4m13s | all steps pass — block merged verbatim (`added 14, changed 0, elab now 108`); the golden-statements diff was pure insertion, so every pre-existing `pins`/`elab` entry is byte-identical |

The oracle lane went green on every push including the first (`16/16` from
`a8cf4ac` onward); its runs are paired with the lean runs in row 9.

