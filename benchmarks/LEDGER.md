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
| — | *(brief issuance, no theorem)* BRIEF_010 issued: T6 at any strip law, and the contour correction C12 | arena-ai-coding-agent | [#12](https://github.com/sblaplace/improved_black_scholes/pull/12) | **GREEN** — no `.lean` file changed, no pin moved; graded on whether the docs lane stays green, and it did: `lint` green on every subsequent run through the implementation, most recently run 35646623031. The brief carried its own numeric route-check (ledger C4, incl. the 74.2% contour discrepancy that produced C12) and specified the two guards its implementation lands: oracle mutant M15 and the `[CONTOUR]` lint check — both landed with row 10. Its predecessor's row (row 9) is the reason this one is separate: "a brief whose proof is asserted but not checker-backed is RED", so the verdict here is about the documentation; the theorem's verdict is row 10. |
| 10 | BRIEF_010 (T6 at any strip law + contour correction C12 implemented) | arena-ai-coding-agent | [#16](https://github.com/sblaplace/improved_black_scholes/pull/16) | **GREEN** @ `2cb2833`, lean run 35646623031 (oracle lane run 35646622979) — `lake build` + `#print axioms` audit + **Statement pins (elab, all 139)** + the oracle↔Lean pointwise cross-verifier + `lint` (incl. `[CONTOUR]`) all pass; the build line is `✔ [8930/8932] Built ImprovedBS.Pricing`, and all 107 audited constants sit on `[propext, Classical.choice, Quot.sound]`, never `sorryAx` (the BRIEF_010 section adds 25 theorems; the section's six plain defs — `cmPriceKernel`, `contourCharFun`, `cmPriceIntegral`, `strikeTransform`, `dampedModelFreeCall`, `fourierCM` — are pins but not audit entries). Scope: new module `ImprovedBS/Pricing.lean`, 31 declarations (`cmPriceKernel`, `contourCharFun`, `cmPriceIntegral`, `strikeTransform`, `dampedModelFreeCall`, `fourierCM`, `cmPriceKernel_eq_shift`, `gbm_contourCharFun_eq`, `gbmCharFactor_pricing_continuous`, `gbmCharFactor_pricing_norm`, `cmPriceKernel_integrable`, `gbm_cmPriceKernel_integrable`, `cmDenom_factor`, `integral_Ioi_cexp_neg_mul_eq_inv`, `ofReal_exp_eq_cexp`, `norm_cexp_I_mul_ofReal`, `strikeTransform_eq`, `integrable_strikeTransform`, `dampedModelFreeCall_eq_dampedCallPrice`, `continuous_dampedModelFreeCall`, `integrable_dampedModelFreeCall_of_exp_moment`, `fourierDampedModelFreeCall_eq`, `fourierCM_eq_fourier`, `fourierCM_inversion`, `cmPriceIntegral_eq_damped_modelFreeCall`, `carrMadan_eq_modelFreeCall`, `cmPriceIntegrand_reflect`, `carrMadan_im_eq_zero`, `carrMadan_eq_re`, `carrMadan_re_eq_modelFreeCall`, `gbm_carrMadan_eq_bsCall`), all in `REQUIRED` + `PROTECTED`, statement pins 108 → 139 in both layers with the 108 pre-existing entries byte-identical, audit list extended by 25, `deferred: {}` untouched, T1–T5 and BRIEF_004–009 statements unchanged. The law is abstract: every analytic input (H-moment, H-tail, H-decay, contour continuity) is a premise — the CGMY exponent is nowhere assumed, and `gbm_carrMadan_eq_bsCall` discharges the premises at the lognormal law via `gaussianReal_exp_moment`/`exp_moments_of_exp_tail` (unpinned bridge helpers). `[CONTOUR]` lint check: `cmPriceKernel` must sit on `u − i(α+1)` and not `+ ↑α * I`, cheat killed by name (28 lint mutants, 5 controls). Oracle side: `carr_madan_by_law` (Carr–Madan evaluated at any law through its characteristic function), `test_carr_madan_free_law` (identity at 3 laws + contour-flip rejection) and mutants M15 (kernel moved to the wrong contour) / M16 (strike-transform exponent), killed by that test alone. Nine-run lean arc (seven red on elaboration/API shape at the tag, one red by design, one green) — the CI history below has the table; the distinctive shapes this round: kabstract rewrites the *first-found* instance on **both** sides of an `Eq` (a shared `↑(u*k)` factor inside `Complex.exp` consumed a `Complex.ofReal_mul` rewrite meant for the other side — spend a third rewrite deliberately), `integral_ofReal`'s RCLike-generic `↑` does not syntactically match a `Complex.ofReal` goal even when `ppDisplay` shows it matching (route through a concrete `have` typed in the goal's own coercion context), `neg_div` is `(-b)/a = -(b/a)` so the goal's `-(b/a)` needs `neg_mul`, and `Real.rpow_natCast` bridges the `|u| ^ 2` vs `|u| ^ (2:ℝ)` exponent spellings at the decay hypothesis. One batch-edit race (run 35644344321) of the same class row 9 hit. Authored without a toolchain. |
| 11 | BRIEF_011 (the CGMY exponent, its Levy measure, and the moment strip — BSM-2 kit items 1–2) | arena-ai-coding-agent | [#17](https://github.com/sblaplace/improved_black_scholes/pull/17) | **GREEN** @ `03be381`, lean run 35779316727 (oracle lane run 35779316766) — `lake build` + `#print axioms` audit (148 entries: the 107 previous plus the 41 new CGMY theorems, every one on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) + **Statement pins (elab, all 165)** + the oracle↔Lean pointwise cross-verifier + `lint` (incl. `[CGMY]`) all pass; the build line is `⚠ [8931/8933] Built ImprovedBS.CGMY`, i.e. the module elaborates with warnings only. Reached on the 5th run — the documentation commit that records it (`4971c45`, run 35780267323) re-grades green — and the arc is the informative part: two red on elaboration (20 errors, then 4 — all API shape at the tag, none of it mathematics), one red by design on the empty `elab` block, one green with the block merged (`added 26, changed 0, elab now 165`). Two of those repairs are worth naming: `HasDerivAt.cpow_const` at this tag is a ℂ → ℂ lemma, so the mean-value step differentiates on ℂ at `↑t` and restricts with `HasDerivAt.comp_ofReal`; and the right base's continuity genuinely needs `G > 0` **and** `α > 0` (correction C15), because its imaginary part is `u`, which vanishes at `u = 0` — the branch condition then has to be carried by the real part. That is the one landed statement that moved during the brief (`cgmy_contour_continuous` gained two hypotheses; 164 pins byte-identical, the diff in `tests/golden_statements.json`), and it is C14 in a new place: `G`'s positivity enters the pricing line's continuity, but still no `min (G, M)`. Scope: new module `ImprovedBS/CGMY.lean`, 52 declarations (11 plain defs — `cgmyExponent`, `cgmyCharFactor`, `cgmyContour`, `cgmyOldContour`, `cgmyBaseLeft`, `cgmyBaseRight`, `cgmyTemperedRate`, `cgmyTemperedConstant`, `cgmyTemperedCorrection`, `cgmyDecayThreshold`, `cgmyLevyDensity` — plus 41 theorems), all in `REQUIRED` + `PROTECTED`, statement pins 139 → 165 (26 new: 8 defs + 18 theorems; the 139 pre-existing entries byte-identical, `deferred: {}` untouched, no T1–T5 or BRIEF_004–010 statement moved), audit list 107 → 148 (+41 `#print axioms` entries). `[CGMY]` lint check: `cgmyExponent` must carry `Γ(-Y)` and both tempered bases, `cgmy_cmPriceKernel_integrable` must CONSUME `cmPriceKernel_integrable` at the explicit `cgmyDecayThreshold` instead of re-deriving kernel integrability, all four headline statements must carry the corrected condition `α + 1 < M` and must not contain a `min` over `G`/`M`, and the C14 witness `cgmyOldContour_base_right_re` must state `G − α` (29 lint mutants, 5 controls). Oracle side: the compensated one-sided Levy integral (series-corrected `expm1` helpers — no mass cancellation, no `exp` overflow) and `cgmy_exponent_by_pieces`; locally `test_bs.py` 18/18 (incl. `test_cgmy_contour`), `test_lint.py` 7/7, `test_mutants.py` 4/4, `test_crosscheck.py` 6/6, `test_pins.py` 12/12, `lean_lint.py` OK (10 files, 214 declarations). Correction C14 is this row's: the pricing line `v = u − i(α+1)` needs `α + 1 < M` alone — `G` constrains only the old line `u + iα`, where `Re(G + iv) = G − α` goes negative once `α ≥ G`; the `min (G, M)` spelling in `docs/03` §D1 and `docs/04`'s queue swapped which rate tempers which half. The acceptance item `docs/04` states — continuity and decay on the contour, discharging BRIEF_010 §5's (H-decay) at the concrete exponent so item 4 lands without re-proof — is `cgmy_contour_continuous`/`cgmy_charFactor_contour_continuous` + `cgmy_contour_decay` + `cgmy_cmPriceKernel_integrable`. Labelled NOT machine-checked in the module header: the Levy–Khintchine representation itself (that the compensated integral of `ν` equals the closed-form `ψ`; mathlib v4.34.0 has no Levy–Khintchine theorem) and the Taylor step from `∫ (1 ∧ x²) ν < ∞` to the compensated integrand — both route-checked numerically. Authored without a toolchain. |
| — | *(brief issuance, no theorem)* BRIEF_012 issued: the machine-checked non-uniqueness witness (BSM-2 kit item 7, C13) | arena-ai-coding-agent | [#18](https://github.com/sblaplace/improved_black_scholes/pull/18) | **GREEN** @ `a3d3939`, lean run 36035539204 (oracle lane run 36035539099) — `lake build` + the `#print axioms` audit on all 148 entries + statement pins (all 165) + `lint` + `oracle` all pass. No `.lean` file changed, no pin moved, `deferred: {}` untouched; as with the BRIEF_010 issuance row above, this verdict is about the **documentation**, not a theorem — nothing in `ImprovedBS/NonUniqueness.lean` exists yet, so no claim in the brief is machine-checked, and the theorem's verdict gets its own row when the implementation is graded. The brief carries its own numeric route-check (ledger C4) run through the repository's existing `model_free_prices`/`model_free_forward` with **no new oracle code** — both witnesses' drifts, parity gaps and bound pairs at exact dyadic values, a drift canary `p = (1/4, 5/8, 3/8)` whose parity gap moves to `0.25` (which is what makes the drift hypothesis load-bearing), and a 17-point sweep of the martingale segment `p₃ = p₁/2`, `p₂ = 1 − 3p₁/2` with 0 violations and call prices exactly `p₁/2` over all of `[0, 1/3]` — so the brief asks for `martingale_set_call_eq` as a theorem rather than leaving the range a measurement. It also specifies the guards its implementation must land: the `[NONUNIQ]` lint check with three clauses and oracle mutants M17/M18. **Unmitigated risk recorded in the brief:** the issuing sandbox had no Lean toolchain *and* no network (`curl` to both `leanprover-community.github.io` and `raw.githubusercontent.com` fails at the TLS layer), so ledger C3's "verify every mathlib name at the pinned tag" step could not run; the names §1–§2 relies on are long-standing and low-risk, and the fallback is written down. Same PR repairs README staleness BRIEF_011 left behind, every figure measured against live harness output: the theorem-stack table was missing **both** the BRIEF_010 and BRIEF_011 rows, the status table was missing BRIEF_011's, and the live counts were `17/17` (now `18/18`), `28` lint cheats (now `29`), `139` pins (now `165`, matching `pin_statements.py --check`), `15` mutants (now `17`), `14/14` (now `18/18`), `25` cheats (now `29`), "All three"/"four harnesses" (now five) and `CGMY.lean` absent from the layout. Per-brief historical counts (`49 → 60`, `108 → 139`, run ids) deliberately untouched: records, not live claims. |
| 12 | BRIEF_012 (the machine-checked non-uniqueness witness — BSM-2 kit item 7, C13) | arena-ai-coding-agent | [#19](https://github.com/sblaplace/improved_black_scholes/pull/19) | **GREEN** @ `a61be00`, lean run 36052072620 (oracle lane run 36052072567) — `lake build` + `#print axioms` audit (186 entries: the 148 previous plus the 38 new theorems, every one on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) + **Statement pins (elab, all 210)** + the oracle↔Lean pointwise cross-verifier + `lint` (incl. `[NONUNIQ]`) all pass; the build line is `✔ [8930/8934] Built ImprovedBS.NonUniqueness (5.0s)` — the module elaborates with **no** warnings. Reached on the 3rd lean run, and the arc is short because the numbers were fixed before the Lean: one red on two `linarith` calls (an atom split by `cancelDenoms`, see the CI history — not mathematics), one red by design on the empty `elab` block, one green with the block merged (`added 45, changed 0, elab now 210`). **What is now a theorem:** `static_skeleton_does_not_select_measure` — two probability laws `witnessMeasureA ≠ witnessMeasureB` on the spots `(1/2, 1, 2)`, mutually absolutely continuous (`witness_equivalent`), both with `∫ id = S e^{(r−q)τ}` at `S = K = τ = 1`, `r = q = 0`, both satisfying BRIEF_009's `model_free_put_call_parity` and `model_free_call_bounds` *by instantiation*, and `modelFreeCall A = 1/4 ≠ 1/8 = modelFreeCall B`; an 11-clause conjunction, each clause one of the named theorems. Plus the sharp form: the martingale set on those atoms is the segment `(p₁, 1 − 3p₁/2, p₁/2)`, `p₁ ∈ [0, 2/3]` (`martingale_set_param`, `martingale_set_eq_segment`, `martingale_set_mem`) and **the call on it is exactly `p₁/2`** (`martingale_set_call_eq`), so every price in `[0, 1/3]` is a martingale price (`martingale_set_price_range`) while the skeleton's bounds say `0 ≤ call ≤ 1`. This is C13's finding 2 made machine-checked: the static layer does not select the measure, the dynamic half of the thesis needs a *named* selection principle (item 3), and the README's dynamic/static split is no longer prose. Scope: new module `ImprovedBS/NonUniqueness.lean`, 45 declarations (7 defs — `trinomialMeasure`, `witnessSpotLo/Mid/Hi`, `witnessMeasureA/B`, `martingaleSegment` — plus 38 theorems), all in `REQUIRED` + `PROTECTED`, statement pins 165 → 210 (the 165 pre-existing entries byte-identical, `deferred: {}` untouched, no landed statement moved), audit list 148 → 186. `[NONUNIQ]` lint check: `witnessA/B_parity` and `witnessA/B_bounds` must **cite** `model_free_put_call_parity`/`model_free_call_bounds` and may not mention `max_sub_swap_eq`; the headline must carry every clause (both probability facts, `A ≠ B`, `A ≪ B`, `B ≪ A`, both drifts, both parities, both bound pairs, the price `≠`); `trinomialMeasure` must be exactly three `Measure.dirac` atoms, one per weight. Its three cheats in `tests/test_lint.py` — N1 collapsed Dirac, N2 parity re-derived from `max_sub_swap_eq`, N3 headline without the price `≠` — are each killed by `[NONUNIQ]` and by nothing else (N1/N3 regenerate the source pins first, as an author without a toolchain would); 32 lint mutants, 5 controls. Oracle side: **no new oracle function** (the brief's rule) — the witness laws are `Fraction` *data* in `experiments/black_scholes.py`, priced by the existing `model_free_prices`/`model_free_forward`; `test_nonuniqueness_witness` asserts the whole route-check table in exact arithmetic (both drifts, both prices bit-exact, both parity gaps, both bound pairs, `call(A) ≠ call(B)`, the 17-point sweep of the segment with call `= p₁/2` at every point and range exactly `[0, 1/3]`, two drift canaries); mutants M17 (B's `p₃ : 1/8 → 3/8`), M18 (call payoff → linear payoff `s − K`, so `call(A) = call(B) = 0` with no probability touched) and M19 (B := A, the oracle twin of N1) are killed by it — M17/M19 by it alone, M18 also by the two other tests that price against the same payoff line. Locally `test_bs.py` 19/19, `test_mutants.py` 4/4 (20 mutants), `test_lint.py` 7/7, `test_pins.py` 12/12, `test_crosscheck.py` 6/6, `lean_lint.py` OK (11 files, 259 declarations). Correction C16 is this row's: two numerical slips in the brief's own route-check table, found by implementing it — the drift canary `(1/4, 5/8, 3/8)` has mass `5/4` and mean `3/2`, not `1.25`, and the plain gap identity does *not* hold at it (only the mass-weighted form does); and the brief's literal M18 (call priced with the put payoff) is **blind at this witness**, since at `K = F` with `r = 0` call and put coincide at both laws. Authored without a toolchain; every mathlib name read at the v4.34.0 source before pushing, and the module compiled with no name or shape error on its first build — the only red was tactic behaviour. |
| — | *(brief issuance, no theorem)* BRIEF_013 issued: the Esscher drift — BSM-2 kit item 3, the named pricing measure at CGMY | arena-ai-coding-agent | [#20](https://github.com/sblaplace/improved_black_scholes/pull/20) | **GREEN** — lean run 36056829975 (oracle lane 36056829795): `lake build` + the `#print axioms` audit on all 186 entries + statement pins (all 210) + `lint` + `oracle` all pass on the documentation diff. No `.lean` file changed, no pin moved, `deferred: {}` untouched; as with the BRIEF_010 and BRIEF_012 issuance rows above, this verdict is about the **documentation**, not a theorem — nothing in `ImprovedBS/Esscher.lean` exists yet, and the theorem's verdict gets its own row when the implementation is graded. The brief carries its own numeric route-check (ledger C4) run through the repository's existing CGMY oracle primitives: the family-closure identity on 3780 points (worst resid `1.1e-13`), the curvature closed form `κ'' = CΓ(2−Y)[(M−u)^{Y−2} + (G+u)^{Y−2}]` with O(h²) convergence and all 540 samples positive, strict monotonicity of the Esscher map over 43200 increments, existence-and-uniqueness at 427 in-range targets (worst residual `1.3e-13`) with 5 out-of-range targets correctly rejected, the antisymmetry/zero-drift exact anchors (`θ₀ = (M−G−1)/2`, worst `9e-14`), the symmetric range closed form `H = |CΓ(−Y)|·|(G+M)^Y − (G+M−1)^Y − 1|` (worst resid `4.4e-14`), the tilted decay on the shifted contour (880 probes, 0 violations), and three mutation canaries measured at O(1). It specifies the guards its implementation must land: the `[ESSCHER]` lint check with four clauses (E1 the hollowed shift, E2 the re-derived integrability, E3 the dropped `1 < G + M`) and oracle mutants M20/M21. **Numbering recorded in the brief:** C13's provisional "BRIEF_013 = Pareto witness / BRIEF_014 = Haug anchor" assignment is superseded — the kit ordering (item 7 → item 3) takes the numbers, and the two C13 repair briefs stay queued after the kit items, numbered at issue. Issued with the mathlib name check run at the tag (ledger C3) — the mitigation BRIEF_012's issue could not run. |
| 13 | BRIEF_013 (the Esscher drift at CGMY — BSM-2 kit item 3, the named pricing measure) | arena-ai-coding-agent | [#20](https://github.com/sblaplace/improved_black_scholes/pull/20) | **GREEN** @ `8147206`, lean run 36072416203 (oracle lane run 36072416317) — `lake build` + `#print axioms` audit (211 entries: the 186 previous plus the 25 new theorems, every one on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) + **Statement pins (source and elab, all 240)** + the oracle↔Lean pointwise cross-verifier + `lint` (incl. `[ESSCHER]`) all pass; the build line is `⚠ [8933/8935] Built ImprovedBS.Esscher (5.7s)` — three warnings, none mathematical: the two unused-variable notes are the brief's own `hY₂`/`hG` signature arguments that the Γ-rewrite and no-solution proofs carry for shape rather than use. Reached on the 8th lean run after seven red, and every red was elaboration/API shape at the v4.34.0 tag, never mathematics: (1) 26 errors — `Real.hasDerivAt_rpow_const` takes its base and exponent **implicitly** (`{x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p)`), so explicit base arguments landed in the disjunction slot, plus `𝓝` needing `open scoped Topology`, `intermediate_value_Ioo` taking `a ≤ b`, `convex_Ioo`/`convex_Icc` taking explicit endpoints, and the Γ normal form `Γ(−Y)·Y·(Y−1) = Γ(2−Y)` needing its rewrites aimed at the goal because the context holds `−Y + 1` where the lemma wants `1 − Y`; (2–6) 15 → 8 → 9 → 5 errors — `strictMonoOn_of_deriv_pos`'s derivative hypothesis is `∀ x ∈ interior D` (rewrite `isOpen_Ioo.interior_eq` in the *right* case), `HasDerivAt.congr_of_eventuallyEq` binds self to the **right** side of `=ᶠ`, the ∃! packs as `⟨θ, ⟨hθI, hθ⟩, ?_⟩`, the unfolded rpow arguments appear as `M − (φ + 1)` rather than `M − φ − 1`, and the inner `HasDerivAt`s must not eta-contract (`HSub.hSub M`, `(fun _ ↦ M) − id` are not defeq to the written lambdas at `convert`'s transparency — pinned via `congr_of_eventuallyEq` pointwise); (7) **build GREEN**, elab-pins step red by design on the 30 missing pairs, block printed paste-ready; (8) green with the block merged verbatim (`added 30, changed 0, elab now 240`). The one recurring lesson: `Function.comp` is opaque to `convert`, so every `HasDerivAt.comp` leaves a function-equality goal that `ext; simp [Function.comp_apply]` closes. **What is now a theorem:** the Esscher shift keeps CGMY inside the family — `esscher_cgmy_shift` (`ψ^θ` at `(G+θ, M−θ)`) and `esscher_tilt_factorization` (`φ^θ(v) = φ_{G+θ, M−θ}(v)·φ_{G,M}(−iθ)`); the cumulant `κ` is strictly convex on the strip (`cgmyCumulant_eq_strip`, the second derivative `CΓ(2−Y)[(M−u)^{Y−2} + (G+u)^{Y−2}]` via `cgmyGamma_two_sub_eq`, positivity, strict monotonicity of `κ′`); so the drift map `θ ↦ κ(θ+1) − κ(θ)` is strictly increasing on `[−G, M−1]` (`esscherDriftMap_strictMono`), its edge values give the closed-form bound `H = |CΓ(−Y)|·|(G+M)^Y − (G+M−1)^Y − 1|`, and the drift equation solves uniquely in `(−G, M−1)` exactly below `H` (`esscher_exists_unique_of_mem_range`), never at or above it (`esscher_no_solution_of_outside_range`), with the zero at the exact `θ₀ = (M−G−1)/2` (`esscher_theta_zero_unique`); at the solution the tilted factor is the numeraire drift, `φ_{G+θ, M−θ}(−i) = e^{τ(r−q)}` (`esscher_drift_factor`, via `esscherExponent_neg_I_eq`), the tilted numeraire condition `1 < M − θ` holds on the whole strip (`esscher_tilted_numeraire`), the tempering correction is shift-invariant (`esscher_correction_invariant`), and pricing at the tilted rates stays on the original contour's integrability (`esscher_cmPriceKernel_integrable` consuming `cgmy_cmPriceKernel_integrable`). Scope: new module `ImprovedBS/Esscher.lean`, 30 declarations (5 defs — `esscherExponent`, `cgmyCumulant`, `esscherDriftMap`, `esscherThetaZero`, `esscherDriftBound` — plus 25 theorems), all in `REQUIRED` + `PROTECTED`, statement pins 210 → 240 source with the 210 pre-existing entries byte-identical and `deferred: {}` untouched, elab 210 → 240, audit list 186 → 211. **Re-scope as briefed:** item 3 lands at the characteristic-factor level — the tree has no CGMY law as a measure, so the expectation-level twin of `integral_spot_mul_phi_eq_forward` stays gated on a law construction. `[ESSCHER]` lint check, four clauses: the shift must be defined for a general `ψ` (E1 hollows it to CGMY-only), pricing at the tilted rates must **cite** `cgmy_cmPriceKernel_integrable` rather than re-derive integrability (E2), the headline must carry `1 < G + M` (E3 drops it), and the bound must be the edge-value closed form. Its three cheats in `tests/test_lint.py` are each killed by `[ESSCHER]` and by nothing else; 35 lint mutants, 5 controls. Oracle side: six new functions (`esscher_exponent`, `cgmy_cumulant`, `esscher_drift_map`, `esscher_theta_zero`, `esscher_drift_bound`, `esscher_solve`) and `test_esscher_drift` on four witness sets (θ\* to 1e-6, residuals ≤ 1e-12, the closure identity to 1e-10, antisymmetry to 1e-11, two out-of-range canaries); mutants M20 (shift sign flipped — the closure breaks at O(1)) and M21 (inner abs dropped from `H` — `H < 0` on the `Y < 1` sets) are killed by it. Locally `test_bs.py` 20/20, `test_mutants.py` 22/22, `test_lint.py` 7/7, `lean_lint.py` OK (12 files, 291 declarations). |

| 14 | BRIEF_014 (the normalized CGMY → GBM corner — BSM-2 kit item 6) | arena-ai-coding-agent | [#22](https://github.com/sblaplace/improved_black_scholes/pull/22) | **GREEN** @ `b0cb26a`, lean run 36111570530 (oracle lane 36111570572) — `lake build` + `#print axioms` audit (226 entries: the 211 previous plus the 15 new theorems, every one on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) + **Statement pins (source and elab, all 257)** + the oracle↔Lean pointwise cross-verifier + `lint` (incl. `[CORNER]`) all pass; the build line is `✔ [8934/8936] Built ImprovedBS.Corner (3.8s)`. Reached on the 4th lean run — one red on seven elaboration errors, two red by design on the empty `elab` block, one green with the block merged verbatim (`added 17, changed 0, elab now 257`) — see the CI history below. **What is now a theorem, all of it one-sided (`𝓝[<] 2`) and none of it an equality at the pole:** at the scale `C_Y = (σ²/2)(2−Y)` the Γ pole cancels — `cgmyCornerGamma_eq`, `ε Γ(−Y) = Γ(3−Y)/(Y(Y−1))` on `1 < Y < 2`, citing BRIEF_013's `cgmyGamma_two_sub_eq` — so `C_Y Γ(−Y) → σ²/4` (`cgmyCornerGamma_tendsto`) and the bracket tends to `B₂(v) = −2v² + 2i(G−M)v` at every fixed `v` in `−M < Im v < G` (`cgmyBracket_tendsto`, `Filter.Tendsto.const_cpow` at four nonzero bases), giving the uncorrected corner `ψ_Y(v) → −(σ²/2)v² + i(σ²/2)(G−M)v` (`cgmyCornerExponent_tendsto`); route A's algebraic normalization `Ψ_Y(v) = ψ_Y(v) + i(r−q−κ_Y(1))v` has `Ψ_Y(−i) = r − q` **exact at every `Y`** (`cornerForward_numeraire`, consuming `cgmyExponent_strip`, with `cornerForwardFactor_numeraire` at factor level), converges to the risk-neutral GBM exponent (`cornerForwardExponent_tendsto`) and its factor converges to BRIEF_005's own `gbmCharFactor ((r−q−σ²/2)τ) ((σ²/2)τ) v` (`cornerForwardFactor_tendsto`); route B needs no correction at all — `θ₀ = (M−G−1)/2` lies in `(−G, M−1)` when `1 < G + M` (`cornerEsscherZero_mem`), solves the Esscher equation at every `Y` (`cornerEsscherZero_numeraire` citing `esscher_drift_factor`/`esscherDriftMap_zero`, `cornerEsscherZero_exponent` via `esscherExponent_neg_I_eq`), and the tilt *is* the same exponent at the shifted rates `G′ = (G+M−1)/2`, `M′ = (G+M+1)/2` (`cornerEsscherZero_tendsto` consuming `esscher_cgmy_shift`, strip hypotheses carried at the **shifted** rates), landing on the zero-carry GBM exponent `−(σ²/2)v² − i(σ²/2)v`; and the attainable drift half-width collapses to `(σ²/2)(G+M−1)` (`cornerEsscherBound_tendsto`, from the landed `esscherDriftBound` body). Scope: new module `ImprovedBS/Corner.lean` (556 lines), 17 declarations (2 defs — `cgmyCornerC`, `cornerForwardExponent` — plus 15 theorems), all in `REQUIRED` + `PROTECTED`; statement pins 240 → 257 source with the 240 pre-existing entries byte-identical, elab 240 → 257, audit list 211 → 226. One deliberate deviation from the brief's hypothesis list: `cgmyBracket_tendsto` is stated with `0 < M`, not `M > 1` — the bracket limit needs only a nonzero base, and `1 < M` is what the numéraire `u = 1` costs (`cgmyCornerCumulant_one_tendsto`, `cornerForward_numeraire`), so the theorem is proved where it is true rather than where the section's standing assumptions would have put it. **Re-scope as briefed:** the corner lands at the characteristic-factor level — no CGMY probability measure, no Lévy–Khintchine, no convergence of option prices, and no interchange of the `Y`-limit with the Carr–Madan integral (pointwise convergence at each `v` is not a uniform dominating bound on the contour). `[CORNER]` lint check, five clauses: the scale must carry `σ²/2` and `2 − Y` and the file must never mention `Real.Gamma (-2)` (whole-file), the Γ identity must cite `cgmyGamma_two_sub_eq` + `Real.Gamma_add_one`, the forward-exponent body must be built from `cgmyExponent`/`cgmyCumulant` and never `gbmCharFactor`, the factor target must be `gbmCharFactor` and route B must consume `esscher_cgmy_shift`/`esscher_drift_factor`, and every limit statement must carry `𝓝[<] 2` with its (shifted) strip hypotheses. Its five cheats in `tests/test_lint.py` (G1–G5) are each killed by `[CORNER]` and by nothing else; 40 lint mutants, 5 controls. Oracle side: two new primitives (`corner_scale`, `corner_forward_exponent`) and `test_gbm_corner` — the pre-brief route-check promoted out of `scripts/check_gbm_corner.py` and deleted there, so the model side sits in the oracle and the independently expanded GBM target stays in the test; mutants M22 (scale doubled: the limit still exists and is still finite, it is just twice the variance) and M23 (drift correction dropped: `G − M` survives the limit at O(σ²)) are killed by it. Locally `test_bs.py` 21/21, `test_mutants.py` 4/4 (24 mutants), `test_lint.py` 7/7, `test_pins.py` 12/12, `test_crosscheck.py` 6/6, `lean_lint.py` OK (13 files, 310 declarations). Correction C17, recorded at issuance, is what this row implements. |
| — | *(brief issuance, no theorem)* BRIEF_015 issued: the Pareto witness for `Levy.lean`'s tail hypothesis (C13 finding 3, the first queued repair brief) | arena-ai-coding-agent | [#23](https://github.com/sblaplace/improved_black_scholes/pull/23) | **GREEN** — lean run 36118090090 on the documentation commit; documentation only: no `.lean` file, pin, lint rule, oracle function or test changed. Findings at issue: **F1** mathlib already ships `ProbabilityTheory.paretoMeasure` at rev `5ed2965` (read via the GitHub API), so C13's hand-rolled `withDensity` law is superseded and the only new analysis is the tail `μ[x,∞) = t^r·x^(−r)`; **F2** that tail meets `htail` *with equality* at `c = t^r, α = r, x₀ = t`, so together with C7 the headline is `levy_tail_hypothesis_satisfiable_iff : (∃ law, htail) ↔ 0 < α`, and C7's prose becomes a theorem; **F3** an `r = 3` instance puts C7 correction 1 on record. Route-check (scratch quadrature, 12 laws): normalization worst `3.6e-9`, tail closed form worst rel `5.7e-8` on 96 points, `htail` margin `2.2e-16` (equality), exponential and Gaussian canaries fail `htail` with finite `E[e^X]`, and one **weak mutant** found (`c = t^(−r)` still satisfies the inequality at `t > 1`), which is why the oracle test must assert the tail with equality. Specifies `[PARETO]` (4 clauses, lint mutants 40 → 44), oracle M24/M25, pins 257 → 268, audit 226 → 237. |
| 15 | BRIEF_015 (the Pareto witness for `Levy.lean`'s tail hypothesis — C13 finding 3) | arena-ai-coding-agent | [#23](https://github.com/sblaplace/improved_black_scholes/pull/23) | **GREEN** @ `df470d1`, lean run 36119639468 (oracle lane 36119639528) — `lake build` + `#print axioms` audit (237 entries: the 226 previous plus the 11 new theorems, every one on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) + statement pins (source 268, elab 268; the 257 pre-existing entries byte-identical, `added 11, changed 0`) + `lint` (incl. `[PARETO]`, 44 mutants / 5 controls) + `oracle` (incl. `test_pareto_witness`, M24/M25 killed by it). `ImprovedBS/ParetoWitness.lean`: the Pareto tail `paretoMeasure t r (Ici x) = ofReal (t^r · x^(−r))` for mathlib's own law (F1), `htail` discharged with equality, `exp_moment_infinite_of_tail_lower_bound` / `no_drift_makes_spot_integrable` instantiated by citation (incl. `r = 3`, F3), C7's `α ≤ 0` remark proved (`levy_tail_hypothesis_unsatisfiable_of_nonpos`, via `tendsto_cdf_atTop`), the headline `levy_tail_hypothesis_satisfiable_iff : (∃ law, htail) ↔ 0 < α`, and the Dirac discriminator. Green on the 3rd lean run; see the CI history. |

| — | *(brief issuance, no theorem)* BRIEF_016 issued: the external anchor (the published Carr–Madan 1999 test case) and the term-structure falsifier (C13 finding 4, the second and last queued repair brief) | arena-ai-coding-agent | [#24](https://github.com/sblaplace/improved_black_scholes/pull/24) | **GREEN** — lean run [36122383398](https://github.com/sblaplace/improved_black_scholes/actions/runs/36122383398) (oracle lane run [36122383329](https://github.com/sblaplace/improved_black_scholes/actions/runs/36122383329)): `lake build` (no `.lean` diff, mathlib cache) + lint + oracle all pass on the documentation commits `ac56aa4` → `b255836`. Documentation only: no `.lean` file, pin, lint rule, audit entry or workflow changed. **Findings at issue:** **F1** the anchor is public and is this repository's own method (Carr & Madan 1999 §5, Table 1, Case 4: `σ = .25, ν = 2.0, θ = −.10, τ = .25`, `S = 100`, `r = .05`, `q = .03`); **F2** the published three-strike row is the **put** price (the call at `K = 77` is `≈23.84`), and the paper prints its own **wrong** VGPS row at the same strikes — a free negative control; **F3** the Case-4 parameters are exactly CGMY at `Y = 0` (`C = 1/ν`, `s = √(θ² + 2σ²/ν)`, `G, M = (s ± θ)/σ²` ⇒ `C = .5`, `G = 2.708…`, `M = 5.908…`, `1 < M`), where `Γ(−Y)` has a pole so the corner exponent must be written explicitly; **F4** C13's parenthetical decay `τ^(−1/2)` is wrong — the cited exponential-Lévy large-time rate is `O(τ^(−1))` (Figueroa-López–Forde–Jacquier), the measurement agrees, and correcting it *widens* the RED; **F5** the market side is a published exponent table with a regime change (El Amrani–Guyon: `α = 0.43/0.44/0.45` for SPX/SX5E/DAX above three weeks; `0.19/0.04/0.08` below; Gatheral–Jaisson–Rosenbaum `α ∈ (0.3, 0.5)`, SPX fit `τ^(−0.44)`). **Route-check** (Python stdlib only, the router's own `carr_madan_denom` at `α = 1.5`, `u_max = 2000`, `n = 80000`): puts `0.635631 / 0.678705 / 0.724436` vs published `.6356 / .6787 / .7244` (`|diff|` `3.1e−5 / 4.9e−6 / 3.6e−5`); the wrong VGPS row rejected by `0.3929 / 0.4488 / 0.8140`; VG → GBM as `ν ↓ 0` at `err/ν → 2.31`; ATM skew `−1.33362, −0.68164, −0.32191, −0.14639, −0.05267` (VG Case 4) and `−0.17869, −0.09335, −0.04797, −0.02437, −0.00985` (CGMY `1,5,10,.7`) at `τ = .25…5`, giving the pre-registered bands `[0.90, 1.15]` (model) vs `(0.30, 0.50)` (market) — **disjoint**, the RED. Specifies the oracle primitives, `test_term_structure_anchor`, mutants M26–M29, tests 22 → 23 and mutants 26 → 30, with pins/audit/lint **unchanged** at 268/237/44. **One transcription caveat on record:** the three literals were read from a PDF text extraction with mangled leading characters, so the implementer must verify them against the paper's rendering before pinning; the identification itself is established (the computed puts match to four decimals and fail the VGPS row). |

| — | *(brief issuance, no theorem)* BRIEF_017 issued: the CGMY-law feasibility brief (the audit, the route call, and the first law brief's specification) | arena-ai-coding-agent | [#24](https://github.com/sblaplace/improved_black_scholes/pull/24) | **GREEN** — lean run [36123266057](https://github.com/sblaplace/improved_black_scholes/actions/runs/36123266057) (oracle lane run [36123266059](https://github.com/sblaplace/improved_black_scholes/actions/runs/36123266059)) on the issuance commit `4111b67`. Documentation only (an issuance row for a feasibility brief, not a new row for a theorem; the implementation gets its own row). **Findings at issue:** mathlib at `5ed2965` ships **no** Lévy–Khintchine, infinitely-divisible, stable-law, subordinator or Bochner machinery (only the convergence files), so a CGMY law must be **built**; what it does ship is four usable layers — the Gamma law (`gammaMeasure`), the Γ-integral identities (`integral_rpow_mul_exp_neg_mul_Ioi`, `Real.Gamma_add_one`), the mgf layer (`mgf`, `cgf`, `iteratedDeriv_mgf`, `complexMGF` = charFun on the imaginary axis) and the convergence layer (`charFun_conv`, `Measure.ext_of_charFun`, `isTightMeasureSet_of_tendsto_charFun`, `ProbabilityMeasure.tendsto_of_tendsto_charFun`, Prokhorov's `isCompact_closure_of_isTightMeasureSet`, `MeasureTheory.mconv`). **Route call, decided in the brief:** Stage 1 = the family's `Y ↓ 0` corner, i.e. the **variance-gamma law** = difference of two independent Gamma laws (`(M/(M−u))^{Cτ}(G/(G+u))^{Cτ}` on the landed strip `(−G, M)`; the Γ pole cancels through `Real.Gamma_add_one` alone: `Γ(−Y)·Y = −Γ(1−Y) → −1`; and it is the *published* law of BRIEF_016's anchor under its F3 map) — the first CGMY-family measure, landing the expectation-level twins of items 3 and 5 at a non-Gaussian law; Stage 2 = the general-`Y` law by the compound-Poisson truncation limit (specified, four named sub-goals, queued behind Stage 1; item 6's expectation-level twin waits on it). Traps named: `Real.Gamma 0 = 0`/`Gamma (−1) = 0` make a raw `Y = 0`/`Y = 1` evaluation *silently* the Dirac law (canary: the deterministic price `0.49502543252569353`), and `H_Y ~ C/Y → ∞` degenerates the landed in-range/out-of-range split at the corner. Route-check (stdlib only, through the router's oracle): corner `|ψ_Y − ψ₀|/Y` → finite constants (O(Y)); law mgf vs the **published** VG CF at Carr–Madan Case 4 worst relative gap `3.4e−15`; the Γ mgf identity by quadrature worst `1.1e−13` over 11 cases including `Cτ = .125`; θ₀ zeroes the `Y = 0` drift to `5.6e−17`; the tilt map's mgf identity `2.2e−16`; `H_Y` `100.5/1000.5/10000.5` at `Y = 10⁻²/10⁻³/10⁻⁴`. Specifies the Stage-1 implementation: `ImprovedBS/VGLaw.lean` (~16 declarations), a `[VGLaw]` lint check with four clauses (limit-not-evaluation at `Y = 0`; `gammaMeasure`-built with no hand-rolled density; the Γ integral consumed, not re-derived; the numéraire in the tilt), oracle `test_vg_law`, mutants M30–M33 (assuming BRIEF_016's M26–M29 land first), lint mutants 44 → 48, pins/audit by the landed count. |

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
   the range in which the hypothesis says anything. *(Now a theorem:
   `levy_tail_hypothesis_unsatisfiable_of_nonpos`, BRIEF_015, row 15.)* Recorded in the module
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

## CI history for row 10 (PR #16)

Nine lean runs. As in rows 5, 6, 7 and 9, every red was elaboration or API
shape at the v4.34.0 tag — the mathematics was pinned by the numeric
route-check before any Lean was written (C4/C12). The workflow's per-error
context blocks (added mid-arc, commit `173c2b7`) are what made toolchain-free
iteration convergent; rounds 5–8 each had three or fewer errors left, all
decoded from the PR comment.

| # | head | `lake build` | cause |
|---|---|---|---|
| 1 | `7b2653e` | fail | ~52 errors: placeholder `rfl` proofs replaced wholesale; §1 (kernel + `contourCharFun`) already green |
| 2 | `d1dc8d1` | fail | ~50 new-class errors: binder `(hS : 0 ≤ S)` has no `.le`; `α + 2 ≢ α + 1 + 1` at a `δ := 1` call; no `IntegrableOn.const_mul` at the tag; `Real.fourierInv_eq'` unreachable by `rw` (route via `fourierInv_eq_fourier_neg` + `fourier_real_eq_integral_exp_smul`); calc reassociation through `/` |
| 3 | `173c2b7` | fail 35636025244 | ~52 errors, now with per-error goal context published to the PR (workflow change in the same commit); redex-shape rewrites dominate |
| 4 | `6244e5d` | fail 35640860665 | 18 errors left: `strikeTransform_eq` rebuilt as a top-level calc; mvar-headed `rw [lemma _ arg]`; un-pinned `integral_ofReal`; the fourierCM ↔ `fourierDampedModelFreeCall_eq` mul-order bridge (`hfcAll`); `S * 1` and `-(δ*k)` spellings |
| 5 | `d4c61f0` | fail 35642912616 | 3 errors: kabstract rewrites *all* occurrences of the first-found instance (`conv_lhs => rw` for one-sided); `field_simp` stalls on a folded shifted denominator (manual `inv_eq_one_div`/`div_sub_div`); a payoff-domination bound that was *false* for `x < 0` had survived two rounds (re-dominated via `Integrable.const_mul`); `integral_ofReal` needs every implicit pinned |
| 6 | `9f419f5` | fail 35644344321 | 3 errors: `rw [integral_ofReal]` cannot match the goal — the lemma's RCLike-generic `↑` and the goal's `Complex.ofReal` differ syntactically while `ppDisplay` shows them identical; routed through a concrete `have hkey` typed in the goal's own coercion context. *Also* a same-file batch-edit race (last writer wins) silently dropped two of three edits — the class row 9's run 2 hit |
| 7 | `aa1d191` | fail 35645277965 | 1 error: the reordered `unfold` + `Complex.ofReal_mul` ran while the RHS's own `C` factor still held `↑(u*k)` — kabstract's first-found instance split *that* (on both sides of the `Eq`), burning a rewrite and leaving the inner `↑(exp(-r·τ) * ∫ …)` unsplit |
| 8 | `3bb3645` | **build GREEN**, red by design 35645939103 | restore the original order and spend three `Complex.ofReal_mul` rewrites; build closes (`Build completed successfully (8932 jobs)`), audit clean, and the pins step prints the paste-ready `elab_delta` with all 31 entries — `neg_div` (its pattern is `(-b)/a`, the goal's is `-(b/a)` → `neg_mul`) and the `|u| ^ 2` vs `|u| ^ (2:ℝ)` decay exponent (`Real.rpow_natCast` at the use site) fixed in the same round |
| 9 | `2cb2833` | **GREEN** 35646623031 | block merged (`added 31, changed 0, elab now 139`); the golden-statements diff was pure insertion, so every pre-existing `pins`/`elab` entry is byte-identical; all lanes pass and the axioms audit is posted to the PR |

The oracle lane went green on every push; its runs are paired with the lean
runs in row 10 (most recently 35646622979).


### C12 — the Carr–Madan contour in `Fourier.lean` is not the pricing contour (found while scoping BRIEF_010)

**Date:** 2026-09-21. **Trigger:** BRIEF_010's route-check, run before any Lean
was written (ledger C4). Found by the brief, recorded here rather than edited
away (the C1 posture, one level down).

`ImprovedBS/Fourier.lean`'s
`carrMadanKernel φ α u = φ (↑u + ↑α * I) * (cmDenom α u)⁻¹` — and
`ImprovedBS/Inversion.lean`'s `carrMadanInversion`, which inherits it — puts the
model factor on the line `Im v = +α`, and BRIEF_005's module header states the
call value as `V = e^{−rτ}/(2π)·∫ e^{−iuτ} φ(u + iα)/cmDenom du`. The price the
tree actually damps (`dampedCallPrice`, BRIEF_008) is
`k ↦ e^{αk}·e^{−rτ}·E[(S e^X − S e^k)⁺]`, and *its* forward transform sits on the
line `Im v = −(α+1)`:

    ∫_ℝ e^{iuk} f(k) dk = e^{−rτ} · S · φ(u − i(α+1)) / cmDenom(α,u)

The two lines coincide only at `α = −1/2`, which `0 < α` excludes. Measured on
2026-09-21 at `S=100, K=110, τ=1, r=0.05, q=0.02, σ=0.25, α=1.5`: the formula on
`u − i(α+1)` reproduces the closed form `7.112102348131359` to **9.99e-16**
relative — this is what the oracle's `bs_call_by_fourier_inversion` implements,
and what `test_fourier_inversion` asserts at `2e-11` — while the same formula on
`u + iα` returns `1.819563153701569`, a **74.2% relative error**. From the
definition side, direct quadrature of `∫ e^{iuk} f(k) dk` matches
`e^{−rτ}·S·φ(u − i(α+1))/cmDenom(α,u)` to `1.16e-16` / `5.38e-16` / `8.16e-16` at
`u = 0, 0.7, −2.0`, and misses the `u + iα` identity by `1.28e-01` / `2.25e-01` /
`5.41e-01` at the same points.

**Why it survived, and what is not affected.** BRIEF_005's deliverable is a
*conditional* integrability theorem whose hypothesis names its own contour, so the
theorem is true on either line — the hypothesis is a hypothesis. The tempered decay
is contour-independent to leading order (CGMY at `C=1, G=5, M=10, Y=0.7, τ=1`:
`−Re ψ/|u|^Y` at `u = 2000` measures `3.731206` on the pricing line and `3.731207`
on the tree's), which is precisely why the mismatch was invisible to it. And
`Inversion.lean` §4 never consumes `carrMadanKernel`: its five main theorems are
about `𝓕⁻ (𝓕 f)` at the lognormal law and are correct as stated. **No pinned
statement moves, and no def body is edited**: the correction is to an
*identification* — a docstring's claim about what an integrable kernel is — not to
a proof. It is the C1-item-1 failure mode (a claim that certifies nothing) in its
identification-level form, and it is the reason BRIEF_010's pricing identity is
stated on `u − i(α+1)`.

**What it costs, and what now guards it.** BRIEF_010 adds the kernel on the
pricing line (`cmPriceKernel`) and proves the exact relation
`cmPriceKernel φ α u = carrMadanKernel (fun v => φ (v − (2α+1)·i)) α u`, so
BRIEF_005's integrability theorem applies to it verbatim, with the same
`c, D, Y, u₀` — the correction costs one pointwise identity, not a new domination
argument. The prose correction lands in the doc-comments of `Fourier.lean` and
`Inversion.lean`, which is free under the pins (comments are stripped: the 108
pre-existing entries stay byte-identical, and the audit trail for the change is
this entry, not a pin diff). The guard lands with the same PR: a `[CONTOUR]` route
check in `scripts/lean_lint.py` with a cheat seeded in `tests/test_lint.py`, and
oracle mutant **M15** (contour swap in `bs_call_by_fourier_inversion`), killed by
the existing `test_fourier_inversion` alone — measured relative error `7.44e-01`
against that test's `2e-11` tolerance.

### C13 — the thesis conflated two skeletons; the widening needs a selection principle

**Date:** 2026-09-21. **Trigger:** external review of the README/thesis
against the landed tree. The reviewer's praise and its three findings are
recorded here in the repo's own terms; what follows is what was wrong, what
was already handled, and the repair queue.

1. **Two skeletons, and the repo's claims were about the wrong one.** The
   "arbitrage-free skeleton that makes a closed form exist" unpacks into a
   *static* layer (parity, no-arbitrage bounds, price as discounted
   expectation under a pricing measure — model-free) and a *dynamic* layer
   (a self-financing replicating portfolio, a *unique* martingale measure,
   the PDE as its consequence). Every preservation result in the tree is
   static: `ImprovedBS/Skeleton.lean` (BRIEF_009) proves parity and bounds
   for any law with the drift condition — real work, correctly done, but
   about the layer that was never in danger. Two sentences were the
   unearned dynamic-layer claims: docs/03's "hedging stays a
   single-martingale principle" and the BSM-2 kit's "the drift is fixed by
   the martingale condition". With jumps, the martingale condition is one
   equation and does not select a measure — Esscher, minimal-entropy,
   mean-correcting and calibrated choices are all arbitrage-free and price
   the same call differently. Both sentences are corrected in docs/03; the
   README's thesis now states the split. The BSM-2 kit gains item 7 (the
   selection principle's necessity is a theorem), and item 3 is amended to
   "fixed *at a named pricing measure*". One refinement the reviewer's own
   construction needed: within a single exponential-Lévy model the Esscher
   martingale equation is strictly monotone in the parameter (the cumulant
   is strictly convex), so non-uniqueness lives *across* selection
   principles, not within the Esscher family — the witness must be
   cross-family, or finite (a one-period trinomial suffices).
2. **The non-uniqueness theorem is queued, as the review demanded — and it
   consumes the model-free layer.** BRIEF_012: two distinct probability
   measures, both with the drift condition (hence both satisfying the
   skeleton layer's three facts, so parity and bounds hold for both), giving
   different call prices. That is the machine-checked statement that
   static-skeleton preservation is necessary-but-not-sufficient — a RED
   verdict on the thesis's dynamic half, which by this ledger's rules is a
   result, not an incident.
3. **The flagship negative theorem's hypothesis is unwitnessed in-system.**
   `ImprovedBS/Levy.lean`'s tail bound enters as a hypothesis (mathlib has
   no α-stable law), and C7 already recorded that the hypothesis is
   unsatisfiable for `α ≤ 0` — satisfiability was known to matter and left
   at prose. BRIEF_013 constructs a witness: a Pareto law
   (`Measure.withDensity` against Lebesgue on `[1, ∞)`, density
   `α·x^(−(α+1))`), proves it a probability measure with the tail lower
   bound, and instantiates the obstruction theorem at it — no hypothesis.
   The same review's general point stands: pins catch weakening, not
   vacuous hypotheses; the witness is the cheap defense for the node the
   thesis leans on hardest.
4. **The oracle and the Lean twin share an author.** Agreement between them
   is weaker evidence than the crosscheck section claims by omission.
   BRIEF_014 pins published benchmark values (Haug's standard test cases)
   as literal constants in `tests/` — one genuinely external anchor — and
   adds the review's term-structure falsifier to the oracle: pure
   exponential-Lévy smiles are too steep at short tenors and decay like
   `τ^(−1/2)` at long ones, while the market's smile persists; the model's
   measured ATM-skew decay exponent is compared against the *cited* market
   power law, and the outcome lands in docs/02 as a RED against the
   T6-direction taken alone (the dynamic half of why the literature went
   to stochastic time changes — cf. the Dupire point: static smile-matching
   was solved in 1994, so the widening must be judged on dynamics, not on
   surface fit).
5. **Already handled before the review arrived:** the damping parameter's
   own moment strip. C12 (PR #12) records the pricing contour
   `v = u − i(α+1)`, its containment condition `α + 1 < min(G, M)` (the
   review's `α < M − 1` is the same inequality on the right wing) and the
   numéraire condition `1 < M`; `Fourier.lean`'s decay requirement was
   already a named hypothesis (`hdecay`), never an unbacked premise. The
   machine-checked discharge of that hypothesis at the concrete CGMY
   exponent is BRIEF_011's stated deliverable.
6. **Novelty calibration.** The README called T6 "a genuinely new approach,
   not a reimplementation". Its content is Carr–Madan (1999) and CGMY
   (2002) restated; exponential-Lévy pricing by Fourier inversion has been
   in production at dealers for two decades. The README's contribution
   claim is now the defensible one, hoisted from the license section: the
   machine-checked restatement and the grading apparatus around it.

The review's two closing questions are the program's: the current tree is a
*price* program (the hedging horizon in docs/03's "Beyond BSM-2" is where
hedging enters, as error bounds rather than replication), and the
measure-selection question is now the BSM-2 kit's item 7.

### C14 — the pricing-line condition is `α + 1 < M`, not `min (G, M)` (found while scoping BRIEF_011)

`docs/03` §D1 and `docs/04`'s queue state the CGMY strip condition as
`α + 1 < min(G, M)`. On the pricing contour `v = u − i(α+1)` (C12) that
spelling is **not** the condition the mathematics uses, and one half of it
is vacuous there:

    M − iv = (M − (α+1)) − iu        Re = M − (α+1)     ← needs α + 1 < M
    G + iv = (G + α+1) + iu          Re = G + α + 1     ← positive for FREE

so the cpow branch on the pricing line is constrained by `M` alone; `G`
constrains nothing. `G` binds only the OLD line `v = u + iα` that
`Fourier.lean`'s `carrMadanKernel` sits on, where `G + iv = G + i(u + iα)` has
real part `G − α` (`cgmyOldContour_base_right_re`) — negative once `α ≥ G`.
In other words the docs' `min` is the *intersection* of the two lines'
conditions, and the prose that justified it (`the strip is α + 1 < G`) swapped
which tempering rate controls which half of the law: `M` tempers the positive
half `C e^{−Mx} x^{−1−Y}` and `G` the negative half `C e^{−G|x|} |x|^{−1−Y}`.

The landed statements use `α + 1 < M` — the strictly weaker (and actually
used) hypothesis, with `G > 0` the only requirement on `G`:

* `cgmyExponent_contour_re_le`, `cgmyExponent_contour_re_le_half` and
  `cgmy_contour_decay` all carry `(hMG : α + 1 < M)`;
* `cgmyOldContour_base_right_re` keeps the witness `Re(G + iv) = G − α` in the
  tree, so the correction is a theorem rather than a remark;
* the `[CGMY]` lint check fails if any of those statements grows a `min` over
  `G`/`M` or loses its `α + 1 < M`, and mutant C2 in `tests/test_lint.py` seeds
  exactly that regression (`α + 1 < min G M`) so the guard is falsified rather
  than assumed;
* `tests/test_bs.py::test_cgmy_contour` asserts the two lines' base reals
  numerically (`(M − (α+1), G + α + 1)` on the pricing line, `G − α` on the
  old one) at three parameter points, including the M-side witness
  `G = 0.5, M = 10, α = 1.5` where `G < α < M − 1 = 9`.

Numeric route check (C4), re-run against the exact constants and threshold the
Lean defs now use: 5040 pricing-line points plus the threshold triple for each
of 48 parameter sets in `C ∈ {0.5, 1}`, `G ∈ {0.05, 0.5, 5}`,
`M ∈ {1, 3, 10}`, `Y ∈ {0.3, 0.7, 0.99, 1.3, 1.7, 1.9}`, `α ∈ {0.5, 1, 2}`
restricted to `α + 1 < M` — **0 violations**, and the pointwise estimates on
both regimes (the sharp `y^Y cos(πY/2) ≤ Re((a+iy)^Y)` for `Y < 1`, and the
mean-value `Re((a+iy)^Y) ≤ y^Y cos(πY/2) + 2^{Y−1} Y a y^{Y−1}` for
`1 ≤ Y < 2`, `a ≤ y`) never violated on their grids either. `Re ψ` is exactly
even in `u` (two-base split vs raw: `3.8e-15`).

What this correction does **not** change: `Fourier.lean`'s `carrMadanKernel`
stays on `u + iα` (it is the `α`-damped kernel, and on that line `α < G` is
the right condition), `cmPriceKernel` stays on `u − i(α+1)`, and the numéraire
condition `1 < M` (`cgmy_numeraire_strip`) is untouched — it is the same `M`
that the pricing line needs, which is why the docs' right-hand wing
`α < M − 1` was already correct.

## CI history for row 11 (PR #17)

Five runs. The module is 52 declarations written and read against the pinned tag
in a sandbox with no toolchain, so this lane was the first thing that ever
compiled it — which is why the first two runs are elaboration, not mathematics.

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `76ca8dd` | first push: 20 errors, all API shape. `Ioo`/`Ioi` are `Set.Ioo`/`Set.Ioi` and `autoImplicit false` makes that a hard error; `cgmyCharFactor_add` needs the τ-coercion split before `add_mul`; the old-line witness's `mul_assoc` cannot see through `I * (↑α * I)`; `sin (πY) < 0` for `1 < Y < 2` was feeding `sin_neg_of_neg_of_neg_pi_lt` a POSITIVE argument; the two `positivity` steps for `M^Y + G^Y ≥ 0` and `2^{Y−1}·Y ≥ 0` were simply false as stated, so the two nonnegativity lemmas gained `0 ≤ G`, `0 ≤ M`, `0 ≤ Y`; `Complex.conj_add`/`conj_mul` do not exist (`conj_mul'` does) and a `rw` rewrites only the first occurrence. | build fail 20 errors |
| 2 | `8d36a4c` | 4 errors left: `simp` leaves `G + -α = G - α`; `simpa [hexp] using hreal` loops because `Complex.ofReal_sub` unfolds `↑(Y−1)` straight back into `↑Y − 1`; `rw [← Real.rpow_one \|u\|]` fires on the base of the other `\|u\| ^ (Y−1)` as well as on the standalone factor (its pattern is a bare variable); and `cgmy_contour_continuous` **could not be proved as stated** — the right base `G + α + 1 + iu` has imaginary part `u`, which vanishes at `u = 0`, so its real part must carry the slit-plane condition, which needs `G > 0` and `α > 0`. Correction C15; the statement moved openly. | build fail 4 errors |
| 3 | `ae9fcfe` | **build GREEN** (`⚠ [8931/8933] Built ImprovedBS.CGMY`) and the audit green on all 148 entries, red *by design* on the 26 new declarations having no `elab` entry. The workflow published the paste-ready `elab_delta` to the PR (26 entries). | fail (by design) |
| 4 | `03be381` | the delta merged verbatim: `added 26, changed 0, elab now 165` — no pre-existing elaborated type or axiom list moved, so the commit is a pure insertion into the golden file. | **GREEN** |
| 5 | `4971c45` | this row's documentation commit (row verdict, CI history, C15, the `docs/03` §D1 item-2 correction, the `docs/04` queue row and the brief's LANDED status) re-graded green — lean run 35780267323 (oracle lane 35780267417), `lint` and `oracle` on the docs-only diff. | GREEN |

Two things the arc says about the brief itself, both already in its text: the
numeric route-check (ledger C4) was run *before* the Lean, which is why every
failure above is a name/shape failure and not a wrong estimate; and the
acceptance bar `docs/04` stated — continuity and decay on the contour,
discharging BRIEF_010 §5's (H-decay) — needed one refinement of its hypothesis
list (C15), which is exactly the kind of thing a brief is supposed to find rather
than inherit.

### C15 — the contour's continuity needs `G > 0` and `α > 0`: on the right base the branch condition is carried by the real part (found by CI run 35777615606)

**Date:** 2026-09-22. **Trigger:** the first `lake build` of
`ImprovedBS/CGMY.lean` failed `cgmy_contour_continuous` with `linarith failed to
find a contradiction` — the goal was `0 < Re(G + α + 1 + iu)`, and the theorem
carried only `0 < Y` and `α + 1 < M`. The mathematics, not the tactic:

* the left base of the pricing line is `M − iv = M − (α+1) − iu`, whose real part
  is `M − (α+1) > 0` and whose imaginary part is `−u`, so at `u = 0` the
  `slitPlane` contains it *through its real part* — and `α + 1 < M` is exactly
  what supplies that. This is C14, again;
* the right base is `G + iv = G + α + 1 + iu`, whose imaginary part is `u` — it
  VANISHES at `u = 0`. So at the origin the `slitPlane` must be entered through
  `Re = G + α + 1 > 0`, which needs `G > 0` and `α > 0`. Neither `α + 1 < M` nor
  `G`'s positivity alone gives it, and the theorem as written had neither.

**Resolution.** `cgmy_contour_continuous` now takes `(hG : 0 < G)` and
`(hα : 0 < α)` — the first landed statement to move during BRIEF_011
(`cgmy_charFactor_contour_continuous`, unpinned, takes the same two; the call in
`cgmy_cmPriceKernel_integrable` passes them from its own hypotheses). One pin of
the 165 moved; the other 164 are byte-identical, so the change shows up as a
one-line diff in `tests/golden_statements.json` — which is the point of pinning.
Nothing about the *pricing* hypothesis changed: `α + 1 < M` alone remains the
condition on the contour, and no statement anywhere gained a `min` over `G`/`M`.

**Why it is worth a correction rather than a silent edit.** The acceptance item in
`docs/04` reads "the CGMY factor's continuity and decay on the contour `u ↦ u −
i(α+1)` for `0 < α`, `α + 1 < min(G, M)`" — the parameter range of the model
(`C, G, M > 0`, here also `0 < α`) was prose, and the theorem had to make it
explicit. It also locates the branch condition precisely: on the pricing line the
`M`-side base is what `α + 1 < M` protects at the *origin*, and the `G`-side base
is protected there by the parameter range instead — while `G`'s own constraint on
the line (`G + α + 1 > 0`) is the one that would fail first if `G` were allowed to
go negative, which is why the landed hypothesis is `0 < G` and not `0 < M`.

## CI history for row 12 (PR #19)

Three lean runs. The module is 45 declarations written and read against the
pinned tag in a sandbox with no toolchain (elan/lean release hosts unreachable;
the mathlib *source* at v4.34.0 was fetched and every name grepped before the
first push), so this lane was the first thing that ever compiled it. Unlike
rows 10 and 11 there was no elaboration round: the first build had two errors,
both the same tactic behaviour, and neither was a name, a shape or the
mathematics.

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `3a238a8` | `lake build` red with exactly two errors, both `linarith failed to find a contradiction`, at the two places where the proof had kept `hexp : 1 * Real.exp ((0 - 0) * 1) = 1` in context and asked `linarith` to combine it with a hypothesis or goal containing `p₁ / 2`. Cause: linarith's `cancelDenoms` preprocessing `ring_nf`s every hypothesis that contains a numeral division, and `ring_nf` normalizes *inside* atoms — so `Real.exp ((0 - 0) * 1)` became `Real.exp 0` on the side with the division and stayed `Real.exp ((0 - 0) * 1)` in `hexp`; two atoms, no contradiction. Everything else in the file elaborated (the log shows only the two errors and the unreachable-tactic linter on three `first \| … \| …` fallbacks that turned out never to fire: `rfl` for `trinomialMeasure_apply`, `norm_num` for `martingale_set_call_eq`, `congr 1 <;> norm_num` for `witnessA/B_mem_segment`). Oracle lane green (run 36044790367). | fail |
| 2 | `ede39bb` | the exponential simplified away with `simp only [sub_self, zero_mul, Real.exp_zero, one_mul]` *before* linarith, the fallbacks dropped. **build GREEN** (`✔ [8930/8934] Built ImprovedBS.NonUniqueness (5.0s)`, no warnings on the module) and the audit green on all 186 entries; red *by design* on the 45 new declarations having no `elab` entry. The workflow published the paste-ready `elab_delta` (45 entries) to the PR. Lean run 36045727487. | fail (by design) |
| 3 | `a61be00` | the delta merged verbatim: `added 45, changed 0, elab now 210` — no pre-existing elaborated type or axiom list moved, so the commit is a pure insertion into the golden file. Lean run 36052072620, oracle lane 36052072567. | **GREEN** |
| 4 | `654a07f` | this row's documentation commit (row verdict, CI history, C16, the `docs/03` §D1 item-7 status, the `docs/04` queue row, the brief's LANDED status, README) re-graded green on the docs-only diff — lean run 36053168986 (oracle lane 36053168937). | GREEN |

One incident outside CI, recorded because it could have cost a commit's
provenance: the GitHub token expired between runs 2 and 3, and on reconnection
the sandbox's working tree was restored from its patchset onto the *base*
commit, so the first attempt to commit the merged delta captured the entire PR
as a single commit on top of `7e2b8ac`. The push was rejected as non-fast-forward
(the remote had `3a238a8`/`ede39bb`), which is the right outcome; the fix was
`git reset --soft origin/<branch>` and re-committing only the golden-file diff.
Nothing was force-pushed and the remote history is the three commits above.

### C16 — the brief's own route-check table had two slips, found by implementing it (BRIEF_012, PR #19)

**Date:** 2026-09-24. **Trigger:** writing `test_nonuniqueness_witness` to
assert "the whole route-check table" of BRIEF_012 in exact `Fraction`
arithmetic, and writing the mutants the brief specified.

1. **The drift canary's mean.** The table row says `p = (1/4, 5/8, 3/8)`:
   "`sum(p) ≠ 1`, `E[S_T] = 1.25 ≠ 1`, parity gap jumps to `0.25`". The mass is
   `5/4` (right), the traded-parity gap is `3/8 − 1/8 = 1/4` (right), but the
   mean is `1/8 + 5/8 + 6/8 = 3/2`, not `1.25` — `1.25` is the *mass*. And the
   prose below the table — "the *unfixed* gap identity still holds" — is false
   at this canary in the form Lean states it: `model_free_parity_gap` needs
   `IsProbabilityMeasure`, and at mass `5/4` the identity
   `call − put = e^{−rτ}(E[S_T] − K)` reads `1/4 = 1/2`. Only the mass-weighted
   form `call − put = E[S_T] − K·mass` survives, which is not the theorem. The
   brief's M17 is nevertheless the right mutant (it kills the test three ways —
   mass, drift, traded parity), so it is committed as specified; the test
   asserts the correct numbers and adds a *normalized* wrong-drift canary
   `(1/4, 1/2, 1/4)` (mass 1, mean `9/8`) at which the gap identity and the
   bounds genuinely hold while traded parity fails by `1/8` — which is the
   BRIEF_009 seam the prose was reaching for.
2. **The literal M18 is blind at the witness.** The brief specifies M18 as "the
   call payoff evaluated with the put's `max(K−s, 0)`, which destroys
   `call(A) ≠ call(B)` without touching any probability". At `S = K = 1`,
   `r = 0` the forward is the strike, so `call = put` at *every* martingale law
   on these atoms (`1/4 = 1/4`, `1/8 = 1/8`): pricing the call with the put
   payoff changes nothing the witness test can see, and the mutant would
   survive it — the mutation harness would have reported the test as vacuous
   for that seed. It is M13's twin and only `test_model_free_skeleton`
   (`K ≠ F`) sees it. The committed M18 is the *linear* payoff `s − K`, which
   is what actually destroys the disagreement without touching a probability:
   on the whole martingale segment the linear payoff is pinned by the drift
   (`call(A) = call(B) = E[S_T] − K = 0`), the convex one is not — the
   mechanism of the theorem, seeded as a bug. M19 (B's weights replaced by
   A's) was added as the oracle twin of the lint's N1: every clause survives
   except the one that *is* the theorem.

**Why it is a correction and not a footnote.** The brief's authority rested on
"measured before the Lean — ledger C4": a route-check table run through the
repository's own oracle. Two cells of that table were wrong and one of its
two specified falsifiers could not falsify. None of it touched the theorem —
A, B, the segment, `p₁/2` and the `0.25` gap are all exactly as stated, and
the Lean landed with no mathematical repair — but a table that is quoted as
evidence has to be re-run, not re-read, which is what
`test_nonuniqueness_witness` now does on every oracle run. The brief's text
is left as issued (it is a record); this entry, the test's docstring and the
mutants' comments carry the corrected numbers.

### C17 — the GBM corner needs a normalized scale, not just `Y → 2` (BRIEF_014 issuance)

**Date:** 2026-09-25. **Trigger:** issuing BSM-2 kit item 6 against the *landed*
`cgmyExponent`, rather than against the shorthand in docs/03 §D1. This is a
correction to a proposed theorem, **not** a CI verdict or a landed Lean proof.

The old item 6 said `ψ_CGMY → ψ_GBM as Y → 2 (or G,M → σ²/2)` with no scaling
of `C`. The first limit is **false**: `Γ(−Y) ~ 1/[2(2−Y)]`; at fixed `C=.35`,
`G=M=3`, `v=1`, the bracket tends `−2` and `Re ψ` goes to `−∞`.
`tests/test_bs.py::test_gbm_corner` measures `Re ψ = −2.980` at `Y=1.9`
and `−349.411` at `Y=1.999`, with `(2−Y)Re ψ → −.35`. Taking
`G,M → σ²/2` at fixed noninteger `Y` is not a Gaussian limit either: the
`Y`-th complex powers remain nonquadratic (at `Y=1.5, C=.2,
G=M=σ²/2=1.125`, with `σ=1.5` and `M>1`, the measured ratio
`Re ψ(2)/Re ψ(1)` is `3.691`, not the Gaussian `4`). Worse,
evaluating `Y=2` directly
in Lean cannot be substituted for a limit: `Real.Gamma (-2) = 0` at its pole
by convention, so it silently returns the wrong exponent.

**Repaired specification (issued, unproved):** `1 < Y < 2`,
`C_Y=(σ²/2)(2−Y)`, and `Y ↑ 2`, so the Gamma recurrence gives
`C_YΓ(−Y) → σ²/4`. The bracket has polynomial limit
`−2v²+2i(G−M)v`, yielding variance `σ²` but still an uncorrected log-drift.
BRIEF_014 records two *distinct* bridges to GBM: an algebraic forward
normalization `r−q−κ_Y(1)` at general carry (not an Esscher measure), and a
named Esscher selection at exact zero carry `θ₀=(M−G−1)/2`. The numeric
route-check against an independently expanded polynomial falls from maximum
relative exponent error `5.05e−2` at
`ε=.1` to `5.85e−5` at `ε=.0001` for the forward-normalized route; doubling
`C_Y` leaves a `1.257` discrepancy and dropping the correction a `.563`
discrepancy. These checks are **not** a machine-checked limit, a CGMY law
construction, or convergence of prices; the latter need further theorems.
C13's provisional "BRIEF_014 = Haug" assignment remains archival; the
external-anchor repair is still queued and will be numbered at issue.

## CI history for row 14 (PR #22)

Four lean runs, and the shape is by now the house shape: one round of
elaboration, two rounds of the by-design pin bootstrap, one green.

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `0259a27` | `lake build` red with exactly seven errors, all in `ImprovedBS/Corner.lean` — and every one of them a tactic that outlived its goal or an API shape, never the mathematics. Four were the "no goals to be solved" class (`ring` after a `field_simp` that had already closed the pole-cancellation algebra, `norm_num` after a `convert` that had already matched, `ring` after `simp` on the two real-part lemmas). The other three: `by continuity` does **not** solve `ContinuousAt (fun Y : ℝ => 3 - Y) 2` here (it delegates to `aesop`, which has no continuity rules in scope), so both uses are now built from `continuousAt_id`/`continuousAt_const`; `simpa` will not see through `Complex.ofReal ∘ _`, so transporting the pole coefficient to ℂ needs `Function.comp_def` **and** `Complex.ofReal_mul` (the composed function and the un-pushed cast are two separate failures, and the error message shows both); and `simp` normalizes the real norm to `‖x‖ ↦ |x|` *and* `Real.rpow_two`, so a `have` written with `‖ ‖` around `^ (2 : ℝ)` matches nothing — the edge value had to be stated as `|(G+M)^2 − (G+M−1)^2 − 1|`. Oracle lane green (run 36107933100). | fail |
| 2 | `60aa9ef` | **build GREEN** (`Build completed successfully (8936 jobs)`) and the audit green on all 226 entries; red *by design* on the 17 new declarations having no `elab` entry. The workflow published the paste-ready `elab_delta` (17 entries) to the PR. Lean run 36109890412. | fail (by design) |
| 3 | `f702cd4` | the `[CORNER]` lint mutants (G1–G5) commit: no `.lean` file changed, build green again, same by-design red on the pins — the bootstrap stays red until the block is committed, which is the point. Lean run 36110197470. | fail (by design) |
| 4 | `b0cb26a` | the delta merged verbatim: `added 17, changed 0, elab now 257` — a pure insertion into the golden file, so no pre-existing elaborated type or axiom list moved. Lean run 36111570530, oracle lane 36111570572. | **GREEN** |

Two process notes, recorded for the same reason row 12 recorded its own. The
first commit of this row was amended and force-pushed once: its message was
written with backticks inside a double-quoted `-m`, so bash ran the quoted
Lean identifiers as command substitutions and the committed text came out as
an ImageMagick usage dump. Nothing but the message changed; `git commit -F -`
with a quoted heredoc is the fix. And the GitHub token expired between runs 3
and 4, which cost a round-trip to reconnect — no effect on the tree, since
CI logs are published to the PR precisely so a sandbox that cannot reach
Actions' blob storage can still read them through `api.github.com`.

### C18 — the corner's route-check is a test now, and the bracket hypothesis is weaker than the brief wrote

**Date:** 2026-09-25. **Trigger:** landing BRIEF_014, whose work item 4 says
"make the pre-brief numerical checks a committed oracle test"; and stating
`cgmyBracket_tendsto` against the hypotheses the proof actually uses.

1. **`scripts/check_gbm_corner.py` was deleted, not duplicated.** The brief
   allows either ("reuse this script or move its independent routes into
   `tests/test_bs.py`"). Reusing it would have left the same seven route
   checks running in two places under two different grading regimes — the
   script asserting its own canaries, the suite asserting mutants — which is
   how a numeric check quietly becomes decoration. The routes now live in
   `tests/test_bs.py::test_gbm_corner`, graded by the suite, by the mutation
   harness (M22 doubled scale, M23 dropped drift correction) and by the same
   two-independent-sides rule as every other oracle identity: the model side
   (`corner_scale`, `corner_forward_exponent`) is in the oracle, the GBM
   target is expanded by hand inside the test, so no single mutation can move
   both sides of one comparison. The script's canaries are now assertions,
   including the pole rejection (`Y = 2` raises) that C17 exists for.
2. **`cgmyBracket_tendsto` holds under `0 < M`, not `M > 1`.** The brief
   states the section's standing assumptions as `G > 0`, `M > 1`; the bracket
   limit at fixed `v` needs only that the four bases `M − iv`, `M`, `G + iv`,
   `G` are nonzero, which is `M > 0` and `G > 0` plus the strip
   `−M < Im v < G`. The `M > 1` is what the *numéraire* costs: `u = 1` has to
   sit in `(−G, M)` for `cgmyCornerCumulant_one_tendsto` and
   `cornerForward_numeraire`. Stating the bracket with `M > 1` would have been
   true and narrower than the theorem; the C14/C15 pattern is to record which
   hypothesis each statement actually consumes, so that is what is committed.

Neither changes a claim: the brief's repaired specification, its route-check
table (every cell re-measured and reproduced to Float noise — worst residual
`1.0e−4` at `ε = 1e−4`, from the range route; the recurrence row differs in
its last digits only because the committed test forms `C_Y` as `(σ²/2)(2 − Y)`,
the way the Lean definition reads, rather than as `(σ²/2)ε`) and its two
bridges to GBM all land exactly as issued. The
brief's text is left as issued; this entry and the module header carry the
two changes.

## CI history for row 15 (PR #23)

| # | head | what the run decided | outcome |
|---|------|----------------------|---------|
| 1 | `95f48aa` (run 36118644804) | first push of `ImprovedBS/ParetoWitness.lean`, 11 theorems | RED, **one** error: `integrableOn_Ici_iff_integrableOn_Ioi` carries an auto-param (`‖f b‖ₑ ≠ ∞ := by finiteness`) at the tag, so `.mpr` on the bare name is `Unknown constant`. Every other declaration elaborated on the first push — including the tail integral, the CDF route for C7 and the Dirac discriminator, whose names had not all been verified at issue |
| 2 | `8d950f0` (run 36119192150) | the auto-param passed explicitly (`(… (by simp)).mpr h`) | RED by design on pins: `lake build` + `#print axioms` audit **GREEN** (all 237), and the empty `elab` block for the 11 new names printed as `elab_delta` |
| 3 | `df470d1` (run 36119639468) | the delta merged verbatim (`added 11, changed 0, elab now 268`), dead `first` alternatives removed | **GREEN** — every lane |



### C19 — the cited Lévy skew decay is `τ^(−1)`, not `τ^(−1/2)` (BRIEF_016 issuance)

**Date:** 2026-09-25. **Trigger:** issuing the external-anchor / term-structure
brief (ledger C13 finding 4), whose text restated the reviewer's parenthetical
"decay like `τ^(−1/2)` at long ones" as part of the falsifier's rationale. This
is a correction to the reviewer's reasoning as the ledger transcribed it, **not**
a CI verdict; it is recorded because the falsifier's pre-registered band depends
on which rate is the cited one.

The cited large-maturity rate for the ATM implied-vol skew of an
exponential-Lévy model is `O(τ^(−1))`: Figueroa-López, Forde and Jacquier,
*The large-time smile and skew for exponential Lévy models*, prove
`∂_x[σ̂_t(x)²·t] → a₀(0) = 8(p₀ − 1/2)` (Proposition 4.1) — the derivative of the
dimensionless variance settles to a finite constant, so the skew in
log-moneyness dies like `1/τ`. `τ^(−1/2)` is the rate of the *standardized
skewness* in the Edgeworth expansion, not of this object; it is not what the
literature quotes for the skew, and it is not what the model does. Measured for
the brief, with `ψ = ∂σ_BS/∂k` at `k = 0` by central difference (`h = .005`)
and a log-log fit over `τ ∈ [.25, 5]`:

| witness | `α_model` | `|ψ|·τ` over the window |
|---|---|
| VG at Carr–Madan Case 4 (`r = .05`, `q = .03`) | **1.0857** | `.263 … .341` |
| CGMY `C = 1, G = 5, M = 10, Y = .7`, `r = q = 0` | **0.9682** | `.0447 … .0493` |

Both sit at `≈ 1/τ`, consistently with the citation. `|ψ|·√τ` on the same
window *decreases* (`CGMY`: `.0893 → .0220`), which is the `τ^(−1/2)` form being
falsified by the model itself. The correction does not soften the RED — it
*tightens* it: the family decays like `1/τ` while the market's published fits
decay like `τ^(−0.36..−0.45)` (El Amrani–Guyon `0.43/0.44/0.45` for SPX/SX5E/DAX
above three weeks; Gatheral–Jaisson–Rosenbaum `α ∈ (0.3, 0.5)`), so the family —
not the market — is on the wrong side of the conventional stochastic-vol rate.
The pre-registered bands are `[0.90, 1.15]` (model) against `(0.30, 0.50)`
(market): disjoint by `≥ 0.40`. The brief's `docs/02` RED is to be phrased as a
**magnitude** failure with a theory-correct rate, not as a wrong exponent form.
