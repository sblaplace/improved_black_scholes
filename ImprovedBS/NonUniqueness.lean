/-
  ImprovedBS/NonUniqueness.lean — BRIEF_012: the non-uniqueness witness
  (BSM-2 kit item 7).

  What this file proves, in one line:

    two distinct, mutually absolutely continuous probability laws for the
    terminal spot -- both with the drift condition E[S_T] = S e^{(r-q)τ},
    both satisfying BRIEF_009's parity and no-arbitrage bounds -- price the
    same call differently.                  -- static_skeleton_does_not_select_measure

  So the static skeleton of docs/03 §D1 item 5 (parity + bounds, the only
  model-free content the tree has) does NOT determine the pricing measure.
  That is the incomplete-market fact BSM-2 is about, made machine-checked at
  the smallest law that can carry it: three atoms.

  The numeric contract (fixed by the brief, re-asserted by
  tests/test_bs.py::test_nonuniqueness_witness at the same numbers before any
  Lean was written -- ledger C4):

    S = 1, τ = 1, r = 0, q = 0, K = 1, spots (1/2, 1, 2), spot map X := id.

    law A : weights (1/2, 1/4, 1/4)   E[S_T] = 1   call = put = 1/4
    law B : weights (1/4, 5/8, 1/8)   E[S_T] = 1   call = put = 1/8

  Both are points of the segment (★) of §5: with normalization and drift on
  three fixed atoms, the martingale set is one-dimensional,

    p₃ = p₁/2,  p₂ = 1 − 3p₁/2,  p₁ ∈ [0, 2/3],     call = p₁/2,

  so A is p₁ = 1/2 and B is p₁ = 1/4, and the call price sweeps [0, 1/3].

  Why three atoms and not a named law. The brief's item 3 (a named tempered
  law) is out of scope here on purpose: a witness has to be *checkable*, and
  the three-point law is the one at which every integral is a finite sum
  (`integral_dirac`), every a.e. statement is a statement at three points
  (`ae_dirac_eq`), and equivalence of measures is `smul`/`add` algebra of
  absolute continuity. Nothing about the measures is opaque, so nothing about
  the theorem can be an artefact of an opaque object.

  Route commitments (the `[NONUNIQ]` check in scripts/lean_lint.py):
  * `witnessA_parity`/`witnessB_parity` cite `model_free_put_call_parity` and
    `witnessA_bounds`/`witnessB_bounds` cite `model_free_call_bounds`: the
    witness must be graded by BRIEF_009's layer, not by a private re-derivation
    from `max_sub_swap_eq` (which would prove nothing about that layer);
  * the headline is a real conjunction: both drifts, both parities, both
    bound pairs, measure distinctness, mutual `≪`, and `≠` on the two
    `modelFreeCall` values -- no clause may be dropped;
  * `trinomialMeasure` is the sum of THREE `Measure.dirac` atoms; collapsing
    it to one Dirac makes A = B and the theorem vacuous.

  Design rules inherited from BRIEF_003--011 and applied here:
  * every mathlib name below was read at the v4.34.0 source before pushing
    (ledger C3); the file is CI-compiled only, this tree has no toolchain;
  * the witness laws are stated by their table, not by a formula that happens
    to evaluate to it, so the pins (`tests/golden_statements.json`) pin the
    numbers; the segment (★) is a separate `def` and the witnesses are proved
    to lie on it (`witnessA_mem_segment`, `witnessB_mem_segment`);
  * no existing declaration is touched: this file only consumes
    `modelFreeCall`/`modelFreePut`, `model_free_put_call_parity` and
    `model_free_call_bounds` from ImprovedBS/Skeleton.lean.

  The route (each step is one lemma):
    §1  the three-point law: `trinomialMeasure`, its mass, its integral as a
        finite sum, a.e. statements at the atoms, and `≪` between two such
        laws whenever the dominating one charges every atom.
    §2  the witness laws A and B: probability, integrability, nonnegativity,
        drift, and the two call values 1/4 and 1/8.
    §3  the skeleton at A and B: parity and the bounds, by instantiating
        BRIEF_009 -- the four theorems the lint requires to cite the layer.
    §4  the headline conjunction `static_skeleton_does_not_select_measure`,
        with `witnessA_ne_B`, `witnessCall_ne`, `witness_equivalent`.
    §5  the martingale segment (★): parametrization, membership, the price
        along it, non-degeneracy and the price range; A and B on it.
-/
import ImprovedBS.Skeleton

noncomputable section

namespace BSM

open MeasureTheory

/-!
---------------------------------------------------------------------------
§1  The three-point law
---------------------------------------------------------------------------
-/

/-- **A three-point law**: mass `pᵢ` at the spot `sᵢ`, as a sum of three
scaled Dirac measures. It is a probability measure exactly when the weights
are nonnegative and sum to one (`trinomialMeasure_isProbability`); it is
defined for all real weights so that the algebra of §5 can be stated before
the constraints are imposed. -/
noncomputable def trinomialMeasure (p₁ p₂ p₃ s₁ s₂ s₃ : ℝ) : Measure ℝ :=
  ENNReal.ofReal p₁ • Measure.dirac s₁ + ENNReal.ofReal p₂ • Measure.dirac s₂
    + ENNReal.ofReal p₃ • Measure.dirac s₃

/-- The mass of a set: `add_apply`, `smul_apply` and `smul_eq_mul` are all `rfl`,
so the whole identity is. -/
theorem trinomialMeasure_apply (p₁ p₂ p₃ s₁ s₂ s₃ : ℝ) (A : Set ℝ) :
    trinomialMeasure p₁ p₂ p₃ s₁ s₂ s₃ A
      = ENNReal.ofReal p₁ * Measure.dirac s₁ A + ENNReal.ofReal p₂ * Measure.dirac s₂ A
        + ENNReal.ofReal p₃ * Measure.dirac s₃ A := by
  unfold trinomialMeasure
  rfl

/-- Nonnegative weights summing to one make a probability measure:
`dirac sᵢ univ = 1`, then `ENNReal.ofReal` is additive on nonnegative reals. -/
theorem trinomialMeasure_isProbability (p₁ p₂ p₃ s₁ s₂ s₃ : ℝ)
    (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h₃ : 0 ≤ p₃) (hsum : p₁ + p₂ + p₃ = 1) :
    IsProbabilityMeasure (trinomialMeasure p₁ p₂ p₃ s₁ s₂ s₃) := by
  refine ⟨?_⟩
  rw [trinomialMeasure_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_add h₁ h₂, ← ENNReal.ofReal_add (add_nonneg h₁ h₂) h₃, hsum,
    ENNReal.ofReal_one]

/-- Every real function is integrable against a finite sum of finite Dirac
atoms: `integrable_dirac` (a point has finite `‖f a‖ₑ`), scaled by a finite
weight (`ENNReal.ofReal_ne_top`), added. -/
theorem trinomialMeasure_integrable (f : ℝ → ℝ) (p₁ p₂ p₃ s₁ s₂ s₃ : ℝ) :
    Integrable f (trinomialMeasure p₁ p₂ p₃ s₁ s₂ s₃) := by
  have hi₁ : Integrable f (ENNReal.ofReal p₁ • Measure.dirac s₁) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hi₂ : Integrable f (ENNReal.ofReal p₂ • Measure.dirac s₂) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hi₃ : Integrable f (ENNReal.ofReal p₃ • Measure.dirac s₃) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold trinomialMeasure
  exact (hi₁.add_measure hi₂).add_measure hi₃

/-- **The integral is a finite sum**: `∫ f d(trinomial) = Σ pᵢ f(sᵢ)` for
nonnegative weights (`integral_add_measure`, `integral_smul_measure`,
`integral_dirac`, then `ENNReal.toReal_ofReal`). This is the lemma that turns
every price and every drift below into arithmetic. -/
theorem trinomialMeasure_integral (f : ℝ → ℝ) (p₁ p₂ p₃ s₁ s₂ s₃ : ℝ)
    (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h₃ : 0 ≤ p₃) :
    ∫ s, f s ∂(trinomialMeasure p₁ p₂ p₃ s₁ s₂ s₃) = p₁ * f s₁ + p₂ * f s₂ + p₃ * f s₃ := by
  have hi₁ : Integrable f (ENNReal.ofReal p₁ • Measure.dirac s₁) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hi₂ : Integrable f (ENNReal.ofReal p₂ • Measure.dirac s₂) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hi₃ : Integrable f (ENNReal.ofReal p₃ • Measure.dirac s₃) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold trinomialMeasure
  rw [integral_add_measure (hi₁.add_measure hi₂) hi₃, integral_add_measure hi₁ hi₂,
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h₁, ENNReal.toReal_ofReal h₂, ENNReal.toReal_ofReal h₃,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- An a.e. statement against a three-point law is a statement at the three
atoms: `ae (dirac a) = pure a`, scaled (`ae_smul_measure`) and added
(`ae_add_measure_iff`). -/
theorem trinomialMeasure_ae_of_atoms {P : ℝ → Prop} (p₁ p₂ p₃ s₁ s₂ s₃ : ℝ)
    (h₁ : P s₁) (h₂ : P s₂) (h₃ : P s₃) :
    ∀ᵐ s ∂(trinomialMeasure p₁ p₂ p₃ s₁ s₂ s₃), P s := by
  have hd : ∀ a : ℝ, P a → ∀ᵐ s ∂(Measure.dirac a), P s := by
    intro a ha
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 ha
  unfold trinomialMeasure
  exact ae_add_measure_iff.2
    ⟨ae_add_measure_iff.2
      ⟨Measure.ae_smul_measure (hd s₁ h₁) _, Measure.ae_smul_measure (hd s₂ h₂) _⟩,
      Measure.ae_smul_measure (hd s₃ h₃) _⟩

/-- **Absolute continuity between three-point laws on the same atoms**: any
`q`-law is dominated by a `p`-law that charges every atom. Atom by atom
`c • dirac ≪ dirac ≪ c' • dirac` (`smul_absolutelyContinuous`,
`AbsolutelyContinuous.smul_right`), and each atom of `p` sits inside `p`'s
sum (`AbsolutelyContinuous.add_right`/`add_right'`). No ENNReal arithmetic is
needed: this is the lattice algebra of `≪`. -/
theorem trinomialMeasure_absolutelyContinuous_of_pos (q₁ q₂ q₃ p₁ p₂ p₃ s₁ s₂ s₃ : ℝ)
    (h₁ : 0 < p₁) (h₂ : 0 < p₂) (h₃ : 0 < p₃) :
    trinomialMeasure q₁ q₂ q₃ s₁ s₂ s₃ ≪ trinomialMeasure p₁ p₂ p₃ s₁ s₂ s₃ := by
  have e₁ : ENNReal.ofReal p₁ ≠ 0 := (ENNReal.ofReal_pos.2 h₁).ne'
  have e₂ : ENNReal.ofReal p₂ ≠ 0 := (ENNReal.ofReal_pos.2 h₂).ne'
  have e₃ : ENNReal.ofReal p₃ ≠ 0 := (ENNReal.ofReal_pos.2 h₃).ne'
  unfold trinomialMeasure
  refine Measure.AbsolutelyContinuous.add_left (Measure.AbsolutelyContinuous.add_left ?_ ?_) ?_
  · exact (Measure.smul_absolutelyContinuous.smul_right e₁).trans
      ((Measure.AbsolutelyContinuous.rfl.add_right _).add_right _)
  · exact (Measure.smul_absolutelyContinuous.smul_right e₂).trans
      ((Measure.AbsolutelyContinuous.rfl.add_right' _).add_right _)
  · exact (Measure.smul_absolutelyContinuous.smul_right e₃).trans
      (Measure.AbsolutelyContinuous.rfl.add_right' _)

/-!
---------------------------------------------------------------------------
§2  The witness laws A and B
---------------------------------------------------------------------------
-/

/-- The three spots: the down state `1/2`. -/
noncomputable def witnessSpotLo : ℝ := 1 / 2

/-- The three spots: the flat state `1` (which is also the forward `S e^{(r-q)τ}`
and the strike `K`). -/
noncomputable def witnessSpotMid : ℝ := 1

/-- The three spots: the up state `2`. -/
noncomputable def witnessSpotHi : ℝ := 2

/-- **Witness law A**: weights `(1/2, 1/4, 1/4)` on `(1/2, 1, 2)`.
`E[S_T] = 1/4 + 1/4 + 1/2 = 1`, call `= 1/4 · (2 − 1) = 1/4`. -/
noncomputable def witnessMeasureA : Measure ℝ :=
  trinomialMeasure (1 / 2) (1 / 4) (1 / 4) witnessSpotLo witnessSpotMid witnessSpotHi

/-- **Witness law B**: weights `(1/4, 5/8, 1/8)` on `(1/2, 1, 2)`.
`E[S_T] = 1/8 + 5/8 + 1/4 = 1`, call `= 1/8 · (2 − 1) = 1/8`. -/
noncomputable def witnessMeasureB : Measure ℝ :=
  trinomialMeasure (1 / 4) (5 / 8) (1 / 8) witnessSpotLo witnessSpotMid witnessSpotHi

/-- The call payoff at the down state: `(1/2 − 1)⁺ = 0`. -/
theorem witness_call_payoff_lo : max (witnessSpotLo - 1) 0 = 0 :=
  max_eq_right (by norm_num [witnessSpotLo])

/-- The call payoff at the flat state: `(1 − 1)⁺ = 0`. -/
theorem witness_call_payoff_mid : max (witnessSpotMid - 1) 0 = 0 :=
  max_eq_right (by norm_num [witnessSpotMid])

/-- The call payoff at the up state: `(2 − 1)⁺ = 1`. -/
theorem witness_call_payoff_hi : max (witnessSpotHi - 1) 0 = 1 := by
  rw [max_eq_left (by norm_num [witnessSpotHi] : (0 : ℝ) ≤ witnessSpotHi - 1)]
  norm_num [witnessSpotHi]

/-- A is a probability measure: `1/2 + 1/4 + 1/4 = 1`. -/
theorem witnessA_prob : IsProbabilityMeasure witnessMeasureA := by
  unfold witnessMeasureA
  exact trinomialMeasure_isProbability (1 / 2) (1 / 4) (1 / 4) _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- B is a probability measure: `1/4 + 5/8 + 1/8 = 1`. -/
theorem witnessB_prob : IsProbabilityMeasure witnessMeasureB := by
  unfold witnessMeasureB
  exact trinomialMeasure_isProbability (1 / 4) (5 / 8) (1 / 8) _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The two probability facts are the typeclass argument of BRIEF_009's theorems;
-- register them so that §3 can instantiate the layer without `haveI`.
attribute [instance] witnessA_prob witnessB_prob

/-- The integral against A as a finite sum (weights `(1/2, 1/4, 1/4)`). -/
theorem witnessMeasureA_integral (f : ℝ → ℝ) :
    ∫ s, f s ∂witnessMeasureA
      = 1 / 2 * f witnessSpotLo + 1 / 4 * f witnessSpotMid + 1 / 4 * f witnessSpotHi :=
  trinomialMeasure_integral f (1 / 2) (1 / 4) (1 / 4) witnessSpotLo witnessSpotMid witnessSpotHi
    (by norm_num) (by norm_num) (by norm_num)

/-- The integral against B as a finite sum (weights `(1/4, 5/8, 1/8)`). -/
theorem witnessMeasureB_integral (f : ℝ → ℝ) :
    ∫ s, f s ∂witnessMeasureB
      = 1 / 4 * f witnessSpotLo + 5 / 8 * f witnessSpotMid + 1 / 8 * f witnessSpotHi :=
  trinomialMeasure_integral f (1 / 4) (5 / 8) (1 / 8) witnessSpotLo witnessSpotMid witnessSpotHi
    (by norm_num) (by norm_num) (by norm_num)

/-- The spot map `id` is integrable against A (BRIEF_009's `hX`). -/
theorem witnessA_integrable : Integrable id witnessMeasureA := by
  unfold witnessMeasureA
  exact trinomialMeasure_integrable id _ _ _ _ _ _

/-- The spot map `id` is integrable against B (BRIEF_009's `hX`). -/
theorem witnessB_integrable : Integrable id witnessMeasureB := by
  unfold witnessMeasureB
  exact trinomialMeasure_integrable id _ _ _ _ _ _

/-- Spots are nonnegative A-a.e. (BRIEF_009's `hX0`): true at the three atoms. -/
theorem witnessA_nonneg : ∀ᵐ s ∂witnessMeasureA, 0 ≤ id s := by
  unfold witnessMeasureA
  exact trinomialMeasure_ae_of_atoms _ _ _ _ _ _
    (by norm_num [witnessSpotLo]) (by norm_num [witnessSpotMid]) (by norm_num [witnessSpotHi])

/-- Spots are nonnegative B-a.e. (BRIEF_009's `hX0`): true at the three atoms. -/
theorem witnessB_nonneg : ∀ᵐ s ∂witnessMeasureB, 0 ≤ id s := by
  unfold witnessMeasureB
  exact trinomialMeasure_ae_of_atoms _ _ _ _ _ _
    (by norm_num [witnessSpotLo]) (by norm_num [witnessSpotMid]) (by norm_num [witnessSpotHi])

/-- **The drift condition at A**, in BRIEF_009's exact shape with
`S = 1, r = 0, q = 0, τ = 1`: `E_A[S_T] = 1/2·1/2 + 1/4·1 + 1/4·2 = 1`. -/
theorem witnessA_drift : ∫ s, id s ∂witnessMeasureA = 1 * Real.exp ((0 - 0) * 1) := by
  rw [witnessMeasureA_integral]
  simp only [id_eq]
  norm_num [witnessSpotLo, witnessSpotMid, witnessSpotHi]

/-- **The drift condition at B**: `E_B[S_T] = 1/4·1/2 + 5/8·1 + 1/8·2 = 1`. -/
theorem witnessB_drift : ∫ s, id s ∂witnessMeasureB = 1 * Real.exp ((0 - 0) * 1) := by
  rw [witnessMeasureB_integral]
  simp only [id_eq]
  norm_num [witnessSpotLo, witnessSpotMid, witnessSpotHi]

/-- **The call at A is `1/4`**: only the up state pays, with weight `1/4`. -/
theorem witnessA_call : modelFreeCall witnessMeasureA id 1 0 1 = 1 / 4 := by
  unfold modelFreeCall
  rw [witnessMeasureA_integral]
  simp only [id_eq]
  rw [witness_call_payoff_lo, witness_call_payoff_mid, witness_call_payoff_hi]
  norm_num

/-- **The call at B is `1/8`**: only the up state pays, with weight `1/8`. -/
theorem witnessB_call : modelFreeCall witnessMeasureB id 1 0 1 = 1 / 8 := by
  unfold modelFreeCall
  rw [witnessMeasureB_integral]
  simp only [id_eq]
  rw [witness_call_payoff_lo, witness_call_payoff_mid, witness_call_payoff_hi]
  norm_num

/-!
---------------------------------------------------------------------------
§3  The skeleton at A and B -- instantiating BRIEF_009, not re-deriving it
---------------------------------------------------------------------------
-/

/-- **Parity holds at A**, by `model_free_put_call_parity` with
`S = K = τ = 1`, `r = q = 0`: the forward spread is `1·e⁰ − 1·e⁰`. -/
theorem witnessA_parity :
    modelFreeCall witnessMeasureA id 1 0 1 - modelFreePut witnessMeasureA id 1 0 1
      = 1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1) :=
  model_free_put_call_parity 1 1 1 0 0 id witnessA_integrable witnessA_drift

/-- **Parity holds at B**, by `model_free_put_call_parity`. -/
theorem witnessB_parity :
    modelFreeCall witnessMeasureB id 1 0 1 - modelFreePut witnessMeasureB id 1 0 1
      = 1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1) :=
  model_free_put_call_parity 1 1 1 0 0 id witnessB_integrable witnessB_drift

/-- **The no-arbitrage bounds hold at A**, by `model_free_call_bounds`:
`(1·e⁰ − 1·e⁰)⁺ ≤ call_A ≤ 1·e⁰`. -/
theorem witnessA_bounds :
    max (1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1)) 0
        ≤ modelFreeCall witnessMeasureA id 1 0 1 ∧
      modelFreeCall witnessMeasureA id 1 0 1 ≤ 1 * Real.exp (-0 * 1) :=
  model_free_call_bounds 1 1 1 0 0 id witnessA_integrable witnessA_drift (by norm_num)
    witnessA_nonneg

/-- **The no-arbitrage bounds hold at B**, by `model_free_call_bounds`. -/
theorem witnessB_bounds :
    max (1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1)) 0
        ≤ modelFreeCall witnessMeasureB id 1 0 1 ∧
      modelFreeCall witnessMeasureB id 1 0 1 ≤ 1 * Real.exp (-0 * 1) :=
  model_free_call_bounds 1 1 1 0 0 id witnessB_integrable witnessB_drift (by norm_num)
    witnessB_nonneg

/-!
---------------------------------------------------------------------------
§4  The headline: the skeleton does not select the measure
---------------------------------------------------------------------------
-/

/-- **The two prices differ**: `1/4 ≠ 1/8`. -/
theorem witnessCall_ne :
    modelFreeCall witnessMeasureA id 1 0 1 ≠ modelFreeCall witnessMeasureB id 1 0 1 := by
  rw [witnessA_call, witnessB_call]
  norm_num

/-- **The two laws differ** -- in the strongest sense available: they price
the same claim differently, so they cannot be the same measure. -/
theorem witnessA_ne_B : witnessMeasureA ≠ witnessMeasureB := by
  intro h
  exact witnessCall_ne (by rw [h])

/-- **The two laws are equivalent** (mutually absolutely continuous): both
charge exactly the three atoms, so neither can be dismissed as living on a
different event space. Non-uniqueness here is not a null-set artefact. -/
theorem witness_equivalent :
    witnessMeasureA ≪ witnessMeasureB ∧ witnessMeasureB ≪ witnessMeasureA := by
  unfold witnessMeasureA witnessMeasureB
  exact ⟨trinomialMeasure_absolutelyContinuous_of_pos (1 / 2) (1 / 4) (1 / 4) (1 / 4) (5 / 8) (1 / 8)
      witnessSpotLo witnessSpotMid witnessSpotHi (by norm_num) (by norm_num) (by norm_num),
    trinomialMeasure_absolutelyContinuous_of_pos (1 / 4) (5 / 8) (1 / 8) (1 / 2) (1 / 4) (1 / 4)
      witnessSpotLo witnessSpotMid witnessSpotHi (by norm_num) (by norm_num) (by norm_num)⟩

/-- **BSM-2 kit item 7: the static skeleton does not select the pricing
measure.** Two probability laws `A ≠ B` for the terminal spot, equivalent to
each other, both satisfying the drift condition `E[S_T] = S e^{(r−q)τ}` and
both satisfying BRIEF_009's parity and no-arbitrage bounds at
`S = K = τ = 1`, `r = q = 0` -- and `modelFreeCall` at A is not
`modelFreeCall` at B. Every conjunct is one of the named theorems above; the
conjunction is stated in full so that no clause can be silently dropped
(the `[NONUNIQ]` check reads this statement). -/
theorem static_skeleton_does_not_select_measure :
    IsProbabilityMeasure witnessMeasureA ∧ IsProbabilityMeasure witnessMeasureB ∧
    witnessMeasureA ≠ witnessMeasureB ∧
    (witnessMeasureA ≪ witnessMeasureB ∧ witnessMeasureB ≪ witnessMeasureA) ∧
    (∫ s, id s ∂witnessMeasureA = 1 * Real.exp ((0 - 0) * 1)) ∧
    (∫ s, id s ∂witnessMeasureB = 1 * Real.exp ((0 - 0) * 1)) ∧
    (modelFreeCall witnessMeasureA id 1 0 1 - modelFreePut witnessMeasureA id 1 0 1
        = 1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1)) ∧
    (modelFreeCall witnessMeasureB id 1 0 1 - modelFreePut witnessMeasureB id 1 0 1
        = 1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1)) ∧
    (max (1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1)) 0
        ≤ modelFreeCall witnessMeasureA id 1 0 1 ∧
      modelFreeCall witnessMeasureA id 1 0 1 ≤ 1 * Real.exp (-0 * 1)) ∧
    (max (1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1)) 0
        ≤ modelFreeCall witnessMeasureB id 1 0 1 ∧
      modelFreeCall witnessMeasureB id 1 0 1 ≤ 1 * Real.exp (-0 * 1)) ∧
    modelFreeCall witnessMeasureA id 1 0 1 ≠ modelFreeCall witnessMeasureB id 1 0 1 :=
  ⟨witnessA_prob, witnessB_prob, witnessA_ne_B, witness_equivalent, witnessA_drift,
    witnessB_drift, witnessA_parity, witnessB_parity, witnessA_bounds, witnessB_bounds,
    witnessCall_ne⟩

/-!
---------------------------------------------------------------------------
§5  The martingale segment (★): the whole set of witnesses on three atoms
---------------------------------------------------------------------------
-/

/-- **The segment (★)**: the three-point laws on `(1/2, 1, 2)` with
`p₂ = 1 − 3p₁/2`, `p₃ = p₁/2`, parametrized by the down weight `p₁`. It is a
probability measure with the drift condition exactly for `p₁ ∈ [0, 2/3]`
(`martingale_set_mem`), and every such law is a point of it
(`martingale_set_eq_segment`). -/
noncomputable def martingaleSegment (p₁ : ℝ) : Measure ℝ :=
  trinomialMeasure p₁ (1 - 3 * p₁ / 2) (p₁ / 2) witnessSpotLo witnessSpotMid witnessSpotHi

/-- **The parametrization of (★)**: normalization and the drift equation
`p₁/2 + p₂ + 2p₃ = 1` on the atoms `(1/2, 1, 2)` pin `p₃` and `p₂` to `p₁`.
Two linear equations in three unknowns: the martingale set is a segment, not
a point -- that is the non-uniqueness, before any price is computed. -/
theorem martingale_set_param (p₁ p₂ p₃ : ℝ) (hsum : p₁ + p₂ + p₃ = 1)
    (hdrift : p₁ / 2 + p₂ + 2 * p₃ = 1) :
    p₃ = p₁ / 2 ∧ p₂ = 1 - 3 * p₁ / 2 :=
  ⟨by linarith, by linarith⟩

/-- The drift integral of a three-point law on the witness atoms IS the linear
form of (★): `∫ id = p₁/2 + p₂ + 2p₃`. -/
theorem trinomial_witness_drift (p₁ p₂ p₃ : ℝ) (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h₃ : 0 ≤ p₃) :
    ∫ s, id s ∂(trinomialMeasure p₁ p₂ p₃ witnessSpotLo witnessSpotMid witnessSpotHi)
      = p₁ / 2 + p₂ + 2 * p₃ := by
  rw [trinomialMeasure_integral id p₁ p₂ p₃ _ _ _ h₁ h₂ h₃]
  simp only [id_eq, witnessSpotLo, witnessSpotMid, witnessSpotHi]
  ring

/-- **Every martingale law on the atoms is on the segment**: nonnegative
weights summing to one with the drift condition (in BRIEF_009's shape) make
`trinomialMeasure p₁ p₂ p₃` equal to `martingaleSegment p₁`. -/
theorem martingale_set_eq_segment (p₁ p₂ p₃ : ℝ) (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hdrift : ∫ s, id s ∂(trinomialMeasure p₁ p₂ p₃ witnessSpotLo witnessSpotMid witnessSpotHi)
      = 1 * Real.exp ((0 - 0) * 1)) :
    trinomialMeasure p₁ p₂ p₃ witnessSpotLo witnessSpotMid witnessSpotHi = martingaleSegment p₁ := by
  rw [trinomial_witness_drift p₁ p₂ p₃ h₁ h₂ h₃] at hdrift
  -- `1 * exp ((0 - 0) * 1)` is `1`; normalize it away BEFORE linarith, whose
  -- denominator-cancelling step would `ring_nf` the exponential's argument on
  -- one side only and split the atom (CI run 36044790368).
  simp only [sub_self, zero_mul, Real.exp_zero, one_mul] at hdrift
  have hdrift' : p₁ / 2 + p₂ + 2 * p₃ = 1 := by linarith
  obtain ⟨h3, h2⟩ := martingale_set_param p₁ p₂ p₃ hsum hdrift'
  unfold martingaleSegment
  rw [h2, h3]

/-- **Membership in the martingale set**: for `p₁ ∈ [0, 2/3]` the point of the
segment is a probability measure satisfying the drift condition. -/
theorem martingale_set_mem (p₁ : ℝ) (h0 : 0 ≤ p₁) (h1 : p₁ ≤ 2 / 3) :
    IsProbabilityMeasure (martingaleSegment p₁) ∧
      ∫ s, id s ∂(martingaleSegment p₁) = 1 * Real.exp ((0 - 0) * 1) := by
  have h₂ : 0 ≤ 1 - 3 * p₁ / 2 := by linarith
  have h₃ : 0 ≤ p₁ / 2 := by linarith
  unfold martingaleSegment
  refine ⟨trinomialMeasure_isProbability _ _ _ _ _ _ h0 h₂ h₃ (by ring), ?_⟩
  rw [trinomial_witness_drift p₁ _ _ h0 h₂ h₃]
  simp only [sub_self, zero_mul, Real.exp_zero, one_mul]
  ring

/-- **The call along the segment is `p₁/2`**: only the up state pays, and its
weight is `p₃ = p₁/2`. -/
theorem martingale_set_call_eq (p₁ : ℝ) (h0 : 0 ≤ p₁) (h1 : p₁ ≤ 2 / 3) :
    modelFreeCall (martingaleSegment p₁) id 1 0 1 = p₁ / 2 := by
  have h₂ : 0 ≤ 1 - 3 * p₁ / 2 := by linarith
  have h₃ : 0 ≤ p₁ / 2 := by linarith
  unfold modelFreeCall martingaleSegment
  rw [trinomialMeasure_integral _ p₁ _ _ _ _ _ h0 h₂ h₃]
  simp only [id_eq]
  rw [witness_call_payoff_lo, witness_call_payoff_mid, witness_call_payoff_hi]
  norm_num

/-- **The segment is not a point**: two admissible parameters with distinct
laws (distinct because their prices `1/4 ≠ 1/8` differ). -/
theorem martingale_set_nondegenerate :
    ∃ p₁ p₁' : ℝ, p₁ ≠ p₁' ∧ (0 ≤ p₁ ∧ p₁ ≤ 2 / 3) ∧ (0 ≤ p₁' ∧ p₁' ≤ 2 / 3) ∧
      martingaleSegment p₁ ≠ martingaleSegment p₁' := by
  refine ⟨1 / 2, 1 / 4, by norm_num, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  intro h
  have hA := martingale_set_call_eq (1 / 2) (by norm_num) (by norm_num)
  have hB := martingale_set_call_eq (1 / 4) (by norm_num) (by norm_num)
  rw [h, hB] at hA
  norm_num at hA

/-- **The price range**: every value in `[0, 1/3]` is the call price at some
point of the segment -- the arbitrage-free interval on three atoms, attained. -/
theorem martingale_set_price_range (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1 / 3) :
    ∃ p₁ : ℝ, 0 ≤ p₁ ∧ p₁ ≤ 2 / 3 ∧ modelFreeCall (martingaleSegment p₁) id 1 0 1 = c :=
  ⟨2 * c, by linarith, by linarith,
    by rw [martingale_set_call_eq (2 * c) (by linarith) (by linarith)]; ring⟩

/-- **A is the point `p₁ = 1/2` of the segment.** -/
theorem witnessA_mem_segment : witnessMeasureA = martingaleSegment (1 / 2) := by
  unfold witnessMeasureA martingaleSegment
  congr 1 <;> norm_num

/-- **B is the point `p₁ = 1/4` of the segment.** -/
theorem witnessB_mem_segment : witnessMeasureB = martingaleSegment (1 / 4) := by
  unfold witnessMeasureB martingaleSegment
  congr 1 <;> norm_num

end BSM
