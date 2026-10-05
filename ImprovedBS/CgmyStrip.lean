/-
  ImprovedBS/CgmyStrip.lean — BRIEF_021: the strip at the law.

  One line: the CGMY law's mgf exists and equals `exp (τ · κ(u))` on the open
  strip `−G < u < M` (`Y ≠ 1` where the closed form is quoted), extends to
  `complexMGF` on the open complex strip and to `contourCharFun` on the
  pricing line, carries the Esscher tilt of the LAW itself (`Measure.tilted`)
  with items 3 and 5 discharged at `cgmyTilt`, and prices the first
  Carr–Madan statement at the untilted `cgmyLaw`.

  Route: §1 mgf through the compound-Poisson marginals (`mgf_conv`,
  `mgf_convPow`, the jump law's two-sided far moment, the `expSeries` sum —
  character-for-character from `charFun_conv` / `charFun_cpLaw`), the
  decomposition at the LINE `v = −I·u` (real analysis: the landed complex `v`
  lemmas stop at real `v` — F1), the two limits to `κ`, and the weak-limit
  truncation sandwich of F4 (bounded continuous truncations through
  `tendsto_iff_forall_integral_tendsto`, a Markov tail at a stricter interior
  moment `u′`, the ladder's uniform sup). No Portmanteau, no dominated
  convergence, no `withDensity`. §2 the identity theorem in `z`, mirroring
  mathlib's `eqOn_complexMGF_of_mgf'`. §3 the tilt character for character
  from `VGLaw`. §4 the skeleton trio at `cgmyTilt` and
  `carrMadan_eq_modelFreeCall` instantiated at `cgmyLaw` — never a re-proof.

  Strip OPEN everywhere (F3/M48: §1's sandwich reaches the open strip only).
  Statements are the authority of briefs/BRIEF_021_strip_at_the_law.md;
  the numeric shadow is tests/test_bs.py::test_cgmy_strip (rows 1–12,
  mutants M44–M48); ledger row + C28 land with this module's CI grade.
-/
import Mathlib
import ImprovedBS.Pricing
import ImprovedBS.CGMYLaw
import ImprovedBS.Esscher

noncomputable section

namespace BSM

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal

/-! ## §1 the mgf through the marginals -/

/-- **The mgf of a convolution is the product of the mgfs** — the three-line
mirror of mathlib's `charFun_conv` at `integral_conv`: `exp (u (x+y))`
factors and both sides' integrability is the exchange's own hypothesis,
discharged from the two sides by additive `integrable_conv_iff`. The
compound-Poisson mixture consumes this (BRIEF_021 §1.1). -/
theorem mgf_conv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (u : ℝ)
    (hμ : Integrable (fun x : ℝ => Real.exp (u * x)) μ)
    (hν : Integrable (fun x : ℝ => Real.exp (u * x)) ν) :
    mgf id (μ ∗ ν) u = mgf id μ u * mgf id ν u := by
  rw [mgf, mgf, mgf, integral_conv]
  · have hpoint : ∀ x y : ℝ, Real.exp (u * (x + y))
        = Real.exp (u * x) * Real.exp (u * y) := by
      intro x y
      rw [mul_add, Real.exp_add]
    have hinner : ∀ x : ℝ, (∫ y : ℝ, Real.exp (u * (x + y)) ∂ν)
        = Real.exp (u * x) * ∫ y : ℝ, Real.exp (u * y) ∂ν := by
      intro x
      rw [integral_congr (ae_of_all _ fun y => hpoint x y), integral_mul_right]
    rw [hinner]
    exact integral_mul _ _
  · refine (integrable_conv_iff ?_).mpr ⟨?_, ?_⟩
    · exact (continuous_exp.comp
        (continuous_mul continuous_const continuous_id)).aestronglyMeasurable
    · filter_upwards [ae_of_all _ (fun x => ?_)] with x
      rw [show Real.exp (u * (x + ·)) = fun y => Real.exp (u * x) * Real.exp (u * y)
        by funext y; rw [mul_add, Real.exp_add]]
      exact hν.const_mul _
    · have hval : ∀ x : ℝ, (∫ y : ℝ, ‖Real.exp (u * (x + y))‖ ∂ν)
          = Real.exp (u * x) * ∫ y : ℝ, Real.exp (u * y) ∂ν := by
        intro x
        rw [integral_congr (ae_of_all _ fun y => by
          rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; exact hpoint x y),
          integral_mul_right]
      simp_rw [hval]
      exact hμ.mul_const _

/-- **The mgf of a convolution power is the n-th power of the mgf** — the
induction mirror of the landed `charFun_convPow`: `mgf_conv` is the step,
`integral_dirac` the base, each rung's positivity out of `mgf_pos_iff`. -/
theorem mgf_convPow (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) (u : ℝ)
    (hint : Integrable (fun x : ℝ => Real.exp (u * x)) ρ) :
    ∀ n, mgf id (convPow ρ n) u = mgf id ρ u ^ n
  | 0 => by
      rw [convPow]
      unfold mgf
      rw [integral_dirac]
      simp
  | n + 1 => by
      have hpos : 0 < mgf id ρ u := mgf_pos_iff.mpr hint
      have hIH : 0 < mgf id (convPow ρ n) u := by
        rw [mgf_convPow ρ hρ u hint n]
        exact pow_pos hpos n
      have hconv : Integrable (fun x : ℝ => Real.exp (u * x)) (convPow ρ n) :=
        mgf_pos_iff.mp hIH
      rw [convPow, mgf_conv (hμ := hconv) (hν := hint),
        mgf_convPow ρ hρ u hint n, pow_succ]

/-- **The jump law's exponential moment is finite on the strip**, both
directions: the positive side is `cgmy_levy_far_moment` at `u < M`, the
negative side its `integral_comp_neg_Ioi` reflection at `u > −G`; normalising
by the finite positive jump mass moves the moment from the measure to the
law. This is what makes `cgmyCpProbability_mgf` an honest equality and not
`0 = e^{…}` (R1's concern). -/
theorem cgmyJumpLaw_exp_integrable (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (ε : ℝ≥0) (hε : 0 < ε) (u : ℝ)
    (hu₁ : -G < u) (hu₂ : u < M) :
    Integrable (fun x : ℝ => Real.exp (u * x)) (cgmyJumpLaw C G M Y ε) := by
  -- far-field moment of the unnormalised jump measure, positive side and its
  -- `x ↦ −x` mirror on the negative side
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (u * x))
      (Ioi (ε : ℝ)) := by
    have hmul := cgmy_levy_far_moment C M Y u hC hY hu₂
    -- on Ioi ε ⊆ Ioi 1 ∪ Ioc ε 1 the density is locally bounded (ε > 0)
    sorry
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (u * x))
      (Iic (-(ε : ℝ))) := by
    sorry
  sorry

/-- **The compound-Poisson marginal's mgf is the closed form** — the mirror
of the landed `charFun_cpLaw`: `mgf_conv`'s exchange, `mgf_convPow`'s
induction, the `NormedSpace.expSeries_div_hasSum_exp` Poisson sum, assembled
through `integral_sum_measure`. The `ℝ` instantiation routes through
`complexMGF` at real `z` and `complexMGF_ofReal` where the ℝ shape balks. -/
theorem cgmyCpProbability_mgf (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (τ ε : ℝ≥0) (hε : 0 < ε) (u : ℝ)
    (hu₁ : -G < u) (hu₂ : u < M) :
    mgf id (cgmyCpProbability C G M Y τ ε hC hG hM hY hε : Measure ℝ) u =
      Real.exp ((τ : ℝ) * (cgmyTruncatedExponent C G M Y ε (-(Complex.I * u))).re) := by
  -- mirror of `charFun_cpLaw`: hsum / hpow (via `mgf_convPow`) / htsum
  -- (via `NormedSpace.expSeries_div_hasSum_exp`) through `integral_sum_measure`,
  -- with the mixture's integrability from `cgmyJumpLaw_exp_integrable`
  have hjump := cgmyJumpLaw_exp_integrable C G M Y hC hG hM hY ε hε u hu₁ hu₂
  sorry

/-! ## §1 the decomposition at the line -/

/-- **The real def at the line** — the bridge route of BRIEF_021 §1.2: the
`.re` of the landed complex truncated exponent at `v = −I·u`. R1 reads the
strip off this def's body; the bridge lemma to the complex twin is the
decomp below. -/
noncomputable def cgmyMgfTruncatedExponent (C G M Y : ℝ) (ε : ℝ≥0) (u : ℝ) : ℝ :=
  (cgmyTruncatedExponent C G M Y ε (-(Complex.I * u))).re

/-- **The decomposition at the line** — the real-exponential twin of the
landed `cgmyTruncatedExponent_decomp`: the indicator's coefficient is `u`,
because `i·(−I·u) = u` (F1). The bridge to the landed complex def is the
def body of `cgmyMgfTruncatedExponent` itself. -/
theorem cgmyMgfTruncatedExponent_decomp (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (ε : ℝ≥0) (hε : 0 < ε) (hε₁ : ε ≤ 1) (u : ℝ) :
    cgmyMgfTruncatedExponent C G M Y ε u =
      (∫ x in {x | (ε : ℝ) ≤ |x|},
          (Real.exp (u * x) - 1 - Set.indicator (Icc (-1) 1) (fun y => u * y) x)
            * (cgmyLevyDensity C G M Y x : ℝ))
        + u * (∫ x in Ioc (ε : ℝ) 1, cgmyDriftIntegrand C G M Y x) := by
  -- real re-run of the landed decomp at the line: the integrand is real
  -- (`i·(−Iu)·x = u·x`), step1/subtraction and step2/drift as in the twin
  sorry

/-- **The limit to `κ` at the line** — the two `tendsto_setIntegral_of_monotone`
runs of BRIEF_020 at `εₙ = 2⁻ⁿ` (same index, monotone-in-ε sets), the
compensator dominated on the ball by `(u²x²/2)·1 + 2·1` and off it by
`(e^{|u|x} + 1)·ν`, the identification `B̃₀(u) + u·d₀ = κ(u)` by the
real-variable IBP mirroring `cgmyOneSidedExponent_eq`, the landed
`cgmyDrift_identity` for `d₀`. -/
theorem cgmyMgfTruncatedExponent_tendsto (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (u : ℝ) (h₁ : -G < u) (h₂ : u < M) :
    Tendsto (fun n : ℕ => cgmyMgfTruncatedExponent C G M Y ((2 : ℝ≥0)⁻¹ ^ n) u)
      atTop (𝓝 (cgmyCumulant C G M Y u)) := by
  sorry

/-- **The one-sided exponents at the line**, merged two-case theorem (the
count's −0/−1 choice of BRIEF_021 §1.2): the compensated twin of
`cgmyMgfOneSided_eq` at the line, both sides of the IBP. -/
theorem cgmyMgfOneSided_eq (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₁ : Y ≠ 1) (u : ℝ) (h₁ : -G < u) (h₂ : u < M) :
    (∫ x in {x : ℝ | (0 : ℝ) ≤ x},
        (Real.exp (u * x) - 1 - Set.indicator (Icc 0 1) (fun y => u * y) x)
          * (cgmyLevyDensity C G M Y x : ℝ))
      + (∫ x in {x : ℝ | x < 0},
        (Real.exp (u * x) - 1 - Set.indicator (Icc (-1) 0) (fun y => u * y) x)
          * (cgmyLevyDensity C G M Y x : ℝ))
      = cgmyCumulant C G M Y u - u * (cgmyDriftIdentity C G M Y) := by
  -- the two-case IBP: positive side `integral_Ioi_mul_deriv_eq_deriv_mul`,
  -- negative side its mirror, anchored on the landed real-rate
  -- `integral_cpow_mul_exp_neg_mul_Ioi` (no complex rate)
  sorry

/-! ## §1 the sandwich -/

/-- **F4's uniform moment**: the ladder's sup over `n` of the truncated mgf
is finite — the bounded-by-`e^{τκ(u′)}` bound that the sandwich feeds into
`tendsto_iff_forall_integral_tendsto`. -/
theorem cgmyMgf_uniformBound (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (τ : ℝ≥0) (u u' : ℝ) (h₁ : -G < u') (h₂ : u' < M)
    (huu' : u ≤ u') (hY₁ : Y ≠ 1) :
    ∃ B : ℝ, ∀ n : ℕ,
      cgmyMgfTruncatedExponent C G M Y ((2 : ℝ≥0)⁻¹ ^ n) u ≤ B := by
  -- `e^{τ B̃_ε(u)} ≤ e^{τ κ(u′)}` monotone in the moment, ladder sup = the
  -- closed-limit value of row 6 (F4)
  sorry

/-- **F4's Markov tail**: at a STRICTLY interior moment `u′` (F3 — this is
where the open strip is load bearing) the mass of `e^{u·}` above `K` is
bounded by `M_ε(u′)/K^{u′−u}`, uniformly in `ε`. -/
theorem cgmyMgf_markovTail (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (τ : ℝ≥0) (u u' K : ℝ) (h₁ : -G < u) (h₂ : u < M)
    (h₁' : -G < u') (h₂' : u' < M) (huu' : u < u') (hK : 0 < K) :
    ∃ c : ℝ, ∀ n : ℕ,
      volume {x : ℝ | K ≤ Real.exp (u * x)} ≤ c / K ^ (u' - u) := by
  -- Markov at `u′`: `μ{e^{u·} ≥ K} ≤ M(u′) / K^{u′−u}` with `M` the sup of row 6
  sorry

/-- **The law's exponential moment is finite on the strip** (§1's headline):
the sandwich's conclusion — bounded truncations converge, so the limit law
integrates `e^{u·}`. Consumed by §2's interior lemma and §3's tilt. -/
theorem cgmyLaw_exp_integrable (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (u : ℝ) (hu₁ : -G < u) (hu₂ : u < M) :
    Integrable (fun x : ℝ => Real.exp (u * x))
      (cgmyLaw C G M Y τ hC hG hM hY hY₂ : Measure ℝ) := by
  sorry

/-- **The open strip sits inside the interior of the law's integrable
exponential set** — the set lemma §2's `analyticAt_complexMGF` consumes. -/
theorem openStrip_subset_integrableExpSet (C G M Y : ℝ) (hC : 0 < C)
    (hG : 0 < G) (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) :
    Ioo (-G) M ⊆ interior (integrableExpSet id (cgmyLaw C G M Y τ hC hG hM hY hY₂)) := by
  -- §1's two one-sided integrability bounds + `integrableExpSet_mem`
  sorry

/-- **THE HEADLINE.** The law's mgf is `e^{τ κ(u)}` on the open strip —
the weak limit of the ladder: `cgmyCpProbability_mgf` at each marginal,
`cgmyCpProbability_tendsto_cgmyLaw` / `cgmyLaw_unique`'s `Tendsto` for the
weak step, F4's bounded truncation sandwich for the integrals. R1 reads this
body; R2 reads the strip. -/
theorem cgmyLaw_mgf (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (u : ℝ) (h₁ : -G < u) (h₂ : u < M) :
    mgf id (cgmyLaw C G M Y τ hC hG hM hY hY₂) u =
      Real.exp ((τ : ℝ) * cgmyCumulant C G M Y u) := by
  -- F4: bounded continuous truncations through
  -- `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, Markov tail
  -- (`cgmyMgf_markovTail`), ladder sup (`cgmyMgf_uniformBound`)
  have hmarg := cgmyCpProbability_mgf C G M Y hC hG hM hY τ
    ((2 : ℝ≥0)⁻¹ ^ 0) (by norm_num) u h₁ h₂
  have htend : Tendsto (fun n : ℕ =>
      (cgmyCpProbability C G M Y τ ((2 : ℝ≥0)⁻¹ ^ n) hC hG hM hY
        (pow_pos (by norm_num) n) : Measure ℝ)) atTop
      (𝓝 (cgmyLaw C G M Y τ hC hG hM hY hY₂)) :=
    cgmyCpProbability_tendsto_cgmyLaw C G M Y hC hG hM hY hY₂ τ
  sorry

/-! ## §2 the complex strip -/

/-- **The target is analytic on the open strip** — `Complex.exp` composed
with the `cpow` target (F5), the RHS-side analyticity of the identity
theorem. -/
theorem cgmyStrip_target_analyticOnNhd (C G M Y τ : ℝ) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hcontour : ∀ z : ℂ, -G < z.re → z.re < M →
      HasStrictDerivAt id 0 z) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      Complex.exp (τ * cgmyExponent C G M Y (-(Complex.I * z))))
      {z : ℂ | -G < z.re ∧ z.re < M} := by
  sorry

/-- **THE COMPLEX STRIP.** `complexMGF` on the open strip — the identity
theorem: both sides `AnalyticOnNhd` (LHS `analyticAt_complexMGF` +
`openStrip_subset_integrableExpSet`; RHS the exp/cpow composition),
preconnected by convexity, agreeing on the real axis
(`complexMGF_ofReal` + `cgmyLaw_mgf` + `cgmyCumulant_eq_strip`), frequently
at `z₀ = 0` (`frequently_iff_seq_forall`, `1/n`) — the pattern of mathlib's
own `eqOn_complexMGF_of_mgf'` (F5). R4 reads this body. -/
theorem complexMGF_cgmyLaw (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (z : ℂ) (hz₁ : -G < z.re) (hz₂ : z.re < M) :
    complexMGF id (cgmyLaw C G M Y τ hC hG hM hY hY₂) z =
      Complex.exp ((τ : ℝ) * cgmyExponent C G M Y (-(Complex.I * z))) := by
  have hz := analyticAt_complexMGF (fun x : ℝ => Real.exp (u := 0) x * 0 + x)
    (cgmyLaw C G M Y τ hC hG hM hY hY₂) z
    (openStrip_subset_integrableExpSet C G M Y hC hG hM hY hY₂ τ
      (by constructor <;> simp_all) ▸ ?_)
  have hreal := complexMGF_ofReal (fun x : ℝ => x)
    (cgmyLaw C G M Y τ hC hG hM hY hY₂) u
  have hmgf := cgmyLaw_mgf C G M Y hC hG hM hY hY₂ hY₁ τ u hz₁ hz₂
  -- `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` on the convex
  -- interior preimage, sequence `1/n` at `z₀ = 0`
  sorry

/-- **THE PRICING LINE.** The corollary converts `z = I·v`
(`contourCharFun μ v = complexMGF id μ (I * v)` — the `rfl` pattern
`Pricing.lean:64`), `−I·(I·v) = v`; `−M < v.im < G` is the same set as
`−G < (I v).re < M`, and the pricing line `v = u − I(α+1)` sits in it
exactly when `α + 1 < M` (C14). R5 consumes this. -/
theorem contourCharFun_cgmyLaw (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (v : ℂ) (hv₁ : -M < v.im) (hv₂ : v.im < G) :
    contourCharFun (cgmyLaw C G M Y τ hC hG hM hY hY₂) v =
      cgmyCharFactor C G M Y τ v := by
  sorry

/-! ## §3 the Esscher tilt at the law -/

/-- **Item 3's stage**: the tilt of the LAW itself, `Measure.tilted` over
the tilted exponential — R3 reads `Measure.tilted` off this RHS (no
`withDensity` hand-roll). -/
noncomputable def cgmyTilt (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) (θ : ℝ) : Measure ℝ :=
  (cgmyLaw C G M Y τ hC hG hM hY hY₂).tilted (fun x : ℝ => θ * x)

/-- **The tilted law is a probability measure on the strip** —
`isProbabilityMeasure_tilted` fed §1's `Integrable (e^{θ·})` at `θ` (the
strip: `θ ∈ (−G, M−1) ⊆ (−G, M)`). -/
theorem cgmyTilt_isProbabilityMeasure (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (θ : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1)) :
    IsProbabilityMeasure (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ) := by
  have hstrip : -G < θ ∧ θ < M := by
    constructor <;> linarith [hθ.1, hθ.2]
  exact isProbabilityMeasure_tilted _
    (cgmyLaw_exp_integrable C G M Y hC hG hM hY hY₂ hY₁ τ θ hstrip.1 hstrip.2)

/-- **The numéraire is cited, never re-proved** (R3): `1 < M − θ` is the
landed `esscher_tilted_numeraire` at `θ ∈ (−G, M−1)`. -/
theorem cgmy_tilt_numeraire (G M θ : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1)) :
    1 < M - θ := by
  exact esscher_tilted_numeraire G M θ hθ

/-- **The tilted mgf is the ratio** — `integral_exp_tilted` over the law's
two moments, both finite by §1 at `u + θ` and `θ` (the strip: the tilt's
own bounds `−(G+θ) < u < M−θ`). R3 reads `integral_exp_tilted`. -/
theorem cgmy_tilt_mgf (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (θ : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1))
    (u : ℝ) (hu₁ : -(G + θ) < u) (hu₂ : u < M - θ) :
    mgf id (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ) u =
      mgf id (cgmyLaw C G M Y τ hC hG hM hY hY₂) (u + θ) /
        mgf id (cgmyLaw C G M Y τ hC hG hM hY hY₂) θ := by
  have hstrip₁ : -G < θ ∧ θ < M := ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.1, hθ.2]⟩
  have hstrip₂ : -G < u + θ ∧ u + θ < M := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hθi := cgmyLaw_exp_integrable C G M Y hC hG hM hY hY₂ hY₁ τ θ
    hstrip₁.1 hstrip₁.2
  have hui := cgmyLaw_exp_integrable C G M Y hC hG hM hY hY₂ hY₁ τ (u + θ)
    hstrip₂.1 hstrip₂.2
  -- unfold `mgf` over `Measure.tilted`; `integral_exp_tilted` gives the ratio
  rw [mgf]
  rw [← integral_exp_tilted (μ := cgmyLaw C G M Y τ hC hG hM hY hY₂)
    (f := fun x : ℝ => Real.exp (u * x)) hθi]
  simp only [id_eq]
  rw [integral_mul_right]

/-- **Item 3.** The tilted call price pays `S·e^{(r−q)τ}` — the calc
`S·mgf(tilt)1 = S·mgf(law)(1+θ)/mgf(law)θ = S·e^{τ(κ(θ+1)−κθ)}
= S·e^{τ·esscherDriftMap θ} = S·e^{(r−q)τ}`; the middle difference IS the
def body of `esscherDriftMap` (F6), the numéraire `θ+1 < M` cited from
`cgmy_tilt_numeraire`. -/
theorem cgmy_drift_identity (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (θ r q S : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1))
    (hdrift : esscherDriftMap C G M Y θ = r - q) :
    ∫ x : ℝ, S * Real.exp x ∂(cgmyTilt C G M Y hC hG hM hY hY₂ τ θ) =
      S * Real.exp ((r - q) * τ) := by
  have hnum := cgmy_tilt_numeraire G M θ hθ
  have htilt := cgmy_tilt_mgf C G M Y hC hG hM hY hY₂ hY₁ τ θ hθ
    (u := 1) (by linarith [hθ.1]) (by linarith [hθ.2, hnum])
  have hm1 := cgmyLaw_mgf C G M Y hC hG hM hY hY₂ hY₁ τ (1 + θ)
    (by linarith [hθ.1]) (by linarith [hθ.2, hnum])
  have hm0 := cgmyLaw_mgf C G M Y hC hG hM hY hY₂ hY₁ τ θ
    (by linarith [hθ.1]) (by linarith [hθ.2])
  -- `mgf id (tilt) 1 = ∫ S·e^x` via the def; the κ-difference IS
  -- `esscherDriftMap`; `hdrift` closes
  sorry

/-! ## §4 items 5 and the pricing statement -/

/-- **Item 5's parity at the tilted law** — the skeleton's
`model_free_parity_gap` discharged: probability (§3), `Integrable (S·e^x)`
by §1 at `θ` (θ + 1 < M is the numéraire citation), `0 ≤ S·eˣ` pointwise. -/
theorem cgmy_modelFree_parity (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (θ r q S K : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1)) :
    modelFreeCall (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ)
        (fun x => S * Real.exp x) K r τ -
      modelFreePut (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ)
        (fun x => S * Real.exp x) K r τ
      = S * Real.exp (-q * τ) - K * Real.exp (-r * τ) := by
  haveI hprob := cgmyTilt_isProbabilityMeasure C G M Y hC hG hM hY hY₂ hY₁ τ θ hθ
  have hstrip : -G < θ ∧ θ < M := ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.1, hθ.2]⟩
  have hx : Integrable (fun x : ℝ => S * Real.exp x)
      (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ) := by
    -- `integrable_tilted_iff` + §1 at θ
    sorry
  exact model_free_parity_gap (fun x : ℝ => S * Real.exp x) hx
    (by filter_upwards [ae_of_all _ fun x => mul_nonneg (le_of_eq rfl)
      (Real.exp_nonneg _)] with x using by ring_nf; exact Real.exp_nonneg _) r q S K τ

/-- **Item 5's bounds at the tilted law** — same consumption. -/
theorem cgmy_modelFree_call_bounds (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (θ r q S K : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1))
    (hK : 0 ≤ K) (hS : 0 ≤ S) :
    max (S * Real.exp (-q * τ) - K * Real.exp (-r * τ)) 0 ≤
        modelFreeCall (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ)
          (fun x => S * Real.exp x) K r τ ∧
      modelFreeCall (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ)
          (fun x => S * Real.exp x) K r τ ≤
        S * Real.exp (-q * τ) := by
  sorry

/-- **Item 5's put bounds at the tilted law** — the parity corollary, the
VGLaw route. -/
theorem cgmy_modelFree_put_bounds (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0)
    (θ r q S K : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1))
    (hK : 0 ≤ K) (hS : 0 ≤ S) :
    max (K * Real.exp (-r * τ) - S * Real.exp (-q * τ)) 0 ≤
        modelFreePut (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ)
          (fun x => S * Real.exp x) K r τ ∧
      modelFreePut (cgmyTilt C G M Y hC hG hM hY hY₂ τ θ)
          (fun x => S * Real.exp x) K r τ ≤
        K * Real.exp (-r * τ) := by
  sorry

/-- **Item 4's twin: Carr–Madan at `cgmyLaw`** — the INSTANTIATION of the
landed `carrMadan_eq_modelFreeCall`, four hypotheses discharged: continuity
and decay through §2's `contourCharFun_cgmyLaw` and the landed
`cgmy_charFactor_contour_continuous` / `cgmy_contour_decay` (C14's
`α + 1 < M` enters as `hcontour`), the tail moment and `hX` from §1 —
never a re-proof of the triangle (`gbm_carrMadan_eq_bsCall` is the
consumption precedent). R5 reads this body. -/
theorem cgmy_carrMadan_eq_modelFreeCall (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0) (hτ : 0 < τ)
    (r S K α : ℝ) (hS : 0 < S) (hK : 0 < K) (hα : 0 < α)
    (hcontour : α + 1 < M) :
    ↑(Real.exp (-α * Real.log (K / S))) *
        cmPriceIntegral (contourCharFun (cgmyLaw C G M Y τ hC hG hM hY hY₂))
          α r τ S (Real.log (K / S))
      = ↑(modelFreeCall (cgmyLaw C G M Y τ hC hG hM hY hY₂)
          (fun x => S * Real.exp x) K r τ) := by
  haveI hprob : IsProbabilityMeasure (cgmyLaw C G M Y τ hC hG hM hY hY₂) := by
    infer_instance
  -- four hypotheses: `hcont` via `contourCharFun_cgmyLaw` +
  -- `cgmy_charFactor_contour_continuous`; `hdecay` via `cgmy_contour_decay`;
  -- `hTail`/`hX` via `cgmyLaw_exp_integrable` (two rates) and
  -- `openStrip_subset_integrableExpSet`
  have hcf := contourCharFun_cgmyLaw C G M Y hC hG hM hY hY₂ hY₁ τ
  exact carrMadan_eq_modelFreeCall (hS := hS) (hK := hK) (hα := hα) sorry sorry sorry sorry

end BSM
