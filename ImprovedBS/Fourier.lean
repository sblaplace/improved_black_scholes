/-
  ImprovedBS.Fourier — BRIEF_005 / T6 sub-goal 2: absolute convergence of the
  tempered Carr–Madan contour.

  docs/03 §D1 states T6 ("the Fourier pricing kernel survives a wider
  increment law") as three provable sub-goals: (1) the alpha-stable moment
  obstruction, landed in ImprovedBS/Levy.lean (BRIEF_004); (2) ABSOLUTE
  CONVERGENCE of the Carr–Madan integrand on a contour strictly inside the
  moment strip, for a tempered-stable exponent — this module; (3) agreement
  with the risk-neutral expectation — future work.

  THE THEOREM, AND ITS TWO INDEPENDENT HALVES

  The Carr–Madan call value is, up to the provenance of the contour shift,

      V = e^{-rτ}/(2π) · ∫_ℝ e^{-iuτ} · φ(u + iα) / (α² + α − u² + i(2α+1)u) du

  with `φ(v) = E[exp (i v X_τ)]` the analytic continuation of the log-price's
  characteristic function at a fixed maturity (the model's `exp (τ ψ)` is
  already inside `φ`), and `0 < α` the damping that keeps the strike
  transform finite. Absolute integrability of that integrand is the product
  of two facts of different kind:

  * PAYOFF SIDE (exact, this module's `cmDenom_u4_le`): a polynomial identity,

        (α² + α − u²)² + ((2α+1)u)² = u⁴ + (2α² + 2α + 1) · u² + (α² + α)²,

    so the denominator's modulus is at least `u²`, its inverse at most `1/u²`
    (stated multiplicatively as `u²‖denom(u)⁻¹‖ ≤ 1`), and for `0 < α` it has
    no zero on ℝ (the constant term `(α·(α+1))² > 0`). There is no asymptotics
    anywhere: it is a `ring` identity plus positivity of two coefficients.
  * MODEL SIDE (`integrable_exp_neg_abs_rpow`): the two-sided tempered tail
    `u ↦ exp (−c·|u|^Y)` is integrable for every `0 < c` and every `0 < Y`.
    Tempering buys exactly this: the value is `2·c^{−1/Y}·Γ(1/Y + 1)` (mathlib
    computes the one-sided value), and the regime boundary is `Y = 0`, where
    the integrand is a positive constant and the integral diverges — which is
    the analysis-side form of "the moment strip is nonempty only because the
    tempered index is positive".

  The join is a domination argument: on a compact window the integrand is
  bounded by continuity, off the window the tempered decay of `φ` dominates
  the `1/u²` from the payoff side.

  HYPOTHESIS DISCIPLINE (same posture as BRIEF_004)

  mathlib v4.34.0 has NO tempered-stable (CGMY) law — exactly as it has no
  symmetric alpha-stable law. BRIEF_004 answered by taking the power tail as
  a hypothesis and saying so; the same applies here one analytic layer up.

  * MACHINE-CHECKED: if `φ` is continuous along the contour `u ↦ u + iα` and
    satisfies the tempered decay `‖φ(u + iα)‖ ≤ D · exp (−c·|u|^Y)` there,
    then the pricing kernel is integrable (`carrMadanKernel_integrable`), and
    the dressed pricing integrand (phase `e^{iuτ}`, discount, `1/(2π)`) is
    integrable (`carrMadan_price_integrable`).
  * THE WITNESSING INSTANCE, MACHINE-CHECKED: the GBM model factor
    `gbmCharFactor m s v = exp (i·m·v − s·v²)` (with `m = (r−q−σ²/2)τ` and
    `s = σ²τ/2`) satisfies the hypothesis with `Y = 2` — its contour modulus is
    exactly `exp (sα² − αm) · exp (−s·u²)` (`gbmCharFactor_contour_norm`) — so
    the classical Fourier-pricing kernel is integrable in this repository as a
    theorem (`gbm_carrMadanKernel_integrable`), not as literature.
  * NOT MACHINE-CHECKED (hypothesis, cited): that the CGMY characteristic
    function `exp (τ·C·Γ(−Y)·[(M−iv)^Y − M^Y + (G+iv)^Y − G^Y] + iv·drift)`
    satisfies the tempered bound with its own `Y` on contours inside the
    strip. That is the genuinely hard analytic layer — complex `cpow`, branch
    control, asymptotics — and it is the next sub-goal. Nothing here asserts
    it; it enters only as the hypothesis `hdecay`.

  Numerical route-checks for both halves were run before any Lean and are
  recorded in briefs/BRIEF_005_t6_tempered_contour.md (ledger C4's rule:
  break the route on numbers first). Every mathlib name in this file is now
  verified at the pinned tag v4.34.0 — the first CI run caught four renamings
  left over from offline authoring (`Complex.abs`/`abs_exp` → `Complex.norm_exp`,
  `Set.indicator_of_not_mem` → `indicator_of_notMem`, lowercase
  `integrableOn_univ`, `Real.continuous_rpow_const`), and all call sites use
  the tag-verified spellings.

  Authored without a local Lean toolchain, under the same discipline as
  BRIEF_004: every mathlib name used below was checked against the pinned tag
  v4.34.0 (the file it lives in is recorded in the brief), and what could not
  be checked offline is isolated as noted.
-/

-- `import Mathlib` deliberately, matching ImprovedBS/Core.lean and
-- ImprovedBS/Levy.lean: narrow imports can only be validated with a
-- toolchain, and this tree is authored in environments that have none.
import Mathlib

noncomputable section

namespace BSM

open MeasureTheory Filter
open scoped ENNReal Topology

/-!
--------------------------------------------------------------------------
§1  The tempered tail: `∫_ℝ exp (−c·|u|^Y) du < ∞` for `0 < c`, `0 < Y`
--------------------------------------------------------------------------

This is the model-side integrability theorem. Mathlib v4.34.0 already computes
the one-sided VALUE (`Mathlib/MeasureTheory/Integral/Gamma.lean`:
`integral_exp_neg_mul_rpow`, `= b ^ (−1/p) · Γ(1/p + 1)`), and already
produces the one-sided integrability statement
(`integrableOn_rpow_mul_exp_neg_mul_rpow` in
`Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`). What is
needed here is the two-sided statement; the proof is the evenness argument,
and its shape is copied directly from mathlib's own
`integrable_rpow_mul_exp_neg_mul_sq` in that file: split at 0, transport the
left half across the negation isometry, dominate.
-/

/-- **The two-sided tempered tail is integrable** for every `0 < c` and every
`0 < Y`. This is what tempering buys: the Gaussian case is `Y = 2`, the
tempered-stable range is `Y ∈ (0, 2)`, and every positive index works — while
`Y = 0` is a positive constant integrand and diverges, the analysis-side form
of "the moment strip is nonempty only because the tempered index is positive".
-/
theorem integrable_exp_neg_abs_rpow {c Y : ℝ} (hc : 0 < c) (hY : 0 < Y) :
    Integrable fun u : ℝ => Real.exp (-c * |u| ^ Y) := by
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-c * x ^ Y)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := Y) (s := 0) (b := c)
      neg_one_lt_zero hY hc
    simpa using h
  have hmeas : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi
  have hcont : Continuous fun u : ℝ => Real.exp (-c * |u| ^ Y) :=
    Real.continuous_exp.comp
      (continuous_const.mul ((Real.continuous_rpow_const hY.le).comp continuous_abs))
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, ?_⟩
  · -- the left half-line: transport the right one across `u ↦ −u`
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_Iio, neg_zero, abs_neg]
    refine Integrable.mono' hbase (hcont.measurable.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hmeas] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (le_of_lt hx)]
    exact le_refl _
  · -- the right half-line, up to a null boundary point
    refine Integrable.mono' hbase (hcont.measurable.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hmeas] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (le_of_lt hx)]
    exact le_refl _

/-!
--------------------------------------------------------------------------
§2  The Carr–Madan denominator: an exact quartic lower bound
--------------------------------------------------------------------------
-/

/-- The dampened call's strike-transform denominator,
`α² + α − u² + i(2α+1)u`, written so `Complex.norm_add_mul_I` applies. -/
def cmDenom (α u : ℝ) : ℂ :=
  ↑(α ^ 2 + α - u ^ 2) + ↑((2 * α + 1) * u) * Complex.I

/-- The expansion at the heart of the payoff side: an exact polynomial
identity, `≥ u⁴` with both lower coefficients non-negative. Numerically
route-checked on 2·10⁵ random inputs before formalising (brief, scope item 2).
-/
theorem cmDenom_expand (α u : ℝ) :
    (α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2
      = u ^ 4 + (2 * α ^ 2 + 2 * α + 1) * u ^ 2 + (α ^ 2 + α) ^ 2 := by ring

theorem cmDenom_u4_le (α u : ℝ) :
    u ^ 4 ≤ (α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2 := by
  rw [cmDenom_expand]
  have hcoef : 0 ≤ 2 * α ^ 2 + 2 * α + 1 := by
    nlinarith [sq_nonneg α, sq_nonneg (α + 1)]
  have hmid : 0 ≤ (2 * α ^ 2 + 2 * α + 1) * u ^ 2 := mul_nonneg hcoef (sq_nonneg u)
  have h4 : 0 ≤ u ^ 4 := by positivity
  have hconst := sq_nonneg (α ^ 2 + α)
  linarith

/-- The same sum seen from the complex side: the denominator's modulus is the
square root of it. -/
theorem cmDenom_norm (α u : ℝ) :
    ‖cmDenom α u‖ = Real.sqrt ((α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2) := by
  unfold cmDenom
  exact Complex.norm_add_mul_I (α ^ 2 + α - u ^ 2) ((2 * α + 1) * u)

theorem cmDenom_sq_pos (α : ℝ) (hα : 0 < α) (u : ℝ) :
    0 < (α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2 := by
  rw [cmDenom_expand]
  have hconst : 0 < (α ^ 2 + α) ^ 2 := by
    have h : 0 < α * (α + 1) := mul_pos hα (by linarith)
    have hx : α ^ 2 + α = α * (α + 1) := by ring
    rw [hx]; positivity
  have hcoef : 0 ≤ 2 * α ^ 2 + 2 * α + 1 := by
    nlinarith [sq_nonneg α, sq_nonneg (α + 1)]
  have hmid : 0 ≤ (2 * α ^ 2 + 2 * α + 1) * u ^ 2 := mul_nonneg hcoef (sq_nonneg u)
  have h4 : 0 ≤ u ^ 4 := by positivity
  linarith

/-- For `0 < α` the denominator has no zero on the real contour: at `u = 0` the
constant term `(α·(α+1))²` is positive, and at `u ≠ 0` the quartic term is. -/
theorem cmDenom_ne_zero (α : ℝ) (hα : 0 < α) (u : ℝ) : cmDenom α u ≠ 0 := by
  intro hz
  have hnormsq : ‖cmDenom α u‖ ^ 2
      = (α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2 := by
    rw [cmDenom_norm]
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hz0 : ‖cmDenom α u‖ = 0 := by rw [hz, norm_zero]
  have hsum : (α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2 = 0 := by
    rw [← hnormsq, hz0]; norm_num
  exact ne_of_gt (cmDenom_sq_pos α hα u) hsum

theorem cmDenom_continuous (α : ℝ) : Continuous fun u : ℝ => cmDenom α u := by
  unfold cmDenom
  continuity

/-- The `1/u²` decay of the inverse denominator, in the multiplicative form
this module actually uses: `u² · ‖denom(u)⁻¹‖ ≤ 1` for `1 ≤ |u|`.
Stated without reciprocals of order-theoretic lemmas so that every step is a
core `mul_le_mul` fact. -/
theorem cmDenom_inv_norm_mul_sq_le (α : ℝ) (hα : 0 < α) {u : ℝ} (hu : 1 ≤ |u|) :
    u ^ 2 * ‖(cmDenom α u)⁻¹‖ ≤ 1 := by
  have hne := cmDenom_ne_zero α hα u
  have hnormpos : 0 < ‖cmDenom α u‖ := norm_pos_iff.mpr hne
  have hsq : u ^ 2 ≤ ‖cmDenom α u‖ := by
    rw [cmDenom_norm]
    have h4 : (u ^ 2) ^ 2 ≤ (α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2 := by
      have h : (u ^ 2) ^ 2 = u ^ 4 := by ring
      rw [h]; exact cmDenom_u4_le α u
    calc u ^ 2 = Real.sqrt ((u ^ 2) ^ 2) := (Real.sqrt_sq (sq_nonneg u)).symm
      _ ≤ Real.sqrt ((α ^ 2 + α - u ^ 2) ^ 2 + ((2 * α + 1) * u) ^ 2) :=
        Real.sqrt_le_sqrt h4
  have hinv_nonneg : 0 ≤ ‖cmDenom α u‖⁻¹ := inv_nonneg.mpr hnormpos.le
  calc u ^ 2 * ‖(cmDenom α u)⁻¹‖ = u ^ 2 * ‖cmDenom α u‖⁻¹ := by rw [norm_inv]
    _ ≤ ‖cmDenom α u‖ * ‖cmDenom α u‖⁻¹ := mul_le_mul_of_nonneg_right hsq hinv_nonneg
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hnormpos)

/-!
--------------------------------------------------------------------------
§3  The kernel and its absolute integrability under tempered decay
--------------------------------------------------------------------------
-/

/-- The Carr–Madan pricing kernel on the contour `v = u + iα`: the model
factor `φ` (the log-price characteristic function at a fixed maturity, times
whatever real discount prefactors one keeps inside it) divided by the
strike-transform denominator. -/
def carrMadanKernel (φ : ℂ → ℂ) (α : ℝ) (u : ℝ) : ℂ :=
  φ (↑u + ↑α * Complex.I) * (cmDenom α u)⁻¹

theorem carrMadanKernel_continuous {φ : ℂ → ℂ} {α : ℝ} (hα : 0 < α)
    (hcont : Continuous fun u : ℝ => φ (↑u + ↑α * Complex.I)) :
    Continuous fun u : ℝ => carrMadanKernel φ α u := by
  unfold carrMadanKernel
  exact hcont.mul ((cmDenom_continuous α).inv₀ fun u => cmDenom_ne_zero α hα u)

/-- **Absolute convergence of the tempered contour (T6 sub-goal 2).**
If the model factor is continuous on the contour and satisfies the tempered
decay `‖φ(u + iα)‖ ≤ D · exp (−c·|u|^Y)` for `|u| ≥ u₀` with `0 < c`, `0 < Y`,
then the Carr–Madan kernel is integrable on ℝ.

The hypothesis is stated for a general `φ` on purpose — see the module header
for the hypothesis discipline and for what is NOT machine-checked. -/
theorem carrMadanKernel_integrable {φ : ℂ → ℂ} {α : ℝ} (hα : 0 < α)
    (hcont : Continuous fun u : ℝ => φ (↑u + ↑α * Complex.I))
    {c D Y : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) {u₀ : ℝ}
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| →
      ‖φ (↑u + ↑α * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y)) :
    Integrable (carrMadanKernel φ α) volume := by
  -- the compact window and a bound for the kernel on it
  obtain ⟨B, hB⟩ := IsCompact.bddAbove
    (isCompact_Icc.image
      (Continuous.norm (carrMadanKernel_continuous hα hcont)))
  have humem₀ : (0 : ℝ) ∈ Set.Icc (-(max u₀ 1)) (max u₀ 1) := by
    rw [Set.mem_Icc]
    refine ⟨by linarith [le_max_right u₀ (1 : ℝ)], by linarith [le_max_right u₀ (1 : ℝ)]⟩
  have hBnonneg : 0 ≤ B :=
    le_trans (norm_nonneg _)
      (hB ⟨(0 : ℝ), humem₀, rfl⟩)
  -- the dominating function: the window constant plus the global tempered tail
  -- (`integrableOn_const`'s auto-discharge tactics go into a depth-limit loop
  -- on this goal in CI, so both side-conditions are proved here explicitly,
  -- with names verified at the pinned tag)
  have hvol : volume (Set.Icc (-(max u₀ 1)) (max u₀ 1)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hCe : ‖B‖ₑ ≠ ⊤ := by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top
  have hwin_int : Integrable ((Set.Icc (-(max u₀ 1)) (max u₀ 1)).indicator fun _ : ℝ => B) :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (hs := hvol) (hC := hCe)) measurableSet_Icc
  have htail_int : Integrable fun u : ℝ => D * Real.exp (-c * |u| ^ Y) :=
    (integrable_exp_neg_abs_rpow hc hY).const_mul D
  have hg_int : Integrable
      (fun u : ℝ => (Set.Icc (-(max u₀ 1)) (max u₀ 1)).indicator (fun _ : ℝ => B) u
        + D * Real.exp (-c * |u| ^ Y)) volume :=
    hwin_int.add htail_int
  -- the pointwise domination
  have hbound : ∀ u : ℝ, ‖carrMadanKernel φ α u‖ ≤
      (Set.Icc (-(max u₀ 1)) (max u₀ 1)).indicator (fun _ : ℝ => B) u
        + D * Real.exp (-c * |u| ^ Y) := by
    intro u
    have htail_nn : 0 ≤ D * Real.exp (-c * |u| ^ Y) := mul_nonneg hD (Real.exp_pos _).le
    by_cases huW : |u| ≤ max u₀ 1
    · -- inside the window: bounded by continuity on the compact interval
      have humem : u ∈ Set.Icc (-(max u₀ 1)) (max u₀ 1) := by
        rw [Set.mem_Icc]; exact abs_le.mp huW
      rw [Set.indicator_of_mem humem]
      calc ‖carrMadanKernel φ α u‖ ≤ B := hB ⟨u, humem, rfl⟩
        _ ≤ B + D * Real.exp (-c * |u| ^ Y) := le_add_of_nonneg_right htail_nn
    · -- outside: tempered decay dominates the `1/u²` from the payoff side
      push_neg at huW
      have humem : u ∉ Set.Icc (-(max u₀ 1)) (max u₀ 1) := by
        rw [Set.mem_Icc]
        rintro ⟨-, h2⟩
        exact not_le.mpr huW h2
      rw [Set.indicator_of_notMem humem, zero_add]
      have hu₀ : u₀ ≤ |u| := le_trans (le_max_left _ _) huW.le
      have h1 : (1 : ℝ) ≤ |u| := le_trans (le_max_right _ _) huW.le
      have hu2 : (1 : ℝ) ≤ u ^ 2 := by
        have h : (1 : ℝ) * 1 ≤ |u| * |u| :=
          mul_le_mul h1 h1 (by norm_num) (abs_nonneg u)
        rw [one_mul, ← pow_two, sq_abs] at h
        exact h
      calc ‖carrMadanKernel φ α u‖
          ≤ ‖carrMadanKernel φ α u‖ * u ^ 2 := le_mul_of_one_le_right (norm_nonneg _) hu2
        _ = ‖φ (↑u + ↑α * Complex.I) * (cmDenom α u)⁻¹‖ * u ^ 2 := rfl
        _ = ‖φ (↑u + ↑α * Complex.I)‖ * (‖(cmDenom α u)⁻¹‖ * u ^ 2) := by
            rw [norm_mul, mul_assoc]
        _ ≤ ‖φ (↑u + ↑α * Complex.I)‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (by rw [mul_comm]; exact cmDenom_inv_norm_mul_sq_le α hα h1) (norm_nonneg _)
        _ = ‖φ (↑u + ↑α * Complex.I)‖ := mul_one _
        _ ≤ D * Real.exp (-c * |u| ^ Y) := hdecay u hu₀
  refine hg_int.mono'
    (carrMadanKernel_continuous hα hcont).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have hind_nn : 0 ≤ (Set.Icc (-(max u₀ 1)) (max u₀ 1)).indicator (fun _ : ℝ => B) u := by
    by_cases hm : u ∈ Set.Icc (-(max u₀ 1)) (max u₀ 1)
    · rw [Set.indicator_of_mem hm]; exact hBnonneg
    · rw [Set.indicator_of_notMem hm]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg hind_nn (mul_nonneg hD (Real.exp_pos _).le))]
  exact hbound u

/-- The oscillatory phase `e^{i u τ}` of the pricing integral. Its modulus is
one, so dressing the kernel with it never affects absolute convergence. -/
def carrMadanPhase (tau u : ℝ) : ℂ := Complex.exp (Complex.I * ↑(u * tau))

/-- The modulus of a complex exponential is the real exponential of the real
part — at mathlib v4.34.0 that is `Complex.norm_exp`, from
`Mathlib/Analysis/Complex/Trigonometric.lean` (`Complex.abs` does not exist at
the tag; the norm spelling is the only one). The phase form
`‖exp (I * ↑x)‖ = 1` is `Complex.norm_exp_I_mul_ofReal`, used directly. -/
theorem carrMadanPhase_norm (tau u : ℝ) : ‖carrMadanPhase tau u‖ = 1 := by
  unfold carrMadanPhase
  exact Complex.norm_exp_I_mul_ofReal (u * tau)

/-- The full dressed pricing integrand — phase, discount factor, `1/(2π)` —
is integrable whenever the kernel is. The phase contributes only a modulus-1
multiplier (`Integrable.bdd_mul`), the real prefactor is a scalar
(`Integrable.smul`). -/
theorem carrMadan_price_integrable {φ : ℂ → ℂ} {α : ℝ} (hα : 0 < α)
    (hcont : Continuous fun u : ℝ => φ (↑u + ↑α * Complex.I))
    {c D Y : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) {u₀ : ℝ}
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| →
      ‖φ (↑u + ↑α * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (r tau : ℝ) :
    Integrable (fun u : ℝ => ((Real.exp (-r * tau) / (2 * Real.pi) : ℝ) : ℂ) •
      (carrMadanPhase tau u * carrMadanKernel φ α u)) volume := by
  refine Integrable.smul ((Real.exp (-r * tau) / (2 * Real.pi) : ℝ) : ℂ)
    ((carrMadanKernel_integrable hα hcont hc hD hY hdecay).bdd_mul ?_ ?_)
  · have hphase_cont : Continuous fun u : ℝ => carrMadanPhase tau u := by
      unfold carrMadanPhase
      continuity
    exact hphase_cont.measurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u =>
      le_of_eq (carrMadanPhase_norm tau u)

/-!
--------------------------------------------------------------------------
§4  The witnessing instance: GBM is tempered with `Y = 2`
--------------------------------------------------------------------------

The classical Black–Scholes–Merton log-price factor
`exp (i·m·v − s·v²)` (`m = (r−q−σ²/2)τ`, `s = σ²τ/2 > 0`) satisfies the
decay hypothesis EXACTLY: on the contour `v = u + iα` the exponent's real part
is `s·α² − α·m − s·u²`. So the pricing kernel is integrable by §3, with no
hypothesis left open — the Gaussian case is the one the theory already knows,
and it is the one the machine checks first.
-/

/-- The continued GBM model factor: `v ↦ exp (i·m·v − s·v²)`, with `s` the
half-variance rate `σ²τ/2` and `m` the log-drift per unit time times `τ`. -/
def gbmCharFactor (m s : ℝ) (v : ℂ) : ℂ :=
  Complex.exp (Complex.I * ↑m * v - ↑s * v ^ 2)

/-- The contour modulus. On the contour `v = u + iα`, the exponent's real part
is `s·α² − α·m − s·u²`, so `Complex.norm_exp` gives the modulus EXACTLY — the
tempered hypothesis will be met with equality, `Y = 2`, `c = s`,
`D = exp (s·α² − α·m)`. -/
theorem gbmCharFactor_contour_norm (m s u α : ℝ) :
    ‖gbmCharFactor m s (↑u + ↑α * Complex.I)‖
      = Real.exp (s * α ^ 2 - α * m) * Real.exp (-(s * u ^ 2)) := by
  have hre : (Complex.I * ↑m * (↑u + ↑α * Complex.I)
        - ↑s * (↑u + ↑α * Complex.I) ^ 2).re = s * α ^ 2 - α * m - s * u ^ 2 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
      Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, pow_two]
    ring
  unfold gbmCharFactor
  rw [Complex.norm_exp, hre, ← Real.exp_add]
  congr 1
  ring

theorem gbmCharFactor_contour_continuous (m s α : ℝ) :
    Continuous fun u : ℝ => gbmCharFactor m s (↑u + ↑α * Complex.I) := by
  unfold gbmCharFactor
  continuity

/-- **The GBM Carr–Madan kernel is integrable.** The tempered hypothesis is
met with `Y = 2`, `c = s`, `D = exp (s·α² − α·m)`, `u₀ = 0` — the bound is
satisfied with equality by `gbmCharFactor_contour_norm`. -/
theorem gbm_carrMadanKernel_integrable (m s : ℝ) (hs : 0 < s) {α : ℝ}
    (hα : 0 < α) :
    Integrable (carrMadanKernel (gbmCharFactor m s) α) volume := by
  refine carrMadanKernel_integrable hα (gbmCharFactor_contour_continuous m s α)
    hs (Real.exp_pos _).le (Y := 2) (by norm_num) (u₀ := 0) ?_
  intro u _
  rw [gbmCharFactor_contour_norm, Real.rpow_two, sq_abs, neg_mul]
  exact le_refl _

/-- The dressed GBM pricing integrand: phase, discount, `1/(2π)`. -/
theorem gbm_carrMadan_price_integrable (m s : ℝ) (hs : 0 < s) {α : ℝ}
    (hα : 0 < α) (r tau : ℝ) :
    Integrable (fun u : ℝ => ((Real.exp (-r * tau) / (2 * Real.pi) : ℝ) : ℂ) •
      (carrMadanPhase tau u * carrMadanKernel (gbmCharFactor m s) α u)) volume := by
  refine carrMadan_price_integrable hα (gbmCharFactor_contour_continuous m s α)
    hs (Real.exp_pos _).le (Y := 2) (by norm_num) (u₀ := 0) ?_ r tau
  intro u _
  rw [gbmCharFactor_contour_norm, Real.rpow_two, sq_abs, neg_mul]
  exact le_refl _

end BSM
