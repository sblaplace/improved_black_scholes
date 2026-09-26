/-
  ImprovedBS/CGMYLaw.lean — BRIEF_020: the CGMY law. The `ε ↓ 0` limit of
  BRIEF_019's truncated exponent, its tightness, its existence by Prokhorov +
  Lévy continuity, and the identification of its characteristic function with
  the tree's pricing factor. This is the second half of Stage 2.

  In one line: the compound-Poisson marginals of the truncated CGMY jump law
  converge weakly, along `εₙ = 2⁻ⁿ`, to a probability measure `cgmyLaw` whose
  characteristic function is `exp (τ · L(v))` with

      L(v) = ∫ (e^{ivx} − 1 − ivx·1_{|x|≤1}) ν(dx)  +  iv · C∫₀¹ x^{−Y}(e^{−Mx} − e^{−Gx}) dx

  the Lévy–Khintchine exponent of `cgmyLevyDensity` with the unit-ball
  compensator — and for `Y ≠ 1` that `L` *is* the landed `cgmyExponent`, so
  `cgmyCharFactor` is the characteristic function of a law in the tree.

  Three things make this a construction rather than a citation, and each has a
  measured numeric shadow in `tests/test_bs.py::test_cgmy_law`:

  * **The limit needs no dominated-convergence theorem** (F1, ledger C25). At
    every `ε > 0` the truncated exponent splits *exactly*,
    `A_ε = B_ε + iv·d_ε` (`cgmyTruncatedExponent_decomp`; measured `7.3e−15`
    over 18 rows), and each piece is dominated on all of `ℝ ∖ {0}`: the
    compensated integrand is `O(x^{1−Y})` at `0` for every `Y < 2`, and the
    *paired* drift integrand is `O(x^{1−Y})` because `e^{−Mx} − e^{−Gx} = O(x)`.
    So `ε ↓ 0` is two instances of `tendsto_setIntegral_of_monotone`, both at
    rate `ε^{2−Y}` (measured slopes `1.4996 / 0.9997 / 0.4998`). The drift is
    *not* zero — `d₀ = −1.641132` at `Y = 3/2` — and dropping it is mutant M40.
  * **The law is constructed, not cited** (F3). mathlib at the tag has
    `ProbabilityMeasure.tendsto_of_tendsto_charFun`, but that lemma *takes* the
    limit `μ₀`; there is no Bochner theorem at the tag. The route that exists:
    tightness from the pointwise CF limit plus continuity at `0`
    (`isTightMeasureSet_of_tendsto_charFun`), Prokhorov
    (`isCompact_closure_of_isTightMeasureSet`), a convergent subsequence
    (`IsCompact.tendsto_subseq`), identification of the subsequence's limit CF
    by `tendsto_nhds_unique`, and then Lévy continuity for the *whole* sequence.
    `cgmyLaw` is *defined* as `Filter.limUnder atTop` of the marginals, and
    `cgmyLaw_exists` is the theorem that makes that definition honest.
  * **`Y = 1` is a pole of the formula, not of the law** (F2). Nothing in §1–§2
    divides by `Γ(−Y)` or `1 − Y`, so the law and its CF are stated on all of
    `0 < Y < 2`; only §3's identification carries `Y ≠ 1`. Measured:
    `|ψ_{1±δ} − L₁| = O(δ)` from both sides (`4.42e−4 / 4.40e−4` at `δ = 10⁻³`).

  §3 is the only part that cites G1 — the complex-rate Γ integral
  `∫ x^{s−1} e^{−zx} = Γ(s) z^{−s}` for `Re z > 0`, which is *not* at the tag in
  that form (the shipped `integral_cpow_mul_exp_neg_mul_Ioi` has a **real**
  rate) and is proved here by the identity theorem on the half-plane, anchored
  on the shipped real-rate lemma. The one-sided closed forms then follow by a
  single integration by parts each: the `0 < Y < 1` form from G1 directly, and
  the `1 < Y < 2` compensated form from the `0 < Y < 1` form at `Y − 1`.

  Deliberately not here (BRIEF_020's out-of-scope list): the mgf on the strip
  and the Esscher tilt at the law, the CF at complex `v`, any pricing statement
  at `cgmyLaw`, a general Lévy–Khintchine theorem, and any change to the landed
  truncated family, which is consumed rather than re-derived.

  Mathlib names verified at v4.34.0.
-/
import Mathlib
import ImprovedBS.CGMY
import ImprovedBS.CompoundPoisson

noncomputable section

namespace BSM

open MeasureTheory Filter Set ProbabilityTheory Complex
open scoped Topology ENNReal NNReal

/-!
---------------------------------------------------------------------------
§0  Bridges: the density, two elementary bounds on `e^{iθ}`, and power weights
---------------------------------------------------------------------------
-/

/-- The density is Borel measurable (the same bridge the landed modules use). -/
theorem cgmyLevyDensity_measurable (C G M Y : ℝ) :
    Measurable fun x : ℝ => cgmyLevyDensity C G M Y x := by
  unfold cgmyLevyDensity
  refine (measurable_const.mul ?_).mul ?_
  · refine Real.continuous_exp.measurable.comp ?_
    exact (Measurable.ite (p := fun x : ℝ => 0 < x) measurableSet_Ioi measurable_const
      measurable_const).neg.mul continuous_abs.measurable
  · exact measurable_of_continuousOn_compl_singleton 0 (by
      refine ContinuousOn.rpow_const continuous_abs.continuousOn fun x hx => Or.inl ?_
      simp only [mem_compl_iff, mem_singleton_iff] at hx
      exact (abs_pos.mpr hx).ne')

/-- The density vanishes at the origin (`0 ^ (−1−Y) = 0` for `Y > 0`). -/
theorem cgmyLevyDensity_zero (C G M Y : ℝ) (hY : 0 < Y) : cgmyLevyDensity C G M Y 0 = 0 := by
  unfold cgmyLevyDensity
  rw [abs_zero, Real.zero_rpow (by linarith : (-1 - Y) < 0).ne, mul_zero]

/-- `ν(x) ≤ C |x|^{−1−Y}`: the tempering factor is at most one. -/
theorem cgmyLevyDensity_le (C G M Y : ℝ) (hC : 0 ≤ C) (hG : 0 ≤ G) (hM : 0 ≤ M) (x : ℝ) :
    cgmyLevyDensity C G M Y x ≤ C * |x| ^ (-1 - Y) := by
  unfold cgmyLevyDensity
  have hexp : Real.exp (-(if 0 < x then M else G) * |x|) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
    exact mul_nonneg (by split_ifs <;> assumption) (abs_nonneg x)
  calc C * Real.exp (-(if 0 < x then M else G) * |x|) * |x| ^ (-1 - Y)
      ≤ C * 1 * |x| ^ (-1 - Y) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC)
          (Real.rpow_nonneg (abs_nonneg x) _)
    _ = C * |x| ^ (-1 - Y) := by rw [mul_one]

/-- The density is integrable on `(1, ∞)`: the landed far-field moment at `u = 0`. -/
theorem cgmyLevyDensity_integrableOn_Ioi_one (C G M Y : ℝ) (hC : 0 < C) (hM : 0 < M)
    (hY : 0 < Y) : IntegrableOn (cgmyLevyDensity C G M Y) (Ioi 1) := by
  have h : IntegrableOn (fun x : ℝ => C * (Real.exp (-M * x) * x ^ (-1 - Y))) (Ioi 1) := by
    simpa only [sub_zero] using cgmy_levy_far_moment C M Y 0 hC hY hM
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  beta_reduce
  rw [cgmyLevyDensity_pos_of_pos (lt_trans zero_lt_one hx)]
  ring

/-- The density is integrable on `(−∞, −1)`: the mirror of the previous line. -/
theorem cgmyLevyDensity_integrableOn_Iio_neg_one (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hY : 0 < Y) : IntegrableOn (cgmyLevyDensity C G M Y) (Iio (-1)) := by
  have h : IntegrableOn (fun x : ℝ => C * (Real.exp (-G * x) * x ^ (-1 - Y))) (Ioi 1) := by
    simpa only [sub_zero] using cgmy_levy_far_moment C G Y 0 hC hY hG
  have h' := h.comp_neg
  rw [Set.neg_Ioi] at h'
  refine h'.congr_fun (fun x hx => ?_) measurableSet_Iio
  have hx' : x < 0 := lt_trans hx (by norm_num)
  beta_reduce
  rw [cgmyLevyDensity_neg_of_neg hx', neg_mul_neg]
  ring

/-- The density is integrable off the unit ball. -/
theorem cgmyLevyDensity_integrableOn_compl_Icc (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) : IntegrableOn (cgmyLevyDensity C G M Y) (Icc (-1 : ℝ) 1)ᶜ := by
  have hset : (Icc (-1 : ℝ) 1)ᶜ = Iio (-1) ∪ Ioi 1 := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
    try exact Iff.rfl
  rw [hset]
  exact (cgmyLevyDensity_integrableOn_Iio_neg_one C G M Y hC hG hY).union
    (cgmyLevyDensity_integrableOn_Ioi_one C G M Y hC hM hY)

/-- `|x|^p` is integrable on `[−1, 1]` for `p > −1`: the positive half is
`intervalIntegrable_rpow'`, the negative half is its reflection. -/
theorem integrableOn_abs_rpow_Icc {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun x : ℝ => |x| ^ p) (Icc (-1 : ℝ) 1) := by
  have hP : IntegrableOn (fun x : ℝ => |x| ^ p) (Ioo (0 : ℝ) 1) := by
    have h : IntegrableOn (fun x : ℝ => x ^ p) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 hp
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioo
    beta_reduce
    rw [abs_of_pos hx.1]
  have hN : IntegrableOn (fun x : ℝ => |x| ^ p) (Ioo (-1 : ℝ) 0) := by
    have h := hP.comp_neg
    rw [Set.neg_Ioo, neg_zero] at h
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioo
    beta_reduce
    rw [abs_neg]
  have hpos : IntervalIntegrable (fun x : ℝ => |x| ^ p) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hP
  have hneg : IntervalIntegrable (fun x : ℝ => |x| ^ p) volume (-1) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr hN
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp (hneg.trans hpos)

/-- `x² ν(x)` is integrable on the unit ball: it is dominated by `C |x|^{1−Y}`,
integrable because `1 − Y > −1`. This is the `∫ (1 ∧ x²) ν < ∞` half on both sides. -/
theorem cgmy_sq_mul_levyDensity_integrableOn (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) :
    IntegrableOn (fun x : ℝ => x ^ 2 * cgmyLevyDensity C G M Y x) (Icc (-1 : ℝ) 1) := by
  have hmaj : IntegrableOn (fun x : ℝ => C * |x| ^ (1 - Y)) (Icc (-1 : ℝ) 1) :=
    (integrableOn_abs_rpow_Icc (by linarith)).const_mul C
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((continuous_id.pow 2).measurable.mul
      (cgmyLevyDensity_measurable C G M Y)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x _hx
    have hν : 0 ≤ cgmyLevyDensity C G M Y x := cgmyLevyDensity_nonneg hC.le x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg x) hν)]
    calc x ^ 2 * cgmyLevyDensity C G M Y x
        ≤ x ^ 2 * (C * |x| ^ (-1 - Y)) :=
          mul_le_mul_of_nonneg_left (cgmyLevyDensity_le C G M Y hC.le hG.le hM.le x)
            (sq_nonneg x)
      _ ≤ C * |x| ^ (1 - Y) := by
          rcases eq_or_ne x 0 with rfl | hx0
          · rw [zero_pow two_ne_zero, zero_mul]
            exact mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg _) _)
          · have habs : 0 < |x| := abs_pos.mpr hx0
            have hpow : x ^ 2 * |x| ^ (-1 - Y) = |x| ^ (1 - Y) := by
              rw [← sq_abs x, ← Real.rpow_two, ← Real.rpow_add habs]
              congr 1
              ring
            rw [← hpow]
            exact le_of_eq (by ring)

/-- `‖e^{ivx} − 1‖ ≤ 2` (the far-field bound of BRIEF_019, as a lemma). -/
theorem norm_cexp_mul_I_sub_one_le_two (v x : ℝ) :
    ‖Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1‖ ≤ 2 := by
  have h1 : ‖Complex.exp ((v : ℂ) * (x : ℂ) * I)‖ = 1 := by
    have hre : ((v : ℂ) * (x : ℂ) * I).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [Complex.norm_exp, hre, Real.exp_zero]
  calc ‖Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1‖
      ≤ ‖Complex.exp ((v : ℂ) * (x : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, norm_one]; norm_num

/-- **The second-order Taylor bound on the whole plane**:
`‖e^ζ − 1 − ζ‖ ≤ 3 e^{max(0, Re ζ)} ‖ζ‖²`. For `‖ζ‖ ≤ 1` this is mathlib's
`Complex.norm_exp_sub_one_sub_id_le`; for `‖ζ‖ > 1` the crude bound
`‖e^ζ‖ + 1 + ‖ζ‖ ≤ e^{max(0,Re ζ)}(2 + ‖ζ‖)` is already `≤ 3 e^{max(0,Re ζ)} ‖ζ‖²`.
No mean-value theorem, no remainder integral. -/
theorem norm_cexp_sub_one_sub_le (ζ : ℂ) :
    ‖Complex.exp ζ - 1 - ζ‖ ≤ 3 * Real.exp (max 0 ζ.re) * ‖ζ‖ ^ 2 := by
  have hexp : ‖Complex.exp ζ‖ ≤ Real.exp (max 0 ζ.re) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  have h1 : 1 ≤ Real.exp (max 0 ζ.re) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (le_max_left _ _)
  rcases le_or_gt ‖ζ‖ 1 with h | h
  · calc ‖Complex.exp ζ - 1 - ζ‖ ≤ ‖ζ‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le h
      _ ≤ 3 * Real.exp (max 0 ζ.re) * ‖ζ‖ ^ 2 := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Real.exp (max 0 ζ.re) - 1)
            (sq_nonneg ‖ζ‖)]
  · calc ‖Complex.exp ζ - 1 - ζ‖ ≤ ‖Complex.exp ζ - 1‖ + ‖ζ‖ := norm_sub_le _ _
      _ ≤ (‖Complex.exp ζ‖ + ‖(1 : ℂ)‖) + ‖ζ‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Real.exp (max 0 ζ.re) + 1) + ‖ζ‖ := by rw [norm_one]; linarith
      _ ≤ Real.exp (max 0 ζ.re) * (2 + ‖ζ‖) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr h1) (norm_nonneg ζ)]
      _ ≤ Real.exp (max 0 ζ.re) * (3 * ‖ζ‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          nlinarith [h, mul_lt_mul_of_pos_left h (lt_trans zero_lt_one h)]
      _ = 3 * Real.exp (max 0 ζ.re) * ‖ζ‖ ^ 2 := by ring

/-- `‖e^{iθ} − 1 − iθ‖ ≤ 3 θ²` for real `θ = v x`: the previous bound on the
imaginary axis, where `e^{max(0, Re ζ)} = 1`. -/
theorem norm_cexp_mul_I_sub_one_sub_le (v x : ℝ) :
    ‖Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1 - (v : ℂ) * (x : ℂ) * I‖ ≤ 3 * (v * x) ^ 2 := by
  have hre : ((v : ℂ) * (x : ℂ) * I).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  have hnorm : ‖(v : ℂ) * (x : ℂ) * I‖ = |v * x| := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  have h := norm_cexp_sub_one_sub_le ((v : ℂ) * (x : ℂ) * I)
  rw [hre, max_self, Real.exp_zero, mul_one, hnorm, sq_abs] at h
  exact h

/-- The **compensated integrand** of the Lévy–Khintchine form,
`e^{ivx} − 1 − ivx·1_{|x|≤1}`: the truncated exponent's integrand with the
unit-ball compensator subtracted. The compensator is what makes the `ε ↓ 0`
limit absolutely convergent — without it the integrand is `~ ivx·|x|^{−1−Y}`,
which is not integrable at `0` for `Y ≥ 1` (BRIEF_019 F3). -/
def cgmyCompensatedIntegrand (v x : ℝ) : ℂ :=
  Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1 -
    Set.indicator (Icc (-1 : ℝ) 1) (fun y : ℝ => (v : ℂ) * (y : ℂ) * I) x

theorem cgmyCompensatedIntegrand_measurable (v : ℝ) :
    Measurable fun x : ℝ => cgmyCompensatedIntegrand v x := by
  unfold cgmyCompensatedIntegrand
  have hcont : Continuous fun x : ℝ => Complex.exp ((v : ℂ) * (x : ℂ) * I) :=
    Complex.continuous_exp.comp
      (Continuous.mul (continuous_const.mul Complex.continuous_ofReal) continuous_const)
  refine (hcont.measurable.sub measurable_const).sub ?_
  exact Measurable.indicator
    (Continuous.mul (continuous_const.mul Complex.continuous_ofReal) continuous_const).measurable
    measurableSet_Icc

/-- For fixed `x` the compensated integrand is continuous in `v`. -/
theorem cgmyCompensatedIntegrand_continuous_left (x : ℝ) :
    Continuous fun v : ℝ => cgmyCompensatedIntegrand v x := by
  unfold cgmyCompensatedIntegrand
  have hexp : Continuous fun v : ℝ => Complex.exp ((v : ℂ) * (x : ℂ) * I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)
  have hlin : Continuous fun v : ℝ => (v : ℂ) * (x : ℂ) * I :=
    (Complex.continuous_ofReal.mul continuous_const).mul continuous_const
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp only [Set.indicator_of_mem hx]
    exact (hexp.sub continuous_const).sub hlin
  · simp only [Set.indicator_of_notMem hx, sub_zero]
    exact hexp.sub continuous_const

/-- Reflection: `E_v(−x) = E_{−v}(x)`, which is how the negative half-line folds
onto the positive one. -/
theorem cgmyCompensatedIntegrand_neg (v x : ℝ) :
    cgmyCompensatedIntegrand v (-x) = cgmyCompensatedIntegrand (-v) x := by
  have key : (v : ℂ) * ((-x : ℝ) : ℂ) * I = ((-v : ℝ) : ℂ) * (x : ℂ) * I := by
    rw [Complex.ofReal_neg, Complex.ofReal_neg]
    ring
  unfold cgmyCompensatedIntegrand
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hx' : -x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', key]
  · have hx' : -x ∉ Icc (-1 : ℝ) 1 := fun h => hx ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', key]

theorem norm_cgmyCompensatedIntegrand_le_of_mem {v x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖cgmyCompensatedIntegrand v x‖ ≤ 3 * (v * x) ^ 2 := by
  unfold cgmyCompensatedIntegrand
  rw [Set.indicator_of_mem hx]
  exact norm_cexp_mul_I_sub_one_sub_le v x

theorem norm_cgmyCompensatedIntegrand_le_of_notMem {v x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) :
    ‖cgmyCompensatedIntegrand v x‖ ≤ 2 := by
  unfold cgmyCompensatedIntegrand
  rw [Set.indicator_of_notMem hx, sub_zero]
  exact norm_cexp_mul_I_sub_one_le_two v x

/-- Near-zero dominator, uniform over `|v| ≤ R`: `‖E_v ν‖ ≤ 3R²·x²ν(x)` on the unit ball. -/
theorem norm_cgmyCompensated_mul_le_of_mem (C G M Y : ℝ) (hC : 0 ≤ C) {v R x : ℝ}
    (hv : |v| ≤ R) (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)‖
      ≤ 3 * R ^ 2 * (x ^ 2 * cgmyLevyDensity C G M Y x) := by
  have hν : 0 ≤ cgmyLevyDensity C G M Y x := cgmyLevyDensity_nonneg hC x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
  have hvx : (v * x) ^ 2 ≤ R ^ 2 * x ^ 2 := by
    have hv2 : v ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs v]
      exact pow_le_pow_left₀ (abs_nonneg v) hv 2
    calc (v * x) ^ 2 = v ^ 2 * x ^ 2 := by ring
      _ ≤ R ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right hv2 (sq_nonneg x)
  calc ‖cgmyCompensatedIntegrand v x‖ * cgmyLevyDensity C G M Y x
      ≤ (3 * (v * x) ^ 2) * cgmyLevyDensity C G M Y x :=
        mul_le_mul_of_nonneg_right (norm_cgmyCompensatedIntegrand_le_of_mem hx) hν
    _ ≤ (3 * (R ^ 2 * x ^ 2)) * cgmyLevyDensity C G M Y x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvx (by norm_num)) hν
    _ = 3 * R ^ 2 * (x ^ 2 * cgmyLevyDensity C G M Y x) := by ring

/-- Far-field dominator: `‖E_v ν‖ ≤ 2ν(x)` off the unit ball, for every `v`. -/
theorem norm_cgmyCompensated_mul_le_of_notMem (C G M Y : ℝ) (hC : 0 ≤ C) (v : ℝ) {x : ℝ}
    (hx : x ∉ Icc (-1 : ℝ) 1) :
    ‖cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)‖
      ≤ 2 * cgmyLevyDensity C G M Y x := by
  have hν : 0 ≤ cgmyLevyDensity C G M Y x := cgmyLevyDensity_nonneg hC x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
  exact mul_le_mul_of_nonneg_right (norm_cgmyCompensatedIntegrand_le_of_notMem hx) hν

theorem cgmyCompensated_mul_measurable (C G M Y : ℝ) (v : ℝ) :
    Measurable fun x : ℝ => cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ) :=
  (cgmyCompensatedIntegrand_measurable v).mul
    (Complex.continuous_ofReal.measurable.comp (cgmyLevyDensity_measurable C G M Y))

/-!
---------------------------------------------------------------------------
§1  The decomposition and the limit exponent
---------------------------------------------------------------------------
-/

/-- The **paired drift integrand** `C x^{−Y}(e^{−Mx} − e^{−Gx})`.

Both legs sit inside one integrand because only the difference is integrable at
`0`: each leg alone is `x^{−Y}`, whose integral diverges for `Y ≥ 1` (measured:
`C∫_ε^1 x^{−Y}e^{−Mx}dx = 122.47` at `ε = 2⁻¹⁴`, `Y = 3/2`, growing like
`ε^{1−Y}` — mutant M39, lint clause `[CGMYLaw]` R2). The difference is
`O(x^{1−Y})` because `e^{−Mx} − e^{−Gx} = O(x)`, which is integrable for every
`Y < 2`. This is ledger correction C25: the two sides' `ivx` pieces *pair* into
this finite nonzero drift; they do not cancel. -/
def cgmyDriftIntegrand (C G M Y : ℝ) (x : ℝ) : ℝ :=
  C * x ^ (-Y) * (Real.exp (-M * x) - Real.exp (-G * x))

/-- **The Lévy–Khintchine exponent** of `cgmyLevyDensity C G M Y` with the
unit-ball compensator: `L(v) = B₀(v) + iv·d₀`, the `ε ↓ 0` limit of
`cgmyTruncatedExponent` (`cgmyTruncatedExponent_tendsto`).

It is an honest pair of absolutely convergent integrals on all of `0 < Y < 2`
— no `Γ`, no `1 − Y`, hence finite at `Y = 1` where the closed form
`cgmyExponent` has its pole (F2). -/
def cgmyLKExponent (C G M Y : ℝ) (v : ℝ) : ℂ :=
  (∫ x : ℝ, cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)) +
    (v : ℂ) * I * ((∫ x in Ioc (0 : ℝ) 1, cgmyDriftIntegrand C G M Y x : ℝ) : ℂ)

/-- The compensated integrand times the density is Bochner-integrable on all of
`ℝ`. Dominator: `3v²·x²ν(x)` on the unit ball, i.e. `C|x|^{1−Y}` (integrable
because `1 − Y > −1`), and `2ν` off it, where the landed `cgmy_levy_far_moment`
applies at `u = 0` to both tails. -/
theorem cgmyCompensatedIntegrand_integrable (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (v : ℝ) :
    Integrable (fun x : ℝ =>
      cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)) volume :=
    (cgmyCompensated_mul_measurable C G M Y v).aestronglyMeasurable
  have hIcc : IntegrableOn (fun x : ℝ =>
      cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)) (Icc (-1 : ℝ) 1) := by
    refine Integrable.mono'
      ((cgmy_sq_mul_levyDensity_integrableOn C G M Y hC hG hM hY hY₂).const_mul (3 * |v| ^ 2))
      hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact norm_cgmyCompensated_mul_le_of_mem C G M Y hC.le le_rfl hx
  have hcompl : IntegrableOn (fun x : ℝ =>
      cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)) (Icc (-1 : ℝ) 1)ᶜ := by
    refine Integrable.mono'
      ((cgmyLevyDensity_integrableOn_compl_Icc C G M Y hC hG hM hY).const_mul 2)
      hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    exact norm_cgmyCompensated_mul_le_of_notMem C G M Y hC.le v hx
  have h := hIcc.union hcompl
  rw [Set.union_compl_self] at h
  exact integrableOn_univ.mp h

/-- `|e^{−a} − e^{−b}| ≤ |a − b|` for `a, b ≥ 0`: `exp` is 1-Lipschitz on the
nonpositive half-line (from `x + 1 ≤ e^x` and `e^{−a} ≤ 1`). -/
theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    intro a b ha hab
    have h1 : a - b + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp (a - b)
    have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (a - b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
    rw [h2]
    calc Real.exp (-a) - Real.exp (-a) * Real.exp (a - b)
        = Real.exp (-a) * (1 - Real.exp (a - b)) := by ring
      _ ≤ Real.exp (-a) * (b - a) := by
          refine mul_le_mul_of_nonneg_left ?_ h4
          linarith
      _ ≤ 1 * (b - a) := by
          refine mul_le_mul_of_nonneg_right h3 ?_
          linarith
      _ = b - a := one_mul _
  rcases le_total a b with hab | hab
  · have h0 : 0 ≤ Real.exp (-a) - Real.exp (-b) := by
      have := Real.exp_le_exp.mpr (neg_le_neg hab)
      linarith
    rw [abs_of_nonneg h0, abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith [key a b ha hab]
  · have h0 : Real.exp (-a) - Real.exp (-b) ≤ 0 := by
      have := Real.exp_le_exp.mpr (neg_le_neg hab)
      linarith
    rw [abs_of_nonpos h0, abs_of_nonneg (by linarith : 0 ≤ a - b)]
    linarith [key b a hb hab]

/-- The paired drift integrand is integrable on `Ioc 0 1`: the dominator is
`C|M − G|·x^{1−Y}` from `|e^{−Mx} − e^{−Gx}| ≤ |M − G|·x` on `x ≥ 0`, and
`x^{1−Y}` is integrable at `0` because `1 − Y > −1`. -/
theorem cgmyDriftIntegrand_integrableOn (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) :
    IntegrableOn (cgmyDriftIntegrand C G M Y) (Ioc (0 : ℝ) 1) := by
  show IntegrableOn (fun x : ℝ => C * x ^ (-Y) * (Real.exp (-M * x) - Real.exp (-G * x)))
    (Ioc (0 : ℝ) 1)
  have hmaj : IntegrableOn (fun x : ℝ => C * |M - G| * x ^ (1 - Y)) (Ioc (0 : ℝ) 1) := by
    have h : IntegrableOn (fun x : ℝ => x ^ (1 - Y)) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)
    have h' : IntegrableOn (fun x : ℝ => x ^ (1 - Y)) (Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr h)
    exact h'.const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable (ContinuousOn.mul
      (continuousOn_const.mul (continuousOn_id.rpow_const
        fun x (hx : x ∈ Ioc (0 : ℝ) 1) => Or.inl (ne_of_gt hx.1)))
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.sub
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn))
      measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hC,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hlip : |Real.exp (-M * x) - Real.exp (-G * x)| ≤ |M - G| * x := by
      have := abs_exp_neg_sub_exp_neg_le (mul_nonneg hM.le hx0.le) (mul_nonneg hG.le hx0.le)
      rw [neg_mul, neg_mul]
      calc |Real.exp (-(M * x)) - Real.exp (-(G * x))| ≤ |M * x - G * x| := this
        _ = |M - G| * x := by rw [← sub_mul, abs_mul, abs_of_pos hx0]
    have hpow : x ^ (-Y) * x = x ^ (1 - Y) := by
      rw [show (1 - Y) = -Y + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    calc C * x ^ (-Y) * |Real.exp (-M * x) - Real.exp (-G * x)|
        ≤ C * x ^ (-Y) * (|M - G| * x) :=
          mul_le_mul_of_nonneg_left hlip (mul_nonneg hC.le (Real.rpow_nonneg hx0.le _))
      _ = C * |M - G| * (x ^ (-Y) * x) := by ring
      _ = C * |M - G| * x ^ (1 - Y) := by rw [hpow]

/-- **The decomposition** (F1, ledger C25): at every `0 < ε ≤ 1` the truncated
exponent splits *exactly* into the compensated integral over `{ε ≤ |x|}` and the
paired drift over `Ioc ε 1`. This is an identity, not a limit — the `ivx·1_{|x|≤1}`
piece is integrable on `{ε ≤ |x|}` for `ε > 0`, so it is a plain `integral_sub`
plus the reflection `x ↦ −x` that folds the negative side onto `Ioc ε 1`.
Measured `≤ 7.3e−15` over 18 rows. -/
theorem cgmyTruncatedExponent_decomp (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (ε : ℝ≥0) (hε : 0 < ε) (hε₁ : ε ≤ 1) (v : ℝ) :
    cgmyTruncatedExponent C G M Y ε (v : ℂ)
      = (∫ x in {x : ℝ | (ε : ℝ) ≤ |x|},
          cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
        + (v : ℂ) * I * ((∫ x in Ioc (ε : ℝ) 1, cgmyDriftIntegrand C G M Y x : ℝ) : ℂ) := by
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
  have hε₁' : (ε : ℝ) ≤ 1 := by exact_mod_cast hε₁
  have hSmeas : MeasurableSet {x : ℝ | (ε : ℝ) ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hd_meas : Measurable fun x : ℝ => cgmyLevyDensity C G M Y x :=
    cgmyLevyDensity_measurable C G M Y
  -- the density has finite mass on the truncation set (BRIEF_019)
  have hmass := cgmyJumpMass_lt_top C G M Y ε hC hG hM hY hε
  rw [cgmyJumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  have hd_int : IntegrableOn (fun x : ℝ => cgmyLevyDensity C G M Y x) {x : ℝ | (ε : ℝ) ≤ |x|} :=
    ⟨hd_meas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => cgmyLevyDensity_nonneg hC.le x)).mpr
        hmass⟩
  -- Step 1: subtracting the compensated integral leaves the compensator's integral
  have hstep1 : cgmyTruncatedExponent C G M Y ε (v : ℂ)
      - ∫ x in {x : ℝ | (ε : ℝ) ≤ |x|},
          cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)
      = ∫ x in {x : ℝ | (ε : ℝ) ≤ |x|},
          Set.indicator (Icc (-1 : ℝ) 1) (fun y : ℝ => (v : ℂ) * (y : ℂ) * I) x
            * (cgmyLevyDensity C G M Y x : ℂ) := by
    rw [cgmyTruncatedExponent,
      ← integral_sub (cgmyTruncatedExponent_integrable C G M Y ε hC hG hM hY hε v)
        (cgmyCompensatedIntegrand_integrable C G M Y hC hG hM hY hY₂ v).integrableOn]
    refine setIntegral_congr_fun hSmeas fun x _ => ?_
    simp only [cgmyCompensatedIntegrand]
    ring
  -- Step 2: the compensator's integral is the paired drift
  have hstep2 : (∫ x in {x : ℝ | (ε : ℝ) ≤ |x|},
        Set.indicator (Icc (-1 : ℝ) 1) (fun y : ℝ => (v : ℂ) * (y : ℂ) * I) x
          * (cgmyLevyDensity C G M Y x : ℂ))
      = (v : ℂ) * I * ((∫ x in Ioc (ε : ℝ) 1, cgmyDriftIntegrand C G M Y x : ℝ) : ℂ) := by
    -- fold the indicator into the domain
    have h1 : (∫ x in {x : ℝ | (ε : ℝ) ≤ |x|},
        Set.indicator (Icc (-1 : ℝ) 1) (fun y : ℝ => (v : ℂ) * (y : ℂ) * I) x
          * (cgmyLevyDensity C G M Y x : ℂ))
        = ∫ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1 : ℝ) 1,
            (v : ℂ) * (x : ℂ) * I * (cgmyLevyDensity C G M Y x : ℂ) := by
      rw [← setIntegral_indicator measurableSet_Icc]
      refine setIntegral_congr_fun hSmeas fun x _ => ?_
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    -- the truncated ball is two intervals
    have hset : {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1 : ℝ) 1
        = Icc (-1 : ℝ) (-(ε : ℝ)) ∪ Icc (ε : ℝ) 1 := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_union]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases le_or_gt 0 x with hx | hx
        · right
          rw [abs_of_nonneg hx] at h1
          exact ⟨h1, h3⟩
        · left
          rw [abs_of_neg hx] at h1
          exact ⟨h2, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · have hxneg : x < 0 := by linarith
          refine ⟨?_, h1, by linarith⟩
          rw [abs_of_neg hxneg]
          linarith
        · have hxpos : 0 < x := by linarith
          refine ⟨?_, by linarith, h2⟩
          rw [abs_of_pos hxpos]
          exact h1
    have hdisj : Disjoint (Icc (-1 : ℝ) (-(ε : ℝ))) (Icc (ε : ℝ) 1) := by
      rw [Set.disjoint_left]
      rintro x ⟨_, hx₂⟩ ⟨hx₃, _⟩
      linarith
    -- integrability of the compensator integrand on the truncated ball
    have hint : IntegrableOn (fun x : ℝ => (v : ℂ) * (x : ℂ) * I * (cgmyLevyDensity C G M Y x : ℂ))
        ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1 : ℝ) 1) := by
      refine Integrable.mono' ((hd_int.mono_set inter_subset_left).const_mul |v|) ?_ ?_
      · exact ((((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).measurable).mul
          (Complex.continuous_ofReal.measurable.comp hd_meas)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem (hSmeas.inter measurableSet_Icc)] with x hx
        have hν : 0 ≤ cgmyLevyDensity C G M Y x := cgmyLevyDensity_nonneg hC.le x
        have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.2.1, hx.2.2⟩
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hν]
        calc |v| * |x| * cgmyLevyDensity C G M Y x
            ≤ |v| * 1 * cgmyLevyDensity C G M Y x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx1 (abs_nonneg v)) hν
          _ = |v| * cgmyLevyDensity C G M Y x := by ring
    rw [hset] at hint
    rw [h1, hset, setIntegral_union hdisj measurableSet_Icc (hint.mono_set subset_union_left)
      (hint.mono_set subset_union_right)]
    -- both pieces as interval integrals over `[ε, 1]`, the negative one reflected
    have hneg : (∫ x in Icc (-1 : ℝ) (-(ε : ℝ)),
          (v : ℂ) * (x : ℂ) * I * (cgmyLevyDensity C G M Y x : ℂ))
        = ∫ x in (ε : ℝ)..1,
            (v : ℂ) * ((-x : ℝ) : ℂ) * I * (cgmyLevyDensity C G M Y (-x) : ℂ) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ -(ε : ℝ)),
        ← intervalIntegral.integral_comp_neg]
    have hpos : (∫ x in Icc (ε : ℝ) 1, (v : ℂ) * (x : ℂ) * I * (cgmyLevyDensity C G M Y x : ℂ))
        = ∫ x in (ε : ℝ)..1, (v : ℂ) * (x : ℂ) * I * (cgmyLevyDensity C G M Y x : ℂ) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hε₁']
    have hiiP : IntervalIntegrable
        (fun x : ℝ => (v : ℂ) * (x : ℂ) * I * (cgmyLevyDensity C G M Y x : ℂ)) volume (ε : ℝ) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hε₁']
      exact hint.mono_set subset_union_right
    have hiiN : IntervalIntegrable
        (fun x : ℝ => (v : ℂ) * ((-x : ℝ) : ℂ) * I * (cgmyLevyDensity C G M Y (-x) : ℂ))
        volume (ε : ℝ) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hε₁']
      have h := (hint.mono_set subset_union_left).comp_neg
      rw [Set.neg_Icc, neg_neg, neg_neg] at h
      exact h
    rw [hneg, hpos, ← intervalIntegral.integral_add hiiN hiiP]
    -- pointwise on `[ε, 1]` the two legs pair into the drift
    have hpt : ∀ x ∈ uIcc (ε : ℝ) 1,
        (v : ℂ) * ((-x : ℝ) : ℂ) * I * (cgmyLevyDensity C G M Y (-x) : ℂ)
          + (v : ℂ) * (x : ℂ) * I * (cgmyLevyDensity C G M Y x : ℂ)
        = (v : ℂ) * I * (cgmyDriftIntegrand C G M Y x : ℂ) := by
      intro x hx
      rw [Set.uIcc_of_le hε₁'] at hx
      have hx0 : 0 < x := lt_of_lt_of_le hε' hx.1
      have hxneg : -x < 0 := neg_neg_of_pos hx0
      rw [cgmyLevyDensity_pos_of_pos hx0, cgmyLevyDensity_neg_of_neg hxneg, neg_neg,
        cgmyDriftIntegrand]
      have hpow : x * x ^ (-1 - Y) = x ^ (-Y) := by
        rw [show (-Y) = 1 + (-1 - Y) by ring, Real.rpow_add hx0, Real.rpow_one]
      rw [← hpow]
      have hexp : Real.exp (G * -x) = Real.exp (-G * x) := by rw [mul_neg, neg_mul]
      rw [hexp]
      push_cast
      ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le hε₁', integral_complex_ofReal]
  rw [hstep2] at hstep1
  linear_combination hstep1

/-- **The limit** (F1): along the ladder `εₙ = 2⁻ⁿ` the truncated exponent
converges to the Lévy–Khintchine exponent. Two instances of
`tendsto_setIntegral_of_monotone` through the decomposition: the sets
`{2⁻ⁿ ≤ |x|}` increase to `{0}ᶜ` (whose integral is the full one because the
integrand vanishes at `0`) and `Ioc 2⁻ⁿ 1` increases to `Ioc 0 1`. Both converge
at rate `ε^{2−Y}` — measured `1.4996 / 0.9997 / 0.4998` at `Y = ½, 1, 3/2`. -/
theorem cgmyTruncatedExponent_tendsto (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (v : ℝ) :
    Tendsto (fun n : ℕ => cgmyTruncatedExponent C G M Y ((2 : ℝ≥0)⁻¹ ^ n) (v : ℂ))
      atTop (𝓝 (cgmyLKExponent C G M Y v)) := by
  -- the ladder, as real numbers
  have hcoe : ∀ n : ℕ, (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) = (2 : ℝ)⁻¹ ^ n := fun n => by simp
  have hpos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := fun n => pow_pos (by norm_num) n
  have hle1 : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have hanti : ∀ m n : ℕ, m ≤ n → (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m := fun m n h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have hsmall : ∀ x : ℝ, 0 < x → ∃ n : ℕ, (2 : ℝ)⁻¹ ^ n < x := fun x hx =>
    exists_pow_lt_of_lt_one hx (by norm_num)
  have hε₀ : ∀ n : ℕ, (0 : ℝ≥0) < (2 : ℝ≥0)⁻¹ ^ n := fun n =>
    pow_pos (inv_pos.mpr (by norm_num)) n
  have hε₁ : ∀ n : ℕ, (2 : ℝ≥0)⁻¹ ^ n ≤ 1 := fun n => by
    rw [← NNReal.coe_le_coe, hcoe, NNReal.coe_one]
    exact hle1 n
  -- the compensated family: `{2⁻ⁿ ≤ |x|} ↑ {0}ᶜ`
  have h1 : Tendsto (fun n : ℕ => ∫ x in {x : ℝ | (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) ≤ |x|},
      cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)) atTop
      (𝓝 (∫ x, cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))) := by
    have hint := cgmyCompensatedIntegrand_integrable C G M Y hC hG hM hY hY₂ v
    have hmono : Monotone fun n : ℕ => {x : ℝ | (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) ≤ |x|} := by
      intro m n hmn x hx
      simp only [mem_ofPred_eq, hcoe] at hx ⊢
      exact le_trans (hanti m n hmn) hx
    have hmeasS : ∀ n : ℕ, MeasurableSet {x : ℝ | (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) ≤ |x|} :=
      fun n => measurableSet_le measurable_const continuous_abs.measurable
    have hT := tendsto_setIntegral_of_monotone hmeasS hmono hint.integrableOn
    have hU : (∫ x in ⋃ n : ℕ, {x : ℝ | (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) ≤ |x|},
        cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
        = ∫ x, cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have hx0 : x = 0 := by
        by_contra hne
        obtain ⟨n, hn⟩ := hsmall |x| (abs_pos.mpr hne)
        exact hx (mem_iUnion.mpr ⟨n, by simp only [mem_ofPred_eq, hcoe]; exact hn.le⟩)
      subst hx0
      rw [cgmyLevyDensity_zero C G M Y hY, Complex.ofReal_zero, mul_zero]
    rw [hU] at hT
    exact hT
  -- the drift family: `Ioc 2⁻ⁿ 1 ↑ Ioc 0 1`
  have h2 : Tendsto (fun n : ℕ => ∫ x in Ioc (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) 1,
      cgmyDriftIntegrand C G M Y x) atTop
      (𝓝 (∫ x in Ioc (0 : ℝ) 1, cgmyDriftIntegrand C G M Y x)) := by
    have hint := cgmyDriftIntegrand_integrableOn C G M Y hC hG hM hY hY₂
    have hmono : Monotone fun n : ℕ => Ioc (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) 1 := by
      intro m n hmn
      show Ioc (((2 : ℝ≥0)⁻¹ ^ m : ℝ≥0) : ℝ) 1 ⊆ Ioc (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) 1
      rw [hcoe, hcoe]
      exact Ioc_subset_Ioc_left (hanti m n hmn)
    have hmeasS : ∀ n : ℕ, MeasurableSet (Ioc (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) 1) :=
      fun n => measurableSet_Ioc
    have hU : (⋃ n : ℕ, Ioc (((2 : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ) 1) = Ioc (0 : ℝ) 1 := by
      ext x
      simp only [mem_iUnion, mem_Ioc, hcoe]
      constructor
      · rintro ⟨n, hn, hx1⟩
        exact ⟨lt_trans (hpos n) hn, hx1⟩
      · rintro ⟨hx0, hx1⟩
        obtain ⟨n, hn⟩ := hsmall x hx0
        exact ⟨n, hn, hx1⟩
    have hT := tendsto_setIntegral_of_monotone hmeasS hmono (by rw [hU]; exact hint)
    rw [hU] at hT
    exact hT
  have h2c := h2.ofReal
  have hsum := h1.add (h2c.const_mul ((v : ℂ) * I))
  refine hsum.congr fun n => ?_
  exact (cgmyTruncatedExponent_decomp C G M Y hC hG hM hY hY₂ _ (hε₀ n) (hε₁ n) v).symm

/-- The Lévy–Khintchine exponent vanishes at `0`, as every characteristic
exponent must. -/
theorem cgmyLKExponent_zero (C G M Y : ℝ) : cgmyLKExponent C G M Y 0 = 0 := by
  have h : ∀ x : ℝ, cgmyCompensatedIntegrand 0 x = 0 := by
    intro x
    simp [cgmyCompensatedIntegrand, Set.indicator_apply]
  simp [cgmyLKExponent, h]

/-- **Continuity of the limit exponent.** `continuous_of_dominated` will not do
for the near-zero piece — its bound has to be uniform in the parameter — so that
piece is `continuousAt_of_dominated` at each `v₀`, with the dominator
`3(|v₀|+1)²·x²ν(x)` for `|v| ≤ |v₀| + 1`; the far piece is dominated by `2ν`
uniformly. Only `ContinuousAt … 0` is consumed downstream, by the tightness
argument. -/
theorem cgmyLKExponent_continuous (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) : Continuous (cgmyLKExponent C G M Y) := by
  have hmeas : ∀ v : ℝ, AEStronglyMeasurable
      (fun x : ℝ => cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ)) volume :=
    fun v => (cgmyCompensated_mul_measurable C G M Y v).aestronglyMeasurable
  have hcont : ∀ x : ℝ, Continuous fun v : ℝ =>
      cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ) :=
    fun x => (cgmyCompensatedIntegrand_continuous_left x).mul continuous_const
  -- the near piece
  have hnear : Continuous fun v : ℝ => ∫ x in Icc (-1 : ℝ) 1,
      cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ) := by
    refine continuous_iff_continuousAt.mpr fun v₀ => ?_
    refine continuousAt_of_dominated
      (bound := fun x : ℝ => 3 * (|v₀| + 1) ^ 2 * (x ^ 2 * cgmyLevyDensity C G M Y x))
      ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun v => (hmeas v).restrict
    · have hball : ∀ᶠ v in 𝓝 v₀, |v| ≤ |v₀| + 1 := by
        filter_upwards [Metric.ball_mem_nhds v₀ zero_lt_one] with v hv
        rw [Metric.mem_ball, Real.dist_eq] at hv
        linarith [abs_sub_abs_le_abs_sub v v₀]
      filter_upwards [hball] with v hv
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact norm_cgmyCompensated_mul_le_of_mem C G M Y hC.le hv hx
    · exact (cgmy_sq_mul_levyDensity_integrableOn C G M Y hC hG hM hY hY₂).const_mul _
    · exact ae_of_all _ fun x => (hcont x).continuousAt
  -- the far piece
  have hfar : Continuous fun v : ℝ => ∫ x in (Icc (-1 : ℝ) 1)ᶜ,
      cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ) := by
    refine continuous_of_dominated (bound := fun x : ℝ => 2 * cgmyLevyDensity C G M Y x)
      ?_ ?_ ?_ ?_
    · exact fun v => (hmeas v).restrict
    · intro v
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
      exact norm_cgmyCompensated_mul_le_of_notMem C G M Y hC.le v hx
    · exact (cgmyLevyDensity_integrableOn_compl_Icc C G M Y hC hG hM hY).const_mul 2
    · exact ae_of_all _ hcont
  -- assemble
  have hsplit : cgmyLKExponent C G M Y = fun v : ℝ =>
      ((∫ x in Icc (-1 : ℝ) 1, cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
        + ∫ x in (Icc (-1 : ℝ) 1)ᶜ,
            cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
        + (v : ℂ) * I * ((∫ x in Ioc (0 : ℝ) 1, cgmyDriftIntegrand C G M Y x : ℝ) : ℂ) := by
    funext v
    rw [cgmyLKExponent, ← integral_add_compl (measurableSet_Icc : MeasurableSet (Icc (-1 : ℝ) 1))
      (cgmyCompensatedIntegrand_integrable C G M Y hC hG hM hY hY₂ v)]
  rw [hsplit]
  exact (hnear.add hfar).add
    ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)

/-!
---------------------------------------------------------------------------
§2  The law
---------------------------------------------------------------------------
-/

/-- **Lévy's continuity theorem, existence half, on the line** (F3): a sequence
of probability measures whose characteristic functions converge pointwise to a
function continuous at `0` converges weakly to *some* probability measure.
mathlib at the tag has the version that *takes* the limit
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`); the limit is produced here by
tightness (`isTightMeasureSet_of_tendsto_charFun`), Prokhorov
(`isCompact_closure_of_isTightMeasureSet`), a convergent subsequence
(`IsCompact.tendsto_subseq`), identification of its limit's CF by
`tendsto_nhds_unique`, and Lévy continuity for the whole sequence. -/
theorem exists_tendsto_of_tendsto_charFun {μ : ℕ → ProbabilityMeasure ℝ} {f : ℝ → ℂ}
    (hf : ContinuousAt f 0)
    (h : ∀ t : ℝ, Tendsto (fun n => charFun (μ n : Measure ℝ) t) atTop (𝓝 (f t))) :
    ∃ μ₀ : ProbabilityMeasure ℝ, Tendsto μ atTop (𝓝 μ₀) := by
  have h_tight : IsTightMeasureSet (Set.range fun n => (μ n : Measure ℝ)) :=
    isTightMeasureSet_of_tendsto_charFun (μ := fun n => (μ n : Measure ℝ)) hf h
  have h_tight' :
      IsTightMeasureSet {((ν : ProbabilityMeasure ℝ) : Measure ℝ) | ν ∈ Set.range μ} := by
    convert h_tight using 1
    ext ν
    simp
  have h_compact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet h_tight'
  obtain ⟨μ₀, -, φ, hφ, hsub⟩ :=
    h_compact.tendsto_subseq (x := μ) fun n => subset_closure (Set.mem_range_self n)
  have hsub_cf : ∀ t : ℝ, Tendsto (fun n => charFun (μ (φ n) : Measure ℝ) t) atTop
      (𝓝 (charFun (μ₀ : Measure ℝ) t)) :=
    fun t => ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hsub t
  have hcf : ∀ t : ℝ, charFun (μ₀ : Measure ℝ) t = f t := fun t =>
    tendsto_nhds_unique (hsub_cf t) ((h t).comp hφ.tendsto_atTop)
  refine ⟨μ₀, ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_⟩
  rw [hcf t]
  exact h t

/-- The **truncated compound-Poisson marginal** as a `ProbabilityMeasure`:
BRIEF_019's `cpLaw` at rate `τ·λ_ε` and jump law `cgmyJumpLaw`, packaged with
`cpLaw_isProbabilityMeasure`. This is the sequence `cgmyLaw` is the limit of. -/
def cgmyCpProbability (C G M Y : ℝ) (τ : ℝ≥0) (ε : ℝ≥0) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hε : 0 < ε) : ProbabilityMeasure ℝ :=
  ⟨cpLaw (τ * (cgmyJumpMeasure C G M Y ε Set.univ).toNNReal) (cgmyJumpLaw C G M Y ε),
    cpLaw_isProbabilityMeasure _ _ (cgmyJumpLaw_isProbabilityMeasure C G M Y ε hC hG hM hY hε)⟩

/-- **The CGMY law**: the `ε ↓ 0` limit of the compound-Poisson marginals along
the ladder `εₙ = 2⁻ⁿ`, written as `Filter.limUnder atTop`.

`limUnder` is a *conditional* definition — it picks the limit when one exists and
an arbitrary element otherwise — so the definition is only honest together with
`cgmyLaw_exists`, which is the Prokhorov + Lévy-continuity construction of F3.
There is no closed-form density to write down here, which is the point of the
construction (lint clause `[CGMYLaw]` R1). -/
def cgmyLaw (C G M Y : ℝ) (τ : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) : ProbabilityMeasure ℝ :=
  Filter.limUnder atTop
    (fun n : ℕ => cgmyCpProbability C G M Y τ ((2 : ℝ≥0)⁻¹ ^ n) hC hG hM hY
      (pow_pos (inv_pos.mpr (by norm_num : (0 : ℝ≥0) < 2)) n))

/-- **The marginals' characteristic functions converge** to `exp (τ·L)`:
`charFun_cgmyCpLaw` rewrites each term as `exp (τ·A_{εₙ})` and §1's limit passes
through `Complex.continuous_exp` (`Tendsto.cexp`). No estimate is needed — the CF
convergence is no slower than the exponent's because `exp` is 1-Lipschitz on the
closed left half-plane, where `Re A_ε ≤ 0` keeps it (F8, measured ratio
`≤ 0.9990`). -/
theorem charFun_cgmyCpProbability_tendsto (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) (t : ℝ) :
    Tendsto (fun n : ℕ => charFun
        (cgmyCpProbability C G M Y τ ((2 : ℝ≥0)⁻¹ ^ n) hC hG hM hY
          (pow_pos (inv_pos.mpr (by norm_num : (0 : ℝ≥0) < 2)) n) : Measure ℝ) t)
      atTop (𝓝 (Complex.exp ((τ : ℂ) * cgmyLKExponent C G M Y t))) := by
  have h := (cgmyTruncatedExponent_tendsto C G M Y hC hG hM hY hY₂ t).const_mul (τ : ℂ)
  refine (Tendsto.cexp h).congr fun n => ?_
  exact (charFun_cgmyCpLaw C G M Y _ hC hG hM hY
    (pow_pos (inv_pos.mpr (by norm_num : (0 : ℝ≥0) < 2)) n) τ t).symm

/-- **Tightness of the marginals** (F3): `isTightMeasureSet_of_tendsto_charFun`
applied to the pointwise CF limit and `ContinuousAt (exp ∘ (τ · L)) 0`, which is
`cgmyLKExponent_continuous` plus `Complex.continuous_exp`. Measured through
mathlib's own bound `(R/2)∫_{−2/R}^{2/R}(1 − Re φₙ)`: monotone in `n`, converging
to the limit law's value, and decreasing in `R`. -/
theorem cgmyCpProbability_isTight (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) :
    IsTightMeasureSet (Set.range (fun n : ℕ =>
      (cgmyCpProbability C G M Y τ ((2 : ℝ≥0)⁻¹ ^ n) hC hG hM hY
          (pow_pos (inv_pos.mpr (by norm_num : (0 : ℝ≥0) < 2)) n) : Measure ℝ))) :=
  isTightMeasureSet_of_tendsto_charFun
    (f := fun t : ℝ => Complex.exp ((τ : ℂ) * cgmyLKExponent C G M Y t))
    ((Complex.continuous_exp.comp
      (continuous_const.mul (cgmyLKExponent_continuous C G M Y hC hG hM hY hY₂))).continuousAt)
    (charFun_cgmyCpProbability_tendsto C G M Y hC hG hM hY hY₂ τ)

/-- **Existence of the limit law** (F3): the construction the definition of
`cgmyLaw` rests on — `exists_tendsto_of_tendsto_charFun` (tightness, Prokhorov,
a convergent subsequence, `tendsto_nhds_unique`, Lévy continuity for the whole
sequence) applied to the CF limit `exp (τ·L)`, continuous at `0` by
`cgmyLKExponent_continuous`. mathlib at the tag has no Bochner theorem, so this
is a construction and not a citation. -/
theorem cgmyLaw_exists (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) :
    ∃ μ₀ : ProbabilityMeasure ℝ,
      Tendsto (fun n : ℕ => cgmyCpProbability C G M Y τ ((2 : ℝ≥0)⁻¹ ^ n) hC hG hM hY
        (pow_pos (inv_pos.mpr (by norm_num : (0 : ℝ≥0) < 2)) n)) atTop (𝓝 μ₀) :=
  exists_tendsto_of_tendsto_charFun
    (f := fun t : ℝ => Complex.exp ((τ : ℂ) * cgmyLKExponent C G M Y t))
    ((Complex.continuous_exp.comp
      (continuous_const.mul (cgmyLKExponent_continuous C G M Y hC hG hM hY hY₂))).continuousAt)
    (charFun_cgmyCpProbability_tendsto C G M Y hC hG hM hY hY₂ τ)

/-- The marginals converge to `cgmyLaw` itself: `tendsto_nhds_limUnder` applied
to `cgmyLaw_exists`. -/
theorem cgmyCpProbability_tendsto_cgmyLaw (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) :
    Tendsto (fun n : ℕ => cgmyCpProbability C G M Y τ ((2 : ℝ≥0)⁻¹ ^ n) hC hG hM hY
        (pow_pos (inv_pos.mpr (by norm_num : (0 : ℝ≥0) < 2)) n))
      atTop (𝓝 (cgmyLaw C G M Y τ hC hG hM hY hY₂)) :=
  tendsto_nhds_limUnder (cgmyLaw_exists C G M Y hC hG hM hY hY₂ τ)

/-- **The headline of §2**: the characteristic function of the CGMY law is
`exp (τ · L(v))` — a *theorem* about the limit, not a definition. Lévy continuity
(`tendsto_iff_tendsto_charFun.mp`) applied to the previous line, identified
against `charFun_cgmyCpProbability_tendsto` by `tendsto_nhds_unique`. Note that
`cgmyExponent` does not appear: the CF at the law is `exp (τ L)` first, and
becomes `exp (τ ψ_Y)` only through §3 (lint clause `[CGMYLaw]` R3). -/
theorem charFun_cgmyLaw (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) (t : ℝ) :
    charFun (cgmyLaw C G M Y τ hC hG hM hY hY₂ : Measure ℝ) t
      = Complex.exp ((τ : ℂ) * cgmyLKExponent C G M Y t) :=
  tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
      (cgmyCpProbability_tendsto_cgmyLaw C G M Y hC hG hM hY hY₂ τ) t)
    (charFun_cgmyCpProbability_tendsto C G M Y hC hG hM hY hY₂ τ t)

/-- **Uniqueness**: `cgmyLaw` is the *only* probability measure with that
characteristic function (`Measure.ext_of_charFun`). This is what lets a later
brief replace the `limUnder` construction by any other one without touching the
CF layer above it. -/
theorem cgmyLaw_unique (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (τ : ℝ≥0) (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ)
    (hcf : ∀ t : ℝ, charFun μ t = Complex.exp ((τ : ℂ) * cgmyLKExponent C G M Y t)) :
    μ = cgmyLaw C G M Y τ hC hG hM hY hY₂ := by
  have := hμ
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [hcf t, charFun_cgmyLaw C G M Y hC hG hM hY hY₂ τ t]

/-!
---------------------------------------------------------------------------
§3  G1 and the identification (`Y ≠ 1` from here on)
---------------------------------------------------------------------------
-/

/-- The **complex-rate Γ integral**: `∫₀^∞ x^{s−1} e^{−zx} dx`. mathlib at the
tag ships the real-rate version (`integral_cpow_mul_exp_neg_mul_Ioi`, rate
`r : ℝ`); this is the same integral at a complex rate in the open right
half-plane, which is what the CGMY one-sided legs need at `z = M − iv`. -/
def gammaIntegralComplexRate (s : ℝ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((s : ℂ) - 1) * Complex.exp (-(z * (x : ℂ)))

/-! ### The Γ integrand: continuity, norm, integrability, derivative in the rate -/

theorem cgmy_cpow_continuousOn (c : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ c) (Ioi 0) :=
  continuousOn_of_forall_continuousAt fun x hx =>
    Complex.continuousAt_ofReal_cpow_const x c (Or.inr (ne_of_gt hx))

theorem cgmy_ofReal_rpow_continuousOn (p : ℝ) :
    ContinuousOn (fun x : ℝ => ((x ^ p : ℝ) : ℂ)) (Ioi 0) :=
  Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx))

theorem cgmy_cexp_neg_mul_continuous (z : ℂ) :
    Continuous fun x : ℝ => Complex.exp (-(z * x)) :=
  Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)

theorem cgmyGammaIntegrand_continuousOn (c z : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ c * Complex.exp (-(z * x))) (Ioi 0) :=
  (cgmy_cpow_continuousOn c).mul (cgmy_cexp_neg_mul_continuous z).continuousOn

theorem norm_cexp_neg_mul (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-(z * x))‖ = Real.exp (-z.re * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_cgmyGammaIntegrand {c z : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ c * Complex.exp (-(z * x))‖ = x ^ c.re * Real.exp (-z.re * x) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_cexp_neg_mul]

/-- `x^{Re c} e^{−Re z·x}` is integrable on `(0, ∞)` for `Re c > −1`, `Re z > 0`
(mathlib's `integrableOn_rpow_mul_exp_neg_mul_rpow` at power `1`). -/
theorem integrableOn_rpow_mul_exp_neg_mul {p b : ℝ} (hp : -1 < p) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-b * x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hp one_pos hb
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]

theorem cgmyGammaIntegrand_integrableOn {c z : ℂ} (hc : -1 < c.re) (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ c * Complex.exp (-(z * x))) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul hc hz)
    ((cgmyGammaIntegrand_continuousOn c z).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact le_of_eq (norm_cgmyGammaIntegrand hx)

theorem cgmyGammaIntegrand_hasDerivAt (c : ℂ) (x : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => (x : ℂ) ^ c * Complex.exp (-(w * x)))
      ((x : ℂ) ^ c * (Complex.exp (-(w * x)) * -(1 * (x : ℂ)))) w := by
  have h1 : HasDerivAt (fun w : ℂ => -(w * (x : ℂ))) (-(1 * (x : ℂ))) w :=
    ((hasDerivAt_id w).mul_const (x : ℂ)).neg
  exact (h1.cexp).const_mul _

theorem norm_cgmyGammaIntegrand_deriv {c w : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ c * (Complex.exp (-(w * x)) * -(1 * (x : ℂ)))‖
      = x ^ c.re * (Real.exp (-w.re * x) * x) := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_cexp_neg_mul, norm_neg,
    one_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]

/-- **G1**: for `0 < s` and `0 < Re z`, `∫₀^∞ x^{s−1} e^{−zx} dx = Γ(s)·z^{−s}`.

The identity theorem, not a contour (F4). The left side is differentiable in `z`
on the half-plane by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (the
derivative is `−∫ x^s e^{−zx}`, dominated on `Re z > δ` by `x^s e^{−δx}`, which
is integrable at `s + 1`), hence analytic there by
`DifferentiableOn.analyticOnNhd`; the right side is analytic away from the branch
cut, which the half-plane avoids; the half-plane is convex
(`convex_halfSpace_re_gt`) hence preconnected; and the two agree on the positive
reals — which accumulate at `1` — by the *shipped* real-rate lemma
`integral_cpow_mul_exp_neg_mul_Ioi`. Measured `≤ 2.9e−11` at `z = M − iv`, the
same residual as the real anchor, i.e. the quadrature's and not the identity's. -/
theorem integral_cpow_mul_cexp_neg_mul_Ioi (s : ℝ) (z : ℂ) (hs : 0 < s) (hz : 0 < z.re) :
    gammaIntegralComplexRate s z = (Real.Gamma s : ℂ) * z ^ (-(s : ℂ)) := by
  -- the open right half-plane
  have hUopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have h1U : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
  have hsre : ((s : ℂ) - 1).re = s - 1 := by simp
  -- (a) the left side is complex-differentiable on the half-plane
  have hdiff : ∀ z₀ ∈ {w : ℂ | 0 < w.re}, DifferentiableAt ℂ (gammaIntegralComplexRate s) z₀ := by
    intro z₀ hz₀
    have hz₀' : 0 < z₀.re := hz₀
    have hδ : 0 < z₀.re / 2 := half_pos hz₀'
    have hnhds : {w : ℂ | z₀.re / 2 < w.re} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show z₀.re / 2 < z₀.re by linarith)
    have hbound : IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-(z₀.re / 2) * x)) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul (by linarith) hδ
    have hF'_cont : ContinuousOn (fun x : ℝ =>
        (x : ℂ) ^ ((s : ℂ) - 1) * (Complex.exp (-(z₀ * x)) * -(1 * (x : ℂ)))) (Ioi 0) :=
      (cgmy_cpow_continuousOn ((s : ℂ) - 1)).mul
        ((cgmy_cexp_neg_mul_continuous z₀).continuousOn.mul
          ((continuous_const.mul Complex.continuous_ofReal).neg.continuousOn))
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun (w : ℂ) (x : ℝ) => (x : ℂ) ^ ((s : ℂ) - 1) * Complex.exp (-(w * x)))
      (F' := fun (w : ℂ) (x : ℝ) =>
        (x : ℂ) ^ ((s : ℂ) - 1) * (Complex.exp (-(w * x)) * -(1 * (x : ℂ))))
      (bound := fun x : ℝ => x ^ s * Real.exp (-(z₀.re / 2) * x)) hnhds
      (Eventually.of_forall fun w =>
        (cgmyGammaIntegrand_continuousOn ((s : ℂ) - 1) w).aestronglyMeasurable measurableSet_Ioi)
      (cgmyGammaIntegrand_integrableOn (c := (s : ℂ) - 1) (by rw [hsre]; linarith) hz₀')
      (hF'_cont.aestronglyMeasurable measurableSet_Ioi) ?_ hbound
      (ae_of_all _ fun x w _ => cgmyGammaIntegrand_hasDerivAt ((s : ℂ) - 1) x w)
    · exact key.2.differentiableAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx w hw
      have hx0 : (0 : ℝ) < x := hx
      have hw' : z₀.re / 2 < w.re := hw
      rw [norm_cgmyGammaIntegrand_deriv hx0, hsre]
      have hpow : x ^ (s - 1) * x = x ^ s := by
        rw [Real.rpow_sub_one hx0.ne', div_mul_cancel₀ _ hx0.ne']
      have hexp : Real.exp (-w.re * x) ≤ Real.exp (-(z₀.re / 2) * x) := by
        rw [Real.exp_le_exp]
        have := mul_le_mul_of_nonneg_right hw'.le hx0.le
        linarith
      calc x ^ (s - 1) * (Real.exp (-w.re * x) * x)
          = (x ^ (s - 1) * x) * Real.exp (-w.re * x) := by ring
        _ = x ^ s * Real.exp (-w.re * x) := by rw [hpow]
        _ ≤ x ^ s * Real.exp (-(z₀.re / 2) * x) :=
            mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hx0.le _)
  have hF_an : AnalyticOnNhd ℂ (gammaIntegralComplexRate s) {w : ℂ | 0 < w.re} :=
    DifferentiableOn.analyticOnNhd (fun z₀ hz₀ => (hdiff z₀ hz₀).differentiableWithinAt) hUopen
  -- (b) the right side is analytic off the branch cut
  have hg_an : AnalyticOnNhd ℂ (fun w : ℂ => (Real.Gamma s : ℂ) * w ^ (-(s : ℂ)))
      {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUopen
    have hw' : 0 < w.re := hw
    exact ((differentiableAt_id.cpow (differentiableAt_const (-(s : ℂ)))
      (Complex.mem_slitPlane_iff.mpr (Or.inl hw'))).const_mul
        (Real.Gamma s : ℂ)).differentiableWithinAt
  -- (c) they agree on the positive reals, by the shipped real-rate lemma
  have hagree : ∀ r : ℝ, 0 < r →
      gammaIntegralComplexRate s (r : ℂ) = (Real.Gamma s : ℂ) * (r : ℂ) ^ (-(s : ℂ)) := by
    intro r hr
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := (s : ℂ)) (r := r)
      (by rwa [Complex.ofReal_re]) hr
    have harg : (r : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact Real.pi_ne_zero.symm
    unfold gammaIntegralComplexRate
    rw [h, Complex.Gamma_ofReal, mul_comm, one_div, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  -- (d) the positive reals accumulate at `1` inside the half-plane
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ),
      gammaIntegralComplexRate s w = (Real.Gamma s : ℂ) * w ^ (-(s : ℂ)) := by
    have hmap : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := {(1 : ℝ)}ᶜ))
        rwa [Complex.ofReal_one] at h
      · exact eventually_nhdsWithin_of_forall fun r hr => by
          simpa [Complex.ofReal_eq_one] using hr
    refine hmap.frequently (Eventually.frequently ?_)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds zero_lt_one)]
      with r hr
    exact hagree r hr
  exact hF_an.eqOn_of_preconnected_of_frequently_eq hg_an hUpre h1U hfreq hz

/-- G1 in the form the legs consume: `∫₀^∞ x^p e^{−zx} dx = Γ(p+1) z^{−(p+1)}`
for `p > −1`, `Re z > 0`, with a real power inside the cast. -/
theorem integral_ofReal_rpow_mul_cexp_Ioi {p : ℝ} (hp : -1 < p) {z : ℂ} (hz : 0 < z.re) :
    ∫ x in Ioi (0 : ℝ), ((x ^ p : ℝ) : ℂ) * Complex.exp (-(z * x))
      = (Real.Gamma (p + 1) : ℂ) * z ^ (-((p : ℂ) + 1)) := by
  have h := integral_cpow_mul_cexp_neg_mul_Ioi (p + 1) z (by linarith) hz
  unfold gammaIntegralComplexRate at h
  have e1 : -(((p + 1 : ℝ)) : ℂ) = -((p : ℂ) + 1) := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
  rw [e1] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [Complex.ofReal_cpow hx0.le, Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_right]

theorem integrableOn_ofReal_rpow_mul_cexp {p : ℝ} (hp : -1 < p) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => ((x ^ p : ℝ) : ℂ) * Complex.exp (-(z * x))) (Ioi 0) := by
  refine (cgmyGammaIntegrand_integrableOn (c := (p : ℂ)) (by rwa [Complex.ofReal_re]) hz).congr_fun
    (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  rw [Complex.ofReal_cpow hx0.le]

theorem hasDerivAt_cexp_neg_mul (z : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (-(z * y))) (Complex.exp (-(z * x)) * -(z * 1)) x := by
  have h : HasDerivAt (fun ζ : ℂ => Complex.exp (-(z * ζ)))
      (Complex.exp (-(z * x)) * -(z * 1)) (x : ℂ) :=
    (((hasDerivAt_id (x : ℂ)).const_mul z).neg).cexp
  exact h.comp_ofReal

/-- `z * z^{a−1} = z^a` for `z ≠ 0`. -/
theorem cgmy_mul_cpow_sub_one {z : ℂ} (hz : z ≠ 0) (a : ℂ) : z * z ^ (a - 1) = z ^ a := by
  rw [Complex.cpow_sub _ _ hz, Complex.cpow_one, ← mul_div_assoc, mul_div_cancel_left₀ _ hz]

/-- `exp` is `e^r`-Lipschitz on the half-plane `Re ≤ r` (mean value inequality on
a convex set). -/
theorem norm_cexp_sub_cexp_le {p q : ℂ} {r : ℝ} (hp : p.re ≤ r) (hq : q.re ≤ r) :
    ‖Complex.exp p - Complex.exp q‖ ≤ Real.exp r * ‖p - q‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Complex.exp) (f' := Complex.exp) (s := {w : ℂ | w.re ≤ r}) (C := Real.exp r)
    (fun w _ => (Complex.hasDerivAt_exp w).hasDerivWithinAt)
    (fun w hw => by rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hw)
    (convex_halfSpace_re_le r) hq hp

/-- `‖e^{−zx} − e^{−wx}‖ ≤ e^{−cx} ‖w − z‖ x` for `x ≥ 0` and `c ≤ Re z, Re w`. -/
theorem norm_cexp_neg_mul_sub_le (z w : ℂ) {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hcz : c ≤ z.re)
    (hcw : c ≤ w.re) :
    ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖ ≤ Real.exp (-(c * x)) * (‖w - z‖ * x) := by
  have hz' : (-(z * (x : ℂ))).re ≤ -(c * x) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    have := mul_le_mul_of_nonneg_right hcz hx
    linarith
  have hw' : (-(w * (x : ℂ))).re ≤ -(c * x) := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    have := mul_le_mul_of_nonneg_right hcw hx
    linarith
  calc ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖
      ≤ Real.exp (-(c * x)) * ‖-(z * (x : ℂ)) - -(w * (x : ℂ))‖ := norm_cexp_sub_cexp_le hz' hw'
    _ = Real.exp (-(c * x)) * (‖w - z‖ * x) := by
        rw [show -(z * (x : ℂ)) - -(w * (x : ℂ)) = (w - z) * (x : ℂ) by ring, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hx]

/-- The compensated leg `e^{−zx} − e^{−wx} + (z−w) x e^{−wx}` is `O(x²)` at `0`
and exponentially small at `∞`, uniformly: it is `e^{−wx}(e^ζ − 1 − ζ)` with
`ζ = −(z−w)x`, and `norm_cexp_sub_one_sub_le` does the rest. This is the Taylor
step that CGMY.lean's header labelled prose. -/
theorem norm_cgmyCompensatedLeg_le (z w : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x)) + (z - w) * x * Complex.exp (-(w * x))‖
      ≤ 3 * ‖z - w‖ ^ 2 * (x ^ 2 * (Real.exp (-z.re * x) + Real.exp (-w.re * x))) := by
  have hfac : Complex.exp (-(z * x)) - Complex.exp (-(w * x))
        + (z - w) * x * Complex.exp (-(w * x))
      = Complex.exp (-(w * x)) *
          (Complex.exp (-((z - w) * (x : ℂ))) - 1 - -((z - w) * (x : ℂ))) := by
    rw [show -(z * (x : ℂ)) = -(w * (x : ℂ)) + -((z - w) * (x : ℂ)) by ring, Complex.exp_add]
    ring
  rw [hfac, norm_mul, norm_cexp_neg_mul]
  have hζn : ‖-((z - w) * (x : ℂ))‖ = ‖z - w‖ * x := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]
  have hζre : (-((z - w) * (x : ℂ))).re = -((z.re - w.re) * x) := by
    simp [Complex.mul_re]
  calc Real.exp (-w.re * x) * ‖Complex.exp (-((z - w) * (x : ℂ))) - 1 - -((z - w) * (x : ℂ))‖
      ≤ Real.exp (-w.re * x) *
          (3 * Real.exp (max 0 (-((z - w) * (x : ℂ))).re) * ‖-((z - w) * (x : ℂ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_cexp_sub_one_sub_le _) (Real.exp_pos _).le
    _ = 3 * ‖z - w‖ ^ 2 *
          (x ^ 2 * (Real.exp (-w.re * x) * Real.exp (max 0 (-((z - w) * (x : ℂ))).re))) := by
        rw [hζn]
        ring
    _ ≤ 3 * ‖z - w‖ ^ 2 * (x ^ 2 * (Real.exp (-z.re * x) + Real.exp (-w.re * x))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
        rw [← Real.exp_add, hζre]
        rcases le_total 0 (-((z.re - w.re) * x)) with h0 | h0
        · rw [max_eq_right h0]
          have : -w.re * x + -((z.re - w.re) * x) = -z.re * x := by ring
          rw [this]
          linarith [Real.exp_pos (-w.re * x)]
        · rw [max_eq_left h0, add_zero]
          linarith [Real.exp_pos (-z.re * x)]

/-! ### The one-sided closed forms -/

/-- Integrability of `x^{−1−Y}(e^{−zx} − e^{−wx})` on `(0, ∞)` for `0 < Y < 1`:
dominated by `‖w − z‖ x^{−Y} e^{−cx}`, `c = min (Re z) (Re w)`. -/
theorem integrableOn_rpow_mul_cexp_sub_cexp (Y : ℝ) (z w : ℂ) (hY : 0 < Y) (hY₁ : Y < 1)
    (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => ((x ^ (-1 - Y) : ℝ) : ℂ) *
      (Complex.exp (-(z * x)) - Complex.exp (-(w * x)))) (Ioi 0) := by
  have hc0 : 0 < min z.re w.re := lt_min hz hw
  have hcz : min z.re w.re ≤ z.re := min_le_left _ _
  have hcw : min z.re w.re ≤ w.re := min_le_right _ _
  have hbound : IntegrableOn
      (fun x : ℝ => ‖w - z‖ * (x ^ (-Y) * Real.exp (-(min z.re w.re) * x))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul (by linarith : (-1 : ℝ) < -Y) hc0).const_mul _
  refine Integrable.mono' hbound ?_ ?_
  · exact ((cgmy_ofReal_rpow_continuousOn (-1 - Y)).mul
      ((cgmy_cexp_neg_mul_continuous z).continuousOn.sub
        (cgmy_cexp_neg_mul_continuous w).continuousOn)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hv := norm_cexp_neg_mul_sub_le z w hx0.le hcz hcw
    have hpow : x ^ (-1 - Y) * x = x ^ (-Y) := by
      rw [show (-Y) = (-1 - Y) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    calc x ^ (-1 - Y) * ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖
        ≤ x ^ (-1 - Y) * (Real.exp (-(min z.re w.re * x)) * (‖w - z‖ * x)) :=
          mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg hx0.le _)
      _ = ‖w - z‖ * ((x ^ (-1 - Y) * x) * Real.exp (-(min z.re w.re) * x)) := by
          rw [neg_mul]
          ring
      _ = ‖w - z‖ * (x ^ (-Y) * Real.exp (-(min z.re w.re) * x)) := by rw [hpow]

/-- **The one-sided closed form at complex rates, `0 < Y < 1`**:
`∫₀^∞ x^{−1−Y}(e^{−zx} − e^{−wx}) dx = Γ(−Y)(z^Y − w^Y)` for `Re z, Re w > 0`.
One integration by parts (`integral_Ioi_mul_deriv_eq_deriv_mul`) with
`u = x^{−Y}/(−Y)`, `v = e^{−zx} − e^{−wx}`; both boundary terms vanish because
`‖v‖ ≤ ‖w − z‖ x` at `0` and `x^{−Y}e^{−cx} → 0` at `∞`; the remaining integrals
are G1 at `s = 1 − Y`, and `Γ(1−Y) = −Y Γ(−Y)` closes. -/
theorem integral_rpow_mul_cexp_sub_cexp_Ioi (Y : ℝ) (z w : ℂ) (hY : 0 < Y) (hY₁ : Y < 1)
    (hz : 0 < z.re) (hw : 0 < w.re) :
    ∫ x in Ioi (0 : ℝ), ((x ^ (-1 - Y) : ℝ) : ℂ) *
        (Complex.exp (-(z * x)) - Complex.exp (-(w * x)))
      = (Real.Gamma (-Y) : ℂ) * (z ^ (Y : ℂ) - w ^ (Y : ℂ)) := by
  have hYc : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    exact lt_irrefl _ hw
  -- the Γ-integrals at exponent `-Y`
  have hIz := integral_ofReal_rpow_mul_cexp_Ioi (by linarith : (-1 : ℝ) < -Y) hz
  have hIw := integral_ofReal_rpow_mul_cexp_Ioi (by linarith : (-1 : ℝ) < -Y) hw
  have hIz_int := integrableOn_ofReal_rpow_mul_cexp (by linarith : (-1 : ℝ) < -Y) hz
  have hIw_int := integrableOn_ofReal_rpow_mul_cexp (by linarith : (-1 : ℝ) < -Y) hw
  -- integration by parts data
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => ((y ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)))
      (((x ^ (-1 - Y) : ℝ) : ℂ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h := ((Real.hasDerivAt_rpow_const (p := -Y) (Or.inl hx0.ne')).ofReal_comp).div_const
      (-(Y : ℂ))
    refine h.congr_deriv ?_
    rw [show -Y - 1 = -1 - Y by ring, Complex.ofReal_mul, Complex.ofReal_neg, mul_div_right_comm,
      div_self (neg_ne_zero.mpr hYc), one_mul]
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun y : ℝ => Complex.exp (-(z * y)) - Complex.exp (-(w * y)))
      (Complex.exp (-(z * x)) * -(z * 1) - Complex.exp (-(w * x)) * -(w * 1)) x :=
    fun x _ => (hasDerivAt_cexp_neg_mul z x).sub (hasDerivAt_cexp_neg_mul w x)
  have huv' : IntegrableOn (fun x : ℝ => ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (Complex.exp (-(z * x)) * -(z * 1) - Complex.exp (-(w * x)) * -(w * 1))) (Ioi 0) := by
    have h := (hIz_int.const_mul (z / Y)).sub (hIw_int.const_mul (w / Y))
    refine IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hu'v := integrableOn_rpow_mul_cexp_sub_cexp Y z w hY hY₁ hz hw
  -- the boundary term at `0⁺`
  have h_zero : Tendsto (fun x : ℝ => ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (Complex.exp (-(z * x)) - Complex.exp (-(w * x)))) (𝓝[>] 0) (𝓝 0) := by
    have h1Y : (0 : ℝ) < 1 - Y := by linarith
    have hlim : Tendsto (fun x : ℝ => (‖w - z‖ / Y) * x ^ (1 - Y)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => x ^ (1 - Y)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - Y))) :=
        ((Real.continuousAt_rpow_const 0 (1 - Y) (Or.inr h1Y.le)).tendsto).mono_left
          nhdsWithin_le_nhds
      rw [Real.zero_rpow h1Y.ne'] at h
      have h' := h.const_mul (‖w - z‖ / Y)
      simp only [mul_zero] at h'
      exact h'
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hv0 : ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖ ≤ ‖w - z‖ * x := by
      have := norm_cexp_neg_mul_sub_le z w hx0.le hz.le hw.le
      simpa using this
    have hpow : x ^ (-Y) * x = x ^ (1 - Y) := by
      rw [show (1 - Y) = -Y + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
      norm_neg, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc x ^ (-Y) / Y * ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖
        ≤ x ^ (-Y) / Y * (‖w - z‖ * x) :=
          mul_le_mul_of_nonneg_left hv0 (div_nonneg (Real.rpow_nonneg hx0.le _) hY.le)
      _ = (‖w - z‖ / Y) * (x ^ (-Y) * x) := by ring
      _ = (‖w - z‖ / Y) * x ^ (1 - Y) := by rw [hpow]
  -- the boundary term at `∞`
  have h_infty : Tendsto (fun x : ℝ => ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (Complex.exp (-(z * x)) - Complex.exp (-(w * x)))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => (1 / Y) *
        (x ^ (-Y) * Real.exp (-z.re * x) + x ^ (-Y) * Real.exp (-w.re * x))) atTop (𝓝 0) := by
      have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-Y) z.re hz).add
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-Y) w.re hw)).const_mul (1 / Y)
      simp only [add_zero, mul_zero] at h
      exact h
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hv0 : ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖
        ≤ Real.exp (-z.re * x) + Real.exp (-w.re * x) := by
      calc ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖
          ≤ ‖Complex.exp (-(z * x))‖ + ‖Complex.exp (-(w * x))‖ := norm_sub_le _ _
        _ = Real.exp (-z.re * x) + Real.exp (-w.re * x) := by
            rw [norm_cexp_neg_mul, norm_cexp_neg_mul]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
      norm_neg, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc x ^ (-Y) / Y * ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖
        ≤ x ^ (-Y) / Y * (Real.exp (-z.re * x) + Real.exp (-w.re * x)) :=
          mul_le_mul_of_nonneg_left hv0 (div_nonneg (Real.rpow_nonneg hx.le _) hY.le)
      _ = (1 / Y) * (x ^ (-Y) * Real.exp (-z.re * x) + x ^ (-Y) * Real.exp (-w.re * x)) := by
          ring
  -- integration by parts
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [sub_zero, zero_sub] at hibp
  -- the `u v'` integral in terms of the two Γ-integrals
  have hcomp : ∫ x in Ioi (0 : ℝ), ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (Complex.exp (-(z * x)) * -(z * 1) - Complex.exp (-(w * x)) * -(w * 1))
      = (z / Y) * (∫ x in Ioi (0 : ℝ), ((x ^ (-Y) : ℝ) : ℂ) * Complex.exp (-(z * x)))
        - (w / Y) * ∫ x in Ioi (0 : ℝ), ((x ^ (-Y) : ℝ) : ℂ) * Complex.exp (-(w * x)) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (hIz_int.const_mul _) (hIw_int.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have e1 : -((((-Y : ℝ)) : ℂ) + 1) = (Y : ℂ) - 1 := by
    rw [Complex.ofReal_neg]
    ring
  have hΓ : Real.Gamma (-Y + 1) = -Y * Real.Gamma (-Y) :=
    Real.Gamma_add_one (neg_ne_zero.mpr hY.ne')
  rw [e1, hΓ] at hIz hIw
  rw [hcomp, hIz, hIw] at hibp
  have hfinal := (neg_eq_iff_eq_neg.mpr hibp).symm
  refine hfinal.trans ?_
  rw [← cgmy_mul_cpow_sub_one hz0 (Y : ℂ), ← cgmy_mul_cpow_sub_one hw0 (Y : ℂ)]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  field_simp
  ring

/-- Integrability of the compensated leg `x^{−1−Y}(e^{−zx} − e^{−wx} + (z−w)xe^{−wx})`
on `(0, ∞)` for `1 < Y < 2`: dominated by `3‖z−w‖² x^{1−Y}(e^{−Re z·x} + e^{−Re w·x})`. -/
theorem integrableOn_rpow_mul_cexp_compensated (Y : ℝ) (z w : ℂ) (hY₁ : 1 < Y) (hY₂ : Y < 2)
    (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => ((x ^ (-1 - Y) : ℝ) : ℂ) *
      (Complex.exp (-(z * x)) - Complex.exp (-(w * x))
        + (z - w) * x * Complex.exp (-(w * x)))) (Ioi 0) := by
  have hbound : IntegrableOn (fun x : ℝ => 3 * ‖z - w‖ ^ 2 *
      (x ^ (1 - Y) * Real.exp (-z.re * x) + x ^ (1 - Y) * Real.exp (-w.re * x))) (Ioi 0) :=
    ((integrableOn_rpow_mul_exp_neg_mul (by linarith : (-1 : ℝ) < 1 - Y) hz).add
      (integrableOn_rpow_mul_exp_neg_mul (by linarith : (-1 : ℝ) < 1 - Y) hw)).const_mul _
  refine Integrable.mono' hbound ?_ ?_
  · exact ((cgmy_ofReal_rpow_continuousOn (-1 - Y)).mul
      ((((cgmy_cexp_neg_mul_continuous z).sub (cgmy_cexp_neg_mul_continuous w)).add
        ((continuous_const.mul Complex.continuous_ofReal).mul
          (cgmy_cexp_neg_mul_continuous w))).continuousOn)).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hf := norm_cgmyCompensatedLeg_le z w hx0.le
    have hpow : x ^ (-1 - Y) * x ^ 2 = x ^ (1 - Y) := by
      rw [← Real.rpow_two, ← Real.rpow_add hx0]
      congr 1
      ring
    calc x ^ (-1 - Y) * ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))
          + (z - w) * x * Complex.exp (-(w * x))‖
        ≤ x ^ (-1 - Y) *
            (3 * ‖z - w‖ ^ 2 * (x ^ 2 * (Real.exp (-z.re * x) + Real.exp (-w.re * x)))) :=
          mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hx0.le _)
      _ = 3 * ‖z - w‖ ^ 2 *
            ((x ^ (-1 - Y) * x ^ 2) * (Real.exp (-z.re * x) + Real.exp (-w.re * x))) := by ring
      _ = 3 * ‖z - w‖ ^ 2 *
            (x ^ (1 - Y) * Real.exp (-z.re * x) + x ^ (1 - Y) * Real.exp (-w.re * x)) := by
          rw [hpow]
          ring

/-- **The one-sided compensated closed form at complex rates, `1 < Y < 2`**:
`∫₀^∞ x^{−1−Y}(e^{−zx} − e^{−wx} + (z−w)xe^{−wx}) dx = Γ(−Y)(z^Y − w^Y − (z−w)Y w^{Y−1})`.
One integration by parts with `u = x^{−Y}/(−Y)` and `v = f`, where
`f(0) = f'(0) = 0` kills the boundary term at `0` (`‖f‖ = O(x²)`); the remaining
integral `∫ x^{−Y} f'` is the `0 < Y < 1` closed form at `Y − 1` plus one G1 at
`s = 2 − Y`, and `Γ(2−Y) = (1−Y)Γ(1−Y) = (1−Y)(−Y)Γ(−Y)` closes. -/
theorem integral_rpow_mul_cexp_compensated_Ioi (Y : ℝ) (z w : ℂ) (hY₁ : 1 < Y) (hY₂ : Y < 2)
    (hz : 0 < z.re) (hw : 0 < w.re) :
    ∫ x in Ioi (0 : ℝ), ((x ^ (-1 - Y) : ℝ) : ℂ) *
        (Complex.exp (-(z * x)) - Complex.exp (-(w * x))
          + (z - w) * x * Complex.exp (-(w * x)))
      = (Real.Gamma (-Y) : ℂ) *
          (z ^ (Y : ℂ) - w ^ (Y : ℂ) - (z - w) * (Y : ℂ) * w ^ ((Y : ℂ) - 1)) := by
  have hY : 0 < Y := by linarith
  have hYc : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    exact lt_irrefl _ hw
  -- the `0 < Y < 1` form at `Y − 1`, and G1 at exponent `1 − Y`
  have hP1 := integral_rpow_mul_cexp_sub_cexp_Ioi (Y - 1) z w (by linarith) (by linarith) hz hw
  have hP1_int := integrableOn_rpow_mul_cexp_sub_cexp (Y - 1) z w (by linarith) (by linarith)
    hz hw
  rw [show -1 - (Y - 1) = -Y by ring] at hP1 hP1_int
  have hIw := integral_ofReal_rpow_mul_cexp_Ioi (by linarith : (-1 : ℝ) < 1 - Y) hw
  have hIw_int := integrableOn_ofReal_rpow_mul_cexp (by linarith : (-1 : ℝ) < 1 - Y) hw
  -- integration by parts data
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => ((y ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)))
      (((x ^ (-1 - Y) : ℝ) : ℂ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h := ((Real.hasDerivAt_rpow_const (p := -Y) (Or.inl hx0.ne')).ofReal_comp).div_const
      (-(Y : ℂ))
    refine h.congr_deriv ?_
    rw [show -Y - 1 = -1 - Y by ring, Complex.ofReal_mul, Complex.ofReal_neg, mul_div_right_comm,
      div_self (neg_ne_zero.mpr hYc), one_mul]
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun y : ℝ => Complex.exp (-(z * y)) - Complex.exp (-(w * y))
        + (z - w) * y * Complex.exp (-(w * y)))
      (-z * Complex.exp (-(z * x)) + z * Complex.exp (-(w * x))
        - (z - w) * w * x * Complex.exp (-(w * x))) x := by
    intro x _
    have h1 := (hasDerivAt_cexp_neg_mul z x).sub (hasDerivAt_cexp_neg_mul w x)
    have h2 := (((hasDerivAt_id' x : HasDerivAt (fun y : ℝ => y) 1 x).ofReal_comp).const_mul
      (z - w)).mul (hasDerivAt_cexp_neg_mul w x)
    refine (h1.add h2).congr_deriv ?_
    push_cast
    ring
  have huv' : IntegrableOn (fun x : ℝ => ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (-z * Complex.exp (-(z * x)) + z * Complex.exp (-(w * x))
        - (z - w) * w * x * Complex.exp (-(w * x)))) (Ioi 0) := by
    have h := (hP1_int.const_mul (z / Y)).add (hIw_int.const_mul ((z - w) * w / Y))
    refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    have hpow : x ^ (1 - Y) = x ^ (-Y) * x := by
      rw [show (1 - Y) = -Y + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    simp only [Pi.add_apply, hpow, Complex.ofReal_mul]
    ring
  have hu'v := integrableOn_rpow_mul_cexp_compensated Y z w hY₁ hY₂ hz hw
  -- the boundary term at `0⁺`: `‖f‖ = O(x²)`, so `‖u v‖ = O(x^{2−Y})`
  have h_zero : Tendsto (fun x : ℝ => ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (Complex.exp (-(z * x)) - Complex.exp (-(w * x))
        + (z - w) * x * Complex.exp (-(w * x)))) (𝓝[>] 0) (𝓝 0) := by
    have h2Y : (0 : ℝ) < 2 - Y := by linarith
    have hlim : Tendsto (fun x : ℝ => (6 * ‖z - w‖ ^ 2 / Y) * x ^ (2 - Y)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => x ^ (2 - Y)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (2 - Y))) :=
        ((Real.continuousAt_rpow_const 0 (2 - Y) (Or.inr h2Y.le)).tendsto).mono_left
          nhdsWithin_le_nhds
      rw [Real.zero_rpow h2Y.ne'] at h
      have h' := h.const_mul (6 * ‖z - w‖ ^ 2 / Y)
      simp only [mul_zero] at h'
      exact h'
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hf := norm_cgmyCompensatedLeg_le z w hx0.le
    have he1 : Real.exp (-z.re * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he2 : Real.exp (-w.re * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hpow : x ^ (-Y) * x ^ 2 = x ^ (2 - Y) := by
      rw [← Real.rpow_two, ← Real.rpow_add hx0]
      congr 1
      ring
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
      norm_neg, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc x ^ (-Y) / Y * ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))
          + (z - w) * x * Complex.exp (-(w * x))‖
        ≤ x ^ (-Y) / Y *
            (3 * ‖z - w‖ ^ 2 * (x ^ 2 * (Real.exp (-z.re * x) + Real.exp (-w.re * x)))) :=
          mul_le_mul_of_nonneg_left hf (div_nonneg (Real.rpow_nonneg hx0.le _) hY.le)
      _ ≤ x ^ (-Y) / Y * (3 * ‖z - w‖ ^ 2 * (x ^ 2 * (1 + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Real.rpow_nonneg hx0.le _) hY.le)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
          linarith
      _ = (6 * ‖z - w‖ ^ 2 / Y) * (x ^ (-Y) * x ^ 2) := by ring
      _ = (6 * ‖z - w‖ ^ 2 / Y) * x ^ (2 - Y) := by rw [hpow]
  -- the boundary term at `∞`
  have h_infty : Tendsto (fun x : ℝ => ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (Complex.exp (-(z * x)) - Complex.exp (-(w * x))
        + (z - w) * x * Complex.exp (-(w * x)))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => (1 / Y) *
        (x ^ (-Y) * Real.exp (-z.re * x) + x ^ (-Y) * Real.exp (-w.re * x)
          + ‖z - w‖ * (x ^ (1 - Y) * Real.exp (-w.re * x)))) atTop (𝓝 0) := by
      have h := (((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-Y) z.re hz).add
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-Y) w.re hw)).add
        ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 - Y) w.re hw).const_mul
          ‖z - w‖)).const_mul (1 / Y)
      simp only [add_zero, mul_zero] at h
      exact h
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hv0 : ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))
          + (z - w) * x * Complex.exp (-(w * x))‖
        ≤ Real.exp (-z.re * x) + Real.exp (-w.re * x) + ‖z - w‖ * x * Real.exp (-w.re * x) := by
      calc ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))
            + (z - w) * x * Complex.exp (-(w * x))‖
          ≤ ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))‖
              + ‖(z - w) * x * Complex.exp (-(w * x))‖ := norm_add_le _ _
        _ ≤ (‖Complex.exp (-(z * x))‖ + ‖Complex.exp (-(w * x))‖)
              + ‖(z - w) * x * Complex.exp (-(w * x))‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
        _ = Real.exp (-z.re * x) + Real.exp (-w.re * x)
              + ‖z - w‖ * x * Real.exp (-w.re * x) := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le,
              norm_cexp_neg_mul, norm_cexp_neg_mul]
    have hpow : x ^ (-Y) * x = x ^ (1 - Y) := by
      rw [show (1 - Y) = -Y + 1 by ring, Real.rpow_add hx, Real.rpow_one]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
      norm_neg, Complex.norm_real, Real.norm_of_nonneg hY.le]
    calc x ^ (-Y) / Y * ‖Complex.exp (-(z * x)) - Complex.exp (-(w * x))
          + (z - w) * x * Complex.exp (-(w * x))‖
        ≤ x ^ (-Y) / Y * (Real.exp (-z.re * x) + Real.exp (-w.re * x)
            + ‖z - w‖ * x * Real.exp (-w.re * x)) :=
          mul_le_mul_of_nonneg_left hv0 (div_nonneg (Real.rpow_nonneg hx.le _) hY.le)
      _ = (1 / Y) * (x ^ (-Y) * Real.exp (-z.re * x) + x ^ (-Y) * Real.exp (-w.re * x)
            + ‖z - w‖ * ((x ^ (-Y) * x) * Real.exp (-w.re * x))) := by ring
      _ = (1 / Y) * (x ^ (-Y) * Real.exp (-z.re * x) + x ^ (-Y) * Real.exp (-w.re * x)
            + ‖z - w‖ * (x ^ (1 - Y) * Real.exp (-w.re * x))) := by rw [hpow]
  -- integration by parts
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [sub_zero, zero_sub] at hibp
  have hcomp : ∫ x in Ioi (0 : ℝ), ((x ^ (-Y) : ℝ) : ℂ) / (-(Y : ℂ)) *
      (-z * Complex.exp (-(z * x)) + z * Complex.exp (-(w * x))
        - (z - w) * w * x * Complex.exp (-(w * x)))
      = (z / Y) * (∫ x in Ioi (0 : ℝ), ((x ^ (-Y) : ℝ) : ℂ) *
            (Complex.exp (-(z * x)) - Complex.exp (-(w * x))))
        + ((z - w) * w / Y) * ∫ x in Ioi (0 : ℝ),
            ((x ^ (1 - Y) : ℝ) : ℂ) * Complex.exp (-(w * x)) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hP1_int.const_mul _) (hIw_int.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hpow : x ^ (1 - Y) = x ^ (-Y) * x := by
      rw [show (1 - Y) = -Y + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    simp only [hpow, Complex.ofReal_mul]
    ring
  -- normalise the Γ-values and the exponents
  have e1 : -((((1 - Y : ℝ)) : ℂ) + 1) = ((Y : ℂ) - 1) - 1 := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have e2 : (((Y - 1 : ℝ)) : ℂ) = (Y : ℂ) - 1 := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  have hΓ2 : Real.Gamma (-Y + 1) = -Y * Real.Gamma (-Y) :=
    Real.Gamma_add_one (neg_ne_zero.mpr hY.ne')
  have hΓ1 : Real.Gamma (1 - Y + 1) = (1 - Y) * (-Y * Real.Gamma (-Y)) := by
    rw [Real.Gamma_add_one (by linarith : (1 - Y) < 0).ne, show (1 - Y) = -Y + 1 by ring, hΓ2]
  rw [e2, show -(Y - 1) = -Y + 1 by ring, hΓ2] at hP1
  rw [e1, hΓ1] at hIw
  rw [hcomp, hP1, hIw] at hibp
  have hfinal := (neg_eq_iff_eq_neg.mpr hibp).symm
  refine hfinal.trans ?_
  rw [← cgmy_mul_cpow_sub_one hz0 (Y : ℂ), ← cgmy_mul_cpow_sub_one hw0 (Y : ℂ),
    ← cgmy_mul_cpow_sub_one hw0 ((Y : ℂ) - 1)]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp
  ring

/-- The real shadow of the `0 < Y < 1` closed form at real rates:
`∫₀^∞ x^{−1−Y}(e^{−ax} − e^{−bx}) dx = Γ(−Y)(a^Y − b^Y)`. -/
theorem integral_rpow_mul_exp_sub_exp_Ioi (Y a b : ℝ) (hY : 0 < Y) (hY₁ : Y < 1) (ha : 0 < a)
    (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ (-1 - Y) * (Real.exp (-a * x) - Real.exp (-b * x))
      = Real.Gamma (-Y) * (a ^ Y - b ^ Y) := by
  have h := integral_rpow_mul_cexp_sub_cexp_Ioi Y (a : ℂ) (b : ℂ) hY hY₁
    (by rw [Complex.ofReal_re]; exact ha) (by rw [Complex.ofReal_re]; exact hb)
  rw [← Complex.ofReal_cpow ha.le, ← Complex.ofReal_cpow hb.le] at h
  have hpt : ∀ x : ℝ, ((x ^ (-1 - Y) * (Real.exp (-a * x) - Real.exp (-b * x)) : ℝ) : ℂ)
      = ((x ^ (-1 - Y) : ℝ) : ℂ) *
          (Complex.exp (-((a : ℂ) * x)) - Complex.exp (-((b : ℂ) * x))) := by
    intro x
    rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_neg, neg_mul,
      neg_mul]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [h]
  push_cast
  ring

/-- **The drift identity** (F5, real rate — no G1 involved): the whole paired
drift over `(0, ∞)` is `C Γ(1−Y)(M^{Y−1} − G^{Y−1}) = m^∞`. For `0 < Y < 1` each
leg converges and is the shipped `integral_rpow_mul_exp_neg_mul_Ioi` at
`s = 1 − Y`; for `1 < Y < 2` the pair is the `0 < Y < 1` difference form at
`Y − 1` (`integral_rpow_mul_exp_sub_exp_Ioi`).

This is what the tree's uncompensated `cgmyExponent` differs from the fully
compensated Lévy–Khintchine form by (`iv·m^∞`), and it is the content of
`d₀ + d_far = m^∞` in the oracle (measured `3.0e−10` at `Y = 3/2`,
`1.5e−10` at `Y = ½`). -/
theorem cgmyDrift_identity (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    ∫ x in Ioi (0 : ℝ), cgmyDriftIntegrand C G M Y x
      = C * Real.Gamma (1 - Y) * (M ^ (Y - 1) - G ^ (Y - 1)) := by
  have hfac : ∫ x in Ioi (0 : ℝ), cgmyDriftIntegrand C G M Y x
      = C * ∫ x in Ioi (0 : ℝ), x ^ (-Y) * (Real.exp (-M * x) - Real.exp (-G * x)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    unfold cgmyDriftIntegrand
    ring
  rw [hfac, mul_assoc]
  congr 1
  rcases lt_or_gt_of_ne hY₁ with hlt | hgt
  · -- `0 < Y < 1`: each leg converges separately
    have hint : ∀ a : ℝ, 0 < a →
        IntegrableOn (fun x : ℝ => x ^ (-Y) * Real.exp (-a * x)) (Ioi 0) :=
      fun a ha => integrableOn_rpow_mul_exp_neg_mul (by linarith) ha
    have hval : ∀ a : ℝ, 0 < a → ∫ x in Ioi (0 : ℝ), x ^ (-Y) * Real.exp (-a * x)
        = Real.Gamma (1 - Y) * a ^ (Y - 1) := by
      intro a ha
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < 1 - Y) ha
      have h' : ∫ x in Ioi (0 : ℝ), x ^ (-Y) * Real.exp (-a * x)
          = ∫ t in Ioi (0 : ℝ), t ^ (1 - Y - 1) * Real.exp (-(a * t)) :=
        setIntegral_congr_fun measurableSet_Ioi fun x _ => by
          rw [show (1 - Y - 1) = -Y by ring, neg_mul]
      rw [h', h, one_div, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, neg_sub, mul_comm]
    have hsub : (fun x : ℝ => x ^ (-Y) * (Real.exp (-M * x) - Real.exp (-G * x)))
        = fun x : ℝ => x ^ (-Y) * Real.exp (-M * x) - x ^ (-Y) * Real.exp (-G * x) := by
      funext x
      ring
    rw [hsub, integral_sub (hint M hM) (hint G hG), hval M hM, hval G hG]
    ring
  · -- `1 < Y < 2`: the difference form at `Y − 1`
    have h := integral_rpow_mul_exp_sub_exp_Ioi (Y - 1) M G (by linarith) (by linarith) hM hG
    rw [show -1 - (Y - 1) = -Y by ring, show -(Y - 1) = 1 - Y by ring] at h
    exact h

/-- The pointwise bridge from the CGMY one-sided integrand to the complex-rate
difference form: `(e^{ivx} − 1) e^{−ax} x^{−1−Y} = x^{−1−Y}(e^{−(a−iv)x} − e^{−ax})`. -/
theorem cgmy_leg_integrand_eq (a Y v x : ℝ) :
    (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1) * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
      = ((x ^ (-1 - Y) : ℝ) : ℂ) *
          (Complex.exp (-(((a : ℂ) - I * (v : ℂ)) * x)) - Complex.exp (-((a : ℂ) * x))) := by
  have h1 : Complex.exp ((v : ℂ) * (x : ℂ) * I) * Complex.exp (-((a : ℂ) * x))
      = Complex.exp (-(((a : ℂ) - I * (v : ℂ)) * x)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h2 : ((Real.exp (-a * x) : ℝ) : ℂ) = Complex.exp (-((a : ℂ) * x)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]
  rw [Complex.ofReal_mul, h2, ← h1]
  ring

/-- The compensated variant of the previous bridge. -/
theorem cgmy_leg_integrand_compensated_eq (a Y v x : ℝ) :
    (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1 - (v : ℂ) * (x : ℂ) * I)
        * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
      = ((x ^ (-1 - Y) : ℝ) : ℂ) *
          (Complex.exp (-(((a : ℂ) - I * (v : ℂ)) * x)) - Complex.exp (-((a : ℂ) * x))
            + (((a : ℂ) - I * (v : ℂ)) - a) * x * Complex.exp (-((a : ℂ) * x))) := by
  have h1 : Complex.exp ((v : ℂ) * (x : ℂ) * I) * Complex.exp (-((a : ℂ) * x))
      = Complex.exp (-(((a : ℂ) - I * (v : ℂ)) * x)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h2 : ((Real.exp (-a * x) : ℝ) : ℂ) = Complex.exp (-((a : ℂ) * x)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]
  rw [Complex.ofReal_mul, h2, ← h1]
  ring

/-- **The one-sided closed form, `0 < Y < 1`** (F5): the complex-rate difference
form `integral_rpow_mul_cexp_sub_cexp_Ioi` at `z = a − iv`, `w = a`, which is
one integration by parts from G1. Its *statement* is the integral BRIEF_011's
oracle already pins (`cgmy_exponent_one_sided`, `test_cgmy_contour`); this is
the first time it is a theorem. Reproduced by quadrature to `4.9e−13`. -/
theorem cgmyOneSidedExponent_eq (a Y : ℝ) (v : ℝ) (ha : 0 < a) (hY : 0 < Y)
    (hY₁ : Y < 1) :
    ∫ x in Ioi (0 : ℝ),
        (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1)
          * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
      = (Real.Gamma (-Y) : ℂ)
          * (((a : ℂ) - I * (v : ℂ)) ^ (Y : ℂ) - (a : ℂ) ^ (Y : ℂ)) := by
  have hre : ((a : ℂ) - I * (v : ℂ)).re = a := by simp
  simp_rw [cgmy_leg_integrand_eq a Y v]
  exact integral_rpow_mul_cexp_sub_cexp_Ioi Y ((a : ℂ) - I * (v : ℂ)) (a : ℂ) hY hY₁
    (by rw [hre]; exact ha) (by rw [Complex.ofReal_re]; exact ha)

/-- **The one-sided closed form, fully compensated, `1 < Y < 2`** (F5): the
complex-rate compensated form `integral_rpow_mul_cexp_compensated_Ioi` at
`z = a − iv`, `w = a`, where `z − w = −iv`. Note `f(0) = f'(0) = 0` for
`f(x) = e^{−zx} − e^{−ax} − ivx·e^{−ax}`, which is what kills the boundary term.
Reproduced by quadrature to `2.0e−12`. -/
theorem cgmyOneSidedCompensated_eq (a Y : ℝ) (v : ℝ) (ha : 0 < a) (hY₁ : 1 < Y)
    (hY₂ : Y < 2) :
    ∫ x in Ioi (0 : ℝ),
        (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1 - (v : ℂ) * (x : ℂ) * I)
          * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
      = (Real.Gamma (-Y) : ℂ)
          * (((a : ℂ) - I * (v : ℂ)) ^ (Y : ℂ) - (a : ℂ) ^ (Y : ℂ)
              + I * (v : ℂ) * (Y : ℂ) * (a : ℂ) ^ ((Y : ℂ) - 1)) := by
  have hre : ((a : ℂ) - I * (v : ℂ)).re = a := by simp
  simp_rw [cgmy_leg_integrand_compensated_eq a Y v]
  rw [integral_rpow_mul_cexp_compensated_Ioi Y ((a : ℂ) - I * (v : ℂ)) (a : ℂ) hY₁ hY₂
    (by rw [hre]; exact ha) (by rw [Complex.ofReal_re]; exact ha)]
  ring

/-! ### The two legs of the compensated integral, and the identification -/

theorem cgmy_ofReal_exp_neg_mul (a x : ℝ) :
    ((Real.exp (-a * x) : ℝ) : ℂ) = Complex.exp (-((a : ℂ) * x)) := by
  rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]

theorem cgmy_rpow_measurable (p : ℝ) : Measurable fun x : ℝ => x ^ p :=
  measurable_id.pow_const p

/-- The compensator integrand `v x i · e^{−ax} x^{−1−Y}` is Borel measurable. -/
theorem cgmy_leg_measurable (a Y v : ℝ) :
    Measurable fun x : ℝ =>
      (v : ℂ) * (x : ℂ) * I * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ) :=
  (((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
        (cgmy_rpow_measurable (-1 - Y))))

/-- `x^p e^{−ax}` is integrable on `(1, ∞)` for `p ≤ 0` (dominated by `e^{−ax}`). -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi_one {p a : ℝ} (hp : p ≤ 0) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-a * x)) (Ioi 1) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 1 ha) ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable ((continuousOn_id.rpow_const
        fun x (hx : x ∈ Ioi (1 : ℝ)) => Or.inl (ne_of_gt (lt_trans zero_lt_one hx))).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.exp_nonneg _))]
    exact mul_le_of_le_one_left (Real.exp_nonneg _)
      (Real.rpow_le_one_of_one_le_of_nonpos hx1 hp)

/-- The positive leg of the compensated integral for `0 < Y < 1`: the one-sided
closed form minus the unit-ball compensator `iv∫₀¹ x^{−Y}e^{−ax}`. -/
theorem cgmyLeg_eq_of_lt_one (a Y : ℝ) (v : ℝ) (ha : 0 < a) (hY : 0 < Y) (hY₁ : Y < 1) :
    ∫ x in Ioi (0 : ℝ),
        cgmyCompensatedIntegrand v x * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
      = (Real.Gamma (-Y) : ℂ) * (((a : ℂ) - I * (v : ℂ)) ^ (Y : ℂ) - (a : ℂ) ^ (Y : ℂ))
        - I * (v : ℂ) * ((∫ x in Ioc (0 : ℝ) 1, x ^ (-Y) * Real.exp (-a * x) : ℝ) : ℂ) := by
  have hre : ((a : ℂ) - I * (v : ℂ)).re = a := by simp
  have hI : IntegrableOn (fun x : ℝ => (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1)
      * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)) (Ioi 0) := by
    simp_rw [cgmy_leg_integrand_eq a Y v]
    exact integrableOn_rpow_mul_cexp_sub_cexp Y ((a : ℂ) - I * (v : ℂ)) (a : ℂ) hY hY₁
      (by rw [hre]; exact ha) (by rw [Complex.ofReal_re]; exact ha)
  have hJ : IntegrableOn (fun x : ℝ => (v : ℂ) * (x : ℂ) * I
      * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)) (Ioi 0) := by
    have h := integrableOn_ofReal_rpow_mul_cexp (by linarith : (-1 : ℝ) < -Y) (z := (a : ℂ))
      (by rw [Complex.ofReal_re]; exact ha)
    refine IntegrableOn.congr_fun (h.const_mul ((v : ℂ) * I)) (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    have hpow : x ^ (-Y) = x * x ^ (-1 - Y) := by
      rw [show (-Y) = 1 + (-1 - Y) by ring, Real.rpow_add hx0, Real.rpow_one]
    simp only [hpow, Complex.ofReal_mul, cgmy_ofReal_exp_neg_mul]
    ring
  have hsplit : EqOn
      (fun x : ℝ => cgmyCompensatedIntegrand v x * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ))
      (fun x : ℝ => (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1)
          * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
        - Set.indicator (Ioc (0 : ℝ) 1) (fun x : ℝ => (v : ℂ) * (x : ℂ) * I
            * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)) x) (Ioi 0) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [cgmyCompensatedIntegrand]
    by_cases h1 : x ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, h1⟩),
        Set.indicator_of_mem (show x ∈ Ioc (0 : ℝ) 1 from ⟨hx0, h1⟩)]
      ring
    · push_neg at h1
      rw [Set.indicator_of_notMem (show x ∉ Icc (-1 : ℝ) 1 from fun h => (not_le.mpr h1) h.2),
        Set.indicator_of_notMem (show x ∉ Ioc (0 : ℝ) 1 from fun h => (not_le.mpr h1) h.2)]
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hI (hJ.indicator measurableSet_Ioc),
    setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self,
    cgmyOneSidedExponent_eq a Y v ha hY hY₁]
  congr 1
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx.1
  have hpow : x ^ (-Y) = x * x ^ (-1 - Y) := by
    rw [show (-Y) = 1 + (-1 - Y) by ring, Real.rpow_add hx0, Real.rpow_one]
  simp only [hpow, Complex.ofReal_mul, cgmy_ofReal_exp_neg_mul]
  ring

/-- The positive leg of the compensated integral for `1 < Y < 2`: the fully
compensated one-sided form plus the far compensator `iv∫₁^∞ x^{−Y}e^{−ax}`. -/
theorem cgmyLeg_eq_of_one_lt (a Y : ℝ) (v : ℝ) (ha : 0 < a) (hY₁ : 1 < Y) (hY₂ : Y < 2) :
    ∫ x in Ioi (0 : ℝ),
        cgmyCompensatedIntegrand v x * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
      = (Real.Gamma (-Y) : ℂ) * (((a : ℂ) - I * (v : ℂ)) ^ (Y : ℂ) - (a : ℂ) ^ (Y : ℂ)
            + I * (v : ℂ) * (Y : ℂ) * (a : ℂ) ^ ((Y : ℂ) - 1))
        + I * (v : ℂ) * ((∫ x in Ioi (1 : ℝ), x ^ (-Y) * Real.exp (-a * x) : ℝ) : ℂ) := by
  have hY : 0 < Y := by linarith
  have hre : ((a : ℂ) - I * (v : ℂ)).re = a := by simp
  have hI : IntegrableOn (fun x : ℝ =>
      (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1 - (v : ℂ) * (x : ℂ) * I)
        * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)) (Ioi 0) := by
    simp_rw [cgmy_leg_integrand_compensated_eq a Y v]
    exact integrableOn_rpow_mul_cexp_compensated Y ((a : ℂ) - I * (v : ℂ)) (a : ℂ) hY₁ hY₂
      (by rw [hre]; exact ha) (by rw [Complex.ofReal_re]; exact ha)
  have hJ₁ : IntegrableOn (fun x : ℝ => (v : ℂ) * (x : ℂ) * I
      * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)) (Ioi 1) := by
    refine Integrable.mono'
      ((integrableOn_rpow_mul_exp_neg_mul_Ioi_one (by linarith : -Y ≤ 0) ha).const_mul |v|)
      (cgmy_leg_measurable a Y v).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hpow : x * x ^ (-1 - Y) = x ^ (-Y) := by
      rw [show (-Y) = 1 + (-1 - Y) by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg hx0.le,
      Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx0.le _))]
    rw [← hpow]
    exact le_of_eq (by ring)
  have hJ : IntegrableOn (Set.indicator (Ioi (1 : ℝ)) (fun x : ℝ => (v : ℂ) * (x : ℂ) * I
      * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ))) (Ioi 0) :=
    ((integrableOn_iff_integrable_of_support_subset Set.support_indicator_subset).mp
      (hJ₁.indicator measurableSet_Ioi)).integrableOn
  have hsplit : EqOn
      (fun x : ℝ => cgmyCompensatedIntegrand v x * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ))
      (fun x : ℝ => (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1 - (v : ℂ) * (x : ℂ) * I)
          * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)
        + Set.indicator (Ioi (1 : ℝ)) (fun x : ℝ => (v : ℂ) * (x : ℂ) * I
            * ((Real.exp (-a * x) * x ^ (-1 - Y) : ℝ) : ℂ)) x) (Ioi 0) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [cgmyCompensatedIntegrand]
    by_cases h1 : x ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, h1⟩),
        Set.indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from not_lt.mpr h1)]
      ring
    · push_neg at h1
      rw [Set.indicator_of_notMem (show x ∉ Icc (-1 : ℝ) 1 from fun h => (not_le.mpr h1) h.2),
        Set.indicator_of_mem (show x ∈ Ioi (1 : ℝ) from h1)]
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_add hI hJ,
    setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one),
    cgmyOneSidedCompensated_eq a Y v ha hY₁ hY₂]
  congr 1
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hpow : x ^ (-Y) = x * x ^ (-1 - Y) := by
    rw [show (-Y) = 1 + (-1 - Y) by ring, Real.rpow_add hx0, Real.rpow_one]
  simp only [hpow, Complex.ofReal_mul, cgmy_ofReal_exp_neg_mul]
  ring

/-- **The identification** (the headline of §3): for `Y ≠ 1` the Lévy–Khintchine
exponent of `cgmyLevyDensity` *is* the tree's closed form. `B₀` splits into its
two legs (`x ↦ −x` folds the negative side onto the positive one with `v ↦ −v`
and `M ↦ G`), the legs become the one-sided closed forms (`Y < 1`:
uncompensated, with the unit-ball `ivx` moved to the drift; `Y > 1`: fully
compensated, with `∫_{x>1} x ν` moved to the drift), and the drift closes — for
`Y < 1` by cancellation, for `Y > 1` by `cgmyDrift_identity`. Measured
`|L − ψ_Y| ≤ 6.2e−10`. -/
theorem cgmyLKExponent_eq_cgmyExponent (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (v : ℝ) :
    cgmyLKExponent C G M Y v = cgmyExponent C G M Y (v : ℂ) := by
  have hint := cgmyCompensatedIntegrand_integrable C G M Y hC hG hM hY hY₂ v
  -- the whole line splits into the two half-lines, the negative one reflected
  have hneg : (∫ x in Iic (0 : ℝ), cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
      = ∫ x in Ioi (0 : ℝ),
          cgmyCompensatedIntegrand v (-x) * (cgmyLevyDensity C G M Y (-x) : ℂ) := by
    have h := integral_comp_neg_Ioi (0 : ℝ)
      (fun x : ℝ => cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
    rw [neg_zero] at h
    exact h.symm
  have hsplit : (∫ x, cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
      = (∫ x in Ioi (0 : ℝ), cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
        + ∫ x in Ioi (0 : ℝ),
            cgmyCompensatedIntegrand v (-x) * (cgmyLevyDensity C G M Y (-x) : ℂ) := by
    rw [← integral_add_compl (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))) hint,
      Set.compl_Ioi, hneg]
  -- the positive leg at rate `M`, the reflected negative leg at rate `G` with `v ↦ −v`
  have hlegM : (∫ x in Ioi (0 : ℝ),
        cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
      = C * ∫ x in Ioi (0 : ℝ),
          cgmyCompensatedIntegrand v x * ((Real.exp (-M * x) * x ^ (-1 - Y) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [cgmyLevyDensity_pos_of_pos (show (0 : ℝ) < x from hx)]
    simp only [Complex.ofReal_mul]
    ring
  have hlegG : (∫ x in Ioi (0 : ℝ),
        cgmyCompensatedIntegrand v (-x) * (cgmyLevyDensity C G M Y (-x) : ℂ))
      = C * ∫ x in Ioi (0 : ℝ),
          cgmyCompensatedIntegrand (-v) x * ((Real.exp (-G * x) * x ^ (-1 - Y) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [cgmyLevyDensity_neg_of_neg (neg_neg_of_pos hx0), neg_neg, cgmyCompensatedIntegrand_neg,
      mul_neg, ← neg_mul]
    simp only [Complex.ofReal_mul]
    ring
  have hbase : ((G : ℂ) - I * ((-v : ℝ) : ℂ)) = (G : ℂ) + I * (v : ℂ) := by
    rw [Complex.ofReal_neg]
    ring
  rw [cgmyLKExponent, hsplit, hlegM, hlegG, cgmyExponent]
  rcases lt_or_gt_of_ne hY₁ with hlt | hgt
  · -- `0 < Y < 1`: the two unit-ball compensators are exactly the drift
    rw [cgmyLeg_eq_of_lt_one M Y v hM hY hlt, cgmyLeg_eq_of_lt_one G Y (-v) hG hY hlt, hbase]
    have hint' : ∀ a : ℝ, 0 < a →
        IntegrableOn (fun x : ℝ => x ^ (-Y) * Real.exp (-a * x)) (Ioc 0 1) :=
      fun a ha => (integrableOn_rpow_mul_exp_neg_mul (by linarith) ha).mono_set Ioc_subset_Ioi_self
    have hdrift : (∫ x in Ioc (0 : ℝ) 1, cgmyDriftIntegrand C G M Y x)
        = C * (∫ x in Ioc (0 : ℝ) 1, x ^ (-Y) * Real.exp (-M * x))
          - C * ∫ x in Ioc (0 : ℝ) 1, x ^ (-Y) * Real.exp (-G * x) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_sub ((hint' M hM).const_mul _) ((hint' G hG).const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
      unfold cgmyDriftIntegrand
      ring
    rw [hdrift]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  · -- `1 < Y < 2`: the far compensators plus the unit-ball drift are the whole drift
    rw [cgmyLeg_eq_of_one_lt M Y v hM hgt hY₂, cgmyLeg_eq_of_one_lt G Y (-v) hG hgt hY₂, hbase]
    have hD : ∀ a : ℝ, 0 < a →
        IntegrableOn (fun x : ℝ => x ^ (-Y) * Real.exp (-a * x)) (Ioi 1) :=
      fun a ha => integrableOn_rpow_mul_exp_neg_mul_Ioi_one (by linarith) ha
    have hfar : (∫ x in Ioi (1 : ℝ), cgmyDriftIntegrand C G M Y x)
        = C * (∫ x in Ioi (1 : ℝ), x ^ (-Y) * Real.exp (-M * x))
          - C * ∫ x in Ioi (1 : ℝ), x ^ (-Y) * Real.exp (-G * x) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_sub ((hD M hM).const_mul _) ((hD G hG).const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      unfold cgmyDriftIntegrand
      ring
    have hD₁ : IntegrableOn (cgmyDriftIntegrand C G M Y) (Ioi 1) := by
      have h := ((hD M hM).const_mul C).sub ((hD G hG).const_mul C)
      refine IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, cgmyDriftIntegrand]
      ring
    have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
      rw [Set.disjoint_left]
      rintro x ⟨_, hx₂⟩ hx'
      exact (not_lt.mpr hx₂) hx'
    have hwhole : (∫ x in Ioc (0 : ℝ) 1, cgmyDriftIntegrand C G M Y x)
        + ∫ x in Ioi (1 : ℝ), cgmyDriftIntegrand C G M Y x
        = ∫ x in Ioi (0 : ℝ), cgmyDriftIntegrand C G M Y x := by
      rw [← setIntegral_union hdisj measurableSet_Ioi
        (cgmyDriftIntegrand_integrableOn C G M Y hC hG hM hY hY₂) hD₁,
        Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    have hΓ : Real.Gamma (1 - Y) = -Y * Real.Gamma (-Y) := by
      rw [show (1 - Y) = -Y + 1 by ring]
      exact Real.Gamma_add_one (neg_ne_zero.mpr hY.ne')
    have h := cgmyDrift_identity C G M Y hC hG hM hY hY₂ hY₁
    rw [← hwhole, hfar, hΓ] at h
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] at h'
    rw [Complex.ofReal_cpow hM.le, Complex.ofReal_cpow hG.le, Complex.ofReal_sub,
      Complex.ofReal_one] at h'
    simp only [Complex.ofReal_neg]
    linear_combination (I * (v : ℂ)) * h'

/-- **The identification at the law**: for `Y ≠ 1` the characteristic function of
`cgmyLaw` is the tree's pricing factor `cgmyCharFactor`. From here on, the factor
every CGMY price in this repository is built from is the characteristic function
of a law in the tree. -/
theorem charFun_cgmyLaw_eq_cgmyCharFactor (C G M Y : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (τ : ℝ≥0) (t : ℝ) :
    charFun (cgmyLaw C G M Y τ hC hG hM hY hY₂ : Measure ℝ) t
      = cgmyCharFactor C G M Y (τ : ℝ) (t : ℂ) := by
  rw [charFun_cgmyLaw C G M Y hC hG hM hY hY₂ τ t,
    cgmyLKExponent_eq_cgmyExponent C G M Y hC hG hM hY hY₂ hY₁]
  rfl

end BSM

end
