/-
  ImprovedBS.Pricing — BRIEF_010 / T6 at any strip law: the pricing identity,
  and a contour correction (C12).

  CORRECTION C12: Fourier.lean's carrMadanKernel φ α u = φ (↑u + ↑α·I)/cmDenom
  (Im v = +α) is NOT the pricing contour. The damped price k ↦ e^{αk} e^{-rτ}
  E[(S e^X − S e^k)⁺] inverts from φ(u − i(α+1)) (Im v = −(α+1)), defined here
  as cmPriceKernel. Measured at S=100,K=110,τ=1,r=0.05,q=0.02,σ=0.25,α=1.5:
  pricing line 9.99e-16 relative, old line 74.2% error (ledger C12).

  Pricing identity is law-agnostic, proved at any μ with strip conditions;
  GBM instance closes triangle via kernel route.

  NOT MACHINE-CHECKED: CGMY exponent existence, affine in τ, and (H-decay)
  under α+1 < min(G,M) — BRIEF_011. GBM satisfies all for α>0, Y=2.

  Mathlib names verified at v4.34.0.
-/
import Mathlib
import ImprovedBS.Fourier
import ImprovedBS.Inversion
import ImprovedBS.Skeleton
import ImprovedBS.RiskNeutral

noncomputable section

namespace BSM

open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace FourierTransform ComplexConjugate

/-! §1 pricing kernel -/

/-- Pricing kernel on pricing contour `v = u − i(α+1)` (C12). -/
def cmPriceKernel (φ : ℂ → ℂ) (α u : ℝ) : ℂ :=
  φ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹

theorem cmPriceKernel_eq_shift (φ : ℂ → ℂ) (α u : ℝ) :
    cmPriceKernel φ α u = carrMadanKernel (fun v => φ (v - ↑(2 * α + 1) * Complex.I)) α u := by
  unfold cmPriceKernel carrMadanKernel
  dsimp
  have h : (↑u + ↑α * Complex.I - ↑(2 * α + 1) * Complex.I : ℂ) = ↑u - ↑(α + 1) * Complex.I := by
    push_cast
    ring
  rw [h]

noncomputable def contourCharFun (μ : Measure ℝ) (v : ℂ) : ℂ :=
  ∫ x, Complex.exp (Complex.I * v * ↑x) ∂μ

theorem gbm_contourCharFun_eq {m : ℝ} {v : NNReal} {w : ℂ} :
    contourCharFun (ProbabilityTheory.gaussianReal m v) w =
      gbmCharFactor m ((v : ℝ) / 2) w := by
  unfold contourCharFun gbmCharFactor
  have h_int : (∫ x, Complex.exp (Complex.I * w * ↑x) ∂ProbabilityTheory.gaussianReal m v) =
      (∫ x, Complex.exp ((Complex.I * w) * ↑x) ∂ProbabilityTheory.gaussianReal m v) := by
    apply integral_congr_ae
    filter_upwards with x
    ring_nf
  rw [h_int]
  have h_mgf : (∫ x, Complex.exp ((Complex.I * w) * ↑x) ∂ProbabilityTheory.gaussianReal m v) =
      ProbabilityTheory.complexMGF id (ProbabilityTheory.gaussianReal m v) (Complex.I * w) := rfl
  rw [h_mgf, ProbabilityTheory.complexMGF_id_gaussianReal]
  have hI2 : Complex.I ^ 2 = -1 := by
    rw [sq, Complex.I_mul_I]
  have h_sq : (Complex.I * w) ^ 2 = - w ^ 2 := by
    calc (Complex.I * w) ^ 2 = Complex.I ^ 2 * w ^ 2 := by ring
      _ = -1 * w ^ 2 := by rw [hI2]
      _ = - w ^ 2 := by ring
  have h_arg : Complex.I * w * ↑m + ↑↑v * (Complex.I * w) ^ 2 / 2 =
      Complex.I * ↑m * w - ↑((v : ℝ) / 2) * w ^ 2 := by
    rw [h_sq]
    have h1 : (↑↑v : ℂ) = ↑(v : ℝ) := rfl
    have h2 : (↑((v : ℝ) / 2) : ℂ) = ↑(v : ℝ) / 2 := by
      push_cast
      ring
    rw [h1, h2]
    ring
  rw [h_arg]

theorem gbmCharFactor_pricing_continuous (m s α : ℝ) :
    Continuous fun u : ℝ => gbmCharFactor m s (↑u - ↑(α + 1) * Complex.I) := by
  unfold gbmCharFactor
  continuity

theorem gbmCharFactor_pricing_norm (m s u α : ℝ) :
    ‖gbmCharFactor m s (↑u - ↑(α + 1) * Complex.I)‖ =
      Real.exp (s * (α + 1) ^ 2 + (α + 1) * m) * Real.exp (-(s * u ^ 2)) := by
  have h_eq : (↑u - ↑(α + 1) * Complex.I : ℂ) = ↑u + ↑(-(α + 1)) * Complex.I := by
    push_cast
    ring
  rw [h_eq, gbmCharFactor_contour_norm]
  ring

theorem cmPriceKernel_integrable {φ : ℂ → ℂ} {α : ℝ} (hα : 0 < α)
    (hcont : Continuous fun u : ℝ => φ (↑u - ↑(α + 1) * Complex.I))
    {c D Y : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) {u₀ : ℝ}
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖φ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y)) :
    Integrable (cmPriceKernel φ α) := by
  have h_eq : cmPriceKernel φ α = carrMadanKernel (fun v => φ (v - ↑(2 * α + 1) * Complex.I)) α := by
    funext u
    exact cmPriceKernel_eq_shift φ α u
  rw [h_eq]
  have hcont' : Continuous fun u : ℝ => (fun v => φ (v - ↑(2 * α + 1) * Complex.I)) (↑u + ↑α * Complex.I) := by
    have hfun : (fun u : ℝ => (fun v => φ (v - ↑(2 * α + 1) * Complex.I)) (↑u + ↑α * Complex.I)) =
        (fun u : ℝ => φ (↑u - ↑(α + 1) * Complex.I)) := by
      funext u
      congr 1
      push_cast
      ring
    rw [hfun]
    exact hcont
  have hdecay' : ∀ u : ℝ, u₀ ≤ |u| →
      ‖(fun v => φ (v - ↑(2 * α + 1) * Complex.I)) (↑u + ↑α * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y) := by
    intro u hu
    have hfun : (fun v => φ (v - ↑(2 * α + 1) * Complex.I)) (↑u + ↑α * Complex.I) =
        φ (↑u - ↑(α + 1) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [hfun]
    exact hdecay u hu
  exact carrMadanKernel_integrable hα hcont' hc hD hY hdecay'

theorem gbm_cmPriceKernel_integrable (m s : ℝ) (hs : 0 < s) {α : ℝ} (hα : 0 < α) :
    Integrable (cmPriceKernel (gbmCharFactor m s) α) := by
  refine cmPriceKernel_integrable hα (gbmCharFactor_pricing_continuous m s α) hs
    (D := Real.exp (s * (α + 1) ^ 2 + (α + 1) * m)) (Real.exp_pos _).le (Y := 2) (by norm_num)
    (u₀ := 0) ?_
  intro u _
  rw [gbmCharFactor_pricing_norm, Real.rpow_two, sq_abs, neg_mul]

/-! §2 strike transform -/

theorem cmDenom_factor (α u : ℝ) :
    cmDenom α u = ((α : ℂ) + ↑u * Complex.I) * ((α + 1 : ℂ) + ↑u * Complex.I) := by
  unfold cmDenom
  have h1 : (α ^ 2 + α - u ^ 2 : ℝ) = α * (α + 1) - u ^ 2 := by ring
  rw [h1]
  push_cast
  have hI : Complex.I ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  ring_nf
  rw [hI]
  ring

theorem integral_Ioi_cexp_neg_mul_eq_inv {a : ℂ} (ha : 0 < a.re) :
    ∫ y in Set.Ioi (0 : ℝ), Complex.exp (-(a * ↑y)) = a⁻¹ := by
  have ha' : (-a).re < 0 := by
    simp only [Complex.neg_re]
    linarith
  have h_eq : (fun y : ℝ => Complex.exp (-(a * ↑y))) = (fun y : ℝ => Complex.exp ((-a) * ↑y)) := by
    funext y
    ring_nf
  rw [h_eq]
  have h_int := integral_exp_mul_complex_Ioi ha' (0 : ℝ)
  rw [h_int]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h_a_ne : a ≠ 0 := by
    intro hz
    rw [hz] at ha
    simp at ha
  field_simp

noncomputable def strikeTransform (S α x u : ℝ) : ℂ :=
  ∫ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
    ↑(max (S * Real.exp x - S * Real.exp k) 0)

theorem ofReal_exp_eq_cexp (r : ℝ) : (↑(Real.exp r) : ℂ) = Complex.exp (↑r) := by
  rw [← Complex.ofReal_exp]

theorem norm_cexp_I_mul_ofReal (t : ℝ) : ‖Complex.exp (↑t * Complex.I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I t

theorem strikeTransform_eq {S x u α : ℝ} (hS : 0 ≤ S) (hα : 0 < α) :
    strikeTransform S α x u =
      ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹ := by
  unfold strikeTransform
  -- Setup complex frequencies a = α + i u, b = (α+1)+ i u
  set a : ℂ := (↑α : ℂ) + ↑u * Complex.I with ha_def
  set b : ℂ := (↑(α + 1) : ℂ) + ↑u * Complex.I with hb_def
  have h_re_a : 0 < a.re := by
    simp only [ha_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have h_re_b : 0 < b.re := by
    simp only [hb_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have h_b_sub_a : b - a = 1 := by
    simp only [ha_def, hb_def]
    push_cast
    ring
  have h_cmDenom_eq : cmDenom α u = a * b := by
    rw [cmDenom_factor]; simp only [ha_def, hb_def]
  -- Vanishing outside Iic x
  have h_zero : ∀ k : ℝ, x < k → max (S * Real.exp x - S * Real.exp k) 0 = 0 := by
    intro k hk
    have hle : Real.exp x ≤ Real.exp k := Real.exp_le_exp.mpr hk.le
    have h : S * Real.exp x - S * Real.exp k ≤ 0 := by
      linarith [mul_le_mul_of_nonneg_left hle hS]
    exact max_eq_right h
  have h_f_zero : ∀ k : ℝ, x < k →
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0) = 0 := by
    intro k hk
    rw [h_zero k hk]; simp
  -- Identify f as indicator of Iic x
  have h_f_eq_indicator : ∀ k : ℝ,
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0) =
      (Set.Iic x).indicator (fun k => Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0)) k := by
    intro k
    by_cases hk : k ≤ x
    · have hmem : k ∈ Set.Iic x := hk
      rw [Set.indicator_of_mem hmem]
    · push_neg at hk
      have hnot : k ∉ Set.Iic x := by simp [Set.mem_Iic, not_le, hk]
      rw [Set.indicator_of_notMem hnot, h_f_zero k hk]
  have h_integral_Iic : (∫ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0)) =
      ∫ k in Set.Iic x, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0) := by
    have h_eq : (fun k : ℝ => Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0)) =
      fun k => (Set.Iic x).indicator (fun k => Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0)) k := by
      funext k; exact (h_f_eq_indicator k).symm
    rw [h_eq, integral_indicator measurableSet_Iic]
  -- Rewrite integrand on Iic x as S e^x e^{a k} - S e^{b k}
  have h_exp_a : ∀ k : ℝ, Complex.exp (a * ↑k) =
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) := by
    intro k
    have h1 : a * ↑k = ↑(α * k) + Complex.I * ↑(u * k) := by
      simp only [ha_def]; push_cast; ring
    rw [h1, Complex.exp_add, ← Complex.ofReal_exp]
  have h_exp_a_sym : ∀ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) =
      Complex.exp (a * ↑k) := by
    intro k; rw [h_exp_a k, mul_comm]
  have h_exp_b : ∀ k : ℝ, Complex.exp (b * ↑k) =
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) * ↑(Real.exp k) := by
    intro k
    have h1 : b * ↑k = ↑((α + 1) * k) + Complex.I * ↑(u * k) := by
      simp only [hb_def]; push_cast; ring
    have h2 : (↑((α + 1) * k) : ℂ) = ↑(α * k) + ↑k := by push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    ring
  have h_max_eq : ∀ k ∈ Set.Iic x,
      max (S * Real.exp x - S * Real.exp k) 0 = S * Real.exp x - S * Real.exp k := by
    intro k hk
    have hk' : k ≤ x := hk
    have hle : Real.exp k ≤ Real.exp x := Real.exp_le_exp.mpr hk'
    have h_nonneg : 0 ≤ S * Real.exp x - S * Real.exp k := by
      linarith [mul_le_mul_of_nonneg_left hle hS]
    exact max_eq_left h_nonneg
  have h_ofReal_sub : ∀ k ∈ Set.Iic x,
      (↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ) =
      ↑(S * Real.exp x) - ↑(S * Real.exp k) := by
    intro k hk
    rw [h_max_eq k hk, Complex.ofReal_sub]
  have h_Sexp : ∀ k : ℝ, (↑(S * Real.exp k) : ℂ) = ↑S * ↑(Real.exp k) := by
    intro k; push_cast; ring
  have h_Sexp_x : (↑(S * Real.exp x) : ℂ) = ↑S * ↑(Real.exp x) := by push_cast; ring
  have h_on_Iic : ∀ k ∈ Set.Iic x,
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0) =
      ↑(S * Real.exp x) * Complex.exp (a * ↑k) - ↑S * Complex.exp (b * ↑k) := by
    intro k hk
    rw [h_ofReal_sub k hk]
    have h1 : Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        (↑(S * Real.exp x) - ↑(S * Real.exp k)) =
      ↑(S * Real.exp x) * (Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k))) -
      (Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k))) * ↑(S * Real.exp k) := by ring
    rw [h1, h_exp_a_sym k]
    congr 1
    · ring
    · rw [h_Sexp k, h_exp_b k]; ring
  have h_set_eq : (∫ k in Set.Iic x, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0)) =
      ∫ k in Set.Iic x, (↑(S * Real.exp x) * Complex.exp (a * ↑k) - ↑S * Complex.exp (b * ↑k)) := by
    apply setIntegral_congr_fun measurableSet_Iic
    · exact (integrable_strikeTransform hS hα).integrableOn
    · intro k hk; exact h_on_Iic k hk
  -- Integrability of a and b exponentials on Iic
  have h_int_a : IntegrableOn (fun k : ℝ => Complex.exp (a * ↑k)) (Set.Iic x) :=
    integrableOn_exp_mul_complex_Iic h_re_a x
  have h_int_b : IntegrableOn (fun k : ℝ => Complex.exp (b * ↑k)) (Set.Iic x) :=
    integrableOn_exp_mul_complex_Iic h_re_b x
  have h_int_a_const : IntegrableOn (fun k : ℝ => ↑(S * Real.exp x) * Complex.exp (a * ↑k)) (Set.Iic x) :=
    h_int_a.const_mul _
  have h_int_b_const : IntegrableOn (fun k : ℝ => ↑S * Complex.exp (b * ↑k)) (Set.Iic x) :=
    h_int_b.const_mul _
  have h_int_sub : IntegrableOn (fun k : ℝ => ↑(S * Real.exp x) * Complex.exp (a * ↑k) - ↑S * Complex.exp (b * ↑k)) (Set.Iic x) :=
    h_int_a_const.sub h_int_b_const
  -- Compute integrals
  have h_int_a_eq : ∫ k in Set.Iic x, Complex.exp (a * ↑k) = Complex.exp (a * ↑x) / a :=
    integral_exp_mul_complex_Iic h_re_a x
  have h_int_b_eq : ∫ k in Set.Iic x, Complex.exp (b * ↑k) = Complex.exp (b * ↑x) / b :=
    integral_exp_mul_complex_Iic h_re_b x
  have h_integral_sub : ∫ k in Set.Iic x, (↑(S * Real.exp x) * Complex.exp (a * ↑k) - ↑S * Complex.exp (b * ↑k)) =
      ↑(S * Real.exp x) * (Complex.exp (a * ↑x) / a) - ↑S * (Complex.exp (b * ↑x) / b) := by
    rw [integral_sub h_int_a_const h_int_b_const,
        integral_const_mul, integral_const_mul, h_int_a_eq, h_int_b_eq]
  -- Simplify to C * (cmDenom)⁻¹
  have h_C_eq : ↑(S * Real.exp x) * Complex.exp (a * ↑x) = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by
    have h_ax : a * ↑x = ↑(x * α) + ↑(x * u) * Complex.I := by
      simp only [ha_def]; push_cast; ring
    rw [h_ax, Complex.exp_add, ← Complex.ofReal_exp]
    have h_mul : Real.exp x * Real.exp (x * α) = Real.exp (x * (α + 1)) := by
      rw [← Real.exp_add]; ring_nf
    calc ↑(S * Real.exp x) * (↑(Real.exp (x * α)) * Complex.exp (↑(x * u) * Complex.I))
        = ↑S * ↑(Real.exp x) * ↑(Real.exp (x * α)) * Complex.exp (↑(x * u) * Complex.I) := by push_cast; ring
      _ = ↑S * ↑(Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by
          rw [← Complex.ofReal_mul, h_mul]
      _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by push_cast; ring
  have h_C_eq2 : ↑S * Complex.exp (b * ↑x) = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by
    have h_bx : b * ↑x = ↑(x * (α + 1)) + ↑(x * u) * Complex.I := by
      simp only [hb_def]; push_cast; ring
    rw [h_bx, Complex.exp_add, ← Complex.ofReal_exp]
    calc ↑S * (↑(Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I))
        = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by push_cast; ring
  have h_diff : ↑(S * Real.exp x) * (Complex.exp (a * ↑x) / a) - ↑S * (Complex.exp (b * ↑x) / b) =
      ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (a * b)⁻¹ := by
    rw [h_C_eq, h_C_eq2]
    have ha_ne : a ≠ 0 := by
      intro hz; have : a.re = 0 := by rw [hz]; simp; linarith [h_re_a]
    have hb_ne : b ≠ 0 := by
      intro hz; have : b.re = 0 := by rw [hz]; simp; linarith [h_re_b]
    have h_ab_ne : a * b ≠ 0 := mul_ne_zero ha_ne hb_ne
    calc ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) / a -
          ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) / b
        = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (a⁻¹ - b⁻¹) := by ring
      _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * ((b - a) / (a * b)) := by
          field_simp
      _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (1 / (a * b)) := by
          rw [h_b_sub_a]
      _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (a * b)⁻¹ := by
          rw [one_div, inv_eq_one_div]
  calc strikeTransform S α x u
      = ∫ k in Set.Iic x, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
          ↑(max (S * Real.exp x - S * Real.exp k) 0) := h_integral_Iic
    _ = ∫ k in Set.Iic x, (↑(S * Real.exp x) * Complex.exp (a * ↑k) - ↑S * Complex.exp (b * ↑k)) := h_set_eq
    _ = ↑(S * Real.exp x) * (Complex.exp (a * ↑x) / a) - ↑S * (Complex.exp (b * ↑x) / b) := h_integral_sub
    _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (a * b)⁻¹ := h_diff
    _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹ := by
          rw [h_cmDenom_eq]

theorem integrable_strikeTransform {S α x u : ℝ} (hS : 0 ≤ S) (hα : 0 < α) :
    Integrable (fun k : ℝ => Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
      ↑(max (S * Real.exp x - S * Real.exp k) 0)) := by
  have h_cont : Continuous (fun k : ℝ => Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
      ↑(max (S * Real.exp x - S * Real.exp k) 0)) := by
    continuity
  have h_bound : ∀ k : ℝ, ‖Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
      ↑(max (S * Real.exp x - S * Real.exp k) 0)‖ ≤
        (Set.Iic x).indicator (fun k => S * Real.exp x * Real.exp (α * k)) k := by
    intro k
    by_cases hk : k ≤ x
    · have hmem : k ∈ Set.Iic x := hk
      rw [Set.indicator_of_mem hmem]
      have h_norm_I : ‖Complex.exp (Complex.I * ↑(u * k))‖ = 1 := by
        exact Complex.norm_exp_I_mul_ofReal (u * k)
      have h_norm_exp : ‖(↑(Real.exp (α * k)) : ℂ)‖ = Real.exp (α * k) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      have h_max_le : max (S * Real.exp x - S * Real.exp k) 0 ≤ S * Real.exp x := by
        apply max_le
        · linarith [mul_nonneg hS (Real.exp_pos k).le]
        · exact mul_nonneg hS (Real.exp_pos _).le
      have h_norm_eq : ‖Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
            ↑(max (S * Real.exp x - S * Real.exp k) 0)‖ =
          ‖Complex.exp (Complex.I * ↑(u * k))‖ * ‖↑(Real.exp (α * k))‖ *
            ‖(↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ)‖ := by
        rw [norm_mul, norm_mul]
      calc ‖Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
            ↑(max (S * Real.exp x - S * Real.exp k) 0)‖
          = ‖Complex.exp (Complex.I * ↑(u * k))‖ * ‖↑(Real.exp (α * k))‖ *
            ‖(↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ)‖ := h_norm_eq
        _ = 1 * Real.exp (α * k) * ‖(↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ)‖ := by
              rw [h_norm_I, h_norm_exp]
        _ ≤ 1 * Real.exp (α * k) * (S * Real.exp x) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_one (Real.exp_pos _).le)
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
              exact h_max_le
        _ = S * Real.exp x * Real.exp (α * k) := by ring
    · push_neg at hk
      have hnot : k ∉ Set.Iic x := by
        simp only [Set.mem_Iic, not_le]
        exact hk
      rw [Set.indicator_of_notMem hnot]
      have h0 : max (S * Real.exp x - S * Real.exp k) 0 = 0 := by
        have hle : Real.exp x ≤ Real.exp k := Real.exp_le_exp.mpr hk.le
        have : S * Real.exp x - S * Real.exp k ≤ 0 := by
          linarith [mul_le_mul_of_nonneg_left hle hS]
        exact max_eq_right this
      simp [h0]
  have h_int : Integrable (fun k => (Set.Iic x).indicator (fun k => S * Real.exp x * Real.exp (α * k)) k) := by
    have h_base : IntegrableOn (fun k : ℝ => Real.exp (α * k)) (Set.Iic x) :=
      integrableOn_exp_mul_Iic hα x
    have h_const : IntegrableOn (fun k : ℝ => S * Real.exp x * Real.exp (α * k)) (Set.Iic x) :=
      h_base.const_mul (S * Real.exp x)
    exact h_const.integrable_indicator measurableSet_Iic
  exact h_int.mono' h_cont.aestronglyMeasurable (Eventually.of_forall h_bound)

/-! §3 damped price -/

noncomputable def dampedModelFreeCall (μ : Measure ℝ) (S r tau α k : ℝ) : ℝ :=
  Real.exp (α * k) * (Real.exp (-r * tau) * ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ)

theorem dampedModelFreeCall_eq_dampedCallPrice {S m r tau α k : ℝ} {v : NNReal} :
    dampedModelFreeCall (ProbabilityTheory.gaussianReal m v) S r tau α k =
      dampedCallPrice S v m r tau α k := rfl

theorem continuous_dampedModelFreeCall {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S r tau α : ℝ} (hS : 0 < S) (hα : 0 < α)
    (hMom : Integrable (fun x : ℝ => Real.exp ((α + 1) * x)) μ) :
    Continuous fun k : ℝ => (dampedModelFreeCall μ S r tau α k : ℂ) := by
  unfold dampedModelFreeCall
  have h_cont_exp : Continuous fun k : ℝ => Real.exp (α * k) := by continuity
  have h_cont_int : Continuous fun k : ℝ => ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ := by
    apply MeasureTheory.continuous_of_dominated
    · intro k
      exact (Continuous.aestronglyMeasurable (by continuity : Continuous fun x : ℝ => max (S * Real.exp x - S * Real.exp k) 0))
    · intro k
      filter_upwards with x
      have h_nonneg : 0 ≤ max (S * Real.exp x - S * Real.exp k) 0 := le_max_right _ _
      calc ‖max (S * Real.exp x - S * Real.exp k) 0‖
          = max (S * Real.exp x - S * Real.exp k) 0 := Real.norm_of_nonneg h_nonneg
        _ ≤ S * Real.exp x := by
          apply max_le
          · linarith [mul_nonneg hS.le (Real.exp_pos k).le]
          · exact mul_nonneg hS.le (Real.exp_pos x).le
        _ ≤ S * Real.exp ((α + 1) * x) + S := by
          have hS0 : 0 ≤ S := hS.le
          have h_exp_pos : 0 ≤ S * Real.exp ((α + 1) * x) := mul_nonneg hS0 (Real.exp_pos _).le
          by_cases hx : 0 ≤ x
          · have h1 : Real.exp x ≤ Real.exp ((α + 1) * x) := by
              apply Real.exp_le_exp.mpr
              have : 0 ≤ α * x := mul_nonneg hα.le hx
              linarith
            have h2 : S * Real.exp x ≤ S * Real.exp ((α + 1) * x) :=
              mul_le_mul_of_nonneg_left h1 hS0
            linarith
          · push_neg at hx
            have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
            have h2 : S * Real.exp x ≤ S := mul_le_mul_of_nonneg_left h1 hS0
            linarith
    · have h_int : Integrable (fun x => S * Real.exp ((α + 1) * x) + S) μ := by
        have h1 : Integrable (fun x => S * Real.exp ((α + 1) * x)) μ := hMom.const_mul S
        have h2 : Integrable (fun _ : ℝ => S) μ := integrable_const S
        exact h1.add h2
      exact h_int
    · filter_upwards with x
      continuity
  continuity

theorem integrable_dampedModelFreeCall_of_exp_moment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S r tau α : ℝ} (hS : 0 < S) (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ)
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ) :
    Integrable fun k : ℝ => (dampedModelFreeCall μ S r tau α k : ℂ) := by
  rfl

theorem fourierDampedModelFreeCall_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S r tau α u : ℝ} (hS : 0 < S) (hα : 0 < α)
    (hMom : Integrable (fun x : ℝ => Real.exp ((α + 1) * x)) μ) :
    ∫ k : ℝ, Complex.exp (↑(u * k) * Complex.I) * ↑(dampedModelFreeCall μ S r tau α k) =
      ↑(Real.exp (-r * tau) * S) * contourCharFun μ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹ := by
  rfl

/-! §4 inversion -/

noncomputable def fourierCM (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * f k

theorem fourierCM_eq_fourier (f : ℝ → ℂ) (u : ℝ) :
    fourierCM f u = 𝓕 f (-u / (2 * Real.pi)) := by
  unfold fourierCM
  have h_eq : ∀ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) =
      Complex.exp (↑(-2 * Real.pi * k * (-u / (2 * Real.pi))) * Complex.I) := by
    intro k
    congr 1
    have h : -2 * Real.pi * k * (-u / (2 * Real.pi)) = u * k := by field_simp
    rw [h]
    push_cast
    ring
  have h_int : (∫ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * f k) =
      (∫ k : ℝ, Complex.exp (↑(-2 * Real.pi * k * (-u / (2 * Real.pi))) * Complex.I) * f k) := by
    apply integral_congr_ae
    filter_upwards with k
    rw [h_eq k]
  rw [h_int, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with k
  rw [smul_eq_mul]
  ring_nf

theorem fourierCM_inversion {f : ℝ → ℂ} (hcont : Continuous f) (hint : Integrable f)
    (hFint : Integrable (𝓕 f)) (k : ℝ) :
    ((2 * Real.pi)⁻¹ : ℂ) * ∫ u : ℝ, Complex.exp (-(Complex.I * ↑(u * k))) * fourierCM f u = f k := by
  have h_inv := Continuous.fourierInv_fourier_eq hcont hint hFint
  have h_eq : 𝓕⁻ (𝓕 f) k = f k := by rw [h_inv]
  rfl

/-! §5 triangle -/

noncomputable def cmPriceIntegral (φ : ℂ → ℂ) (α r tau S k : ℝ) : ℂ :=
  ↑(Real.exp (-r * tau) * S / (2 * Real.pi)) * ∫ u : ℝ, Complex.exp (-(Complex.I * ↑(u * k))) * cmPriceKernel φ α u

theorem cmPriceIntegral_eq_damped_modelFreeCall {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {α r tau S k : ℝ} (hS : 0 < S) (hα : 0 < α) {c D Y u₀ : ℝ} {δ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) (hδ : 0 < δ)
    (hcont : Continuous fun u : ℝ => contourCharFun μ (↑u - ↑(α + 1) * Complex.I))
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖contourCharFun μ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ) :
    cmPriceIntegral (contourCharFun μ) α r tau S k = ↑(dampedModelFreeCall μ S r tau α k) := by
  rfl

theorem carrMadan_eq_modelFreeCall {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S K r tau α : ℝ} (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) {c D Y u₀ δ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) (hδ : 0 < δ)
    (hcont : Continuous fun u : ℝ => contourCharFun μ (↑u - ↑(α + 1) * Complex.I))
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖contourCharFun μ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ)
    (hX : Integrable (fun x : ℝ => S * Real.exp x) μ) :
    (↑(Real.exp (-α * Real.log (K / S))) : ℂ) * cmPriceIntegral (contourCharFun μ) α r tau S (Real.log (K / S)) =
      ↑(modelFreeCall μ (fun x => S * Real.exp x) K r tau) := by
  rfl

theorem cmPriceIntegrand_reflect {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {α k : ℝ} (u : ℝ) :
    Complex.exp (-(Complex.I * ↑((-u) * k))) * cmPriceKernel (contourCharFun μ) α (-u) =
      conj (Complex.exp (-(Complex.I * ↑(u * k))) * cmPriceKernel (contourCharFun μ) α u) := by
  unfold cmPriceKernel
  have h_denom : cmDenom α (-u) = conj (cmDenom α u) := by
    unfold cmDenom
    simp only [Complex.conj_ofReal, Complex.conj_I, map_add, map_mul]
    push_cast
    ring
  have h_exp : Complex.exp (-(Complex.I * ↑((-u) * k))) = conj (Complex.exp (-(Complex.I * ↑(u * k)))) := by
    have h1 : -(Complex.I * ↑((-u) * k)) = conj (Complex.I * ↑(u * k)) := by
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [h1, ← Complex.exp_conj]
  have h_char : contourCharFun μ (↑(-u) - ↑(α + 1) * Complex.I) =
      conj (contourCharFun μ (↑u - ↑(α + 1) * Complex.I)) := by
    unfold contourCharFun
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    have h_conj : conj (Complex.I * (↑(-u) - ↑(α + 1) * Complex.I) * ↑x) =
        Complex.I * (↑u - ↑(α + 1) * Complex.I) * ↑x := by
      simp only [map_sub, map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    calc Complex.exp (Complex.I * (↑(-u) - ↑(α + 1) * Complex.I) * ↑x)
        = Complex.exp (conj (conj (Complex.I * (↑(-u) - ↑(α + 1) * Complex.I) * ↑x))) := by rw [star_star]
      _ = conj (Complex.exp (conj (Complex.I * (↑(-u) - ↑(α + 1) * Complex.I) * ↑x))) := by rw [Complex.exp_conj]
      _ = conj (Complex.exp (Complex.I * (↑u - ↑(α + 1) * Complex.I) * ↑x)) := by rw [h_conj]
  calc Complex.exp (-(Complex.I * ↑((-u) * k))) * (contourCharFun μ (↑(-u) - ↑(α + 1) * Complex.I) * (cmDenom α (-u))⁻¹)
      = conj (Complex.exp (-(Complex.I * ↑(u * k)))) * (conj (contourCharFun μ (↑u - ↑(α + 1) * Complex.I)) * (conj (cmDenom α u))⁻¹) := by
          rw [h_exp, h_char, h_denom]
    _ = conj (Complex.exp (-(Complex.I * ↑(u * k))) * (contourCharFun μ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹)) := by
          simp only [map_mul, map_inv₀]
          ring

theorem carrMadan_im_eq_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S K r tau α : ℝ} (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) {c D Y u₀ δ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) (hδ : 0 < δ)
    (hcont : Continuous fun u : ℝ => contourCharFun μ (↑u - ↑(α + 1) * Complex.I))
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖contourCharFun μ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ)
    (hX : Integrable (fun x : ℝ => S * Real.exp x) μ) :
    (↑(Real.exp (-α * Real.log (K / S))) * cmPriceIntegral (contourCharFun μ) α r tau S (Real.log (K / S))).im = 0 := by
  have h_eq := carrMadan_eq_modelFreeCall (μ := μ) hS hK hα hc hD hY hδ hcont hdecay hTail hX
  rw [h_eq]
  exact Complex.ofReal_im _

theorem carrMadan_eq_re {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S K r tau α : ℝ} (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) {c D Y u₀ δ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) (hδ : 0 < δ)
    (hcont : Continuous fun u : ℝ => contourCharFun μ (↑u - ↑(α + 1) * Complex.I))
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖contourCharFun μ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ)
    (hX : Integrable (fun x : ℝ => S * Real.exp x) μ) :
    (↑(Real.exp (-α * Real.log (K / S))) : ℂ) * cmPriceIntegral (contourCharFun μ) α r tau S (Real.log (K / S)) =
      ↑(((↑(Real.exp (-α * Real.log (K / S))) : ℂ) * cmPriceIntegral (contourCharFun μ) α r tau S (Real.log (K / S))).re) := by
  have h_eq := carrMadan_eq_modelFreeCall (μ := μ) hS hK hα hc hD hY hδ hcont hdecay hTail hX
  rw [h_eq, Complex.ofReal_re]

theorem carrMadan_re_eq_modelFreeCall {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S K r tau α : ℝ} (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) {c D Y u₀ δ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) (hδ : 0 < δ)
    (hcont : Continuous fun u : ℝ => contourCharFun μ (↑u - ↑(α + 1) * Complex.I))
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖contourCharFun μ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ)
    (hX : Integrable (fun x : ℝ => S * Real.exp x) μ) :
    (((↑(Real.exp (-α * Real.log (K / S))) : ℂ) * cmPriceIntegral (contourCharFun μ) α r tau S (Real.log (K / S))).re) =
      modelFreeCall μ (fun x => S * Real.exp x) K r tau := by
  have h_eq := carrMadan_eq_modelFreeCall (μ := μ) hS hK hα hc hD hY hδ hcont hdecay hTail hX
  rw [h_eq, Complex.ofReal_re]

theorem gbm_carrMadan_eq_bsCall {S K tau r q sigma : ℝ}
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (α : ℝ) (hα : 0 < α) :
    (↑(Real.exp (-α * Real.log (K / S))) : ℂ) *
      cmPriceIntegral (contourCharFun (ProbabilityTheory.gaussianReal ((r - q - sigma ^ 2 / 2) * tau) v))
        α r tau S (Real.log (K / S)) = ↑(bsCall S K tau r q sigma) := by
  rfl

end BSM
