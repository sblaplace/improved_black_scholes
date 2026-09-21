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
        · linarith [mul_nonneg hS.le (Real.exp_pos k).le]
        · exact mul_nonneg hS.le (Real.exp_pos _).le
      have h_norm_eq : ‖Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
            ↑(max (S * Real.exp x - S * Real.exp k) 0)‖ =
          ‖Complex.exp (Complex.I * ↑(u * k))‖ * ‖(↑(Real.exp (α * k)) : ℂ)‖ *
            ‖(↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ)‖ := by
        simp only [norm_mul]
      calc ‖Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
            ↑(max (S * Real.exp x - S * Real.exp k) 0)‖
          = ‖Complex.exp (Complex.I * ↑(u * k))‖ * ‖(↑(Real.exp (α * k)) : ℂ)‖ *
            ‖(↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ)‖ := h_norm_eq
        _ = 1 * Real.exp (α * k) * ‖(↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ)‖ := by
              rw [h_norm_I, h_norm_exp]
        _ ≤ 1 * Real.exp (α * k) * (S * Real.exp x) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_one (Real.exp_pos _).le)
              have h1 : ‖(↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ)‖
                  = max (S * Real.exp x - S * Real.exp k) 0 := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
              rw [h1]
              exact h_max_le
        _ = S * Real.exp x * Real.exp (α * k) := by ring
    · push_neg at hk
      have hnot : k ∉ Set.Iic x := by
        simp only [Set.mem_Iic, not_le]
        exact hk
      rw [Set.indicator_of_notMem hnot]
      have h0 : max (S * Real.exp x - S * Real.exp k) 0 = 0 := by
        have hle : Real.exp x ≤ Real.exp k := Real.exp_le_exp.mpr hk.le
        have hpos : S * Real.exp x - S * Real.exp k ≤ 0 := by
          linarith [mul_le_mul_of_nonneg_left hle hS]
        exact max_eq_right hpos
      simp [h0]
  have h_int : Integrable (fun k => (Set.Iic x).indicator (fun k => S * Real.exp x * Real.exp (α * k)) k) := by
    have h_base : IntegrableOn (fun k : ℝ => Real.exp (α * k)) (Set.Iic x) :=
      integrableOn_exp_mul_Iic hα x
    have h_const : IntegrableOn (fun k : ℝ => S * Real.exp x * Real.exp (α * k)) (Set.Iic x) :=
      h_base.const_mul (S * Real.exp x)
    exact h_const.integrable_indicator measurableSet_Iic
  exact h_int.mono' h_cont.aestronglyMeasurable (Eventually.of_forall h_bound)

theorem strikeTransform_eq {S x u α : ℝ} (hS : 0 ≤ S) (hα : 0 < α) :
    strikeTransform S α x u =
      ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹ := by
  have hα1 : 0 < α + 1 := by linarith
  have h_re_a : 0 < ((↑α + ↑u * Complex.I : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have h_re_b : 0 < ((↑(α + 1) + ↑u * Complex.I : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have h_factor : cmDenom α u = ((α : ℂ) + ↑u * Complex.I) * ((α + 1 : ℂ) + ↑u * Complex.I) :=
    cmDenom_factor α u
  have h_zero : ∀ k : ℝ, x < k → max (S * Real.exp x - S * Real.exp k) 0 = 0 := by
    intro k hk
    have hle : Real.exp x ≤ Real.exp k := Real.exp_le_exp.mpr hk.le
    have h : S * Real.exp x - S * Real.exp k ≤ 0 := by
      linarith [mul_le_mul_of_nonneg_left hle hS]
    exact max_eq_right h
  have h_f_zero : ∀ k : ℝ, x < k →
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0) = 0 := by
    intro k hk; rw [h_zero k hk]; simp
  have h_f_eq_indicator : ∀ k : ℝ,
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0) =
      (Set.Iic x).indicator (fun k => Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0)) k := by
    intro k; by_cases hk : k ≤ x
    · rw [Set.indicator_of_mem (show k ∈ Set.Iic x from hk)]
    · push_neg at hk
      rw [Set.indicator_of_notMem (show k ∉ Set.Iic x by simp [Set.mem_Iic, not_le, hk]), h_f_zero k hk]
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
  have h_max_eq : ∀ k ∈ Set.Iic x,
      max (S * Real.exp x - S * Real.exp k) 0 = S * Real.exp x - S * Real.exp k := by
    intro k hk
    have hle : Real.exp k ≤ Real.exp x := Real.exp_le_exp.mpr (hk : k ≤ x)
    have h_nonneg : 0 ≤ S * Real.exp x - S * Real.exp k := by linarith [mul_le_mul_of_nonneg_left hle hS]
    exact max_eq_left h_nonneg
  have h_ofReal_sub : ∀ k ∈ Set.Iic x,
      (↑(max (S * Real.exp x - S * Real.exp k) 0) : ℂ) =
      ↑(S * Real.exp x) - ↑(S * Real.exp k) := by
    intro k hk; rw [h_max_eq k hk, Complex.ofReal_sub]
  have h_Sexp : ∀ k : ℝ, (↑(S * Real.exp k) : ℂ) = ↑S * ↑(Real.exp k) := by intro k; push_cast; ring
  have h_exp_a_sym : ∀ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) =
      Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k) := by
    intro k
    have h_exp_a : ((↑α + ↑u * Complex.I : ℂ)) * ↑k = ↑(α * k) + Complex.I * ↑(u * k) := by
      push_cast; ring
    rw [h_exp_a, Complex.exp_add, ← Complex.ofReal_exp, mul_comm]
  have h_exp_b2 : ∀ k : ℝ, Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k) =
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) * ↑(Real.exp k) := by
    intro k
    have h_exp_b : ((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k = ↑((α + 1) * k) + Complex.I * ↑(u * k) := by
      push_cast; ring
    rw [h_exp_b, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    push_cast
    ring
  have h_on_Iic : ∀ k ∈ Set.Iic x,
      Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0) =
      ↑(S * Real.exp x) * Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k) - ↑S * Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k) := by
    intro k hk
    rw [h_ofReal_sub k hk]
    have h1 : Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        (↑(S * Real.exp x) - ↑(S * Real.exp k)) =
      ↑(S * Real.exp x) * (Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k))) -
      (Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k))) * ↑(S * Real.exp k) := by ring
    rw [h1, h_exp_a_sym k, h_Sexp k, h_exp_b2 k]
    ring
  have h_set_eq : (∫ k in Set.Iic x, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) *
        ↑(max (S * Real.exp x - S * Real.exp k) 0)) =
      ∫ k in Set.Iic x, (↑(S * Real.exp x) * Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k) - ↑S * Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k)) := by
    apply setIntegral_congr_fun measurableSet_Iic
    · exact (integrable_strikeTransform hS hα).integrableOn
    · intro k hk; exact h_on_Iic k hk
  have h_int_a : IntegrableOn (fun k : ℝ => Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k)) (Set.Iic x) :=
    integrableOn_exp_mul_complex_Iic h_re_a x
  have h_int_b : IntegrableOn (fun k : ℝ => Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k)) (Set.Iic x) :=
    integrableOn_exp_mul_complex_Iic h_re_b x
  have h_int_a_const : IntegrableOn (fun k : ℝ => ↑(S * Real.exp x) * Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k)) (Set.Iic x) :=
    h_int_a.const_mul _
  have h_int_b_const : IntegrableOn (fun k : ℝ => ↑S * Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k)) (Set.Iic x) :=
    h_int_b.const_mul _
  have h_int_a_eq : ∫ k in Set.Iic x, Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k) = Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑x) / ((↑α + ↑u * Complex.I : ℂ)) :=
    integral_exp_mul_complex_Iic h_re_a x
  have h_int_b_eq : ∫ k in Set.Iic x, Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k) = Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑x) / ((↑(α + 1) + ↑u * Complex.I : ℂ)) :=
    integral_exp_mul_complex_Iic h_re_b x
  have h_integral_sub : ∫ k in Set.Iic x, (↑(S * Real.exp x) * Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k) - ↑S * Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k)) =
      ↑(S * Real.exp x) * (Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑x) / ((↑α + ↑u * Complex.I : ℂ))) - ↑S * (Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑x) / ((↑(α + 1) + ↑u * Complex.I : ℂ))) := by
    rw [integral_sub h_int_a_const h_int_b_const, integral_const_mul, integral_const_mul, h_int_a_eq, h_int_b_eq]
  have h_ax : ((↑α + ↑u * Complex.I : ℂ)) * ↑x = ↑(x * α) + ↑(x * u) * Complex.I := by push_cast; ring
  have h_bx : ((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑x = ↑(x * (α + 1)) + ↑(x * u) * Complex.I := by push_cast; ring
  have h_mul : Real.exp x * Real.exp (x * α) = Real.exp (x * (α + 1)) := by rw [← Real.exp_add]; ring_nf
  have h_C_eq : ↑(S * Real.exp x) * Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑x) = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by
    rw [h_ax, Complex.exp_add, ← Complex.ofReal_exp]
    calc ↑(S * Real.exp x) * (↑(Real.exp (x * α)) * Complex.exp (↑(x * u) * Complex.I))
        = ↑S * ↑(Real.exp x) * ↑(Real.exp (x * α)) * Complex.exp (↑(x * u) * Complex.I) := by push_cast; ring
      _ = ↑S * ↑(Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by rw [← Complex.ofReal_mul, h_mul]
      _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by push_cast; ring
  have h_C_eq2 : ↑S * Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑x) = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by
    rw [h_bx, Complex.exp_add, ← Complex.ofReal_exp]
    calc ↑S * (↑(Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I))
        = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) := by push_cast; ring
  have h_inv_diff : ((↑α + ↑u * Complex.I : ℂ))⁻¹ - ((↑(α + 1) + ↑u * Complex.I : ℂ))⁻¹
      = (((↑α + ↑u * Complex.I : ℂ)) * ((↑(α + 1) + ↑u * Complex.I : ℂ)))⁻¹ := by
    rw [h_factor]
    field_simp
  have h_final : strikeTransform S α x u = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹ := by
    calc strikeTransform S α x u
        = ∫ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) * ↑(max (S * Real.exp x - S * Real.exp k) 0) := rfl
      _ = ∫ k in Set.Iic x, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) * ↑(max (S * Real.exp x - S * Real.exp k) 0) := h_integral_Iic
      _ = ∫ k in Set.Iic x, (↑(S * Real.exp x) * Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑k) - ↑S * Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑k)) := h_set_eq
      _ = ↑(S * Real.exp x) * (Complex.exp (((↑α + ↑u * Complex.I : ℂ)) * ↑x) / ((↑α + ↑u * Complex.I : ℂ))) - ↑S * (Complex.exp (((↑(α + 1) + ↑u * Complex.I : ℂ)) * ↑x) / ((↑(α + 1) + ↑u * Complex.I : ℂ))) := h_integral_sub
      _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (((↑α + ↑u * Complex.I : ℂ))⁻¹ - ((↑(α + 1) + ↑u * Complex.I : ℂ))⁻¹) := by
            rw [div_eq_mul_inv, ← mul_assoc, ← mul_assoc, h_C_eq, h_C_eq2, mul_sub]
      _ = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹ := by
            rw [h_inv_diff]
  exact h_final

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
              have h5 : ((α + 1) * x : ℝ) = x + α * x := by ring
              have h6 : 0 ≤ α * x := mul_nonneg hα.le hx
              rw [h5]
              linarith
            have h2 : S * Real.exp x ≤ S * Real.exp ((α + 1) * x) :=
              mul_le_mul_of_nonneg_left h1 hS0
            linarith
          · push_neg at hx
            have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
            have h2 : S * Real.exp x ≤ S := by
              rw [← mul_one S]
              exact mul_le_mul_of_nonneg_left h1 hS0
            linarith
    · have h_int : Integrable (fun x => S * Real.exp ((α + 1) * x) + S) μ := by
        have h1 : Integrable (fun x => S * Real.exp ((α + 1) * x)) μ := hMom.const_mul S
        have h2 : Integrable (fun _ : ℝ => S) μ := integrable_const S
        exact h1.add h2
      exact h_int
    · filter_upwards with x
      continuity
  continuity

/-- Every exponential moment at a level below an existing one is finite, with
its value bounded through `1`: on `x ≤ 0` the smaller exponential is at most
`1`, on `x ≥ 0` it is dominated by the larger one. The `0 ≤ b` side condition
is what makes the left tail work. -/
theorem exp_moments_of_exp_tail {μ : Measure ℝ} [IsProbabilityMeasure μ] {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c)
    (hTail : Integrable (fun x : ℝ => Real.exp (c * x)) μ) :
    Integrable (fun x : ℝ => Real.exp (b * x)) μ ∧
      ∫ x : ℝ, Real.exp (b * x) ∂μ ≤ 1 + ∫ x : ℝ, Real.exp (c * x) ∂μ := by
  have hpt : ∀ x : ℝ, Real.exp (b * x) ≤ 1 + Real.exp (c * x) := by
    intro x
    by_cases hx : x ≤ 0
    · have h1 : Real.exp (b * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith [(Real.exp_pos (c * x)).le]
    · push_neg at hx
      have h1 : b * x ≤ c * x := by
        have h2 : 0 ≤ (c - b) * x := mul_nonneg (by linarith) hx
        linarith
      have h2 : Real.exp (b * x) ≤ Real.exp (c * x) := Real.exp_le_exp.mpr h1
      linarith
  have hint : Integrable (fun x : ℝ => 1 + Real.exp (c * x)) μ :=
    (integrable_const (1 : ℝ)).add hTail
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (b * x)) μ :=
    (Continuous.aestronglyMeasurable
      (show Continuous fun x : ℝ => Real.exp (b * x) by fun_prop))
  have hbound : ∀ᵐ x ∂μ, ‖Real.exp (b * x)‖ ≤ 1 + Real.exp (c * x) :=
    Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos (b * x)).le]
      exact hpt x)
  have hint1 : Integrable (fun x : ℝ => Real.exp (b * x)) μ := hint.mono' hmeas hbound
  refine ⟨hint1, ?_⟩
  calc ∫ x, Real.exp (b * x) ∂μ
      ≤ ∫ x, (1 + Real.exp (c * x)) ∂μ :=
        integral_mono_ae hint1 hint (Filter.Eventually.of_forall hpt)
    _ = (∫ x, 1 ∂μ) + ∫ x, Real.exp (c * x) ∂μ := integral_add (integrable_const 1) hTail
    _ = 1 + ∫ x, Real.exp (c * x) ∂μ := by
        rw [integral_const, Measure.measure_univ_eq_one]

theorem integrable_dampedModelFreeCall_of_exp_moment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S r tau α : ℝ} (hS : 0 < S) (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ)
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ) :
    Integrable fun k : ℝ => (dampedModelFreeCall μ S r tau α k : ℂ) := by
  -- the two exponential moments the two tails need, from the one (H-tail)
  obtain ⟨hE1, hI1⟩ := exp_moments_of_exp_tail (b := 1) (c := α + 1 + δ) (by linarith) hTail
  obtain ⟨hMom, _⟩ := exp_moments_of_exp_tail (b := α + 1) (c := α + 1 + δ) (by linarith) hTail
  set M : ℝ := ∫ x : ℝ, Real.exp ((α + 1 + δ) * x) ∂μ with hM_def
  have hM0 : (0 : ℝ) ≤ M := by
    rw [hM_def]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
  -- right tail: the payoff is dominated by a moment at the tail level,
  -- with factor e^{-(α+δ)k} (valid pointwise, since the payoff vanishes off {x > k})
  have hpay_tail : ∀ k : ℝ,
      ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ
        ≤ (S * Real.exp (-(α + δ) * k)) * M := by
    intro k
    have hpt : ∀ x : ℝ, max (S * Real.exp x - S * Real.exp k) 0
        ≤ (S * Real.exp (-(α + δ) * k)) * Real.exp ((α + 1 + δ) * x) := by
      intro x
      have hR : 0 ≤ (S * Real.exp (-(α + δ) * k)) * Real.exp ((α + 1 + δ) * x) :=
        mul_nonneg (mul_nonneg hS.le (Real.exp_pos _).le) (Real.exp_pos _).le
      by_cases hx : x ≤ k
      · have h0 : max (S * Real.exp x - S * Real.exp k) 0 = 0 := by
          have hle : Real.exp x ≤ Real.exp k := Real.exp_le_exp.mpr hx
          exact max_eq_right (by linarith [mul_le_mul_of_nonneg_left hle hS.le])
        rw [h0]; exact hR
      · push_neg at hx
        have he2 : x ≤ (α + 1 + δ) * x - (α + δ) * k := by
          have hx1 : (α + 1 + δ) * x - (α + δ) * k = x + (α + δ) * (x - k) := by ring
          rw [hx1]
          have he : 0 ≤ (α + δ) * (x - k) := mul_nonneg (by linarith) (by linarith)
          linarith
        have h2 : Real.exp x ≤ Real.exp ((α + 1 + δ) * x) * Real.exp (-(α + δ) * k) := by
          apply Real.exp_le_exp.mpr
          rw [← Real.exp_add]
          exact he2
        have h1 : max (S * Real.exp x - S * Real.exp k) 0 ≤ S * Real.exp x := by
          apply max_le
          · linarith [mul_nonneg hS.le (Real.exp_pos x).le, mul_nonneg hS.le (Real.exp_pos k).le]
          · exact mul_nonneg hS.le (Real.exp_pos _).le
        have h3 : S * Real.exp x ≤ S * (Real.exp ((α + 1 + δ) * x) * Real.exp (-(α + δ) * k)) :=
          mul_le_mul_of_nonneg_left h2 hS.le
        calc max (S * Real.exp x - S * Real.exp k) 0 ≤ S * Real.exp x := h1
          _ ≤ S * (Real.exp ((α + 1 + δ) * x) * Real.exp (-(α + δ) * k)) := h3
          _ = (S * Real.exp (-(α + δ) * k)) * Real.exp ((α + 1 + δ) * x) := by ring
    have hpay_int : Integrable (fun x => max (S * Real.exp x - S * Real.exp k) 0) μ := by
      refine (hTail.const_mul S).mono' ?_ ?_
      · exact (Continuous.aestronglyMeasurable
          (show Continuous fun x : ℝ => max (S * Real.exp x - S * Real.exp k) 0 by fun_prop))
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        have h1 : max (S * Real.exp x - S * Real.exp k) 0 ≤ S * Real.exp x := by
          apply max_le
          · linarith [mul_nonneg hS.le (Real.exp_pos x).le, mul_nonneg hS.le (Real.exp_pos k).le]
          · exact mul_nonneg hS.le (Real.exp_pos _).le
        have h2 : S * Real.exp x ≤ S * Real.exp ((α + 1 + δ) * x) := by
          apply mul_le_mul_of_nonneg_left _ hS.le
          apply Real.exp_le_exp.mpr
          by_cases hx : 0 ≤ x
          · have h5 : (α + 1 + δ) * x = x + (α + δ) * x := by ring
            have h3 : 0 ≤ (α + δ) * x := mul_nonneg (by linarith) hx
            rw [h5]
            linarith
          · push_neg at hx
            have h3 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
            have h4 : S * Real.exp x ≤ S := by
              rw [← mul_one S]; exact mul_le_mul_of_nonneg_left h3 hS.le
            linarith [(Real.exp_pos _).le]
        linarith
    have hmono : ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ
        ≤ ∫ x, (S * Real.exp (-(α + δ) * k)) * Real.exp ((α + 1 + δ) * x) ∂μ :=
      integral_mono_ae hpay_int (hTail.const_mul (S * Real.exp (-(α + δ) * k)))
        (Filter.Eventually.of_forall hpt)
    have hconst : ∫ x, (S * Real.exp (-(α + δ) * k)) * Real.exp ((α + 1 + δ) * x) ∂μ
        = (S * Real.exp (-(α + δ) * k)) * M := by
      rw [integral_const_mul, ← hM_def]
    calc ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ
        ≤ ∫ x, (S * Real.exp (-(α + δ) * k)) * Real.exp ((α + 1 + δ) * x) ∂μ := hmono
      _ = (S * Real.exp (-(α + δ) * k)) * M := hconst
  -- flat bound: the payoff is at most S e^x, whose integral is bounded through 1
  have hpay_flat : ∀ k : ℝ, ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ ≤ S * (1 + M) := by
    intro k
    have hpt : ∀ x : ℝ, max (S * Real.exp x - S * Real.exp k) 0 ≤ S * Real.exp (1 * x) := by
      intro x
      apply max_le
      · linarith [mul_nonneg hS.le (Real.exp_pos x).le, mul_nonneg hS.le (Real.exp_pos k).le]
      · rw [mul_one]
        exact mul_nonneg hS.le (Real.exp_pos _).le
    have hpay_int : Integrable (fun x => max (S * Real.exp x - S * Real.exp k) 0) μ := by
      refine (hE1.const_mul S).mono' ?_ ?_
      · exact (Continuous.aestronglyMeasurable
          (show Continuous fun x : ℝ => max (S * Real.exp x - S * Real.exp k) 0 by fun_prop))
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact hpt x
    have hmono : ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ
        ≤ ∫ x, S * Real.exp (1 * x) ∂μ :=
      integral_mono_ae hpay_int (hE1.const_mul S) (Filter.Eventually.of_forall hpt)
    have hconst : ∫ x, S * Real.exp (1 * x) ∂μ = S * ∫ x, Real.exp x ∂μ := by
      rw [integral_const_mul]
    calc ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ
        ≤ S * ∫ x, Real.exp x ∂μ := by rw [← hconst]; exact hmono
      _ ≤ S * (1 + M) := mul_le_mul_of_nonneg_left hI1 hS.le
  -- the dominating function: C₁ e^{αk} left of 0, C₂ e^{-δk} right of it
  set C1 : ℝ := Real.exp (-r * tau) * S * (1 + M) with hC1_def
  set C2 : ℝ := Real.exp (-r * tau) * S * M with hC2_def
  have hintg : Integrable (fun k : ℝ =>
      (Set.Iic (0:ℝ)).indicator (fun _ => C1 * Real.exp (α * k)) k
        + (Set.Ioi (0:ℝ)).indicator (fun _ => C2 * Real.exp (-(δ * k))) k) := by
    have h1 : IntegrableOn (fun k : ℝ => C1 * Real.exp (α * k)) (Set.Iic 0) :=
      (integrableOn_exp_mul_Iic hα 0).const_mul C1
    have h2 : IntegrableOn (fun k : ℝ => C2 * Real.exp (-(δ * k))) (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := -δ) (by linarith) 0).const_mul C2
    exact (h1.integrable_indicator measurableSet_Iic).add
      (h2.integrable_indicator measurableSet_Ioi)
  have hnn : ∀ k : ℝ, 0 ≤ dampedModelFreeCall μ S r tau α k := by
    intro k
    unfold dampedModelFreeCall
    apply mul_nonneg (Real.exp_pos _).le
    apply mul_nonneg (Real.exp_pos _).le
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => le_max_right _ _))
  have hbound : ∀ k : ℝ, ‖(dampedModelFreeCall μ S r tau α k : ℂ)‖ ≤
      (Set.Iic (0:ℝ)).indicator (fun _ => C1 * Real.exp (α * k)) k
        + (Set.Ioi (0:ℝ)).indicator (fun _ => C2 * Real.exp (-(δ * k))) k := by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn k)]
    unfold dampedModelFreeCall
    by_cases hk : k ≤ 0
    · have hm1 : k ∈ Set.Iic (0:ℝ) := hk
      have hm2 : k ∉ Set.Ioi (0:ℝ) := by
        intro hm; exact absurd (Set.mem_Ioi.mp hm).le hk
      rw [Set.indicator_of_mem hm1, Set.indicator_of_notMem hm2, add_zero, hC1_def]
      calc Real.exp (α * k) * (Real.exp (-r * tau) * ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ)
          ≤ Real.exp (α * k) * (Real.exp (-r * tau) * (S * (1 + M))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hpay_flat k) (Real.exp_pos _).le) (Real.exp_pos _).le
        _ = Real.exp (-r * tau) * S * (1 + M) * Real.exp (α * k) := by ring
    · push_neg at hk
      have hm1 : k ∈ Set.Ioi (0:ℝ) := hk
      have hm2 : k ∉ Set.Iic (0:ℝ) := by
        intro hm; exact absurd hk hm.le
      rw [Set.indicator_of_notMem hm2, Set.indicator_of_mem hm1, zero_add, hC2_def]
      have hexp : Real.exp (α * k) * Real.exp (-(α + δ) * k) = Real.exp (-(δ * k)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (α * k) * (Real.exp (-r * tau) * ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ)
          ≤ Real.exp (α * k) * (Real.exp (-r * tau) * ((S * Real.exp (-(α + δ) * k)) * M)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hpay_tail k) (Real.exp_pos _).le) (Real.exp_pos _).le
        _ = Real.exp (-r * tau) * S * M * Real.exp (-(δ * k)) := by
              calc Real.exp (α * k) * (Real.exp (-r * tau) * ((S * Real.exp (-(α + δ) * k)) * M))
                  = Real.exp (-r * tau) * S * M * (Real.exp (α * k) * Real.exp (-(α + δ) * k)) := by ring
                _ = Real.exp (-r * tau) * S * M * Real.exp (-(δ * k)) := by rw [hexp]
  exact hintg.mono' (continuous_dampedModelFreeCall hS hα hMom).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

theorem fourierDampedModelFreeCall_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S r tau α u : ℝ} (hS : 0 < S) (hα : 0 < α)
    (hMom : Integrable (fun x : ℝ => Real.exp ((α + 1) * x)) μ) :
    ∫ k : ℝ, Complex.exp (↑(u * k) * Complex.I) * ↑(dampedModelFreeCall μ S r tau α k) =
      ↑(Real.exp (-r * tau) * S) * contourCharFun μ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹ := by
  have hα1 : 0 < α + 1 := by linarith
  -- the two-variable integrand
  set F : ℝ → ℝ → ℂ := fun k x => Complex.exp (↑(u * k) * Complex.I) *
    (Complex.ofReal (Real.exp (α * k)) * (Complex.ofReal (Real.exp (-r * tau)) *
      Complex.ofReal (max (S * Real.exp x - S * Real.exp k) 0))) with hF_def
  have hnorm_eq : ∀ k x : ℝ, ‖F k x‖ =
      Real.exp (α * k) * (Real.exp (-r * tau) * max (S * Real.exp x - S * Real.exp k) 0) := by
    intro k x
    rw [hF_def]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos (α * k)).le, abs_of_nonneg (Real.exp_pos (-r * tau)).le,
      abs_of_nonneg (mul_nonneg hS.le (Real.exp_pos x).le),
      abs_of_nonneg (le_max_right _ _), Complex.norm_exp_ofReal_mul_I]
    simp only [one_mul]
    ring
  have hcontF : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
    rw [hF_def]
    fun_prop
  -- Fubini's criterion
  have hAESM : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) (volume.prod μ) :=
    hcontF.measurable.aestronglyMeasurable
  have hintk : ∀ x : ℝ, Integrable (fun k : ℝ => F k x) volume := by
    intro x
    have hmeas : AEStronglyMeasurable (fun k : ℝ => F k x) volume :=
      (show Continuous fun k : ℝ => F k x by fun_prop).aestronglyMeasurable
    have h_max_le : max (S * Real.exp x - S * Real.exp k) 0 ≤ S * Real.exp x := by
      apply max_le
      · linarith [mul_nonneg hS.le (Real.exp_pos k).le]
      · exact mul_nonneg hS.le (Real.exp_pos _).le
    have h_dom : Integrable (fun k : ℝ => (Set.Iic x).indicator
        (fun k => Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k)) k) volume := by
      have hbase : IntegrableOn (fun k : ℝ => Real.exp (α * k)) (Set.Iic x) :=
        integrableOn_exp_mul_Iic hα x
      exact ((hbase.const_mul (Real.exp (-r * tau) * S * Real.exp x)).integrable_indicator
        measurableSet_Iic)
    refine h_dom.mono' hmeas (Filter.Eventually.of_forall (fun k => ?_))
    by_cases hk : k ≤ x
    · rw [Set.indicator_of_mem (hk : k ∈ Set.Iic x), hnorm_eq k x]
      calc Real.exp (α * k) * (Real.exp (-r * tau) * max (S * Real.exp x - S * Real.exp k) 0)
          ≤ Real.exp (α * k) * (Real.exp (-r * tau) * (S * Real.exp x)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h_max_le (Real.exp_pos _).le) (Real.exp_pos _).le
        _ = Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k) := by ring
    · push_neg at hk
      have hnot : k ∉ Set.Iic x := by
        simp only [Set.mem_Iic, not_le]; exact hk
      rw [Set.indicator_of_notMem hnot, hnorm_eq k x]
      have h0 : max (S * Real.exp x - S * Real.exp k) 0 = 0 := by
        have hle : Real.exp x ≤ Real.exp k := Real.exp_le_exp.mpr hk.le
        exact max_eq_right (by linarith [mul_le_mul_of_nonneg_left hle hS.le])
      rw [h0, mul_zero, mul_zero]
  have h2 : Integrable (fun x : ℝ => ∫ k : ℝ, ‖F k x‖ ∂volume) μ := by
    have hmeas2 : StronglyMeasurable (fun p : ℝ × ℝ => ‖F p.1 p.2‖) := hcontF.norm.stronglyMeasurable
    have hmeas3 : StronglyMeasurable (fun x : ℝ => ∫ k : ℝ, ‖F k x‖ ∂volume) :=
      hmeas2.integral_prod_left'
    have hinnorm : ∀ x : ℝ, ∫ k : ℝ, ‖F k x‖ ∂volume
        ≤ (Real.exp (-r * tau) * S / α) * Real.exp ((α + 1) * x) := by
      intro x
      have hpt : ∀ k : ℝ, ‖F k x‖ ≤ (Set.Iic x).indicator
          (fun k => Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k)) k := by
        intro k
        by_cases hk : k ≤ x
        · rw [Set.indicator_of_mem (hk : k ∈ Set.Iic x), hnorm_eq k x]
          have h_max_le : max (S * Real.exp x - S * Real.exp k) 0 ≤ S * Real.exp x := by
            apply max_le
            · linarith [mul_nonneg hS.le (Real.exp_pos k).le]
            · exact mul_nonneg hS.le (Real.exp_pos _).le
          calc Real.exp (α * k) * (Real.exp (-r * tau) * max (S * Real.exp x - S * Real.exp k) 0)
              ≤ Real.exp (α * k) * (Real.exp (-r * tau) * (S * Real.exp x)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left h_max_le (Real.exp_pos _).le) (Real.exp_pos _).le
            _ = Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k) := by ring
        · push_neg at hk
          have hnot : k ∉ Set.Iic x := by
            simp only [Set.mem_Iic, not_le]; exact hk
          rw [Set.indicator_of_notMem hnot, hnorm_eq k x]
          have h0 : max (S * Real.exp x - S * Real.exp k) 0 = 0 := by
            have hle : Real.exp x ≤ Real.exp k := Real.exp_le_exp.mpr hk.le
            exact max_eq_right (by linarith [mul_le_mul_of_nonneg_left hle hS.le])
          rw [h0, mul_zero, mul_zero]
      have hintF : Integrable (fun k : ℝ => ‖F k x‖) volume := (hintk x).norm
      have hintind : Integrable (fun k : ℝ => (Set.Iic x).indicator
          (fun k => Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k)) k) volume := by
        have hbase : IntegrableOn (fun k : ℝ => Real.exp (α * k)) (Set.Iic x) :=
          integrableOn_exp_mul_Iic hα x
        exact ((hbase.const_mul (Real.exp (-r * tau) * S * Real.exp x)).integrable_indicator
          measurableSet_Iic)
      have hmono : ∫ k : ℝ, ‖F k x‖ ∂volume ≤
          ∫ k : ℝ, (Set.Iic x).indicator
            (fun k => Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k)) k ∂volume :=
        integral_mono_ae hintF hintind (Filter.Eventually.of_forall hpt)
      have hind : ∫ k : ℝ, (Set.Iic x).indicator
            (fun k => Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k)) k
          = Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * x) / α := by
        rw [integral_indicator measurableSet_Iic, integral_const_mul,
          integral_exp_mul_Iic hα x]
      calc ∫ k : ℝ, ‖F k x‖ ∂volume
          ≤ ∫ k : ℝ, (Set.Iic x).indicator
              (fun k => Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * k)) k ∂volume := hmono
        _ = Real.exp (-r * tau) * S * Real.exp x * Real.exp (α * x) / α := hind
        _ = (Real.exp (-r * tau) * S / α) * Real.exp ((α + 1) * x) := by
              have hsplit : Real.exp ((α + 1) * x) = Real.exp (α * x) * Real.exp x := by
                rw [← Real.exp_add]; congr 1; ring
              rw [hsplit]
              ring
    refine (hMom.const_mul (Real.exp (-r * tau) * S / α)).mono' hmeas3.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        have h1 := hinnorm x
        have hpos : 0 ≤ ∫ k : ℝ, ‖F k x‖ ∂volume := integral_nonneg_of_ae
          (Filter.Eventually.of_forall (fun k => norm_nonneg _))
        rw [Real.norm_eq_abs, abs_of_nonneg hpos]
        linarith))
  have hunc0 : Integrable (fun p : ℝ × ℝ => F p.1 p.2) (volume.prod μ) :=
    (integrable_prod_iff' hAESM).mpr ⟨Filter.Eventually.of_forall hintk, h2⟩
  have hunc : Integrable (uncurry F) (volume.prod μ) := hunc0
  have hswap := integral_integral_swap hunc
  -- the two inner integrals in closed form
  have h_inner : ∀ k : ℝ, (∫ x : ℝ, F k x ∂μ) =
      Complex.exp (↑(u * k) * Complex.I) * ↑(dampedModelFreeCall μ S r tau α k) := by
    intro k
    simp only [hF_def, integral_const_mul, integral_ofReal]
    congr 1
    show Complex.ofReal (Real.exp (α * k)) * (Complex.ofReal (Real.exp (-r * tau)) *
      Complex.ofReal (∫ x : ℝ, max (S * Real.exp x - S * Real.exp k) 0 ∂μ))
      = Complex.ofReal (Real.exp (α * k) * (Real.exp (-r * tau) *
          ∫ x : ℝ, max (S * Real.exp x - S * Real.exp k) 0 ∂μ))
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
  have h_outer : ∀ x : ℝ, (∫ k : ℝ, F k x) =
      Complex.ofReal (Real.exp (-r * tau)) *
        (↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹) := by
    intro x
    have hpt : ∀ k : ℝ, F k x = Complex.ofReal (Real.exp (-r * tau)) *
        (Complex.exp (Complex.I * ↑(u * k)) * Complex.ofReal (Real.exp (α * k)) *
          Complex.ofReal (max (S * Real.exp x - S * Real.exp k) 0)) := by
      intro k
      simp only [hF_def]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      ← strikeTransform_eq hS hα]
  calc ∫ k : ℝ, Complex.exp (↑(u * k) * Complex.I) * ↑(dampedModelFreeCall μ S r tau α k)
      = ∫ k : ℝ, ∫ x : ℝ, F k x ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        exact (h_inner k).symm
    _ = ∫ x : ℝ, ∫ k : ℝ, F k x ∂volume ∂μ := hswap
    _ = ∫ x : ℝ, Complex.ofReal (Real.exp (-r * tau)) *
          (↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall h_outer)
    _ = Complex.ofReal (Real.exp (-r * tau)) *
          ((↑S * (cmDenom α u)⁻¹) *
            ∫ x : ℝ, Complex.ofReal (Real.exp ((α + 1) * x)) * Complex.exp (↑(x * u) * Complex.I) ∂μ) := by
        have hpt : ∀ x : ℝ, Complex.ofReal (Real.exp (-r * tau)) *
              (↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹) =
            Complex.ofReal (Real.exp (-r * tau)) *
              ((↑S * (cmDenom α u)⁻¹) *
                (Complex.ofReal (Real.exp ((α + 1) * x)) * Complex.exp (↑(x * u) * Complex.I))) := by
          intro x
          rw [← Complex.ofReal_mul]
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
    _ = ↑(Real.exp (-r * tau) * S) * contourCharFun μ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹ := by
        have hchar : (∫ x : ℝ, Complex.ofReal (Real.exp ((α + 1) * x)) *
            Complex.exp (↑(x * u) * Complex.I) ∂μ) = contourCharFun μ (↑u - ↑(α + 1) * Complex.I) := by
          unfold contourCharFun
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
          have he : Complex.I * (↑u - ↑(α + 1) * Complex.I) * ↑x =
              Complex.I * ↑(x * u) + Complex.ofReal ((α + 1) * x) := by
            calc Complex.I * (↑u - ↑(α + 1) * Complex.I) * ↑x
                = Complex.I * ↑u * ↑x - (Complex.I * Complex.I) * ↑(α + 1) * ↑x := by ring
              _ = Complex.I * ↑u * ↑x + ↑(α + 1) * ↑x := by rw [hI2]; ring
              _ = Complex.I * ↑(x * u) + Complex.ofReal ((α + 1) * x) := by push_cast; ring
          rw [he, Complex.exp_add, ← Complex.ofReal_exp]
          ring
        rw [hchar, ← Complex.ofReal_mul]
        ring

/-! §4 inversion -/

noncomputable def fourierCM (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * f k

theorem fourierCM_eq_fourier (f : ℝ → ℂ) (u : ℝ) :
    fourierCM f u = 𝓕 f (-u / (2 * Real.pi)) := by
  unfold fourierCM
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [smul_eq_mul]
  refine congrArg (fun z : ℂ => z * f t) ?_
  refine congrArg Complex.exp ?_
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hdiv : (-2 * Real.pi * t * (-u / (2 * Real.pi)) : ℝ) = u * t := by
    field_simp
  rw [hdiv]
  ring

theorem fourierCM_inversion {f : ℝ → ℂ} (hcont : Continuous f) (hint : Integrable f)
    (hFint : Integrable (𝓕 f)) (k : ℝ) :
    ((2 * Real.pi)⁻¹ : ℂ) * ∫ u : ℝ, Complex.exp (-(Complex.I * ↑(u * k))) * fourierCM f u = f k := by
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h_inv : 𝓕⁻ (𝓕 f) k = f k := by rw [Continuous.fourierInv_fourier_eq hcont hint hFint]
  -- the inverse transform as an integral, in multiplication form
  have hInvInt : 𝓕⁻ (𝓕 f) k = ∫ v : ℝ, Complex.exp (2 * ↑Real.pi * Complex.I * ↑v * ↑k) * 𝓕 f v := by
    rw [Real.fourierInv_eq' (𝓕 f) k]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    rw [smul_eq_mul]
    congr 1
    push_cast
    ring
  -- reindex the target integral: u = -2πv
  have h_shift : ∀ w : ℝ, (-w / (2 * Real.pi) : ℝ) = (-1 / (2 * Real.pi)) * w := by
    intro w; ring
  have h_int : (∫ u : ℝ, Complex.exp (-(Complex.I * ↑(u * k))) * fourierCM f u) =
      ∫ u : ℝ, (fun v : ℝ => Complex.exp (2 * ↑Real.pi * Complex.I * ↑v * ↑k) * 𝓕 f v) ((-1 / (2 * Real.pi)) * u) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hexp : Complex.exp (-(Complex.I * ↑(w * k))) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-w / (2 * Real.pi)) * ↑k) := by
      congr 1
      push_cast
      field_simp
      ring
    rw [hexp, fourierCM_eq_fourier, h_shift]
  rw [h_int, Measure.integral_comp_mul_left _ (-1 / (2 * Real.pi))]
  have hscale : |(-1 / (2 * Real.pi) : ℝ)⁻¹| = (2 * Real.pi : ℝ) := by
    have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
    have hinv : (-1 / (2 * Real.pi) : ℝ)⁻¹ = -(2 * Real.pi) := by field_simp
    rw [hinv, abs_neg, abs_of_pos hpos]
  rw [hscale, ← hInvInt]
  -- the real scalar acts on ℂ by multiplication
  have hsmulfix : ((2 * Real.pi : ℝ) • (𝓕⁻ (𝓕 f) k)) = ((2 * Real.pi : ℝ) * 𝓕⁻ (𝓕 f) k) := rfl
  rw [hsmulfix, mul_assoc]
  try push_cast
  rw [inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr h2π), one_mul, h_inv]

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
  -- the two moments from the one tail hypothesis
  obtain ⟨hMom, _⟩ := exp_moments_of_exp_tail (b := α + 1) (c := α + 1 + δ) (by linarith) hTail
  -- 𝓕 (damped price) = fourierCM, and fourierCM = the kernel line
  set f' : ℝ → ℂ := fun k => (dampedModelFreeCall μ S r tau α k : ℂ) with hf'_def
  have hcont' : Continuous f' := continuous_dampedModelFreeCall hS hα hMom
  have hint : Integrable f' := integrable_dampedModelFreeCall_of_exp_moment hS hα hδ hTail
  have hCM : ∀ w : ℝ, 𝓕 f' w = fourierCM f' (-2 * Real.pi * w) := by
    intro w
    unfold fourierCM
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [smul_eq_mul]
    refine congrArg (fun z : ℂ => z * f' t) ?_
    refine congrArg Complex.exp ?_
    push_cast
    ring
  have hFint : Integrable (𝓕 f') := by
    have hfc : ∀ v : ℝ, fourierCM f' v =
        ↑(Real.exp (-r * tau) * S) * contourCharFun μ (↑v - ↑(α + 1) * Complex.I) * (cmDenom α v)⁻¹ :=
      fun v => fourierDampedModelFreeCall_eq hS hα hMom
    have hfun : (fun w : ℝ => fourierCM f' (-2 * Real.pi * w)) =
        fun w : ℝ => ↑(Real.exp (-r * tau) * S) * (cmPriceKernel (contourCharFun μ) α (-2 * Real.pi * w)) := by
      funext w
      rw [hfc]
      unfold cmPriceKernel
      ring
    rw [funext hCM, hfun]
    have hKint := cmPriceKernel_integrable hα hcont hc hD hY hdecay
    have hscal := hKint.comp_mul_left' (R := -2 * Real.pi) (by positivity)
    have hrestr : (fun w : ℝ => (Real.exp (-r * tau) * S : ℂ) *
        cmPriceKernel (contourCharFun μ) α (-2 * Real.pi * w)) =
        (Real.exp (-r * tau) * S : ℂ) • (fun w : ℝ => cmPriceKernel (contourCharFun μ) α (-2 * Real.pi * w)) := by
      funext w
      rw [smul_eq_mul]
    rw [hrestr]
    exact Integrable.smul _ hscal
  -- apply the inversion
  have hstep := fourierCM_inversion (f := f') hcont' hint hFint k
  have hkerneq : ∀ w : ℝ, Complex.exp (-(Complex.I * ↑(w * k))) * fourierCM f' w =
      ↑(Real.exp (-r * tau) * S) *
        (Complex.exp (-(Complex.I * ↑(w * k))) * cmPriceKernel (contourCharFun μ) α w) := by
    intro w
    have hfc : fourierCM f' w = ↑(Real.exp (-r * tau) * S) * contourCharFun μ (↑w - ↑(α + 1) * Complex.I) * (cmDenom α w)⁻¹ :=
      fourierDampedModelFreeCall_eq hS hα hMom
    rw [hfc]
    unfold cmPriceKernel
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hkerneq), integral_const_mul] at hstep
  -- hstep : ((2π)⁻¹ : ℂ) * (↑(e^{-rτ}S) * ∫ u, e^{-iuk} cmPriceKernel ...) = f' k
  unfold cmPriceIntegral
  have hconst : ((2 * Real.pi)⁻¹ : ℂ) * (Complex.ofReal (Real.exp (-r * tau) * S) *
      ∫ u : ℝ, Complex.exp (-(Complex.I * ↑(u * k))) * cmPriceKernel (contourCharFun μ) α u) =
      Complex.ofReal (Real.exp (-r * tau) * S / (2 * Real.pi)) *
        ∫ u : ℝ, Complex.exp (-(Complex.I * ↑(u * k))) * cmPriceKernel (contourCharFun μ) α u := by
    have hpi2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hpiC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := RCLike.ofReal_ne_zero.mpr hpi2
    push_cast
    field_simp
  rw [hconst]
  exact hstep

theorem carrMadan_eq_modelFreeCall {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S K r tau α : ℝ} (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) {c D Y u₀ δ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) (hδ : 0 < δ)
    (hcont : Continuous fun u : ℝ => contourCharFun μ (↑u - ↑(α + 1) * Complex.I))
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖contourCharFun μ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ)
    (hX : Integrable (fun x : ℝ => S * Real.exp x) μ) :
    (↑(Real.exp (-α * Real.log (K / S))) : ℂ) * cmPriceIntegral (contourCharFun μ) α r tau S (Real.log (K / S)) =
      ↑(modelFreeCall μ (fun x => S * Real.exp x) K r tau) := by
  have hkK : S * Real.exp (Real.log (K / S)) = K := by
    rw [Real.exp_log (div_pos hK hS), ← mul_div_assoc, mul_comm S K, mul_div_assoc, div_self hS.ne', mul_one]
  have hmain := cmPriceIntegral_eq_damped_modelFreeCall (S := S) (k := Real.log (K / S))
    hS hα hc hD hY hδ hcont hdecay hTail
  have hpay : dampedModelFreeCall μ S r tau α (Real.log (K / S)) =
      Real.exp (α * Real.log (K / S)) * modelFreeCall μ (fun x => S * Real.exp x) K r tau := by
    unfold dampedModelFreeCall modelFreeCall
    rw [hkK]
    ring
  rw [← hpay, ← hmain]
  rw [Complex.ofReal_mul, ← mul_assoc]
  have hcancel : (Complex.ofReal (Real.exp (-α * Real.log (K / S))) *
      Complex.ofReal (Real.exp (α * Real.log (K / S)))) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hcancel, one_mul]

theorem cmPriceIntegrand_reflect {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {α k : ℝ} (u : ℝ) :
    Complex.exp (-(Complex.I * ↑((-u) * k))) * cmPriceKernel (contourCharFun μ) α (-u) =
      conj (Complex.exp (-(Complex.I * ↑(u * k))) * cmPriceKernel (contourCharFun μ) α u) := by
  unfold cmPriceKernel
  have h_denom : cmDenom α (-u) = conj (cmDenom α u) := by
    unfold cmDenom
    simp only [Complex.conj_ofReal, Complex.conj_I, map_mul]
    push_cast
    ring
  have h_exp : Complex.exp (-(Complex.I * ↑((-u) * k))) = conj (Complex.exp (-(Complex.I * ↑(u * k)))) := by
    have h1 : -(Complex.I * ↑((-u) * k)) = conj (-(Complex.I * ↑(u * k))) := by
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [h1, Complex.exp_conj]
  have h_char : contourCharFun μ (↑(-u) - ↑(α + 1) * Complex.I) =
      conj (contourCharFun μ (↑u - ↑(α + 1) * Complex.I)) := by
    unfold contourCharFun
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    have h_conj : Complex.I * (↑(-u) - ↑(α + 1) * Complex.I) * ↑x =
        conj (Complex.I * (↑u - ↑(α + 1) * Complex.I) * ↑x) := by
      simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    calc Complex.exp (Complex.I * (↑(-u) - ↑(α + 1) * Complex.I) * ↑x)
        = Complex.exp (conj (Complex.I * (↑u - ↑(α + 1) * Complex.I) * ↑x)) := by rw [← h_conj]
      _ = conj (Complex.exp (Complex.I * (↑u - ↑(α + 1) * Complex.I) * ↑x)) := by rw [Complex.exp_conj]
  calc Complex.exp (-(Complex.I * ↑((-u) * k))) * (contourCharFun μ (↑(-u) - ↑(α + 1) * Complex.I) * (cmDenom α (-u))⁻¹)
      = conj (Complex.exp (-(Complex.I * ↑(u * k)))) * (conj (contourCharFun μ (↑u - ↑(α + 1) * Complex.I)) * (conj (cmDenom α u))⁻¹) := by
          rw [h_exp, h_char, h_denom]
    _ = conj (Complex.exp (-(Complex.I * ↑(u * k))) * (contourCharFun μ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹)) := by
          simp only [map_mul, map_inv₀]

theorem carrMadan_im_eq_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {S K r tau α : ℝ} (hS : 0 < S) (hK : 0 < K) (hα : 0 < α) {c D Y u₀ δ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) (hδ : 0 < δ)
    (hcont : Continuous fun u : ℝ => contourCharFun μ (↑u - ↑(α + 1) * Complex.I))
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| → ‖contourCharFun μ (↑u - ↑(α + 1) * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (hTail : Integrable (fun x : ℝ => Real.exp ((α + 1 + δ) * x)) μ)
    (hX : Integrable (fun x : ℝ => S * Real.exp x) μ) :
    (↑(Real.exp (-α * Real.log (K / S))) * cmPriceIntegral (contourCharFun μ) α r tau S (Real.log (K / S))).im = 0 := by
  have h_eq := carrMadan_eq_modelFreeCall (μ := μ) (r := r) (tau := tau) hS hK hα hc hD hY hδ hcont hdecay hTail hX
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
  have h_eq := carrMadan_eq_modelFreeCall (μ := μ) (r := r) (tau := tau) hS hK hα hc hD hY hδ hcont hdecay hTail hX
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
  have h_eq := carrMadan_eq_modelFreeCall (μ := μ) (r := r) (tau := tau) hS hK hα hc hD hY hδ hcont hdecay hTail hX
  rw [h_eq, Complex.ofReal_re]

/-- Every real exponential moment of a nondegenerate Gaussian law is finite:
`N(m, v)` is the affine image of `N(0,1)`, where the moment is `e^{cm}` times
the standard-normal moment `e^{c²v/2}` (the repository's `integral_exp_mul_phi`). -/
theorem gaussianReal_exp_moment {m : ℝ} {v : NNReal} (hv : v ≠ 0) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (c * x))
      (ProbabilityTheory.gaussianReal m v) := by
  have hvpos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hv)
  -- N(m, v) is the law of m + √v · Z for Z ~ N(0,1)
  have hmap : ProbabilityTheory.gaussianReal m v
      = (ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => m + Real.sqrt (v : ℝ) * z) := by
    have h1 : ((ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (v : ℝ) * z)).map
        (fun x : ℝ => m + x)
      = (ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => m + Real.sqrt (v : ℝ) * z) := by
      rw [MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [h1, ProbabilityTheory.gaussianReal_map_const_mul,
      ProbabilityTheory.gaussianReal_map_const_add, zero_add]
    exact congrArg (ProbabilityTheory.gaussianReal m) (by
      apply NNReal.eq
      rw [NNReal.coe_mk, NNReal.coe_one, mul_one, Real.sq_sqrt (NNReal.coe_nonneg v)])
  -- the pulled-back function is integrable against N(0,1), by the φ-bridge
  have hemb : MeasurableEmbedding (fun z : ℝ => m + Real.sqrt (v : ℝ) * z) :=
    ((Homeomorph.smulOfNeZero (Real.sqrt (v : ℝ)) hvpos.ne').trans
      (Homeomorph.addLeft m)).measurableEmbedding
  have hcomp : Integrable
      (fun z : ℝ => Real.exp (c * (m + Real.sqrt (v : ℝ) * z)))
      (ProbabilityTheory.gaussianReal 0 1) := by
    rw [integrable_gaussianReal_iff]
    refine ((integrable_exp_mul_phi (c * Real.sqrt (v : ℝ))).const_mul
      (Real.exp (c * m))).congr (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [hmap, hemb.integrable_map_iff]
  rw [show (fun x : ℝ => Real.exp (c * x) ∘ fun z : ℝ => m + Real.sqrt (v : ℝ) * z) =
      fun z : ℝ => Real.exp (c * (m + Real.sqrt (v : ℝ) * z)) from rfl]
  exact hcomp

theorem gbm_carrMadan_eq_bsCall {S K tau r q sigma : ℝ}
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (α : ℝ) (hα : 0 < α) :
    (↑(Real.exp (-α * Real.log (K / S))) : ℂ) *
      cmPriceIntegral (contourCharFun (ProbabilityTheory.gaussianReal ((r - q - sigma ^ 2 / 2) * tau) v))
        α r tau S (Real.log (K / S)) = ↑(bsCall S K tau r q sigma) := by
  -- the law's parameters
  set m : ℝ := (r - q - sigma ^ 2 / 2) * tau with hm_def
  set s : ℝ := (v : ℝ) / 2 with hs_def
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz] at hv
    have hpos : (0:ℝ) < sigma ^ 2 * tau := by positivity
    exact absurd hv.symm (ne_of_gt hpos)
  have hspos : 0 < s := by rw [hs_def, hv]; positivity
  -- (H-tail) and (H-moment) at the lognormal law
  have hTail : Integrable (fun x : ℝ => Real.exp ((α + 2) * x))
      (ProbabilityTheory.gaussianReal m v) := gaussianReal_exp_moment hvne (α + 2)
  obtain ⟨hMom, _⟩ := exp_moments_of_exp_tail (b := α + 1) (c := α + 2) (by linarith) hTail
  -- (H-decay) on the pricing line: the GBM factor's exact Gaussian decay
  have hcont : Continuous fun u : ℝ =>
      contourCharFun (ProbabilityTheory.gaussianReal m v) (↑u - ↑(α + 1) * Complex.I) := by
    have hfun : (fun u : ℝ => contourCharFun (ProbabilityTheory.gaussianReal m v)
          (↑u - ↑(α + 1) * Complex.I)) =
        (fun u : ℝ => gbmCharFactor m s (↑u - ↑(α + 1) * Complex.I)) := by
      funext u; exact gbm_contourCharFun_eq
    rw [hfun]
    exact gbmCharFactor_pricing_continuous m s α
  have hdecay : ∀ u : ℝ, 0 ≤ |u| →
      ‖contourCharFun (ProbabilityTheory.gaussianReal m v) (↑u - ↑(α + 1) * Complex.I)‖ ≤
        Real.exp (s * (α + 1) ^ 2 + (α + 1) * m) * Real.exp (-s * |u| ^ 2) := by
    intro u _
    rw [gbm_contourCharFun_eq, gbmCharFactor_pricing_norm, Real.rpow_two, sq_abs, neg_mul]
  -- the spot map is integrable (the S e^x moment at level 1)
  have hX : Integrable (fun x : ℝ => S * Real.exp x)
      (ProbabilityTheory.gaussianReal m v) :=
    ((gaussianReal_exp_moment hvne 1).const_mul (Real.exp (Real.log S))).congr
      (Filter.Eventually.of_forall (fun x => by rw [Real.exp_log hS]))
  refine Eq.trans ?_ (congrArg Complex.ofReal
    (bsCall_eq_lognormal_expectation S K tau r q sigma hS hK htau hsigma v hv).symm)
  exact carrMadan_eq_modelFreeCall (μ := ProbabilityTheory.gaussianReal m v)
    (S := S) (K := K) (r := r) (tau := tau) (α := α)
    (c := s) (D := Real.exp (s * (α + 1) ^ 2 + (α + 1) * m)) (Y := 2) (u₀ := 0) (δ := 1)
    hS hK hα hspos (Real.exp_pos _).le (by norm_num) one_pos hcont hdecay hTail hMom hX

end BSM
