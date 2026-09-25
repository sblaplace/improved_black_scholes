/-
  ImprovedBS/VGLaw.lean — BRIEF_018: the variance-gamma law, the family's `Y = 0`
  member, as the tree's first CGMY-family probability measure.

  What this file proves, in one line:

    the difference of the two Gamma laws `Gamma(Cτ, M)` and `Gamma(Cτ, G)` is a
    probability measure whose mgf on the landed strip `−G < u < M` is
    `exp(τ · κ₀(u))` with `κ₀(u) = C[log(M/(M−u)) + log(G/(G+u))]`, that
    cumulant is the `Y ↓ 0` corner of the landed `cgmyCumulant` (a one-sided
    limit, never an evaluation), and the Esscher tilt of the law at the drift
    solution is a martingale law at which BRIEF_009's parity and bounds
    instantiate.

  Three laws, and only one of them is proved here (BRIEF_018 F3). At the same
  `(C, G, M)`:

    (a) `vgLaw` — the untilted corner member. Not a martingale law:
        `κ₀(1) = C[log(M/(M−1)) + log(G/(G+1))]` is the mean-rate, equal to
        `−ω` of the VG parameterization;
    (b) the published martingale law BRIEF_016 prices at — (a) translated by
        `(r − q − κ₀(1))τ`. Not constructed here; Stage 1 prices nothing;
    (c) `vgTilt` — the exponential tilt of (a) at `θ` solving
        `vgDriftMap θ = r − q`. This is the tree's Esscher measure, a family
        member at the shifted rates `(G+θ, M−θ)`, and the only law at which
        items 3 and 5 land.

  Nothing in this module evaluates the family at `Y = 0`. `Real.Gamma 0 = 0`,
  so `cgmyExponent C G M 0 v` is silently the Dirac law, not an error; the
  corner is a `Tendsto` on `𝓝[>] 0`. The general-`Y` law (Stage 2) and the
  complex-rate Γ integral (G1) stay out of scope.
-/
import Mathlib
import ImprovedBS.Esscher
import ImprovedBS.Skeleton

noncomputable section

namespace BSM

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal

/-! ## §1 the law -/

/-- The variance-gamma law: the pushforward of the product of the two Gamma
laws `Gamma(Cτ, M)` (positive side) and `Gamma(Cτ, G)` (negative side) under
`p ↦ p.1 − p.2`. Built from mathlib's `gammaMeasure` — no hand-rolled density.
`M` tempers the positive side, which is why `1 < M` is the numéraire condition
and `−G` is not. -/
noncomputable def vgLaw (C G M τ : ℝ) : Measure ℝ :=
  ((gammaMeasure (C * τ) M).prod (gammaMeasure (C * τ) G)).map
    (fun p : ℝ × ℝ => p.1 - p.2)

/-- The `Y = 0` real cumulant `κ₀(u) = C[log(M/(M−u)) + log(G/(G+u))]`, the
difference of the two Gamma cumulants. A separate definition: `cgmyCumulant` at
`Y = 0` is `Γ(0)·0`, not this. -/
noncomputable def vgCumulant (C G M u : ℝ) : ℝ :=
  C * (Real.log (M / (M - u)) + Real.log (G / (G + u)))

/-- The drift the tilt at `θ` delivers: `g(θ) = κ₀(θ+1) − κ₀(θ)`, the `Y = 0`
value of `esscherDriftMap`. -/
noncomputable def vgDriftMap (C G M θ : ℝ) : ℝ :=
  vgCumulant C G M (θ + 1) - vgCumulant C G M θ

/-- The complex corner target `ψ₀(v) = C[log(M/(M−iv)) + log(G/(G+iv))]`, the
Lean-side definition of the oracle's `cgmy_zeroth_exponent`. The same pairing
as `cgmyExponent`: `M` with `M − iv`, `G` with `G + iv`. -/
noncomputable def vgCornerExponent (C G M : ℝ) (v : ℂ) : ℂ :=
  (C : ℂ) * (Complex.log ((M : ℂ) / ((M : ℂ) - Complex.I * v))
    + Complex.log ((G : ℂ) / ((G : ℂ) + Complex.I * v)))

/-- The Esscher tilt of `vgLaw` at `θ`: `withDensity` of `exp(θx)` over the
law's own mgf at `θ`. Definitionally `Measure.tilted` of `x ↦ θx`, which is
what the probability and mgf proofs consume; the body stays the density the
`[VGLaw]` check reads. -/
noncomputable def vgTilt (C G M τ θ : ℝ) : Measure ℝ :=
  (vgLaw C G M τ).withDensity
    (fun x => ENNReal.ofReal (Real.exp (θ * x) / mgf id (vgLaw C G M τ) θ))

/-! ## §2 the Gamma rung -/

theorem gammaMeasure_mgf (a r u : ℝ) (ha : 0 < a) (hr : 0 < r) (hu : u < r) :
    mgf id (gammaMeasure a r) u = (r / (r - u)) ^ a := by
  have hρ : 0 < r - u := sub_pos.mpr hu
  let ρ := r - u
  have hmeas : Measurable (gammaPDF a r) :=
    ENNReal.continuous_ofReal.measurable.comp (measurable_gammaPDFReal a r)
  have hlt : ∀ x, gammaPDF a r x < ⊤ := by
    intro x
    simp [gammaPDF]
  unfold mgf
  simp only [id_eq]
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ hlt)]
  simp_rw [smul_eq_mul, gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  have hae : (fun x => gammaPDFReal a r x * Real.exp (u * x)) =ᵐ[volume]
      (Ioi 0).indicator (fun x =>
        (r ^ a / Real.Gamma a) * (x ^ (a - 1) * Real.exp (-(ρ * x)))) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ (by simp : volume ({(0 : ℝ)} : Set ℝ) = 0)
    intro x hx
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · exfalso
      apply hx
      simp [gammaPDFReal, not_le.mpr hlt, indicator, mem_Ioi, not_lt.mpr hlt.le]
    · rfl
    · exfalso
      apply hx
      have hx0 : 0 ≤ x := hgt.le
      simp only [gammaPDFReal, if_pos hx0, indicator, mem_Ioi, if_pos hgt]
      have hexp : Real.exp (-(r * x)) * Real.exp (u * x) = Real.exp (-(ρ * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * Real.exp (u * x)
          = r ^ a / Real.Gamma a * x ^ (a - 1) *
              (Real.exp (-(r * x)) * Real.exp (u * x)) := by ring
        _ = r ^ a / Real.Gamma a * (x ^ (a - 1) * Real.exp (-(ρ * x))) := by rw [hexp]; ring
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioi, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hρ]
  have hGne : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  open Real in
  calc r ^ a / Gamma a * ((1 / (r - u)) ^ a * Gamma a)
      = r ^ a * ((1 / (r - u)) ^ a * Gamma a) / Gamma a := by rw [div_mul_eq_mul_div]
    _ = r ^ a * (1 / (r - u)) ^ a := by
        rw [← mul_assoc, mul_div_cancel_right₀ _ hGne]
    _ = r ^ a * (1 ^ a / (r - u) ^ a) := by rw [div_rpow zero_le_one hρ.le]
    _ = r ^ a * (1 / (r - u) ^ a) := by rw [one_rpow]
    _ = r ^ a / (r - u) ^ a := by rw [mul_one_div]
    _ = (r / (r - u)) ^ a := by rw [← div_rpow hr.le hρ.le]

/-- `exp(u·)` is integrable against `gammaMeasure a r` for `u < r`. The mgf
just computed is positive, and `mgf` is zero when the exponential is not
integrable, so positivity is integrability. -/
theorem gammaMeasure_exp_integrable (a r u : ℝ) (ha : 0 < a) (hr : 0 < r) (hu : u < r) :
    Integrable (fun x => Real.exp (u * x)) (gammaMeasure a r) := by
  haveI : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  have hpos : 0 < mgf id (gammaMeasure a r) u := by
    rw [gammaMeasure_mgf a r u ha hr hu]
    positivity
  exact mgf_pos_iff.mp hpos

/-! ## §3 the law -/

/-- A product of probability measures, pushed forward, is a probability
measure. Both Gamma laws are one by `isProbabilityMeasure_gammaMeasure`. -/
theorem vgLaw_isProbabilityMeasure (C G M τ : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G)
    (hM : 0 < M) : IsProbabilityMeasure (vgLaw C G M τ) := by
  rw [vgLaw]
  haveI : IsProbabilityMeasure (gammaMeasure (C * τ) M) :=
    isProbabilityMeasure_gammaMeasure (mul_pos hC hτ) hM
  haveI : IsProbabilityMeasure (gammaMeasure (C * τ) G) :=
    isProbabilityMeasure_gammaMeasure (mul_pos hC hτ) hG
  haveI : SFinite (gammaMeasure (C * τ) G) := by rw [gammaMeasure]; infer_instance
  infer_instance

/-- `exp(u·)` is integrable against `vgLaw` on the open strip `−G < u < M`:
the map reduces it to a product of the two Gamma integrabilities, at `u` and
at `−u`. -/
theorem vgLaw_exp_integrable (C G M τ u : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G)
    (hM : 0 < M) (h₁ : -G < u) (h₂ : u < M) :
    Integrable (fun x => Real.exp (u * x)) (vgLaw C G M τ) := by
  have hCτ : 0 < C * τ := mul_pos hC hτ
  have hmap : AEMeasurable (fun p : ℝ × ℝ => p.1 - p.2)
      ((gammaMeasure (C * τ) M).prod (gammaMeasure (C * τ) G)) :=
    (measurable_fst.sub measurable_snd).aemeasurable
  rw [vgLaw, integrable_map_measure
    ((measurable_const_mul u).exp.aestronglyMeasurable) hmap]
  simp only [Function.comp_def]
  have hfun : (fun p : ℝ × ℝ => Real.exp (u * (p.1 - p.2))) =
      fun p => Real.exp (u * p.1) * Real.exp (-u * p.2) := by
    ext p
    rw [← Real.exp_add, neg_mul]
    ring
  rw [hfun]
  haveI : SFinite (gammaMeasure (C * τ) M) := by rw [gammaMeasure]; infer_instance
  haveI : SFinite (gammaMeasure (C * τ) G) := by rw [gammaMeasure]; infer_instance
  exact (gammaMeasure_exp_integrable (C * τ) M u hCτ hM h₂).mul_prod
    (gammaMeasure_exp_integrable (C * τ) G (-u) hCτ hG (by linarith))

/-- The law's mgf on the strip is `exp(τ · κ₀(u))`. `mgf_id_map` pulls the
difference back to the product, `integral_prod_mul` splits it into the two
Gamma mgfs at `u` and `−u`, and `rpow_def_of_pos` reassembles the product of
powers as the exponential of the cumulant. -/
theorem vgLaw_mgf (C G M τ u : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G) (hM : 0 < M)
    (h₁ : -G < u) (h₂ : u < M) :
    mgf id (vgLaw C G M τ) u = Real.exp (τ * vgCumulant C G M u) := by
  have hCτ : 0 < C * τ := mul_pos hC hτ
  have hmap : AEMeasurable (fun p : ℝ × ℝ => p.1 - p.2)
      ((gammaMeasure (C * τ) M).prod (gammaMeasure (C * τ) G)) :=
    (measurable_fst.sub measurable_snd).aemeasurable
  rw [vgLaw, mgf_id_map hmap]
  have hfun : (fun p : ℝ × ℝ => Real.exp (u * (p.1 - p.2))) =
      fun p => Real.exp (u * p.1) * Real.exp (-u * p.2) := by
    ext p
    rw [← Real.exp_add, neg_mul]
    ring
  unfold mgf
  haveI : SFinite (gammaMeasure (C * τ) M) := by rw [gammaMeasure]; infer_instance
  haveI : SFinite (gammaMeasure (C * τ) G) := by rw [gammaMeasure]; infer_instance
  have hsplit := integral_prod_mul (μ := gammaMeasure (C * τ) M) (ν := gammaMeasure (C * τ) G)
    (fun x => Real.exp (u * x)) (fun y => Real.exp (-u * y))
  rw [hfun]
  refine hsplit.trans ?_
  have h1 := gammaMeasure_mgf (C * τ) M u hCτ hM h₂
  have h2 := gammaMeasure_mgf (C * τ) G (-u) hCτ hG (by linarith)
  unfold mgf at h1 h2
  simp only [id_eq] at h1 h2
  rw [h1, h2, sub_neg_eq_add]
  have hpos1 : 0 < M / (M - u) := div_pos hM (by linarith)
  have hpos2 : 0 < G / (G + u) := div_pos hG (by linarith)
  rw [Real.rpow_def_of_pos hpos1 (C * τ), Real.rpow_def_of_pos hpos2 (C * τ), ← Real.exp_add]
  congr 1
  unfold vgCumulant
  ring

/-- The cumulant-generating function is `τ · κ₀` — `log` of the mgf, which is
an exponential. -/
theorem vgLaw_cgf (C G M τ u : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G) (hM : 0 < M)
    (h₁ : -G < u) (h₂ : u < M) :
    cgf id (vgLaw C G M τ) u = τ * vgCumulant C G M u := by
  rw [cgf, vgLaw_mgf C G M τ u hC hτ hG hM h₁ h₂, Real.log_exp]

/-- The mgf at the numéraire point `u = 1`, the special case the drift identity
consumes. `1 < M` puts `1` inside the strip; `−G < 1` is free from `0 < G`. -/
theorem vgLaw_mgf_one (C G M τ : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G) (h₁ : 1 < M) :
    mgf id (vgLaw C G M τ) 1 = Real.exp (τ * vgCumulant C G M 1) :=
  vgLaw_mgf C G M τ 1 hC hτ hG (by linarith) (by linarith) h₁

/-- The derivative of `κ₀` on the open strip:
`κ₀'(u) = C(1/(M−u) − 1/(G+u))`. Both logarithms are differentiable because
both bases stay positive. -/
theorem vgCumulant_hasDerivAt (C G M u : ℝ) (hG : 0 < G) (hM : 0 < M) (h₁ : -G < u)
    (h₂ : u < M) :
    HasDerivAt (vgCumulant C G M) (C * (1 / (M - u) - 1 / (G + u))) u := by
  unfold vgCumulant
  have hMu : M - u ≠ 0 := by linarith
  have hGu : G + u ≠ 0 := by linarith
  have hMpos : 0 < M / (M - u) := div_pos hM (by linarith)
  have hGpos : 0 < G / (G + u) := div_pos hG (by linarith)
  have hdSub : HasDerivAt (fun x => M - x) (-1) u := by
    convert ((hasDerivAt_const u M).sub (hasDerivAt_id u)) using 1
    · ext x
      simp [id]
    · norm_num
  have hdAdd : HasDerivAt (fun x => G + x) 1 u := by
    convert ((hasDerivAt_const u G).add (hasDerivAt_id u)) using 1
    · ext x
      simp [id]
    · norm_num
  have hdDivM : HasDerivAt (fun x => M / (M - x)) (M / (M - u) ^ 2) u := by
    convert ((hasDerivAt_const u M).div hdSub hMu) using 1
    · ring_nf
  have hdDivG : HasDerivAt (fun x => G / (G + x)) (-G / (G + u) ^ 2) u := by
    convert ((hasDerivAt_const u G).div hdAdd hGu) using 1
    · ring_nf
  have hdLogM : HasDerivAt (fun x => Real.log (M / (M - x))) (1 / (M - u)) u := by
    open Real in
    convert hdDivM.log hMpos.ne' using 1
    field_simp
    ring
  have hdLogG : HasDerivAt (fun x => Real.log (G / (G + x))) (-(1 / (G + u))) u := by
    open Real in
    convert hdDivG.log hGpos.ne' using 1
    field_simp
    ring
  convert (hdLogM.add hdLogG).const_mul C using 1 <;> ring

/-! ## §4 the corner, as a limit -/

/-- `κ₀(u)` is the real part of the complex corner at `v = −iu`. The bases
collapse to the positive reals `M − u` and `G + u`, whose complex log is the
real log. -/
theorem vgCumulant_eq_corner_re (C G M u : ℝ) (hG : 0 < G) (hM : 0 < M) (h₁ : -G < u)
    (h₂ : u < M) :
    vgCumulant C G M u = (vgCornerExponent C G M (-(u : ℂ) * Complex.I)).re := by
  have hMu : 0 < M - u := by linarith
  have hGu : 0 < G + u := by linarith
  unfold vgCumulant vgCornerExponent
  have hbaseM : (M : ℂ) - Complex.I * (-(u : ℂ) * Complex.I) = (M - u : ℝ) := by
    rw [mul_left_comm Complex.I (-(u : ℂ)) Complex.I, Complex.I_mul_I, mul_neg_one, neg_neg,
      ← Complex.ofReal_sub]
  have hbaseG : (G : ℂ) + Complex.I * (-(u : ℂ) * Complex.I) = (G + u : ℝ) := by
    rw [mul_left_comm Complex.I (-(u : ℂ)) Complex.I, Complex.I_mul_I, mul_neg_one, neg_neg,
      ← Complex.ofReal_add]
  rw [hbaseM, hbaseG, ← Complex.ofReal_div M (M - u), ← Complex.ofReal_div G (G + u),
    ← Complex.ofReal_log (div_pos hM hMu).le, ← Complex.ofReal_log (div_pos hG hGu).le]
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.ofReal_im]
  ring

/-- The corner of the exponent: `ψ_Y(v) → ψ₀(v)` as `Y ↓ 0`, for every `v` in
the strip `−M < Im v < G`. The strip is what keeps both `cpow` bases in the
open right half-plane, so off zero and off the branch cut; the one-sided filter
is the point — the two-sided limit does not exist, and an evaluation at
`Y = 0` is the Dirac trap. The Γ pole cancels through two `Real.Gamma_add_one`
steps, `Γ(−Y) = −Γ(2−Y)/(Y(1−Y))`, and the bracket's slope is
`HasDerivAt.tendsto_slope_zero_right` on `Y ↦ exp(Y · log z)`. -/
theorem vg_corner (C G M : ℝ) (v : ℂ) (hG : 0 < G) (hM : 0 < M) (hv₁ : -M < v.im)
    (hv₂ : v.im < G) :
    Tendsto (fun Y => cgmyExponent C G M Y v) (𝓝[>] (0 : ℝ))
      (𝓝 (vgCornerExponent C G M v)) := by
  set z : ℂ := (M : ℂ) - Complex.I * v
  set w : ℂ := (G : ℂ) + Complex.I * v
  have hreZ : z.re = M + v.im := by
    simp [z, Complex.sub_re, Complex.mul_re]
  have hreW : w.re = G - v.im := by
    simp [w, Complex.add_re, Complex.mul_re]
    ring
  have hzre : 0 < z.re := by linarith
  have hwre : 0 < w.re := by linarith
  have hz : z ≠ 0 := by
    intro h
    have : z.re = 0 := by rw [h]; simp
    linarith
  have hw : w ≠ 0 := by
    intro h
    have : w.re = 0 := by rw [h]; simp
    linarith
  have hMz : (M : ℂ) ≠ 0 := by
    intro h
    have : ((M : ℂ).re) = 0 := by rw [h]; simp
    simp at this
    linarith
  have hGz : (G : ℂ) ≠ 0 := by
    intro h
    have : ((G : ℂ).re) = 0 := by rw [h]; simp
    simp at this
    linarith
  have harg (c : ℂ) (hc : 0 < c.re) : c.arg ≠ Real.pi := by
    have habs := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hc)
    intro h
    rw [h, abs_of_pos Real.pi_pos] at habs
    linarith [Real.pi_pos]
  -- (z^t − 1)/t → log z, from the exponential of the linear function
  have hslope (c : ℂ) (hc : c ≠ 0) :
      Tendsto (fun t : ℝ => (t : ℂ)⁻¹ * (c ^ (t : ℂ) - 1)) (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.log c)) := by
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.log c) (Complex.log c) 0 := by
      convert hid.mul_const (Complex.log c) using 1
      ring
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.log c))
        (Complex.log c) 0 := by
      convert hlin.cexp using 1
      simp
    refine Filter.Tendsto.congr' ?_ hexp.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [zero_add]
    rw [Complex.real_smul, Complex.ofReal_inv t, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_comm (t : ℂ) (Complex.log c), ← Complex.cpow_def_of_ne_zero hc]
  have hdiff (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0) :
      Tendsto (fun t : ℝ => (t : ℂ)⁻¹ * (c ^ (t : ℂ) - d ^ (t : ℂ))) (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.log c - Complex.log d)) := by
    refine Filter.Tendsto.congr' ?_ ((hslope c hc).sub (hslope d hd))
    filter_upwards with t
    ring
  have hbr : Tendsto (fun Y : ℝ => (Y : ℂ)⁻¹ *
      (z ^ (Y : ℂ) - (M : ℂ) ^ (Y : ℂ) + (w ^ (Y : ℂ) - (G : ℂ) ^ (Y : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.log z - Complex.log (M : ℂ) + (Complex.log w - Complex.log (G : ℂ)))) := by
    refine Filter.Tendsto.congr' ?_ ((hdiff z (M : ℂ) hz hMz).add (hdiff w (G : ℂ) hw hGz))
    filter_upwards with Y
    ring
  -- Γ(−Y) = −Γ(2−Y)/(Y(1−Y)) on (0, 1), and the prefactor tends to −1
  have hΓ2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0),
      Real.Gamma_one]
    norm_num
  have hΓcont : ContinuousAt (fun Y : ℝ => Real.Gamma (2 - Y)) 0 := by
    have hne : ∀ m : ℕ, (2 : ℝ) ≠ -(m : ℝ) := by
      intro m hm
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have houter : ContinuousAt Real.Gamma (2 - 0) := by
      rw [sub_zero]
      exact (Real.differentiableAt_Gamma (s := (2 : ℝ)) hne).continuousAt
    have hcomp : ContinuousAt (Real.Gamma ∘ fun Y : ℝ => 2 - Y) 0 :=
      ContinuousAt.comp houter
        ((show Continuous (fun Y : ℝ => 2 - Y) from continuous_const.sub continuous_id).continuousAt
          (x := 0))
    simpa [Function.comp_def] using hcomp
  have hΓlim : Tendsto (fun Y => Real.Gamma (2 - Y)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have htend := hΓcont.continuousWithinAt (s := Ioi (0 : ℝ)).tendsto
    simpa [sub_zero, hΓ2] using htend
  have hden : Tendsto (fun Y : ℝ => 1 - Y) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have htend :=
      ((show Continuous (fun Y : ℝ => 1 - Y) from continuous_const.sub continuous_id).continuousAt
        (x := 0)).continuousWithinAt (s := Ioi (0 : ℝ)).tendsto
    simpa using htend
  have hquot : Tendsto (fun Y => -Real.Gamma (2 - Y) / (1 - Y)) (𝓝[>] (0 : ℝ))
      (𝓝 (-1 : ℝ)) := by
    have h := hΓlim.neg.div hden (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    norm_num
  have hcoef : Tendsto
      (fun Y : ℝ => (C : ℂ) * ((-Real.Gamma (2 - Y) / (1 - Y) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(C : ℂ))) := by
    have hcast := (Complex.continuous_ofReal.tendsto (-1 : ℝ)).comp hquot
    have h := tendsto_const_nhds.mul hcast
    simp only [Function.comp_def] at h
    convert h using 1
    simp
  have hprod := hcoef.mul hbr
  have hmem : ∀ᶠ Y in 𝓝[>] (0 : ℝ), Y ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)), self_mem_nhdsWithin]
      with Y hY1 hY0
    exact ⟨hY0, hY1⟩
  have hgamma (Y : ℝ) (hY : Y ∈ Ioo (0 : ℝ) 1) :
      Real.Gamma (-Y) = -Real.Gamma (2 - Y) / (Y * (1 - Y)) := by
    have hY0 : Y ≠ 0 := ne_of_gt hY.1
    have h1Y : (1 : ℝ) - Y ≠ 0 := by linarith [hY.2]
    have hneg : -Y ≠ 0 := neg_ne_zero.mpr hY0
    have hstep1 : Real.Gamma (1 - Y) = -Y * Real.Gamma (-Y) := by
      rw [show (1 : ℝ) - Y = -Y + 1 by ring]
      exact Real.Gamma_add_one hneg
    have hstep2 : Real.Gamma (2 - Y) = (1 - Y) * Real.Gamma (1 - Y) := by
      rw [show (2 : ℝ) - Y = 1 - Y + 1 by ring]
      exact Real.Gamma_add_one h1Y
    have hprod' : Real.Gamma (-Y) * (Y * (1 - Y)) = -Real.Gamma (2 - Y) := by
      rw [hstep2, hstep1]
      ring
    rw [eq_div_iff (mul_ne_zero hY0 h1Y)]
    exact hprod'
  have hexp (Y : ℝ) (hY : Y ∈ Ioo (0 : ℝ) 1) :
      cgmyExponent C G M Y v =
        (C : ℂ) * ((-Real.Gamma (2 - Y) / (1 - Y) : ℝ) : ℂ) *
          ((Y : ℂ)⁻¹ * (z ^ (Y : ℂ) - (M : ℂ) ^ (Y : ℂ) +
            (w ^ (Y : ℂ) - (G : ℂ) ^ (Y : ℂ)))) := by
    unfold cgmyExponent
    have hcast : ((Real.Gamma (-Y) : ℝ) : ℂ) =
        ((-Real.Gamma (2 - Y) / (1 - Y) : ℝ) : ℂ) * (Y : ℂ)⁻¹ := by
      rw [hgamma Y hY]
      have hreal : -Real.Gamma (2 - Y) / (Y * (1 - Y)) =
          (-Real.Gamma (2 - Y) / (1 - Y)) * Y⁻¹ := by
        field_simp [ne_of_gt hY.1, show (1 : ℝ) - Y ≠ 0 by linarith [hY.2]]
      rw [hreal]
      push_cast
      ring
    have hC : ((C * Real.Gamma (-Y) : ℝ) : ℂ) = (C : ℂ) * ((Real.Gamma (-Y) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast]
    simp only [z, w]
    ring
  have hmain : Tendsto (fun Y => cgmyExponent C G M Y v) (𝓝[>] (0 : ℝ))
      (𝓝 (-(C : ℂ) * (Complex.log z - Complex.log (M : ℂ) +
        (Complex.log w - Complex.log (G : ℂ))))) := by
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards [hmem] with Y hY
    exact (hexp Y hY).symm
  have hlog (c : ℂ) (hc : c ≠ 0) (hcre : 0 < c.re) (b : ℝ) (hb : 0 < b) :
      Complex.log ((b : ℂ) / c) = -(Complex.log c - Complex.log (b : ℂ)) := by
    rw [div_eq_mul_inv, Complex.log_ofReal_mul hb (inv_ne_zero hc),
      Complex.log_inv c (harg c hcre), ← Complex.ofReal_log hb.le]
    ring
  have htarget : vgCornerExponent C G M v =
      -(C : ℂ) * (Complex.log z - Complex.log (M : ℂ) +
        (Complex.log w - Complex.log (G : ℂ))) := by
    unfold vgCornerExponent
    rw [show (M : ℂ) - Complex.I * v = z by rfl, show (G : ℂ) + Complex.I * v = w by rfl,
      hlog z hz hzre M hM, hlog w hw hwre G hG]
    ring
  rwa [htarget]

/-- The corner of the cumulant: `κ_Y(u) → κ₀(u)` as `Y ↓ 0`, on the strip.
The real section of `vg_corner` at `v = −iu`, cited from
`cgmyCumulant_eq_strip` rather than re-proved. -/
theorem vg_corner_cumulant (C G M u : ℝ) (hG : 0 < G) (hM : 0 < M) (h₁ : -G < u) (h₂ : u < M) :
    Tendsto (fun Y => cgmyCumulant C G M Y u) (𝓝[>] (0 : ℝ)) (𝓝 (vgCumulant C G M u)) := by
  have him : (-(u : ℂ) * Complex.I).im = -u := by
    simp [Complex.mul_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hv₁ : -M < (-(u : ℂ) * Complex.I).im := by
    rw [him]
    linarith
  have hv₂ : (-(u : ℂ) * Complex.I).im < G := by
    rw [him]
    linarith
  have hcorner := vg_corner C G M (-(u : ℂ) * Complex.I) hG hM hv₁ hv₂
  have hcomm : -(Complex.I * (u : ℂ)) = -(u : ℂ) * Complex.I := by ring
  have heq : ∀ Y, cgmyCumulant C G M Y u =
      (cgmyExponent C G M Y (-(u : ℂ) * Complex.I)).re := by
    intro Y
    rw [← hcomm, cgmyCumulant_eq_strip C G M Y u hG hM h₁ h₂]
    simp
  have hre : Tendsto (fun Y => (cgmyExponent C G M Y (-(u : ℂ) * Complex.I)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (vgCornerExponent C G M (-(u : ℂ) * Complex.I)).re) :=
    (Complex.continuous_re.tendsto
      (vgCornerExponent C G M (-(u : ℂ) * Complex.I))).comp hcorner
  rw [← vgCumulant_eq_corner_re C G M u hG hM h₁ h₂] at hre
  exact Filter.Tendsto.congr' (by filter_upwards with Y; exact (heq Y).symm) hre

/-! ## §5 the tilt -/

/-- `vgTilt` is definitionally the exponential tilt, so the shipped
`isProbabilityMeasure_tilted` applies once `exp(θ·)` is integrable — which the
admissible interval `θ ∈ (−G, M−1)` puts inside the strip. -/
theorem vgTilt_isProbabilityMeasure (C G M τ θ : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G)
    (hM : 0 < M) (hθ : θ ∈ Ioo (-G) (M - 1)) :
    IsProbabilityMeasure (vgTilt C G M τ θ) := by
  haveI : IsProbabilityMeasure (vgLaw C G M τ) :=
    vgLaw_isProbabilityMeasure C G M τ hC hτ hG hM
  have hint : Integrable (fun x => Real.exp (θ * x)) (vgLaw C G M τ) :=
    vgLaw_exp_integrable C G M τ θ hC hτ hG hM hθ.1 (by linarith [hθ.2])
  have heq : vgTilt C G M τ θ = (vgLaw C G M τ).tilted (fun x => θ * x) := by
    unfold vgTilt Measure.tilted mgf
    simp only [id_eq]
  rw [heq]
  exact isProbabilityMeasure_tilted hint

/-- The numéraire condition after the tilt is a conclusion, cited from
BRIEF_013 — `θ ∈ (−G, M−1)` already says `θ + 1 < M`. Never a hypothesis. -/
theorem vg_tilt_numeraire (G M θ : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1)) : 1 < M - θ :=
  esscher_tilted_numeraire G M θ hθ

/-- The tilted mgf is the untilted mgf's ratio `M(u+θ)/M(θ)`, by
`integral_exp_tilted` — the density `exp(θx) / mgf(θ)` multiplies the
integrand `exp(ux)` into `exp((u+θ)x)`. -/
theorem vg_tilt_mgf (C G M τ θ u : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G) (hM : 0 < M)
    (hθ : θ ∈ Ioo (-G) (M - 1)) (hu₁ : -(G + θ) < u) (hu₂ : u < M - θ) :
    mgf id (vgTilt C G M τ θ) u =
      mgf id (vgLaw C G M τ) (u + θ) / mgf id (vgLaw C G M τ) θ := by
  have heq : vgTilt C G M τ θ = (vgLaw C G M τ).tilted (fun x => θ * x) := by
    unfold vgTilt Measure.tilted mgf
    simp only [id_eq]
  rw [heq]
  simp only [mgf, id_eq]
  rw [integral_exp_tilted (fun x => θ * x) (fun x => u * x)]
  refine congrArg (fun t => t / ∫ x, Real.exp (θ * x) ∂(vgLaw C G M τ)) ?_
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

/-- The tilted cumulant is the family cumulant at the shifted rates
`(G+θ, M−θ)`: three logarithm rewrites, the law-level image of
`esscher_cgmy_shift`. -/
theorem vg_tilt_cumulant_shift (C G M θ u : ℝ) (hG : 0 < G) (hM : 0 < M) (hθlo : -G < θ)
    (hθhi : θ < M) (hu₁ : -(G + θ) < u) (hu₂ : u < M - θ) :
    vgCumulant C G M (u + θ) - vgCumulant C G M θ = vgCumulant C (G + θ) (M - θ) u := by
  have hM0 : M ≠ 0 := hM.ne'
  have hG0 : G ≠ 0 := hG.ne'
  have hMθ : M - θ ≠ 0 := by linarith
  have hGθ : G + θ ≠ 0 := by linarith
  have hMu : M - (u + θ) ≠ 0 := by linarith
  have hGu : G + (u + θ) ≠ 0 := by linarith
  have hMθu : M - θ - u ≠ 0 := by linarith
  have hGθu : G + θ + u ≠ 0 := by linarith
  unfold vgCumulant
  have hMstep : Real.log (M / (M - (u + θ))) - Real.log (M / (M - θ)) =
      Real.log ((M - θ) / (M - θ - u)) := by
    rw [Real.log_div hM0 hMu, Real.log_div hM0 hMθ]
    have hrearr : Real.log M - Real.log (M - (u + θ)) - (Real.log M - Real.log (M - θ)) =
        Real.log (M - θ) - Real.log (M - θ - u) := by
      rw [show M - (u + θ) = M - θ - u by ring]
      ring
    rw [hrearr, ← Real.log_div hMθ hMθu]
  have hGstep : Real.log (G / (G + (u + θ))) - Real.log (G / (G + θ)) =
      Real.log ((G + θ) / (G + θ + u)) := by
    rw [Real.log_div hG0 hGu, Real.log_div hG0 hGθ]
    have hrearr : Real.log G - Real.log (G + (u + θ)) - (Real.log G - Real.log (G + θ)) =
        Real.log (G + θ) - Real.log (G + θ + u) := by
      rw [show G + (u + θ) = G + θ + u by ring]
      ring
    rw [hrearr, ← Real.log_div hGθ hGθu]
  have hsum : (Real.log (M / (M - (u + θ))) + Real.log (G / (G + (u + θ)))) -
      (Real.log (M / (M - θ)) + Real.log (G / (G + θ))) =
      Real.log ((M - θ) / (M - θ - u)) + Real.log ((G + θ) / (G + θ + u)) := by
    calc (Real.log (M / (M - (u + θ))) + Real.log (G / (G + (u + θ)))) -
          (Real.log (M / (M - θ)) + Real.log (G / (G + θ)))
        = (Real.log (M / (M - (u + θ))) - Real.log (M / (M - θ))) +
          (Real.log (G / (G + (u + θ))) - Real.log (G / (G + θ))) := by ring
      _ = Real.log ((M - θ) / (M - θ - u)) + Real.log ((G + θ) / (G + θ + u)) := by
          rw [hMstep, hGstep]
  rw [← mul_sub, hsum]

/-! ## §6 items 3 and 5, at the tilted law -/

/-- **Item 3, at the law.** With `θ` solving `vgDriftMap θ = r − q`,
`∫ S · exp(x) ∂(vgTilt) = S · exp((r−q)τ)`: the left side is `S` times the
tilted mgf at `1`, the ratio of untilted mgfs is `exp(τ · g(θ))`, and the
drift equation substitutes. -/
theorem vg_drift_identity (C G M τ θ S r q : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G)
    (hM : 0 < M) (hθ : θ ∈ Ioo (-G) (M - 1)) (hdrift : vgDriftMap C G M θ = r - q) :
    ∫ x, S * Real.exp x ∂(vgTilt C G M τ θ) = S * Real.exp ((r - q) * τ) := by
  have hu₁ : -(G + θ) < (1 : ℝ) := by linarith [hθ.1, hG]
  have hu₂ : (1 : ℝ) < M - θ := vg_tilt_numeraire G M θ hθ
  have hθM : θ < M := by linarith [hθ.2]
  have hθ1 : 1 + θ < M := by linarith [hθ.2]
  have hmgf := vg_tilt_mgf C G M τ θ 1 hC hτ hG hM hθ hu₁ hu₂
  have hlaw1 := vgLaw_mgf C G M τ (1 + θ) hC hτ hG hM (by linarith [hθ.1]) hθ1
  have hlawθ := vgLaw_mgf C G M τ θ hC hτ hG hM hθ.1 hθM
  have hden : mgf id (vgLaw C G M τ) θ ≠ 0 := by
    rw [hlawθ]
    exact (Real.exp_pos _).ne'
  calc ∫ x, S * Real.exp x ∂(vgTilt C G M τ θ)
      = S * ∫ x, Real.exp x ∂(vgTilt C G M τ θ) := by rw [integral_const_mul]
    _ = S * mgf id (vgTilt C G M τ θ) 1 := by simp [mgf]
    _ = S * (mgf id (vgLaw C G M τ) (1 + θ) / mgf id (vgLaw C G M τ) θ) := by rw [hmgf]
    _ = S * (Real.exp (τ * vgCumulant C G M (1 + θ)) /
        Real.exp (τ * vgCumulant C G M θ)) := by rw [hlaw1, hlawθ, add_comm]
    _ = S * Real.exp (τ * (vgCumulant C G M (θ + 1) - vgCumulant C G M θ)) := by
        rw [← Real.exp_sub, add_comm]
        ring_nf
    _ = S * Real.exp (τ * vgDriftMap C G M θ) := by rw [vgDriftMap]
    _ = S * Real.exp ((r - q) * τ) := by rw [hdrift]; ring_nf

/-- **Item 5, the call bounds**, instantiated at the tilted law — the first
non-Gaussian law in the tree that discharges BRIEF_009's hypotheses by
construction: probability measure, integrability at `u = 1 + θ`, the drift
identity, and `0 ≤ S · exp` everywhere. -/
theorem vg_modelFree_call_bounds (C G M τ θ S K r q : ℝ) (hC : 0 < C) (hτ : 0 < τ)
    (hG : 0 < G) (hM : 0 < M) (hθ : θ ∈ Ioo (-G) (M - 1))
    (hdrift : vgDriftMap C G M θ = r - q) (hK : 0 ≤ K) (hS : 0 ≤ S) :
    max (S * Real.exp (-q * τ) - K * Real.exp (-r * τ)) 0 ≤
        modelFreeCall (vgTilt C G M τ θ) (fun x => S * Real.exp x) K r τ ∧
      modelFreeCall (vgTilt C G M τ θ) (fun x => S * Real.exp x) K r τ ≤
        S * Real.exp (-q * τ) := by
  haveI : IsProbabilityMeasure (vgTilt C G M τ θ) :=
    vgTilt_isProbabilityMeasure C G M τ θ hC hτ hG hM hθ
  have hExp : Integrable (fun x => Real.exp x) (vgTilt C G M τ θ) := by
    have heq : vgTilt C G M τ θ = (vgLaw C G M τ).tilted (fun x => θ * x) := by
      unfold vgTilt Measure.tilted mgf
      simp only [id_eq]
    have hint : Integrable (fun x => Real.exp (θ * x)) (vgLaw C G M τ) :=
      vgLaw_exp_integrable C G M τ θ hC hτ hG hM hθ.1 (by linarith [hθ.2])
    rw [heq, integrable_tilted_iff hint]
    simp_rw [smul_eq_mul, ← Real.exp_add]
    exact (vgLaw_exp_integrable C G M τ (θ + 1) hC hτ hG hM (by linarith [hθ.1])
      (by linarith [hθ.2])).congr (by filter_upwards with x; ring_nf)
  have hX : Integrable (fun x => S * Real.exp x) (vgTilt C G M τ θ) := hExp.const_mul S
  have hE := vg_drift_identity C G M τ θ S r q hC hτ hG hM hθ hdrift
  have hX0 : ∀ᵐ x ∂(vgTilt C G M τ θ), 0 ≤ S * Real.exp x :=
    Filter.Eventually.of_forall fun x => mul_nonneg hS (Real.exp_pos x).le
  exact model_free_call_bounds S K τ r q (fun x => S * Real.exp x) hX hE hK hX0

/-- **Item 5, the put bounds**, the parity corollary of the call bounds at the
same law — cited, not re-derived. -/
theorem vg_modelFree_put_bounds (C G M τ θ S K r q : ℝ) (hC : 0 < C) (hτ : 0 < τ)
    (hG : 0 < G) (hM : 0 < M) (hθ : θ ∈ Ioo (-G) (M - 1))
    (hdrift : vgDriftMap C G M θ = r - q) (hK : 0 ≤ K) (hS : 0 ≤ S) :
    max (K * Real.exp (-r * τ) - S * Real.exp (-q * τ)) 0 ≤
        modelFreePut (vgTilt C G M τ θ) (fun x => S * Real.exp x) K r τ ∧
      modelFreePut (vgTilt C G M τ θ) (fun x => S * Real.exp x) K r τ ≤
        K * Real.exp (-r * τ) := by
  haveI : IsProbabilityMeasure (vgTilt C G M τ θ) :=
    vgTilt_isProbabilityMeasure C G M τ θ hC hτ hG hM hθ
  have hExp : Integrable (fun x => Real.exp x) (vgTilt C G M τ θ) := by
    have heq : vgTilt C G M τ θ = (vgLaw C G M τ).tilted (fun x => θ * x) := by
      unfold vgTilt Measure.tilted mgf
      simp only [id_eq]
    have hint : Integrable (fun x => Real.exp (θ * x)) (vgLaw C G M τ) :=
      vgLaw_exp_integrable C G M τ θ hC hτ hG hM hθ.1 (by linarith [hθ.2])
    rw [heq, integrable_tilted_iff hint]
    simp_rw [smul_eq_mul, ← Real.exp_add]
    exact (vgLaw_exp_integrable C G M τ (θ + 1) hC hτ hG hM (by linarith [hθ.1])
      (by linarith [hθ.2])).congr (by filter_upwards with x; ring_nf)
  have hX : Integrable (fun x => S * Real.exp x) (vgTilt C G M τ θ) := hExp.const_mul S
  have hE := vg_drift_identity C G M τ θ S r q hC hτ hG hM hθ hdrift
  have hX0 : ∀ᵐ x ∂(vgTilt C G M τ θ), 0 ≤ S * Real.exp x :=
    Filter.Eventually.of_forall fun x => mul_nonneg hS (Real.exp_pos x).le
  exact model_free_put_bounds S K τ r q (fun x => S * Real.exp x) hX hE hK hX0

/-- **Item 5, parity**, instantiated at the tilted law. -/
theorem vg_modelFree_parity (C G M τ θ S K r q : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hG : 0 < G)
    (hM : 0 < M) (hθ : θ ∈ Ioo (-G) (M - 1)) (hdrift : vgDriftMap C G M θ = r - q) :
    modelFreeCall (vgTilt C G M τ θ) (fun x => S * Real.exp x) K r τ -
        modelFreePut (vgTilt C G M τ θ) (fun x => S * Real.exp x) K r τ =
      S * Real.exp (-q * τ) - K * Real.exp (-r * τ) := by
  haveI : IsProbabilityMeasure (vgTilt C G M τ θ) :=
    vgTilt_isProbabilityMeasure C G M τ θ hC hτ hG hM hθ
  have hExp : Integrable (fun x => Real.exp x) (vgTilt C G M τ θ) := by
    have heq : vgTilt C G M τ θ = (vgLaw C G M τ).tilted (fun x => θ * x) := by
      unfold vgTilt Measure.tilted mgf
      simp only [id_eq]
    have hint : Integrable (fun x => Real.exp (θ * x)) (vgLaw C G M τ) :=
      vgLaw_exp_integrable C G M τ θ hC hτ hG hM hθ.1 (by linarith [hθ.2])
    rw [heq, integrable_tilted_iff hint]
    simp_rw [smul_eq_mul, ← Real.exp_add]
    exact (vgLaw_exp_integrable C G M τ (θ + 1) hC hτ hG hM (by linarith [hθ.1])
      (by linarith [hθ.2])).congr (by filter_upwards with x; ring_nf)
  have hX : Integrable (fun x => S * Real.exp x) (vgTilt C G M τ θ) := hExp.const_mul S
  have hE := vg_drift_identity C G M τ θ S r q hC hτ hG hM hθ hdrift
  exact model_free_put_call_parity S K τ r q (fun x => S * Real.exp x) hX hE

end BSM
