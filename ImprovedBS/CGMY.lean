/-
  ImprovedBS.CGMY — BRIEF_011: BSM-2 kit items 1 and 2. The concrete CGMY
  characteristic exponent (the `cpow`/branch work BRIEF_005 deferred), its
  Levy measure, and the tempered moment strip that makes the Carr–Madan
  contour legal.

  THE EXPONENT. `cgmyExponent C G M Y v = C Γ(−Y) [(M − iv)^Y − M^Y +
  (G + iv)^Y − G^Y]`, with `M` tempering the positive half of the Levy
  measure `ν⁺(dx) = C e^{−Mx} x^{−1−Y} dx` and `G` the negative half
  (`C e^{−G|x|} |x|^{−1−Y} dx`). `cgmyCharFactor C G M Y τ = exp(τ ψ)`,
  affine in `τ` (`cgmyCharFactor_add`); `cgmyExponent_strip` evaluates
  `ψ(−iu)` for `u ∈ (−G, M)` as a REAL number (both bases become positive
  reals: `M − u` and `G + u`), which is the exponential-moment statement, and
  `cgmy_numeraire_strip` records that the numéraire point `u = 1` needs `1 < M`.

  CORRECTION C14. On the pricing contour `v = u − i(α+1)` (C12) the two cpow
  bases are `M − iv = (M − (α+1)) − iu` and `G + iv = (G + α+1) + iu`
  (`cgmyExponent_contour`), so the branch condition `Re(M − iv) > 0` is
  EXACTLY `α + 1 < M`: `G` does not constrain the pricing line at all
  (`Re(G + iv) = G + α + 1 > 0` for free). `G` binds only on the OLD line
  `v = u + iα` (the line `Fourier.lean`'s `carrMadanKernel` sits on), where
  `Re(G + iv) = G − α` can go negative (`cgmyOldContour_base_right_re`). The
  prose condition `α + 1 < min(G, M)` is merely the intersection of the two
  lines' conditions; docs/03 §D1 and docs/04's queue justified the min by
  swapping which rate tempers which half, which is what C14 corrects. The
  landed statements use `α + 1 < M` — the condition that is actually used —
  and `cgmy_contour_mem_strip` records the strip instance.

  DECAY ON THE CONTOUR. For `0 < Y < 2`, `Y ≠ 1` both bases have real part
  `≥ 0`, and the two-base real part

      Re ψ(u − i(α+1)) = C Γ(−Y) [Re((a₁ + iy)^Y) + Re((a₂ + iy)^Y) − M^Y − G^Y]

  (`y = |u|`, `a₁ = M − (α+1)`, `a₂ = G + α+1`, both `∈ [0, y]` once
  `y ≥ M + G`) is estimated in the two regimes:

  * `Y < 1`: `Re(z^Y) = ‖z‖^Y cos(arg z · Y)` and `cos` decreasing on
    `[0, π]` give the sharp `y^Y cos(πY/2) ≤ Re((a + iy)^Y)`
    (`cgmy_cpow_re_ge_of_lt_one`), with no correction term;
  * `1 ≤ Y < 2`: the mean value inequality on `t ↦ (t + iy)^Y` with
    derivative bound `‖Y (t + iy)^{Y-1}‖ ≤ Y (2y)^{Y-1}` gives
    `Re((a + iy)^Y) ≤ y^Y cos(πY/2) + 2^{Y-1} Y a y^{Y-1}`
    (`cgmy_cpow_re_le_of_one_le`).

  Both feed the single statement `cgmyExponent_contour_re_le`

      Re ψ(u − i(α+1)) ≤ −r |u|^Y + c' |u|^{Y−1} + K₀          (`|u| ≥ M + G`),

  with `r = 2 C |Γ(−Y) cos(πY/2)|` (`cgmyTemperedRate`, positive on
  `(0,2) \ {1}` by `cgmy_tempered_prod_neg`), `c' = 2^{Y−1} Y (M + G)
  |C Γ(−Y)|` (`cgmyTemperedCorrection`) and `K₀ = C |Γ(−Y)| (M^Y + G^Y)`
  (`cgmyTemperedConstant`). Past the explicit `cgmyDecayThreshold` — which
  carries `M + G`, `4c'/r` and `(4K₀/r)^{1/Y}` — the correction and the
  constant cost at most a quarter of the leading term each, giving (H-decay)
  of BRIEF_010 §5:

      ‖exp(τ ψ(u − i(α+1)))‖ ≤ exp(−(τ r / 2) |u|^Y),

  and hence `cgmy_cmPriceKernel_integrable`: the CGMY Carr–Madan pricing
  kernel is absolutely integrable on the corrected contour, at
  `0 < α`, `α+1 < M` — no condition on `G` beyond `G > 0`.

  THE LEVY MEASURE. `cgmyLevyDensity` is `C e^{−Mx} x^{−1−Y}` on `x > 0` and
  its mirror `C e^{Gx} (−x)^{−1−Y}` on `x < 0`; `cgmy_levy_sq_integrable` is
  the `∫ (1 ∧ x²) ν < ∞` half (the `x²`-weighted near-zero integral,
  requiring `Y < 2`), and `cgmy_levy_far_moment` is the tempered far-field
  moment `∫_{x ≥ 1} e^{ux} ν⁺(dx) < ∞` for `u < M`.

  NOT MACHINE-CHECKED (labelled, not assumed): the Levy–Khintchine
  representation itself, i.e. that the compensated integral of `ν` EQUALS the
  closed-form `ψ`. mathlib v4.34.0 has no Levy–Khintchine theorem (Fourier.lean's
  header carries the same caveat), and the Taylor step from `∫ (1 ∧ x²) ν < ∞`
  to the compensated integrand is prose here. Both are route-checked
  numerically by the oracle (`experiments/black_scholes.py`,
  `tests/test_bs.py::test_cgmy_contour`).

  Mathlib names verified at v4.34.0.
-/
import Mathlib
import ImprovedBS.Fourier
import ImprovedBS.Pricing

noncomputable section

namespace BSM

open MeasureTheory Filter Set

/-! ## §1 the exponent, the contour, and its constants -/

/-- The CGMY characteristic exponent
`ψ(v) = C Γ(−Y) [(M − iv)^Y − M^Y + (G + iv)^Y − G^Y]`. -/
def cgmyExponent (C G M Y : ℝ) (v : ℂ) : ℂ :=
  (C * (Real.Gamma (-Y) : ℂ)) *
    ((M - Complex.I * v) ^ (Y : ℂ) - (M : ℂ) ^ (Y : ℂ) +
      (G + Complex.I * v) ^ (Y : ℂ) - (G : ℂ) ^ (Y : ℂ))

/-- `exp(τ ψ)`: the model's characteristic factor, affine in `τ`. -/
def cgmyCharFactor (C G M Y τ : ℝ) (v : ℂ) : ℂ :=
  Complex.exp (τ * cgmyExponent C G M Y v)

/-- The pricing contour `v = u − i(α+1)` of correction C12. -/
def cgmyContour (α u : ℝ) : ℂ :=
  (u : ℂ) - ((α + 1 : ℝ) : ℂ) * Complex.I

/-- The OLD Carr–Madan line `v = u + iα` that `Fourier.lean`'s `carrMadanKernel`
sits on. Kept so the C14 correction is a statement about two named lines: on this
one it is the `G + iv` base that leaves the right half plane
(`cgmyOldContour_base_right_re`). -/
def cgmyOldContour (α u : ℝ) : ℂ :=
  (u : ℂ) + (α : ℝ) * Complex.I

/-- `M − iv` on the pricing contour: the positive-tail base. -/
def cgmyBaseLeft (M α u : ℝ) : ℂ :=
  ((M - (α + 1) : ℝ) : ℂ) - (u : ℂ) * Complex.I

/-- `G + iv` on the pricing contour: the negative-tail base. -/
def cgmyBaseRight (G α u : ℝ) : ℂ :=
  ((G + (α + 1) : ℝ) : ℂ) + (u : ℂ) * Complex.I

/-- `r = 2 C |Γ(−Y) cos(πY/2)|`: the exponential decay rate of `ψ` along the
pricing contour (`Re ψ(u − i(α+1)) ≈ −r |u|^Y`). Positive for `Y ∈ (0,2) \ {1}`
by `cgmy_tempered_prod_neg`. -/
def cgmyTemperedRate (C Y : ℝ) : ℝ :=
  2 * C * |Real.Gamma (-Y) * Real.cos (Real.pi * Y / 2)|

/-- `K₀ = C |Γ(−Y)| (M^Y + G^Y)`: the exponent's two subtracted real powers,
in modulus. -/
def cgmyTemperedConstant (C G M Y : ℝ) : ℝ :=
  C * |Real.Gamma (-Y)| * (M ^ Y + G ^ Y)

/-- `c' = 2^{Y−1} Y (M+G) |C Γ(−Y)|`: the subleading correction the `Y ≥ 1`
mean-value estimate contributes to `Re ψ` on the contour. (It is unused in the
`Y < 1` regime, where the sharp cos estimate has no correction; the unified
`cgmyExponent_contour_re_le` merely adds the nonnegative term.) -/
def cgmyTemperedCorrection (C G M Y : ℝ) : ℝ :=
  2 ^ (Y - 1) * Y * (M + G) * |C * Real.Gamma (-Y)|

/-- The explicit tail threshold: past it `M + G ≤ |u|` (so the mean-value
hypothesis `a ≤ y` holds), `4c'/r ≤ |u|` (correction at most a quarter of the
leading term) and `(4K₀/r)^{1/Y} ≤ |u|` (constant likewise), leaving `r/2` as
the exponent in the (H-decay) bound. -/
def cgmyDecayThreshold (C G M Y : ℝ) : ℝ :=
  max (M + G)
    (max (4 * cgmyTemperedCorrection C G M Y / cgmyTemperedRate C Y)
      (max 1 ((4 * cgmyTemperedConstant C G M Y / cgmyTemperedRate C Y) ^ (1 / Y))))

/-! ## §2 affine in `τ`, and the contour's two bases -/

theorem cgmyCharFactor_add (C G M Y τ₁ τ₂ : ℝ) (v : ℂ) :
    cgmyCharFactor C G M Y (τ₁ + τ₂) v =
      cgmyCharFactor C G M Y τ₁ v * cgmyCharFactor C G M Y τ₂ v := by
  unfold cgmyCharFactor
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

theorem cgmyCharFactor_zero (C G M Y : ℝ) (v : ℂ) : cgmyCharFactor C G M Y 0 v = 1 := by
  simp [cgmyCharFactor]

theorem cgmyContour_base_left (M α u : ℝ) :
    (M : ℂ) - Complex.I * cgmyContour α u = cgmyBaseLeft M α u := by
  unfold cgmyContour cgmyBaseLeft
  rw [mul_sub, ← mul_assoc, mul_comm Complex.I ((α + 1 : ℝ) : ℂ), mul_assoc, Complex.I_mul_I]
  push_cast
  ring

theorem cgmyContour_base_right (G α u : ℝ) :
    (G : ℂ) + Complex.I * cgmyContour α u = cgmyBaseRight G α u := by
  unfold cgmyContour cgmyBaseRight
  rw [mul_sub, ← mul_assoc, mul_comm Complex.I ((α + 1 : ℝ) : ℂ), mul_assoc, Complex.I_mul_I]
  push_cast
  ring

/-- C12/C14: the exponent on the pricing contour, with both cpow bases. The
bases' real parts are `M − (α+1)` and `G + α + 1`, so the branch condition on
this line is `α + 1 < M` and nothing else. -/
theorem cgmyExponent_contour (C G M Y α u : ℝ) :
    cgmyExponent C G M Y (cgmyContour α u) =
      (C * (Real.Gamma (-Y) : ℂ)) *
        (cgmyBaseLeft M α u ^ (Y : ℂ) - (M : ℂ) ^ (Y : ℂ) +
          cgmyBaseRight G α u ^ (Y : ℂ) - (G : ℂ) ^ (Y : ℂ)) := by
  simp only [cgmyExponent, cgmyBaseLeft, cgmyBaseRight, cgmyContour_base_left,
    cgmyContour_base_right]

/-- `M − iv` on the pricing contour has real part `M − (α+1)`. -/
theorem cgmyContour_base_left_re (M α u : ℝ) : (cgmyBaseLeft M α u).re = M - (α + 1) := by
  unfold cgmyBaseLeft
  simp [Complex.sub_re, Complex.mul_re]

/-- `G + iv` on the pricing contour has real part `G + α + 1 > 0` for free: the
half of C14 that says `G` does not constrain the pricing line. -/
theorem cgmyContour_base_right_re (G α u : ℝ) : (cgmyBaseRight G α u).re = G + (α + 1) := by
  unfold cgmyBaseRight
  simp [Complex.add_re, Complex.mul_re]

/-- C14 witness, old line: `v = u + iα` gives `Re(G + iv) = G − α`, which goes
NEGATIVE once `α ≥ G`. This is the base — and the line — the `min(G,M)` prose was
really about. -/
theorem cgmyOldContour_base_right_re (G α u : ℝ) :
    (G + Complex.I * cgmyOldContour α u).re = G - α := by
  unfold cgmyOldContour
  simp [Complex.add_re, Complex.mul_re]

/-! ## §3 signs: `Γ(−Y) cos(πY/2) < 0` on `(0,2) \ {1}` -/

/-- Euler reflection in the form the sign analysis needs:
`Γ(−Y) = −π / (sin (πY) Γ(1+Y))` for `Y > 0`, `sin (πY) ≠ 0`. -/
theorem cgmyGamma_neg_eq (Y : ℝ) (hY : 0 < Y) (hsin : Real.sin (Real.pi * Y) ≠ 0) :
    Real.Gamma (-Y) = -Real.pi / (Real.sin (Real.pi * Y) * Real.Gamma (1 + Y)) := by
  have hΓ : Real.Gamma (1 + Y) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have href : Real.Gamma (-Y) * Real.Gamma (1 + Y) = -(Real.pi / Real.sin (Real.pi * Y)) := by
    have h := Real.Gamma_mul_Gamma_one_sub (-Y)
    have hone : (1 : ℝ) - -Y = 1 + Y := by ring
    rw [hone] at h
    rw [show Real.pi * -Y = -(Real.pi * Y) by ring, Real.sin_neg, div_neg] at h
    exact h
  have hden : Real.sin (Real.pi * Y) * Real.Gamma (1 + Y) ≠ 0 := mul_ne_zero hsin hΓ
  rw [eq_div_iff hden]
  have h2 : Real.Gamma (-Y) * Real.Gamma (1 + Y) * Real.sin (Real.pi * Y) = -Real.pi := by
    rw [href, neg_mul, div_mul_cancel₀ _ hsin]
  calc Real.Gamma (-Y) * (Real.sin (Real.pi * Y) * Real.Gamma (1 + Y))
      = Real.Gamma (-Y) * Real.Gamma (1 + Y) * Real.sin (Real.pi * Y) := by ring
    _ = -Real.pi := h2

theorem cgmyGamma_neg_neg_of_lt_one {Y : ℝ} (hY : 0 < Y) (hY₁ : Y < 1) :
    Real.Gamma (-Y) < 0 := by
  have hsin : 0 < Real.sin (Real.pi * Y) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    nlinarith [Real.pi_pos]
  have hden : 0 < Real.sin (Real.pi * Y) * Real.Gamma (1 + Y) :=
    mul_pos hsin (Real.Gamma_pos_of_pos (by linarith))
  rw [cgmyGamma_neg_eq Y hY hsin.ne']
  exact div_neg_of_neg_of_pos (by linarith [Real.pi_pos]) hden

theorem cgmyGamma_neg_pos_of_one_lt {Y : ℝ} (hY₁ : 1 < Y) (hY₂ : Y < 2) :
    0 < Real.Gamma (-Y) := by
  have hsin : Real.sin (Real.pi * Y) < 0 := by
    have hsplit : Real.pi * Y = Real.pi * (Y - 1) + Real.pi := by ring
    rw [hsplit, Real.sin_add_pi]
    have h1 : 0 < Real.pi * (Y - 1) := mul_pos Real.pi_pos (by linarith)
    have h2 : Real.pi * (Y - 1) < Real.pi := by nlinarith [Real.pi_pos]
    linarith [Real.sin_pos_of_pos_of_lt_pi h1 h2]
  have hden : Real.sin (Real.pi * Y) * Real.Gamma (1 + Y) < 0 :=
    mul_neg_of_neg_of_pos hsin (Real.Gamma_pos_of_pos (by linarith))
  rw [cgmyGamma_neg_eq Y (by linarith) hsin.ne]
  exact div_pos_of_neg_of_neg (by linarith [Real.pi_pos]) hden

theorem cgmy_cos_half_pos_of_lt_one {Y : ℝ} (hY : 0 < Y) (hY₁ : Y < 1) :
    0 < Real.cos (Real.pi * Y / 2) := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> nlinarith [Real.pi_pos]

theorem cgmy_cos_half_neg_of_one_lt {Y : ℝ} (hY₁ : 1 < Y) (hY₂ : Y < 2) :
    Real.cos (Real.pi * Y / 2) < 0 := by
  refine Real.cos_neg_of_pi_div_two_lt_of_lt ?_ ?_ <;> nlinarith [Real.pi_pos]

/-- Both factors of the tempered rate flip sign at `Y = 1`, so their product is
negative on all of `(0,2) \ {1}`: the rate is positive. -/
theorem cgmy_tempered_prod_neg {Y : ℝ} (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    Real.Gamma (-Y) * Real.cos (Real.pi * Y / 2) < 0 := by
  rcases lt_or_gt_of_ne hY₁ with hlt | hgt
  · exact mul_neg_of_neg_of_pos (cgmyGamma_neg_neg_of_lt_one hY hlt)
      (cgmy_cos_half_pos_of_lt_one hY hlt)
  · exact mul_neg_of_pos_of_neg (cgmyGamma_neg_pos_of_one_lt hgt hY₂)
      (cgmy_cos_half_neg_of_one_lt hgt hY₂)

theorem cgmyTemperedRate_pos {C Y : ℝ} (hC : 0 < C) (hY : 0 < Y) (hY₂ : Y < 2)
    (hY₁ : Y ≠ 1) : 0 < cgmyTemperedRate C Y := by
  unfold cgmyTemperedRate
  exact mul_pos (by positivity) (abs_pos.mpr (cgmy_tempered_prod_neg hY hY₂ hY₁).ne)

/-- `−r = 2 C Γ(−Y) cos(πY/2)`: the sign-free form of the rate that the exponent
estimate multiplies through. Holds in BOTH regimes because the two factors flip
sign together at `Y = 1` (`cgmy_tempered_prod_neg`). -/
theorem cgmy_tempered_rate_neg_eq {C Y : ℝ} (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    -(cgmyTemperedRate C Y) = 2 * C * Real.Gamma (-Y) * Real.cos (Real.pi * Y / 2) := by
  unfold cgmyTemperedRate
  rw [abs_of_neg (cgmy_tempered_prod_neg hY hY₂ hY₁)]
  ring

theorem cgmyTemperedConstant_nonneg {C G M Y : ℝ} (hC : 0 < C) (hG : 0 ≤ G) (hM : 0 ≤ M) :
    0 ≤ cgmyTemperedConstant C G M Y := by
  unfold cgmyTemperedConstant
  exact mul_nonneg (mul_nonneg hC.le (abs_nonneg _))
    (add_nonneg (Real.rpow_nonneg hM Y) (Real.rpow_nonneg hG Y))

theorem cgmyTemperedCorrection_nonneg {C G M Y : ℝ} (hC : 0 < C) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hY : 0 ≤ Y) : 0 ≤ cgmyTemperedCorrection C G M Y := by
  unfold cgmyTemperedCorrection
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hY)
    (add_nonneg hM hG)) (abs_nonneg _)

/-! ## §4 the cpow estimates on the two bases -/

/-- `Re(z^Y) = ‖z‖^Y cos(arg z · Y)` for `z ≠ 0`: the identity every contour
estimate goes through (`Complex.exp_re` plus the branch's `log`). -/
theorem cgmy_cpow_re_eq {z : ℂ} (hz : z ≠ 0) (Y : ℝ) :
    (z ^ (Y : ℂ)).re = ‖z‖ ^ Y * Real.cos (z.arg * Y) := by
  have hre : (Complex.log z * (Y : ℂ)).re = Real.log ‖z‖ * Y := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : (Complex.log z * (Y : ℂ)).im = z.arg * Y := by
    rw [Complex.mul_im, Complex.log_re, Complex.log_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re, hre, him,
    ← Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

/-- `‖a + iy‖ ≥ y` for `y > 0`. -/
theorem cgmy_norm_ge_im {a y : ℝ} (hy : 0 < y) : y ≤ ‖(a : ℂ) + (y : ℂ) * Complex.I‖ := by
  have h2 : ‖(a : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  nlinarith [norm_nonneg ((a : ℂ) + (y : ℂ) * Complex.I), sq_nonneg a, hy.le]

theorem cgmy_arg_mem {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) :
    0 ≤ ((a : ℂ) + (y : ℂ) * Complex.I).arg ∧
      ((a : ℂ) + (y : ℂ) * Complex.I).arg ≤ Real.pi / 2 := by
  have hre : (0 : ℝ) ≤ ((a : ℂ) + (y : ℂ) * Complex.I).re := by
    simpa [Complex.add_re, Complex.mul_re] using ha
  have him : (0 : ℝ) ≤ ((a : ℂ) + (y : ℂ) * Complex.I).im := by
    simpa [Complex.add_im, Complex.mul_im] using hy
  exact ⟨Complex.arg_nonneg_iff.mpr him, Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre)⟩

/-- `cos` is decreasing on `[0, π]` and `arg z · Y ≤ πY/2 ≤ π`: one monotonicity
fact serves the sharp `Y < 1` estimate. -/
theorem cgmy_cos_arg_le {a y Y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) (hY : 0 < Y) (hY₂ : Y < 2) :
    Real.cos (Real.pi * Y / 2) ≤ Real.cos (((a : ℂ) + (y : ℂ) * Complex.I).arg * Y) := by
  obtain ⟨harg₀, harg₂⟩ := cgmy_arg_mem (y := y) ha hy
  refine Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg harg₀ hY.le) ?_ ?_
  · nlinarith [Real.pi_pos]
  · have h := mul_le_mul_of_nonneg_right harg₂ hY.le
    nlinarith [h]

/-- `Y < 1`: each base's real part dominates `y^Y cos(πY/2)` — the sharp estimate
(`Γ(−Y) < 0` regime), with no correction term. -/
theorem cgmy_cpow_re_ge_of_lt_one {a y Y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hY : 0 < Y)
    (hY₂ : Y < 2) (hY₁ : Y < 1) :
    y ^ Y * Real.cos (Real.pi * Y / 2) ≤ (((a : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re := by
  have hz : (a : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have him : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by
      simp [Complex.add_im, Complex.mul_im]
    rw [h] at him
    simp at him
    linarith
  have hcos := cgmy_cos_arg_le (y := y) ha hy.le hY hY₂
  have hcospos := cgmy_cos_half_pos_of_lt_one hY hY₁
  have hnorm := cgmy_norm_ge_im (a := a) hy
  calc y ^ Y * Real.cos (Real.pi * Y / 2)
      ≤ y ^ Y * Real.cos (((a : ℂ) + (y : ℂ) * Complex.I).arg * Y) :=
        mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg hy.le Y)
    _ ≤ ‖(a : ℂ) + (y : ℂ) * Complex.I‖ ^ Y *
          Real.cos (((a : ℂ) + (y : ℂ) * Complex.I).arg * Y) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy.le hnorm hY.le)
          (le_trans hcospos.le hcos)
    _ = (((a : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re := (cgmy_cpow_re_eq hz Y).symm

/-- `1 ≤ Y < 2`: the mean value inequality on `t ↦ (t + iy)^Y`, whose derivative
is `Y (t + iy)^{Y-1}` with `‖Y (t + iy)^{Y-1}‖ = Y ‖t + iy‖^{Y-1} ≤ Y (2y)^{Y-1}`
for `t ≤ y`, gives `Re((a + iy)^Y) ≤ y^Y cos(πY/2) + 2^{Y-1} Y a y^{Y-1}` — the
`Γ(−Y) > 0` regime, where the correction term is what keeps the estimate true
for `a` comparable to `y`. -/
theorem cgmy_cpow_re_le_of_one_le {a y Y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hay : a ≤ y)
    (hY : 1 ≤ Y) (hY₂ : Y < 2) :
    (((a : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re ≤
      y ^ Y * Real.cos (Real.pi * Y / 2) + 2 ^ (Y - 1) * Y * a * y ^ (Y - 1) := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hY1 : 0 ≤ Y - 1 := by linarith
  -- the moving base is always in the slit plane
  have hmem : ∀ t : ℝ, ((t : ℂ) + (y : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro t
    rw [Complex.mem_slitPlane_iff]
    refine Or.inr ?_
    have him : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him]
    exact hy.ne'
  -- the derivative of the moving base
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((s : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ))
      ((Y : ℂ) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (((Y - 1 : ℝ)) : ℂ))) t := by
    intro t
    -- the ℂ → ℂ derivative at the complex point `↑t`, then its restriction to `ℝ`
    have hbase : HasDerivAt (fun z : ℂ => z + (y : ℂ) * Complex.I) 1 (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).add_const ((y : ℂ) * Complex.I)
    have hpow : HasDerivAt (fun z : ℂ => (z + (y : ℂ) * Complex.I) ^ (Y : ℂ))
        ((Y : ℂ) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ ((Y : ℂ) - 1)) * 1) (t : ℂ) :=
      hbase.cpow_const (c := (Y : ℂ)) (hmem t)
    have hreal := hpow.comp_ofReal
    have hexp : (Y : ℂ) - 1 = (((Y - 1 : ℝ)) : ℂ) := by push_cast; ring
    simpa [hexp] using hreal
  -- its norm is bounded by `Y (2y)^{Y-1}` on `[0, a]`
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) a,
      ‖(Y : ℂ) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (((Y - 1 : ℝ)) : ℂ))‖ ≤
        Y * (2 * y) ^ (Y - 1) := by
    intro t ht
    have ht_le : t ≤ y := le_trans ht.2.le hay
    have hnorm_sq : ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = t ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have hnorm_le : ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ 2 * y := by
      have h2 : t ^ 2 + y ^ 2 ≤ (2 * y) ^ 2 := by nlinarith [ht.1, hy]
      nlinarith [norm_nonneg ((t : ℂ) + (y : ℂ) * Complex.I), h2, hnorm_sq, hy]
    rw [norm_mul, Complex.norm_of_nonneg hYpos.le, Complex.norm_cpow_real]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm_le hY1)
      hYpos.le
  -- mean value inequality
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s : ℝ => ((s : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ))
    (f' := fun t : ℝ => (Y : ℂ) * (((t : ℂ) + (y : ℂ) * Complex.I) ^ (((Y - 1 : ℝ)) : ℂ)))
    (a := 0) (b := a) (C := Y * (2 * y) ^ (Y - 1))
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound a ⟨ha, le_rfl⟩
  have hdiff : (((a : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re -
      ((((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re ≤ Y * (2 * y) ^ (Y - 1) * a := by
    have h1 : (((a : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ) -
        (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re ≤
        ‖((a : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ) -
          (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)‖ :=
      Complex.re_le_norm _
    rw [Complex.sub_re] at h1
    linarith [hmvt, h1]
  -- the value at `t = 0`
  have hbase : ((((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re =
      y ^ Y * Real.cos (Real.pi * Y / 2) := by
    have hz : ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      intro h
      have him : (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y := by
        simp [Complex.add_im, Complex.mul_im]
      rw [h] at him
      simp at him
      linarith
    have hnorm : ‖((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ = y := by
      have h2 : ‖((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_add_mul_I]
        ring
      nlinarith [norm_nonneg (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)]
    have harg : (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I).arg = Real.pi / 2 := by
      have h : ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I = Complex.I * (y : ℂ) := by
        push_cast
        ring
      rw [h, Complex.arg_mul_real hy Complex.I, Complex.arg_I]
    rw [cgmy_cpow_re_eq hz Y, hnorm, harg]
    ring_nf
  have h2y : (2 * y) ^ (Y - 1) = 2 ^ (Y - 1) * y ^ (Y - 1) :=
    Real.mul_rpow (by norm_num) hy.le
  rw [hbase] at hdiff
  rw [h2y] at hdiff
  linarith [hdiff]

/-- Mirror symmetry of the real part on the closed right half plane:
`Re((a − iy)^Y) = Re((a + iy)^Y)` for `a ≥ 0`. -/
theorem cgmy_cpow_re_conj {a y Y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) :
    (((a : ℂ) - (y : ℂ) * Complex.I) ^ (Y : ℂ)).re =
      (((a : ℂ) + (y : ℂ) * Complex.I) ^ (Y : ℂ)).re := by
  have harg : ((a : ℂ) + (y : ℂ) * Complex.I).arg ≠ Real.pi := by
    have h := (cgmy_arg_mem (y := y) ha hy.le).2
    intro hπ
    rw [hπ] at h
    linarith [Real.pi_pos]
  have hconj : (a : ℂ) - (y : ℂ) * Complex.I = starRingEnd ℂ ((a : ℂ) + (y : ℂ) * Complex.I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj, Complex.conj_cpow _ _ harg, Complex.conj_ofReal, Complex.conj_re]

/-- The sign of `u` does not matter for the real part: `Re((a − iu)^Y)` depends
only on `|u|`. This is what lets the contour estimates use the `+ i|u|` bases
while `cgmyBaseLeft`/`cgmyBaseRight` carry the signed `u`. -/
theorem cgmy_cpow_re_abs {a u Y : ℝ} (ha : 0 ≤ a) :
    (((a : ℂ) - (u : ℂ) * Complex.I) ^ (Y : ℂ)).re =
      (((a : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have h : (a : ℂ) - (u : ℂ) * Complex.I = (a : ℂ) + ((-u : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, abs_of_neg hu]
  · simp [abs_zero, Complex.ofReal_zero]
  · have h : ((|u| : ℝ) : ℂ) = (u : ℂ) := by rw [abs_of_pos hu]
    rw [h]
    exact cgmy_cpow_re_conj ha hu

/-! ## §5 the real part on the pricing contour, and the decay it forces -/

/-- The two-base real part of the exponent on the pricing contour. This is where
the C14 correction lives: the bases are `M − (α+1)` and `G + α + 1`, so what the
estimate needs from `G` is only `G > 0`. -/
theorem cgmyExponent_contour_re (C G M Y α u : ℝ) (hG : 0 < G) (hM : 0 < M) :
    (cgmyExponent C G M Y (cgmyContour α u)).re =
      C * Real.Gamma (-Y) * ((cgmyBaseLeft M α u ^ (Y : ℂ)).re +
        (cgmyBaseRight G α u ^ (Y : ℂ)).re - M ^ Y - G ^ Y) := by
  have hMre : (((M : ℂ) ^ (Y : ℂ)).re) = M ^ Y := by
    rw [← Complex.ofReal_cpow (le_of_lt hM) Y, Complex.ofReal_re]
  have hGre : (((G : ℂ) ^ (Y : ℂ)).re) = G ^ Y := by
    rw [← Complex.ofReal_cpow (le_of_lt hG) Y, Complex.ofReal_re]
  rw [cgmyExponent_contour, Complex.mul_re]
  have hcoefre : ((C * (Real.Gamma (-Y) : ℂ)).re) = C * Real.Gamma (-Y) := by
    simp [Complex.mul_re]
  have hcoefim : ((C * (Real.Gamma (-Y) : ℂ)).im) = 0 := by
    simp [Complex.mul_im]
  rw [hcoefre, hcoefim, zero_mul, sub_zero]
  simp only [Complex.sub_re, Complex.add_re, hMre, hGre]
  ring

/-- The core (H-decay) estimate: `Re ψ(u − i(α+1)) ≤ −r |u|^Y + c' |u|^{Y−1} + K₀`
for `|u| ≥ M + G`, under the pricing-line condition `α + 1 < M` and no condition
on `G` beyond `G > 0`. This is the C14 correction as a theorem. -/
theorem cgmyExponent_contour_re_le (C G M Y α : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hα : 0 < α) (hMG : α + 1 < M) :
    ∀ u : ℝ, M + G ≤ |u| →
      (cgmyExponent C G M Y (cgmyContour α u)).re ≤
        -(cgmyTemperedRate C Y) * |u| ^ Y +
          cgmyTemperedCorrection C G M Y * |u| ^ (Y - 1) + cgmyTemperedConstant C G M Y := by
  intro u hu
  have hy : 0 < |u| := lt_of_lt_of_le (by linarith : (0 : ℝ) < M + G) hu
  have hL : 0 ≤ M - (α + 1) := by linarith
  have hR : 0 ≤ G + (α + 1) := by linarith
  have hayL : M - (α + 1) ≤ |u| := by linarith
  have hayR : G + (α + 1) ≤ |u| := by linarith
  have hLeq : (cgmyBaseLeft M α u ^ (Y : ℂ)).re =
      ((((M - (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re := by
    unfold cgmyBaseLeft
    exact cgmy_cpow_re_abs hL
  have hReq : (cgmyBaseRight G α u ^ (Y : ℂ)).re =
      ((((G + (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re := by
    unfold cgmyBaseRight
    simpa using cgmy_cpow_re_abs (a := G + (α + 1)) (u := -u) (Y := Y) hR
  -- `ψ(u − i(α+1))` with `y = |u|`: both bases read as `a + iy`, so the whole
  -- statement is about `B1 + B2 − M^Y − G^Y` and its sign is decided by Γ(−Y)
  have hpsi : (cgmyExponent C G M Y (cgmyContour α u)).re =
      C * Real.Gamma (-Y) *
        (((((M - (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re +
          ((((G + (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re -
            M ^ Y - G ^ Y) := by
    rw [cgmyExponent_contour_re C G M Y α u hG hM, hLeq, hReq]
  have hrpow : 0 ≤ |u| ^ (Y - 1) := Real.rpow_nonneg (abs_nonneg u) _
  rcases lt_or_gt_of_ne hY₁ with hlt | hgt
  · -- `Y < 1`: `Γ(−Y) < 0`, both bases dominate `|u|^Y cos(πY/2)`, so multiplying
    -- by the prefactor turns the domination into an UPPER bound. The `c'` term is
    -- NOT used here: it only has to be nonnegative.
    have hΓ : Real.Gamma (-Y) < 0 := cgmyGamma_neg_neg_of_lt_one hY hlt
    have hCΓ : C * Real.Gamma (-Y) < 0 := mul_neg_of_pos_of_neg hC hΓ
    have hb1 := cgmy_cpow_re_ge_of_lt_one (a := M - (α + 1)) (y := |u|) hL hy hY hY₂ hlt
    have hb2 := cgmy_cpow_re_ge_of_lt_one (a := G + (α + 1)) (y := |u|) hR hy hY hY₂ hlt
    have h1 : C * Real.Gamma (-Y) *
        ((((M - (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re ≤
        C * Real.Gamma (-Y) * (|u| ^ Y * Real.cos (Real.pi * Y / 2)) :=
      mul_le_mul_of_nonpos_left hb1 hCΓ.le
    have h2 : C * Real.Gamma (-Y) *
        ((((G + (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re ≤
        C * Real.Gamma (-Y) * (|u| ^ Y * Real.cos (Real.pi * Y / 2)) :=
      mul_le_mul_of_nonpos_left hb2 hCΓ.le
    -- `|Γ(−Y)| = −Γ(−Y)` and `|C Γ(−Y)| = −C Γ(−Y)` on this branch: the constants'
    -- ABS unfolds against the sign, which is what makes `K₀` come out with a `+`
    have hconst : cgmyTemperedConstant C G M Y = -(C * Real.Gamma (-Y) * (M ^ Y + G ^ Y)) := by
      unfold cgmyTemperedConstant
      rw [abs_of_neg hΓ]
      ring
    have hcorr : cgmyTemperedCorrection C G M Y =
        2 ^ (Y - 1) * Y * (M + G) * -(C * Real.Gamma (-Y)) := by
      unfold cgmyTemperedCorrection
      rw [abs_of_neg hCΓ]
    have hc'0 : 0 ≤ cgmyTemperedCorrection C G M Y * |u| ^ (Y - 1) :=
      mul_nonneg (cgmyTemperedCorrection_nonneg hC hG.le hM.le hY.le) hrpow
    have hrate := cgmy_tempered_rate_neg_eq (C := C) hY hY₂ hY₁
    rw [hpsi, hrate, hconst, hcorr]
    nlinarith [h1, h2, hc'0]
  · -- `1 < Y`: `Γ(−Y) > 0`, both bases are dominated by `|u|^Y cos(πY/2)` plus the
    -- mean-value correction `2^{Y−1} Y a |u|^{Y−1}`, and the prefactor preserves the
    -- direction — the `c'` term is genuinely used here.
    have hΓ : 0 < Real.Gamma (-Y) := cgmyGamma_neg_pos_of_one_lt hgt hY₂
    have hCΓ : 0 < C * Real.Gamma (-Y) := mul_pos hC hΓ
    have hb1 := cgmy_cpow_re_le_of_one_le (a := M - (α + 1)) (y := |u|) hL hy hayL hgt.le hY₂
    have hb2 := cgmy_cpow_re_le_of_one_le (a := G + (α + 1)) (y := |u|) hR hy hayR hgt.le hY₂
    have h1 : C * Real.Gamma (-Y) *
        ((((M - (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re ≤
        C * Real.Gamma (-Y) *
          (|u| ^ Y * Real.cos (Real.pi * Y / 2) +
            2 ^ (Y - 1) * Y * (M - (α + 1)) * |u| ^ (Y - 1)) :=
      mul_le_mul_of_nonneg_left hb1 hCΓ.le
    have h2 : C * Real.Gamma (-Y) *
        ((((G + (α + 1) : ℝ) : ℂ) + ((|u| : ℝ) : ℂ) * Complex.I) ^ (Y : ℂ)).re ≤
        C * Real.Gamma (-Y) *
          (|u| ^ Y * Real.cos (Real.pi * Y / 2) +
            2 ^ (Y - 1) * Y * (G + (α + 1)) * |u| ^ (Y - 1)) :=
      mul_le_mul_of_nonneg_left hb2 hCΓ.le
    have hconst : cgmyTemperedConstant C G M Y = C * Real.Gamma (-Y) * (M ^ Y + G ^ Y) := by
      unfold cgmyTemperedConstant
      rw [abs_of_pos hΓ]
    have hcorr : cgmyTemperedCorrection C G M Y =
        2 ^ (Y - 1) * Y * (M + G) * (C * Real.Gamma (-Y)) := by
      unfold cgmyTemperedCorrection
      rw [abs_of_pos hCΓ]
    have hrpowY : 0 ≤ |u| ^ Y := Real.rpow_nonneg (abs_nonneg u) _
    -- `(M − (α+1)) + (G + α + 1) = M + G`: the two bases' offsets sum to exactly the
    -- `(M + G)` that `c'` carries. A ring identity, no hypothesis needed.
    have hsum : M - (α + 1) + (G + (α + 1)) = M + G := by ring
    have hK : 0 ≤ C * Real.Gamma (-Y) * (M ^ Y + G ^ Y) :=
      mul_nonneg hCΓ.le (add_nonneg (Real.rpow_nonneg hM.le Y) (Real.rpow_nonneg hG.le Y))
    have hrate := cgmy_tempered_rate_neg_eq (C := C) hY hY₂ hY₁
    rw [hpsi, hrate, hconst, hcorr]
    nlinarith [h1, h2, hsum, hK, hrpow, hrpowY]


/-- Past `cgmyDecayThreshold` the correction and the constant each cost at most a
quarter of the leading term, leaving `r/2` as the effective rate. -/
theorem cgmyExponent_contour_re_le_half (C G M Y α : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hα : 0 < α) (hMG : α + 1 < M) :
    ∀ u : ℝ, cgmyDecayThreshold C G M Y ≤ |u| →
      (cgmyExponent C G M Y (cgmyContour α u)).re ≤
        -(cgmyTemperedRate C Y / 2) * |u| ^ Y := by
  intro u hu
  -- unfold `cgmyDecayThreshold` once: `le_max_left`/`le_max_right` need a `max` at
  -- the head of the goal's type, and a named def is opaque to them
  have hu' : max (M + G)
      (max (4 * cgmyTemperedCorrection C G M Y / cgmyTemperedRate C Y)
        (max 1 ((4 * cgmyTemperedConstant C G M Y / cgmyTemperedRate C Y) ^ (1 / Y)))) ≤ |u| :=
    hu
  have hr : 0 < cgmyTemperedRate C Y := cgmyTemperedRate_pos (C := C) hC hY hY₂ hY₁
  have hMGle : M + G ≤ |u| := le_trans (le_max_left _ _) hu'
  have hy : 0 < |u| := lt_of_lt_of_le (by linarith : (0 : ℝ) < M + G) hMGle
  have h4c : 4 * cgmyTemperedCorrection C G M Y / cgmyTemperedRate C Y ≤ |u| :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu'
  have h4K : (4 * cgmyTemperedConstant C G M Y / cgmyTemperedRate C Y) ^ (1 / Y) ≤ |u| :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hu'
  have h1 := cgmyExponent_contour_re_le C G M Y α hC hG hM hY hY₂ hY₁ hα hMG u hMGle
  -- the correction term is absorbed
  have hc' : cgmyTemperedCorrection C G M Y * |u| ^ (Y - 1) ≤ (cgmyTemperedRate C Y / 4) * |u| ^ Y := by
    have hle : cgmyTemperedCorrection C G M Y ≤ (cgmyTemperedRate C Y / 4) * |u| := by
      have h := mul_le_mul_of_nonneg_right h4c hr.le
      rw [div_mul_cancel₀ _ hr.ne'] at h
      have hc0 := cgmyTemperedCorrection_nonneg (Y := Y) hC hG.le hM.le hY.le
      nlinarith [h, hy]
    calc cgmyTemperedCorrection C G M Y * |u| ^ (Y - 1)
        ≤ ((cgmyTemperedRate C Y / 4) * |u|) * |u| ^ (Y - 1) :=
          mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hy.le _)
      _ = (cgmyTemperedRate C Y / 4) * (|u| * |u| ^ (Y - 1)) := by ring
      _ = (cgmyTemperedRate C Y / 4) * |u| ^ Y := by
          rw [← Real.rpow_one |u|, ← Real.rpow_add hy]
          congr 1
          ring
  -- the constant is absorbed
  have hK : cgmyTemperedConstant C G M Y ≤ (cgmyTemperedRate C Y / 4) * |u| ^ Y := by
    have hK0 := cgmyTemperedConstant_nonneg (Y := Y) hC hG.le hM.le
    have hpos : 0 ≤ 4 * cgmyTemperedConstant C G M Y / cgmyTemperedRate C Y :=
      div_nonneg (by linarith) hr.le
    have hpow : 4 * cgmyTemperedConstant C G M Y / cgmyTemperedRate C Y ≤ |u| ^ Y := by
      calc 4 * cgmyTemperedConstant C G M Y / cgmyTemperedRate C Y
          = ((4 * cgmyTemperedConstant C G M Y / cgmyTemperedRate C Y) ^ (1 / Y)) ^ Y := by
            rw [← Real.rpow_mul hpos, div_mul_cancel₀ (1 : ℝ) hY.ne', Real.rpow_one]
        _ ≤ |u| ^ Y := Real.rpow_le_rpow (Real.rpow_nonneg hpos (1 / Y)) h4K hY.le
    have h := (div_le_iff₀ hr).mp hpow
    nlinarith [h]
  calc (cgmyExponent C G M Y (cgmyContour α u)).re
      ≤ -(cgmyTemperedRate C Y) * |u| ^ Y +
          cgmyTemperedCorrection C G M Y * |u| ^ (Y - 1) + cgmyTemperedConstant C G M Y := h1
    _ ≤ -(cgmyTemperedRate C Y) * |u| ^ Y +
          (cgmyTemperedRate C Y / 4) * |u| ^ Y + (cgmyTemperedRate C Y / 4) * |u| ^ Y := by
        linarith [hc', hK]
    _ = -(cgmyTemperedRate C Y / 2) * |u| ^ Y := by ring

/-- (H-decay) of BRIEF_010 §5 for the CGMY factor on the pricing contour: the CGMY
modulus decays like `exp(−(τ r/2)|u|^Y)` past the explicit threshold. -/
theorem cgmy_contour_decay (C G M Y τ α : ℝ) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hα : 0 < α) (hMG : α + 1 < M) (hτ : 0 ≤ τ) :
    ∀ u : ℝ, cgmyDecayThreshold C G M Y ≤ |u| →
      ‖cgmyCharFactor C G M Y τ (cgmyContour α u)‖ ≤
        Real.exp (-(τ * cgmyTemperedRate C Y / 2) * |u| ^ Y) := by
  intro u hu
  have h1 := cgmyExponent_contour_re_le_half C G M Y α hC hG hM hY hY₂ hY₁ hα hMG u hu
  have h2 : τ * (cgmyExponent C G M Y (cgmyContour α u)).re ≤
      -(τ * cgmyTemperedRate C Y / 2) * |u| ^ Y := by
    have h := mul_le_mul_of_nonneg_left h1 hτ
    calc τ * (cgmyExponent C G M Y (cgmyContour α u)).re
        ≤ τ * (-(cgmyTemperedRate C Y / 2) * |u| ^ Y) := h
      _ = -(τ * cgmyTemperedRate C Y / 2) * |u| ^ Y := by ring
  have h3 : (τ * cgmyExponent C G M Y (cgmyContour α u)).re =
      τ * (cgmyExponent C G M Y (cgmyContour α u)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold cgmyCharFactor
  rw [Complex.norm_exp, h3]
  exact Real.exp_le_exp.mpr h2

/-! ## §6 continuity on the contour, and the kernel instantiation -/

theorem cgmy_contour_continuous (C G M Y α : ℝ) (hY : 0 < Y) (hMG : α + 1 < M) :
    Continuous fun u : ℝ => cgmyExponent C G M Y (cgmyContour α u) := by
  have hLeft : Continuous fun u : ℝ => ((M - (α + 1) : ℝ) : ℂ) - (u : ℂ) * Complex.I :=
    continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)
  have hRight : Continuous fun u : ℝ => ((G + (α + 1) : ℝ) : ℂ) + (u : ℂ) * Complex.I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hleft_re : ∀ u : ℝ, (((M - (α + 1) : ℝ) : ℂ) - (u : ℂ) * Complex.I).re = M - (α + 1) :=
    fun u => by simp [Complex.sub_re, Complex.mul_re]
  have hright_re : ∀ u : ℝ, (((G + (α + 1) : ℝ) : ℂ) + (u : ℂ) * Complex.I).re = G + (α + 1) :=
    fun u => by simp [Complex.add_re, Complex.mul_re]
  have hLeftPow : Continuous fun u : ℝ =>
      (((M - (α + 1) : ℝ) : ℂ) - (u : ℂ) * Complex.I) ^ (Y : ℂ) :=
    hLeft.cpow continuous_const fun u => by
      rw [Complex.mem_slitPlane_iff, hleft_re u]
      exact Or.inl (by linarith)
  have hRightPow : Continuous fun u : ℝ =>
      (((G + (α + 1) : ℝ) : ℂ) + (u : ℂ) * Complex.I) ^ (Y : ℂ) :=
    hRight.cpow continuous_const fun u => by
      rw [Complex.mem_slitPlane_iff, hright_re u]
      exact Or.inl (by linarith)
  have hfun : (fun u : ℝ => cgmyExponent C G M Y (cgmyContour α u)) =
      fun u : ℝ => (C * (Real.Gamma (-Y) : ℂ)) *
        ((((M - (α + 1) : ℝ) : ℂ) - (u : ℂ) * Complex.I) ^ (Y : ℂ) - (M : ℂ) ^ (Y : ℂ) +
          (((G + (α + 1) : ℝ) : ℂ) + (u : ℂ) * Complex.I) ^ (Y : ℂ) - (G : ℂ) ^ (Y : ℂ)) := by
    funext u
    exact cgmyExponent_contour C G M Y α u
  rw [hfun]
  exact Continuous.mul continuous_const
    (((hLeftPow.sub continuous_const).add hRightPow).sub continuous_const)

theorem cgmy_charFactor_contour_continuous (C G M Y τ α : ℝ) (hY : 0 < Y) (hMG : α + 1 < M) :
    Continuous fun u : ℝ => cgmyCharFactor C G M Y τ (cgmyContour α u) := by
  have h := cgmy_contour_continuous C G M Y α hY hMG
  simp only [cgmyCharFactor]
  exact Complex.continuous_exp.comp (continuous_const.mul h)

/-- BRIEF_010 §5 instantiated at CGMY: the Carr–Madan pricing kernel is
integrable on the corrected contour, for `0 < Y < 2`, `Y ≠ 1`, `0 < α`,
`α + 1 < M` and positive `C`, `G`, `M`, `τ`. -/
theorem cgmy_cmPriceKernel_integrable (C G M Y τ α : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hα : 0 < α) (hMG : α + 1 < M)
    (hτ : 0 < τ) :
    Integrable (cmPriceKernel (cgmyCharFactor C G M Y τ) α) := by
  refine cmPriceKernel_integrable hα (cgmy_charFactor_contour_continuous C G M Y τ α hY hMG)
    (c := τ * cgmyTemperedRate C Y / 2) (D := 1) (Y := Y)
    (by exact div_pos (mul_pos hτ (cgmyTemperedRate_pos hC hY hY₂ hY₁)) two_pos)
    (by norm_num) hY (u₀ := cgmyDecayThreshold C G M Y) ?_
  intro u hu
  simp only [one_mul, cgmyContour]
  exact cgmy_contour_decay C G M Y τ α hC hG hM hY hY₂ hY₁ hα hMG hτ.le u hu

/-! ## §7 the moment strip, and `∫ (1 ∧ x²) ν < ∞` -/

/-- The strip statement the pricing line needs: `α + 1 < M` alone places the
contour's imaginary shift inside `(−G, M)` — because `α + 1 > 0 > −G` is free.
This is C14 as arithmetic, with the `min(G,M)` spelling conspicuously absent. -/
theorem cgmy_contour_mem_strip (G M α : ℝ) (hG : 0 < G) (hα : 0 < α) (hMG : α + 1 < M) :
    -G < α + 1 ∧ α + 1 < M :=
  ⟨by linarith, hMG⟩

/-- The numéraire point `u = 1` lies in the strip exactly when `1 < M`. -/
theorem cgmy_numeraire_strip (G M : ℝ) (hG : 0 < G) (hM : 1 < M) :
    -G < 1 ∧ (1 : ℝ) < M :=
  ⟨by linarith, hM⟩

/-- On the strip `u ∈ (−G, M)` the exponent at `v = −iu` is REAL: both bases
become the positive reals `M − u` and `G + u`, so no branch is involved. This is
the closed form of `E[e^{u X_τ}] = exp(τ ψ(−iu)) < ∞`. -/
theorem cgmyExponent_strip (C G M Y u : ℝ) (hG : 0 < G) (hM : 0 < M) (h₁ : -G < u)
    (h₂ : u < M) :
    cgmyExponent C G M Y (-(Complex.I * (u : ℂ))) =
      ((C * Real.Gamma (-Y) * ((M - u) ^ Y - M ^ Y + (G + u) ^ Y - G ^ Y) : ℝ) : ℂ) := by
  have hMu : 0 < M - u := by linarith
  have hGu : 0 < G + u := by linarith
  have hIu : Complex.I * (-(Complex.I * (u : ℂ))) = (u : ℂ) := by
    rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
    ring
  have hL : (M : ℂ) - Complex.I * (-(Complex.I * (u : ℂ))) = ((M - u : ℝ) : ℂ) := by
    rw [hIu]
    push_cast
    ring
  have hR : (G : ℂ) + Complex.I * (-(Complex.I * (u : ℂ))) = ((G + u : ℝ) : ℂ) := by
    rw [hIu]
    push_cast
    ring
  rw [cgmyExponent, hL, hR,
    ← Complex.ofReal_cpow (le_of_lt hMu) Y, ← Complex.ofReal_cpow (le_of_lt hM) Y,
    ← Complex.ofReal_cpow (le_of_lt hGu) Y, ← Complex.ofReal_cpow (le_of_lt hG) Y]
  push_cast
  ring

/-- The CGMY Levy density: `C e^{−Mx} x^{−1−Y}` on the positive half-line, its
mirror `C e^{Gx} (−x)^{−1−Y}` on the negative one, as one even-in-`|x|` function. -/
def cgmyLevyDensity (C G M Y : ℝ) (x : ℝ) : ℝ :=
  C * Real.exp (-(if 0 < x then M else G) * |x|) * |x| ^ (-1 - Y)

theorem cgmyLevyDensity_nonneg {C G M Y : ℝ} (hC : 0 ≤ C) (x : ℝ) :
    0 ≤ cgmyLevyDensity C G M Y x := by
  unfold cgmyLevyDensity
  exact mul_nonneg (mul_nonneg hC (Real.exp_nonneg _)) (Real.rpow_nonneg (abs_nonneg x) _)

theorem cgmyLevyDensity_pos_of_pos {C G M Y x : ℝ} (hx : 0 < x) :
    cgmyLevyDensity C G M Y x = C * Real.exp (-M * x) * x ^ (-1 - Y) := by
  unfold cgmyLevyDensity
  rw [if_pos hx, abs_of_pos hx]

theorem cgmyLevyDensity_neg_of_neg {C G M Y x : ℝ} (hx : x < 0) :
    cgmyLevyDensity C G M Y x = C * Real.exp (G * x) * (-x) ^ (-1 - Y) := by
  unfold cgmyLevyDensity
  rw [if_neg (not_lt.mpr hx.le), abs_of_neg hx, neg_mul_neg]

/-- `∫ (1 ∧ x²) ν⁺ < ∞`, near-zero half: weighting the density's `x^{−1−Y}` by
`x²` gives the integrable `x^{1−Y}`, which requires `Y < 2`. The tempering rate
`M > 0` enters only through `e^{−Mx} ≤ 1` on `x > 0`, which is what makes the
weighted density a *minorant* of `C x^{1−Y}` there. -/
theorem cgmy_levy_sq_integrable (C M Y : ℝ) (hC : 0 < C) (hM : 0 < M) (hY : 0 < Y)
    (hY₂ : Y < 2) :
    IntegrableOn (fun x : ℝ => x ^ 2 * (C * (Real.exp (-M * x) * x ^ (-1 - Y)))) (Ioo 0 1) := by
  have hmaj : IntegrableOn (fun x : ℝ => C * x ^ (1 - Y)) (Ioo 0 1) :=
    (((intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).2
      (by linarith)).const_mul C)
  refine Integrable.mono' hmaj ?_ ?_
  · refine (ContinuousOn.mul ((continuous_id.pow 2).continuousOn) ?_).aestronglyMeasurable
      measurableSet_Ioo
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn ?_
    exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hexp : Real.exp (-M * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hM, hx0]
    have hpow : x ^ 2 * x ^ (-1 - Y) = x ^ (1 - Y) := by
      rw [← Real.rpow_two, ← Real.rpow_add hx0]
      congr 1
      ring
    have hpos : 0 ≤ x ^ 2 * (C * (Real.exp (-M * x) * x ^ (-1 - Y))) :=
      mul_nonneg (sq_nonneg x)
        (mul_nonneg hC.le (mul_nonneg (Real.exp_nonneg _) (Real.rpow_pos_of_pos hx0 _).le))
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    calc x ^ 2 * (C * (Real.exp (-M * x) * x ^ (-1 - Y)))
        = C * Real.exp (-M * x) * (x ^ 2 * x ^ (-1 - Y)) := by ring
      _ = C * Real.exp (-M * x) * x ^ (1 - Y) := by rw [hpow]
      _ ≤ C * 1 * x ^ (1 - Y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC.le)
            (Real.rpow_nonneg hx0.le _)
      _ = C * x ^ (1 - Y) := by ring

/-- The far-field tempered moment `∫_{x ≥ 1} e^{ux} ν⁺(dx) < ∞` for `u < M`.
Factoring `e^{ux} e^{−Mx} = e^{−(M−u)x}`, the integrand is dominated on `x ≥ 1`
by the pure exponential `e^{−(M−u)x}` (`exp_neg_integrableOn_Ioi`), because
`x^{−1−Y} ≤ 1` there once `0 < Y` (`Real.rpow_le_one_of_one_le_of_nonpos`).
Nothing here needs the Gaussian regime `x → 0`; that is why this half needs no
condition linking `Y` to `2`. -/
theorem cgmy_levy_far_moment (C M Y u : ℝ) (hC : 0 < C) (hY : 0 < Y) (hu : u < M) :
    IntegrableOn (fun x : ℝ => C * (Real.exp (-(M - u) * x) * x ^ (-1 - Y))) (Ioi 1) := by
  have hb : 0 < M - u := by linarith
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-(M - u) * x)) (Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 hb
  have hmain : IntegrableOn (fun x : ℝ => Real.exp (-(M - u) * x) * x ^ (-1 - Y)) (Ioi 1) := by
    refine Integrable.mono' hexp ?_ ?_
    · exact (ContinuousOn.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
        (continuousOn_id.rpow_const fun x hx =>
          Or.inl (ne_of_gt (lt_trans zero_lt_one hx)))).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 ≤ x := le_of_lt hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hpow : x ^ (-1 - Y) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
      have hnn : 0 ≤ Real.exp (-(M - u) * x) * x ^ (-1 - Y) :=
        mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx0.le _)
      rw [Real.norm_of_nonneg hnn]
      exact mul_le_of_le_one_right (Real.exp_nonneg _) hpow
  exact hmain.const_mul C

end BSM
