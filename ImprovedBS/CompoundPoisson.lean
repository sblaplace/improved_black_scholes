/-
  ImprovedBS/CompoundPoisson.lean — BRIEF_019: the compound-Poisson law, and the
  truncated CGMY jump law. This is the first half of Stage 2.

  In one line: the compound-Poisson law of a *probability* jump law `ρ` at rate
  `λ` — the Poisson mixture of convolution powers `∑ₙ pₙ ρ^{*n}` — is a
  probability measure whose characteristic function is `exp (lam (φ_ρ − 1))`; and
  truncating the landed CGMY Levy density to the *symmetric* set
  `{x | ε ≤ |x|}` gives a probability jump law whose compound-Poisson marginal
  at time `τ` has, as exponent, the honest Bochner integral
  `∫_{|x| ≥ ε} (e^{ivx} − 1) ν(dx)`.

  Two conventions, both *measured* rather than asserted (BRIEF_019's
  route-check; ledger C22):

  * the truncation is symmetric — `cgmyJumpMeasure`'s single density set is
    `{x | ε ≤ |x|}`, and no half-line truncation (`Ioi ε`, `Ici ε`,
    `Iic (−ε)`, ...) is written in this module. The one-sided version would
    keep only half of the near-zero `i v x` piece, leaving nothing to cancel
    it: the measured convergence exponent is `+0.4929` at `Y = 1/2` and
    `−0.4798` at `Y = 3/2` (i.e. `ε^{1−Y}`, divergent for `Y ≥ 1`), where the
    symmetric truncation measures `1.4904` and `0.4947` (`ε^{2−Y}`).
  * there is no compensator — `cgmyTruncatedExponent` carries
    `(exp (v x I) − 1)`, never `− v x I`. Compensating the truncated exponent
    gives the *other* exponent `ψ_Y(v) − i v m^∞` (checked to `1.2e−15`
    against the landed one-sided compensated closed form), i.e. a translated
    law, not the tree's.

  The mass theorem *consumes* rather than re-derives BRIEF_011's far-field
  integrability: `cgmyJumpMass_lt_top` cites the landed `cgmy_levy_far_moment`
  for both tails — the positive one at the tempering rate `M`, the mirror one
  at `G` after the substitution `x ↦ −x` — and bounds the compact window
  `Icc (−1) 1` by the truncation alone, `C ε^{−1−Y}`.

  Deliberately *not* here: the `ε ↓ 0` limit, its tightness, and the
  identification of the CGMY law itself (Stage 2b). Once this file lands, the
  object that limit is taken on exists.
-/
import Mathlib
import ImprovedBS.CGMY

noncomputable section

namespace BSM

open MeasureTheory Filter Set ProbabilityTheory Complex
open scoped Topology ENNReal NNReal

/-!
---------------------------------------------------------------------------
§1  The compound-Poisson law and its characteristic function
---------------------------------------------------------------------------
-/

/-- Iterated **additive convolution**: `convPow ρ 0 = δ₀` and
`convPow ρ (n+1) = convPow ρ n ∗ ρ`, the law of the sum of `n` independent
copies of the jump law. `Measure.conv` is mathlib's additive convolution (the
`to_additive` twin of `Measure.mconv`), the pushforward of the product measure
under `+`. -/
noncomputable def convPow (ρ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => Measure.conv (convPow ρ n) ρ

/-- **The compound-Poisson law** of the jump law `ρ` at rate `λ`: the Poisson
mixture of the convolution powers, weighted by `poissonPMFReal lam n`. The rate
is an `ℝ≥0`, matching `poissonMeasure`/`poissonPMFReal`; the jump law is an
arbitrary measure, and `cpLaw_isProbabilityMeasure` needs it to be a
probability measure and nothing else. -/
noncomputable def cpLaw (lam : ℝ≥0) (ρ : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n => ENNReal.ofReal (poissonPMFReal lam n) • convPow ρ n)

/-- The convolution powers of a probability measure are probability measures:
`δ₀` is one, and the additive convolution of two is one by mathlib's instance
`probabilitymeasure_of_probabilitymeasures_conv`. -/
theorem convPow_isProbabilityMeasure (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    ∀ n, IsProbabilityMeasure (convPow ρ n)
  | 0 => by rw [convPow]; infer_instance
  | n + 1 => by
      rw [convPow]
      haveI : IsProbabilityMeasure (convPow ρ n) := convPow_isProbabilityMeasure ρ hρ n
      haveI : IsProbabilityMeasure ρ := hρ
      infer_instance

/-- A probability measure is a finite measure — kept separate from
`convPow_isProbabilityMeasure` because `charFun_conv` wants the
`IsFiniteMeasure` field for both of its arguments. -/
theorem convPow_isFiniteMeasure (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) (n : ℕ) :
    IsFiniteMeasure (convPow ρ n) := by
  haveI : IsProbabilityMeasure (convPow ρ n) := convPow_isProbabilityMeasure ρ hρ n
  exact ⟨by simp⟩

/-- **The characteristic function of a convolution power is the power of the
jump law's**: `charFun (convPow ρ n) t = charFun ρ t ^ n`, by induction on `n`,
with `charFun_conv` (convolution is multiplicative under `charFun`) as the step
and `charFun_dirac` at the base. -/
theorem charFun_convPow (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) (t : ℝ) :
    ∀ n, charFun (convPow ρ n) t = charFun ρ t ^ n
  | 0 => by
      rw [convPow, pow_zero, charFun_dirac]
      simp
  | n + 1 => by
      haveI hn : IsFiniteMeasure (convPow ρ n) := convPow_isFiniteMeasure ρ hρ n
      haveI hρf : IsFiniteMeasure ρ := ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
      rw [convPow, charFun_conv, charFun_convPow ρ hρ t n, pow_succ]

/-- The mass of the compound-Poisson law is `∑' n, poissonPMFReal lam n = 1`: the
`Measure.sum` mass is the tsum of the summands' masses (`Measure.sum_apply`), the
scalar is `Measure.smul_apply`, each convolution power has mass one, and the
`ℝ≥0∞` tsum of the weights is the cast of the real tsum
(`ENNReal.ofReal_tsum_of_nonneg`), which mathlib's `hasSum_one_poissonMeasure`
evaluates. -/
theorem cpLaw_apply_univ (lam : ℝ≥0) (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    cpLaw lam ρ Set.univ = 1 := by
  haveI : ∀ n, IsProbabilityMeasure (convPow ρ n) := convPow_isProbabilityMeasure ρ hρ
  have hsum : HasSum (fun n => poissonPMFReal lam n) 1 := by
    simpa only [poissonPMFReal] using hasSum_one_poissonMeasure lam
  rw [cpLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
      show (0 : ℝ) ≤ poissonPMFReal lam n from poissonPMFReal_nonneg) hsum.summable,
    hsum.tsum_eq, ENNReal.ofReal_one]

/-- **The compound-Poisson law is a probability measure**: `IsProbabilityMeasure`
is a class whose only field is the mass identity. -/
theorem cpLaw_isProbabilityMeasure (lam : ℝ≥0) (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) :
    IsProbabilityMeasure (cpLaw lam ρ) :=
  ⟨cpLaw_apply_univ lam ρ hρ⟩

/-- **The compound-Poisson law's characteristic function**: for every
probability jump law `ρ`,

    `charFun (cpLaw lam ρ) t = exp (λ (charFun ρ t − 1))`.

The sum/integral exchange is `integral_sum_measure` (every summand is a finite
measure and the integrand has modulus one, so the mixed sum is summable), the
convolution powers come from `charFun_convPow`, and the closure is the Poisson
series identity `∑ₙ pₙ zⁿ = exp (λ (z − 1))`. Mathlib's
`charFun_map_cast_poissonMeasure` is the `ρ = δ₁` case of exactly this
statement, and the series is evaluated the same way there:
`NormedSpace.expSeries_div_hasSum_exp`, then `exp (−λ) * exp (λ z) = exp (λ (z − 1))`. -/
theorem charFun_cpLaw (lam : ℝ≥0) (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ) (t : ℝ) :
    charFun (cpLaw lam ρ) t = Complex.exp ((lam : ℂ) * (charFun ρ t - 1)) := by
  haveI hprob : ∀ n, IsProbabilityMeasure (convPow ρ n) := convPow_isProbabilityMeasure ρ hρ
  have hsum : HasSum (fun n => poissonPMFReal lam n) 1 := by
    simpa only [poissonPMFReal] using hasSum_one_poissonMeasure lam
  -- the convolution-power identity, written inline so that the mixture's own
  -- proof body consumes the shipped convolution exchange `charFun_conv` (R2);
  -- the standalone `charFun_convPow` above is the same induction, stated for reuse
  have hpow : ∀ n, charFun (convPow ρ n) t = charFun ρ t ^ n := by
    intro n
    induction n with
    | zero => rw [convPow, pow_zero, charFun_dirac]; simp
    | succ n ih =>
        haveI hn : IsFiniteMeasure (convPow ρ n) := convPow_isFiniteMeasure ρ hρ n
        haveI hρf : IsFiniteMeasure ρ := ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩
        rw [convPow, charFun_conv, ih, pow_succ]
  have htsum : ∀ z : ℂ, ∑' n, (poissonPMFReal lam n : ℂ) * z ^ n
      = Complex.exp ((lam : ℂ) * (z - 1)) := by
    -- the pmf in the `exp * power / factorial` shape the exponential series wants
    have hpmf : ∀ n : ℕ, poissonPMFReal lam n
        = Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (Nat.factorial n : ℝ) := by
      intro n
      unfold poissonPMFReal
      ring
    intro z
    calc ∑' n, (poissonPMFReal lam n : ℂ) * z ^ n
        = ∑' n, Complex.exp (-(lam : ℂ)) *
            (((lam : ℂ) * z) ^ n / (Nat.factorial n : ℂ)) := by
          refine tsum_congr fun n => ?_
          rw [hpmf n, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
            Complex.ofReal_natCast, Complex.ofReal_exp, Complex.ofReal_neg, mul_pow]
          ring
      _ = Complex.exp (-(lam : ℂ)) *
            ∑' n, (((lam : ℂ) * z) ^ n / (Nat.factorial n : ℂ)) :=
          tsum_mul_left
      _ = Complex.exp (-(lam : ℂ)) * Complex.exp ((lam : ℂ) * z) := by
          rw [(NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * z)).tsum_eq,
            Complex.exp_eq_exp_ℂ]
      _ = Complex.exp ((lam : ℂ) * (z - 1)) := by
          rw [← Complex.exp_add]
          congr 1
          ring
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * I)) (cpLaw lam ρ) := by
    rw [cpLaw]
    refine integrable_sum_measure (fun n => ?_) ?_
    · haveI hn : IsProbabilityMeasure (convPow ρ n) := hprob n
      haveI hf : IsFiniteMeasure (ENNReal.ofReal (poissonPMFReal lam n) • convPow ρ n) :=
        ⟨by rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
            exact ENNReal.ofReal_lt_top⟩
      refine Integrable.of_bound ?_ 1 (ae_of_all _ fun x => ?_)
      · have hinner : Continuous fun x : ℝ => t * x * I := by
          refine Continuous.mul ?_ continuous_const
          exact Continuous.mul continuous_const Complex.continuous_ofReal
        exact (Complex.continuous_exp.comp hinner).measurable.aestronglyMeasurable
      · have hre : (t * x * I).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
        show ‖Complex.exp (t * x * I)‖ ≤ 1
        rw [Complex.norm_exp, hre]
        simp
    · have hterm : ∀ n, ∫ x : ℝ, ‖Complex.exp (t * x * I)‖
            ∂(ENNReal.ofReal (poissonPMFReal lam n) • convPow ρ n) = poissonPMFReal lam n := by
        intro n
        haveI : IsFiniteMeasure (convPow ρ n) := convPow_isFiniteMeasure ρ hρ n
        haveI : IsProbabilityMeasure (convPow ρ n) := hprob n
        have hone : (∫ x : ℝ, ‖Complex.exp (t * x * I)‖ ∂(convPow ρ n)) = 1 := by
          have hcongr : (fun x : ℝ => ‖Complex.exp (t * x * I)‖) = fun _ : ℝ => (1 : ℝ) := by
            funext x
            have hre : (t * x * I).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
            rw [Complex.norm_exp, hre, Real.exp_zero]
          rw [hcongr, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
            one_smul]
        rw [integral_smul_measure,
          ENNReal.toReal_ofReal (show (0 : ℝ) ≤ poissonPMFReal lam n from poissonPMFReal_nonneg),
          smul_eq_mul, hone, mul_one]
      simp_rw [hterm]
      exact hsum.summable
  rw [cpLaw, charFun_apply_real, integral_sum_measure hint]
  have hterm : ∀ n, (∫ x : ℝ, Complex.exp (t * x * I)
        ∂(ENNReal.ofReal (poissonPMFReal lam n) • convPow ρ n))
      = (poissonPMFReal lam n : ℂ) * charFun ρ t ^ n := by
    intro n
    haveI : IsFiniteMeasure (convPow ρ n) := convPow_isFiniteMeasure ρ hρ n
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ poissonPMFReal lam n from poissonPMFReal_nonneg),
      Complex.real_smul, ← charFun_apply_real, hpow n]
  simp_rw [hterm]
  exact htsum (charFun ρ t)

/-!
---------------------------------------------------------------------------
§2  The truncated CGMY jump law, and its marginal
---------------------------------------------------------------------------
-/

/-- **The truncated CGMY jump measure**: the landed `cgmyLevyDensity` as a
density over the **symmetric** truncation `{x | ε ≤ |x|}` of Lebesgue measure.
That single set-builder is the whole convention, and it is the version
BRIEF_019 requires: the one-sided truncation is the version whose near-zero
`i v x` piece has no cancellation partner and whose limit diverges for `Y ≥ 1`. -/
noncomputable def cgmyJumpMeasure (C G M Y : ℝ) (ε : ℝ≥0) : Measure ℝ :=
  (volume.restrict {x : ℝ | (ε : ℝ) ≤ |x|}).withDensity
    (fun x => ENNReal.ofReal (cgmyLevyDensity C G M Y x))

/-- **The truncated CGMY jump law**: the truncated measure `ν_ε` normalised by
its mass `λ_ε = ν_ε(ℝ)`. It is a probability measure by
`cgmyJumpMass_lt_top` and `cgmyJumpMass_pos` — the first law in the tree whose
law-level statement is a truncation of the CGMY Levy density rather than a
closed-form density or a difference of Gamma laws. -/
noncomputable def cgmyJumpLaw (C G M Y : ℝ) (ε : ℝ≥0) : Measure ℝ :=
  (cgmyJumpMeasure C G M Y ε Set.univ)⁻¹ • cgmyJumpMeasure C G M Y ε

/-- **The truncated mass `λ_ε = ν_ε(ℝ)` is finite.** The density is read off
`withDensity_apply` at `univ`, and the symmetric truncation set is covered by
three pieces: the far positive tail `Ioi 1`, the window `Icc (−1) 1`, and the
far negative tail `Iic (−1)`. The two **tails** are dominated by the landed
far-field moment `cgmy_levy_far_moment` — the positive one at the tempering rate
`M` (already the density's own rate on `x > 0`), the mirror one at the rate `G`
after the substitution `x ↦ −x` — so far-field integrability is *inherited*
rather than re-derived. The **window** is where the truncation is load bearing:
there `ε ≤ |x| ≤ 1` makes the density at most `C ε^{−1−Y}`, and
`setLIntegral_const` bounds the lintegral by that constant times the finite
volume `volume (Icc (−1) 1) = 2`. -/
theorem cgmyJumpMass_lt_top (C G M Y : ℝ) (ε : ℝ≥0) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hε : 0 < ε) :
    cgmyJumpMeasure C G M Y ε Set.univ < ⊤ := by
  rw [cgmyJumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hset : MeasurableSet {x : ℝ | (ε : ℝ) ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  -- (i) the far positive tail: the landed far-field moment, at the density's own rate
  have hfarM : IntegrableOn (fun x : ℝ => C * (Real.exp (-M * x) * x ^ (-1 - Y))) (Ioi 1) := by
    simpa only [sub_zero] using cgmy_levy_far_moment C M Y 0 hC hY hM
  have hfarM_nn : ∀ᵐ x ∂(volume.restrict (Ioi 1)),
      0 ≤ C * (Real.exp (-M * x) * x ^ (-1 - Y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hC.le (mul_nonneg (Real.exp_nonneg _)
      (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _))
  have p₁ : ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Ioi 1,
      ENNReal.ofReal (cgmyLevyDensity C G M Y x) < ⊤ := by
    calc ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Ioi 1,
          ENNReal.ofReal (cgmyLevyDensity C G M Y x)
        ≤ ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Ioi 1,
            ENNReal.ofReal (C * (Real.exp (-M * x) * x ^ (-1 - Y))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hset.inter measurableSet_Ioi)] with x hx
          have hx0 : 0 < x := lt_trans zero_lt_one hx.2
          refine ENNReal.ofReal_le_ofReal ?_
          rw [cgmyLevyDensity_pos_of_pos hx0]
          exact le_of_eq (by ring)
      _ ≤ ∫⁻ x in Ioi 1,
            ENNReal.ofReal (C * (Real.exp (-M * x) * x ^ (-1 - Y))) :=
          lintegral_mono_set (Set.inter_subset_right)
      _ = ENNReal.ofReal (∫ x in Ioi 1, C * (Real.exp (-M * x) * x ^ (-1 - Y))) :=
          (ofReal_integral_eq_lintegral_ofReal hfarM hfarM_nn).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- (ii) the far negative tail: the mirror exponential, dominated on `-x ≥ 1`
  have hmir : IntegrableOn (fun x : ℝ => C * Real.exp (G * x)) (Iic (-1)) :=
    (integrableOn_exp_mul_Iic hG (-1)).const_mul C
  have hmir_nn : ∀ᵐ x ∂(volume.restrict (Iic (-1))), 0 ≤ C * Real.exp (G * x) :=
    ae_of_all _ fun x => mul_nonneg hC.le (Real.exp_nonneg (G * x))
  have p₃ : ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Iic (-1),
      ENNReal.ofReal (cgmyLevyDensity C G M Y x) < ⊤ := by
    calc ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Iic (-1),
          ENNReal.ofReal (cgmyLevyDensity C G M Y x)
        ≤ ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Iic (-1),
            ENNReal.ofReal (C * Real.exp (G * x)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hset.inter measurableSet_Iic)] with x hx
          have hx0 : x < 0 := lt_of_le_of_lt hx.2 (by norm_num)
          refine ENNReal.ofReal_le_ofReal ?_
          rw [cgmyLevyDensity_neg_of_neg hx0]
          calc C * Real.exp (G * x) * (-x) ^ (-1 - Y)
              ≤ C * Real.exp (G * x) * 1 :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.2]) (by linarith))
                  (mul_nonneg hC.le (Real.exp_nonneg _))
            _ = C * Real.exp (G * x) := by ring
      _ ≤ ∫⁻ x in Iic (-1), ENNReal.ofReal (C * Real.exp (G * x)) :=
          lintegral_mono_set (Set.inter_subset_right)
      _ = ENNReal.ofReal (∫ x in Iic (-1), C * Real.exp (G * x)) :=
          (ofReal_integral_eq_lintegral_ofReal hmir hmir_nn).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- the window: the truncation alone bounds the density
  have p₂ : ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1,
      ENNReal.ofReal (cgmyLevyDensity C G M Y x) < ⊤ := by
    have hvol : volume ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1) < ⊤ := by
      refine lt_of_le_of_lt (measure_mono (inter_subset_right)) ?_
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have hbound : ∀ x ∈ {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1,
        cgmyLevyDensity C G M Y x ≤ C * (ε : ℝ) ^ (-1 - Y) := by
      intro x hx
      obtain ⟨hxs, hxi⟩ := hx
      have hxabs : (ε : ℝ) ≤ |x| := hxs
      have hx1 : |x| ≤ 1 := abs_le.mpr hxi
      have hpow : |x| ^ (-1 - Y) ≤ (ε : ℝ) ^ (-1 - Y) :=
        Real.rpow_le_rpow_of_nonpos hε hxabs (by linarith)
      have hexp1 : Real.exp (-(if 0 < x then M else G) * |x|) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hif : 0 < (if 0 < x then M else G) := by
          by_cases hx0 : 0 < x
          · rwa [if_pos hx0]
          · rwa [if_neg hx0]
        nlinarith [abs_nonneg x]
      rw [cgmyLevyDensity]
      calc C * Real.exp (-(if 0 < x then M else G) * |x|) * |x| ^ (-1 - Y)
          ≤ C * 1 * (ε : ℝ) ^ (-1 - Y) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hexp1 hC.le) hpow
              (Real.rpow_nonneg (abs_nonneg x) _) (mul_nonneg hC.le zero_le_one)
        _ = C * (ε : ℝ) ^ (-1 - Y) := by ring
    calc ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1,
          ENNReal.ofReal (cgmyLevyDensity C G M Y x)
        ≤ ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1,
            ENNReal.ofReal (C * (ε : ℝ) ^ (-1 - Y)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (hset.inter measurableSet_Icc)] with x hx
          exact ENNReal.ofReal_le_ofReal (hbound x hx)
      _ = ENNReal.ofReal (C * (ε : ℝ) ^ (-1 - Y)) *
            volume ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1) := by
          rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol
  -- cover the truncation set by the three pieces
  have hcover : {x : ℝ | (ε : ℝ) ≤ |x|} ⊆
      ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Ioi 1) ∪
        (({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1) ∪
          ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Iic (-1))) := by
    intro x hx
    have hxabs : (ε : ℝ) ≤ |x| := by simpa using hx
    rcases lt_or_ge x 0 with hx0 | hx0
    · rw [abs_of_neg hx0] at hxabs
      rcases lt_or_ge (-1) x with hx1 | hx1
      · exact Or.inr (Or.inl ⟨hx, ⟨hx1.le, by linarith⟩⟩)
      · exact Or.inr (Or.inr ⟨hx, hx1⟩)
    · rw [abs_of_nonneg hx0] at hxabs
      rcases lt_or_ge 1 x with hx1 | hx1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (Or.inl ⟨hx, ⟨by linarith, hx1⟩⟩)
  calc ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|}, ENNReal.ofReal (cgmyLevyDensity C G M Y x)
      ≤ ∫⁻ x in ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Ioi 1) ∪
          (({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1) ∪
            ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Iic (-1))),
          ENNReal.ofReal (cgmyLevyDensity C G M Y x) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Ioi 1,
            ENNReal.ofReal (cgmyLevyDensity C G M Y x)) +
        ∫⁻ x in ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1) ∪
            ({x : ℝ | (ε : ℝ) ≤ |x|} ∩ Iic (-1)),
          ENNReal.ofReal (cgmyLevyDensity C G M Y x) :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Ioi 1,
            ENNReal.ofReal (cgmyLevyDensity C G M Y x)) +
        ((∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Icc (-1) 1,
            ENNReal.ofReal (cgmyLevyDensity C G M Y x)) +
          ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|} ∩ Iic (-1),
            ENNReal.ofReal (cgmyLevyDensity C G M Y x)) :=
        add_le_add le_rfl (lintegral_union_le _ _ _)
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨p₁, ENNReal.add_lt_top.mpr ⟨p₂, p₃⟩⟩

/-- **The truncated mass `λ_ε = ν_ε(ℝ)` is positive.** The density is positive
*everywhere* off the origin, so on the window `Ioc ε (ε+1)` — inside the
positive leg — it is bounded below by the positive constant
`C e^{−M(ε+1)} (ε+1)^{−1−Y}`, whose lintegral over that window is that constant
times `volume (Ioc ε (ε+1)) = 1`. Only one window is needed: the set inclusion
`Ioc ε (ε+1) ⊆ {x | ε ≤ |x|}` is where the symmetric truncation enters, and no
other leg is inspected. -/
theorem cgmyJumpMass_pos (C G M Y : ℝ) (ε : ℝ≥0) (hC : 0 < C) (hM : 0 < M) (hY : 0 < Y)
    (hε : 0 < ε) :
    0 < cgmyJumpMeasure C G M Y ε Set.univ := by
  rw [cgmyJumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hbase : (0 : ℝ) < C * Real.exp (-(M * ((ε : ℝ) + 1))) * ((ε : ℝ) + 1) ^ (-1 - Y) :=
    mul_pos (mul_pos hC (Real.exp_pos _))
      (Real.rpow_pos_of_pos (by linarith [NNReal.coe_nonneg ε]) _)
  have hwin : (0 : ℝ≥0∞) < ∫⁻ _ in Ioc (ε : ℝ) ((ε : ℝ) + 1),
      ENNReal.ofReal (C * Real.exp (-(M * ((ε : ℝ) + 1))) * ((ε : ℝ) + 1) ^ (-1 - Y)) := by
    rw [setLIntegral_const, Real.volume_Ioc,
      show (ε : ℝ) + 1 - (ε : ℝ) = 1 by ring, ENNReal.ofReal_one, mul_one]
    exact ENNReal.ofReal_pos.mpr hbase
  refine lt_of_lt_of_le hwin ?_
  calc ∫⁻ x in Ioc (ε : ℝ) ((ε : ℝ) + 1),
        ENNReal.ofReal (C * Real.exp (-(M * ((ε : ℝ) + 1))) * ((ε : ℝ) + 1) ^ (-1 - Y))
      ≤ ∫⁻ x in Ioc (ε : ℝ) ((ε : ℝ) + 1), ENNReal.ofReal (cgmyLevyDensity C G M Y x) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        refine ENNReal.ofReal_le_ofReal ?_
        have hx0 : 0 < x := lt_of_le_of_lt (NNReal.coe_nonneg ε) hx.1
        have hexp : Real.exp (-(M * ((ε : ℝ) + 1))) ≤ Real.exp (-M * x) :=
          Real.exp_le_exp.mpr (by nlinarith [hx.2, hM])
        have hpow : ((ε : ℝ) + 1) ^ (-1 - Y) ≤ x ^ (-1 - Y) :=
          Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith)
        rw [cgmyLevyDensity_pos_of_pos hx0]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hC.le) hpow
          (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (ε : ℝ) + 1) _)
          (mul_nonneg hC.le (Real.exp_nonneg _))
    _ ≤ ∫⁻ x in {x : ℝ | (ε : ℝ) ≤ |x|}, ENNReal.ofReal (cgmyLevyDensity C G M Y x) := by
        refine lintegral_mono_set ?_
        intro x hx
        simp only [mem_Ioc] at hx
        show (ε : ℝ) ≤ |x|
        rw [abs_of_pos (lt_of_le_of_lt (NNReal.coe_nonneg ε) hx.1)]
        exact hx.1.le

/-- **The truncated jump law is a probability measure**: the mass of a scalar
multiple is the scalar times the mass (`Measure.smul_apply`), which is
`λ_ε⁻¹ · λ_ε = 1` once `λ_ε` is positive and finite. -/
theorem cgmyJumpLaw_isProbabilityMeasure (C G M Y : ℝ) (ε : ℝ≥0) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hε : 0 < ε) :
    IsProbabilityMeasure (cgmyJumpLaw C G M Y ε) := by
  have hlt : cgmyJumpMeasure C G M Y ε Set.univ < ⊤ :=
    cgmyJumpMass_lt_top C G M Y ε hC hG hM hY hε
  have hpos : 0 < cgmyJumpMeasure C G M Y ε Set.univ :=
    cgmyJumpMass_pos C G M Y ε hC hM hY hε
  refine ⟨?_⟩
  rw [cgmyJumpLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hlt.ne

/-- **The truncated exponent**: `∫_{|x| ≥ ε} (e^{ivx} − 1) ν(dx)` over the
symmetric truncation set — the object Stage 2b takes to `cgmyExponent`. There is
no compensator: the `− v x I` piece is the *other* convention, whose value is
this one minus `i v m^∞`, a translated law rather than the tree's exponent. -/
noncomputable def cgmyTruncatedExponent (C G M Y : ℝ) (ε : ℝ≥0) (v : ℂ) : ℂ :=
  ∫ x in {x : ℝ | (ε : ℝ) ≤ |x|},
    (Complex.exp (v * (x : ℂ) * I) - 1) * (cgmyLevyDensity C G M Y x : ℂ)

/-- **The truncated exponent is an absolutely convergent Bochner integral** —
and only *because* of the truncation: the near-zero density is not integrable
(`λ_ε = ν({|x| ≥ ε}) → ∞` like `2C/Y · ε^{−Y}`, measured `665216.62` against
`666666.67` at `Y = 3/2`, `ε = 10⁻⁴`), but on the truncated set
`‖e^{ivx} − 1‖ ≤ 2`, so the integrand is dominated by `2 ν`, whose integral over
that set is finite by `cgmyJumpMass_lt_top`. This is the honest reason the route
truncates, and why the `ε ↓ 0` step is a conditional-convergence argument
rather than dominated convergence (BRIEF_019 F3, ledger C22). -/
theorem cgmyTruncatedExponent_integrable (C G M Y : ℝ) (ε : ℝ≥0) (hC : 0 < C) (hG : 0 < G)
    (hM : 0 < M) (hY : 0 < Y) (hε : 0 < ε) (v : ℝ) :
    IntegrableOn (fun x : ℝ =>
        (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1) * (cgmyLevyDensity C G M Y x : ℂ))
      {x : ℝ | (ε : ℝ) ≤ |x|} := by
  have hd_meas : Measurable fun x : ℝ => cgmyLevyDensity C G M Y x := by
    unfold cgmyLevyDensity
    refine (measurable_const.mul ?_).mul ?_
    · refine Real.continuous_exp.measurable.comp ?_
      exact (Measurable.ite (p := fun x : ℝ => 0 < x) measurableSet_Ioi measurable_const
        measurable_const).neg.mul continuous_abs.measurable
    · exact measurable_of_continuousOn_compl_singleton 0 (by
        refine ContinuousOn.rpow_const continuous_abs.continuousOn fun x hx => Or.inl ?_
        simp only [mem_compl_iff, mem_singleton_iff] at hx
        exact (abs_pos.mpr hx).ne')
  have hset : MeasurableSet {x : ℝ | (ε : ℝ) ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hmass := cgmyJumpMass_lt_top C G M Y ε hC hG hM hY hε
  rw [cgmyJumpMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  have hd_int : IntegrableOn (fun x : ℝ => cgmyLevyDensity C G M Y x)
      {x : ℝ | (ε : ℝ) ≤ |x|} :=
    ⟨hd_meas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => cgmyLevyDensity_nonneg hC.le x)).mpr
        hmass⟩
  have hcont : Continuous fun x : ℝ => Complex.exp ((v : ℂ) * (x : ℂ) * I) :=
    Complex.continuous_exp.comp
      (Continuous.mul (continuous_const.mul Complex.continuous_ofReal) continuous_const)
  have hf_meas : Measurable fun x : ℝ =>
      (Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1) * (cgmyLevyDensity C G M Y x : ℂ) :=
    (hcont.measurable.sub measurable_const).mul
      (Complex.continuous_ofReal.measurable.comp hd_meas)
  refine Integrable.mono' (hd_int.const_mul 2) hf_meas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hset] with x _hx
  have hnrm : ‖Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1‖ ≤ 2 := by
    have h1 : ‖Complex.exp ((v : ℂ) * (x : ℂ) * I)‖ = 1 := by
      have hre : ((v : ℂ) * (x : ℂ) * I).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
      rw [Complex.norm_exp, hre, Real.exp_zero]
    calc ‖Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1‖
        ≤ ‖Complex.exp ((v : ℂ) * (x : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, norm_one]; norm_num
  calc ‖(Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1) * (cgmyLevyDensity C G M Y x : ℂ)‖
      = ‖Complex.exp ((v : ℂ) * (x : ℂ) * I) - 1‖ * cgmyLevyDensity C G M Y x := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (cgmyLevyDensity_nonneg hC.le x)]
    _ ≤ 2 * cgmyLevyDensity C G M Y x :=
        mul_le_mul_of_nonneg_right hnrm (cgmyLevyDensity_nonneg hC.le x)

/-- The truncated exponent vanishes at `v = 0`: the integrand is
`(1 − 1) · density`, so the integral is zero. This is the sanity the
characteristic function needs — `charFun` at `t = 0` must be `exp 0 = 1`. -/
theorem cgmyTruncatedExponent_zero (C G M Y : ℝ) (ε : ℝ≥0) :
    cgmyTruncatedExponent C G M Y ε 0 = 0 := by
  simp [cgmyTruncatedExponent]

/-- **The truncated compound-Poisson marginal**: the compound-Poisson law of the
truncated jump law at rate `τ λ_ε` has characteristic function
`exp (τ · cgmyTruncatedExponent … t)`. The two cancellations are the point of
the statement: the law is the *normalised* `ν_ε/λ_ε` — so its own exponent is
the normalised integral `∫(e^{itx} − 1) ν_ε(dx)/λ_ε` — while the rate carries
the compensating `λ_ε`, leaving the *unnormalised* Bochner integral over the
truncation set, BRIEF_019's `A_ε`, the object Stage 2b takes to `cgmyExponent`
at `τ = 1`. -/
theorem charFun_cgmyCpLaw (C G M Y : ℝ) (ε : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hM : 0 < M)
    (hY : 0 < Y) (hε : 0 < ε) (τ : ℝ≥0) (t : ℝ) :
    charFun (cpLaw (τ * (cgmyJumpMeasure C G M Y ε Set.univ).toNNReal)
        (cgmyJumpLaw C G M Y ε)) t
      = Complex.exp ((τ : ℂ) * cgmyTruncatedExponent C G M Y ε (t : ℂ)) := by
  have hprob : IsProbabilityMeasure (cgmyJumpLaw C G M Y ε) :=
    cgmyJumpLaw_isProbabilityMeasure C G M Y ε hC hG hM hY hε
  have hmass_lt : cgmyJumpMeasure C G M Y ε Set.univ < ⊤ :=
    cgmyJumpMass_lt_top C G M Y ε hC hG hM hY hε
  have hmass_pos : 0 < cgmyJumpMeasure C G M Y ε Set.univ :=
    cgmyJumpMass_pos C G M Y ε hC hM hY hε
  have hmass_ne_top : cgmyJumpMeasure C G M Y ε Set.univ ≠ ⊤ := hmass_lt.ne
  have hmass_ne : cgmyJumpMeasure C G M Y ε Set.univ ≠ 0 := hmass_pos.ne'
  have hmassreal_pos : 0 < (cgmyJumpMeasure C G M Y ε Set.univ).toReal :=
    ENNReal.toReal_pos hmass_ne hmass_ne_top
  have hmassreal_ne : ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ) ≠ 0 := by
    simpa using ne_of_gt hmassreal_pos
  -- the density's measurability, then the two integral bridges
  have hd_meas : Measurable fun x : ℝ => cgmyLevyDensity C G M Y x := by
    unfold cgmyLevyDensity
    refine (measurable_const.mul ?_).mul ?_
    · refine Real.continuous_exp.measurable.comp ?_
      exact (Measurable.ite (p := fun x : ℝ => 0 < x) measurableSet_Ioi measurable_const
        measurable_const).neg.mul continuous_abs.measurable
    · exact measurable_of_continuousOn_compl_singleton 0 (by
        refine ContinuousOn.rpow_const continuous_abs.continuousOn fun x hx => Or.inl ?_
        simp only [mem_compl_iff, mem_singleton_iff] at hx
        exact (abs_pos.mpr hx).ne')
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (cgmyLevyDensity C G M Y x) :=
    ENNReal.continuous_ofReal.measurable.comp hd_meas
  haveI : IsFiniteMeasure (cgmyJumpMeasure C G M Y ε) := ⟨hmass_lt⟩
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * I)) (cgmyJumpMeasure C G M Y ε) := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun x => ?_)
    · have hinner : Continuous fun x : ℝ => t * x * I := by
        refine Continuous.mul ?_ continuous_const
        exact Continuous.mul continuous_const Complex.continuous_ofReal
      exact (Complex.continuous_exp.comp hinner).measurable.aestronglyMeasurable
    · have hre : (t * x * I).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
      show ‖Complex.exp (t * x * I)‖ ≤ 1
      rw [Complex.norm_exp, hre]
      simp
  have hone : Integrable (fun _ : ℝ => (1 : ℂ)) (cgmyJumpMeasure C G M Y ε) :=
    integrable_const 1
  -- the jump law's characteristic function is the normalised integral
  have hchar : charFun (cgmyJumpLaw C G M Y ε) t
      = ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)⁻¹ *
        ∫ x, Complex.exp (t * x * I) ∂(cgmyJumpMeasure C G M Y ε) := by
    rw [cgmyJumpLaw, charFun_apply_real, integral_smul_measure, ENNReal.toReal_inv,
      Complex.real_smul, Complex.ofReal_inv]
  -- the total mass as an integral of `1`
  have hone_int : (∫ _ : ℝ, (1 : ℂ) ∂(cgmyJumpMeasure C G M Y ε))
      = ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ) := by
    rw [integral_const, measureReal_def, Complex.real_smul, mul_one]
  -- subtracting the mass leaves the honest integral
  have hsub : (∫ x, Complex.exp (t * x * I) ∂(cgmyJumpMeasure C G M Y ε))
        - ∫ _ : ℝ, (1 : ℂ) ∂(cgmyJumpMeasure C G M Y ε)
      = ∫ x, (Complex.exp (t * x * I) - 1) ∂(cgmyJumpMeasure C G M Y ε) := by
    rw [← integral_sub hint hone]
  -- the withDensity bridge: the same integral against the Lebesgue density
  have hdens : (∫ x, (Complex.exp (t * x * I) - 1) ∂(cgmyJumpMeasure C G M Y ε))
      = cgmyTruncatedExponent C G M Y ε (t : ℂ) := by
    rw [cgmyJumpMeasure,
      integral_withDensity_eq_integral_toReal_smul hmeas
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
      cgmyTruncatedExponent]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (ENNReal.ofReal (cgmyLevyDensity C G M Y x)).toReal •
        (Complex.exp (t * x * I) - 1)
      = (Complex.exp (t * x * I) - 1) * (cgmyLevyDensity C G M Y x : ℂ)
    rw [ENNReal.toReal_ofReal (cgmyLevyDensity_nonneg hC.le x), Complex.real_smul]
    ring
  -- splitting the integral at `e^{itx} = 1`: mass plus the honest integrand
  have hsplit : (∫ x, Complex.exp (t * x * I) ∂(cgmyJumpMeasure C G M Y ε))
      = ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)
        + ∫ x, (Complex.exp (t * x * I) - 1) ∂(cgmyJumpMeasure C G M Y ε) := by
    rw [← hsub, hone_int]
    ring
  -- assemble: the two normalisations cancel
  have hkey : charFun (cgmyJumpLaw C G M Y ε) t - 1
      = ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)⁻¹ *
        cgmyTruncatedExponent C G M Y ε (t : ℂ) := by
    have hA : ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)⁻¹ *
        ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ) = 1 :=
      inv_mul_cancel₀ hmassreal_ne
    rw [hchar, hsplit, hdens, mul_add, hA]
    ring
  -- the rate's own mass cancels the normalisation of the law
  have hprod : ((τ : ℂ) * ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)) *
      (((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)⁻¹ *
        cgmyTruncatedExponent C G M Y ε (t : ℂ))
      = (τ : ℂ) * cgmyTruncatedExponent C G M Y ε (t : ℂ) := by
    have hA : ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ) *
        ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ hmassreal_ne
    calc ((τ : ℂ) * ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)) *
          (((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)⁻¹ *
            cgmyTruncatedExponent C G M Y ε (t : ℂ))
        = (τ : ℂ) * (((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ) *
            ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ)⁻¹ *
              cgmyTruncatedExponent C G M Y ε (t : ℂ)) := by ring
      _ = (τ : ℂ) * (1 * cgmyTruncatedExponent C G M Y ε (t : ℂ)) := by rw [hA]
      _ = (τ : ℂ) * cgmyTruncatedExponent C G M Y ε (t : ℂ) := by ring
  have hcoe : ((τ * (cgmyJumpMeasure C G M Y ε Set.univ).toNNReal : ℝ≥0) : ℂ)
      = (τ : ℂ) * ((cgmyJumpMeasure C G M Y ε Set.univ).toReal : ℂ) := by
    have hreal : ((τ * (cgmyJumpMeasure C G M Y ε Set.univ).toNNReal : ℝ≥0) : ℝ)
        = (τ : ℝ) * (cgmyJumpMeasure C G M Y ε Set.univ).toReal := by
      rw [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal]
    have hlift : ((τ * (cgmyJumpMeasure C G M Y ε Set.univ).toNNReal : ℝ≥0) : ℂ)
        = (((τ * (cgmyJumpMeasure C G M Y ε Set.univ).toNNReal : ℝ≥0) : ℝ) : ℂ) := rfl
    rw [hlift, hreal, Complex.ofReal_mul]
  rw [charFun_cpLaw (τ * (cgmyJumpMeasure C G M Y ε Set.univ).toNNReal)
    (cgmyJumpLaw C G M Y ε) hprob t, hkey, hcoe, hprod]

end BSM
