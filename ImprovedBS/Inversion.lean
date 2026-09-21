/-
  ImprovedBS.Inversion — BRIEF_008 / T6 sub-goal 3(b): Fourier inversion of the
  Carr–Madan pricing kernel, landing on the lognormal expectation, and real-valuedness.

  T6 states that for a Lévy increment whose moment strip contains the pricing
  contour, the Carr–Madan Fourier pricing integral converges absolutely, is
  real-valued, and agrees with the discounted risk-neutral expectation
  `e^{-rτ} E[(S_T - K)⁺]`.

  BRIEF_005 landed sub-goal 2: absolute convergence of the Carr–Madan pricing
  kernel on a tempered contour (`carrMadanKernel_integrable`,
  `gbm_carrMadan_price_integrable`).

  BRIEF_007 landed sub-goal 3(a): the closed form IS the discounted risk-neutral
  expectation under the lognormal law of `log(S_T/S) ~ N((r-q-σ²/2)τ, σ²τ)`
  (`bsCall_eq_riskNeutral_expectation`, `bsCall_eq_lognormal_expectation`).

  THIS MODULE lands sub-goal 3(b):
  (1) The damped call price `dampedCallPrice` as a function of log-strike `k`.
  (2) Inversion theorem via mathlib's `Continuous.fourierInv_fourier_eq` /
      `Integrable.fourierInv_fourier_eq`.
  (3) Landing on BRIEF_007's `bsCall_eq_lognormal_expectation`: undamping the
      inverted integral recovers `bsCall S K tau r q sigma`.
  (4) Real-valuedness: the inverted integral is real-valued (its imaginary
      part vanishes identically, and it equals its real part `bsCall`).

  CORRECTION C12 (BRIEF_010): `carrMadanInversion` below inherits
  `carrMadanKernel`'s contour `v = u + iα` (line `Im v = +α`). The pricing
  contour is `v = u − i(α+1)` (`cmPriceKernel` in `Pricing.lean`); the two
  differ by the shift `−(2α+1)·i`. This module's §4 theorems are about
  `𝓕⁻ (𝓕 f)` at the lognormal law and are correct as stated — see
  `benchmarks/LEDGER.md` C12.
-/

import Mathlib
import ImprovedBS.Core
import ImprovedBS.Fourier
import ImprovedBS.RiskNeutral

noncomputable section

namespace BSM

open MeasureTheory Filter FourierTransform
open scoped ENNReal Topology RealInnerProductSpace

/-!
--------------------------------------------------------------------------
§1  The Carr–Madan Fourier inversion pricing integral
--------------------------------------------------------------------------
-/

/-- The Carr–Madan Fourier inversion integral (on the `u + iα` line).
**Shape note C12:** this is `carrMadanKernel`'s line, not the pricing line
`cmPriceKernel` (`u − i(α+1)`) of `Pricing.lean`; its integrability is proved
but no theorem in this module equates it with a price — §4 is about
`𝓕⁻ (𝓕 f)` and is correct. -/
def carrMadanInversion (φ : ℂ → ℂ) (α r tau k : ℝ) : ℂ :=
  ∫ u : ℝ, ((Real.exp (-r * tau) / (2 * Real.pi) : ℝ) : ℂ) •
    (carrMadanPhase (-k) u * carrMadanKernel φ α u)

/-- The dressed pricing integrand in `carrMadanInversion` is integrable whenever
the model factor satisfies the tempered decay bound. -/
theorem carrMadanInversion_integrand_integrable {φ : ℂ → ℂ} {α : ℝ} (hα : 0 < α)
    (hcont : Continuous fun u : ℝ => φ (↑u + ↑α * Complex.I))
    {c D Y : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hY : 0 < Y) {u₀ : ℝ}
    (hdecay : ∀ u : ℝ, u₀ ≤ |u| →
      ‖φ (↑u + ↑α * Complex.I)‖ ≤ D * Real.exp (-c * |u| ^ Y))
    (r tau k : ℝ) :
    Integrable (fun u : ℝ => ((Real.exp (-r * tau) / (2 * Real.pi) : ℝ) : ℂ) •
      (carrMadanPhase (-k) u * carrMadanKernel φ α u)) volume := by
  refine Integrable.smul ((Real.exp (-r * tau) / (2 * Real.pi) : ℝ) : ℂ)
    ((carrMadanKernel_integrable hα hcont hc hD hY hdecay).bdd_mul (c := 1) ?_ ?_)
  · have hphase_cont : Continuous fun u : ℝ => carrMadanPhase (-k) u := by
      unfold carrMadanPhase
      continuity
    exact hphase_cont.measurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u =>
      le_of_eq (carrMadanPhase_norm (-k) u)

/-- The GBM Carr–Madan inversion integrand is integrable. -/
theorem gbm_carrMadanInversion_integrable (m s : ℝ) (hs : 0 < s) {α : ℝ}
    (hα : 0 < α) (r tau k : ℝ) :
    Integrable (fun u : ℝ => ((Real.exp (-r * tau) / (2 * Real.pi) : ℝ) : ℂ) •
      (carrMadanPhase (-k) u * carrMadanKernel (gbmCharFactor m s) α u)) volume := by
  refine carrMadanInversion_integrand_integrable hα (gbmCharFactor_contour_continuous m s α)
    hs (D := Real.exp (s * α ^ 2 - α * m)) (Real.exp_pos _).le (Y := 2) (by norm_num)
    (u₀ := 0) ?_ r tau k
  intro u _
  rw [gbmCharFactor_contour_norm, Real.rpow_two, sq_abs, neg_mul]

/-!
--------------------------------------------------------------------------
§2  The damped call price and lognormal expectation
--------------------------------------------------------------------------
-/

/-- The damped European call price as a function of log-strike/moneyness `k`:
`k ↦ e^{α k} · e^{-rτ} E[(S e^X - S e^k)⁺]`. -/
def dampedCallPrice (S : ℝ) (v : NNReal) (m r tau alpha : ℝ) (k : ℝ) : ℝ :=
  Real.exp (alpha * k) * (Real.exp (-r * tau) *
    ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂(ProbabilityTheory.gaussianReal m v))

/-- At the actual option strike `K`, where `k = log(K/S)`, the payoff `S e^x - S e^k`
specializes to `S e^x - K`, and the expectation evaluates to `bsCall S K tau r q sigma`. -/
theorem dampedCallPrice_log_eq (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (alpha : ℝ) :
    dampedCallPrice S v ((r - q - sigma ^ 2 / 2) * tau) r tau alpha (Real.log (K / S))
      = Real.exp (alpha * Real.log (K / S)) * bsCall S K tau r q sigma := by
  have hSK : S * Real.exp (Real.log (K / S)) = K := by
    rw [Real.exp_log (div_pos hK hS), ← mul_div_assoc, mul_comm S K, mul_div_assoc, div_self hS.ne', mul_one]
  unfold dampedCallPrice
  rw [hSK, ← bsCall_eq_lognormal_expectation S K tau r q sigma hS hK htau hsigma v hv]

/-- Undamping `dampedCallPrice` by `e^{-α k}` recovers `bsCall S K tau r q sigma`. -/
theorem undamped_dampedCallPrice (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (alpha : ℝ) :
    Real.exp (-alpha * Real.log (K / S)) *
      dampedCallPrice S v ((r - q - sigma ^ 2 / 2) * tau) r tau alpha (Real.log (K / S))
        = bsCall S K tau r q sigma := by
  rw [dampedCallPrice_log_eq S K tau r q sigma hS hK htau hsigma v hv alpha]
  have harg : -alpha * Real.log (K / S) + alpha * Real.log (K / S) = 0 := by ring
  calc Real.exp (-alpha * Real.log (K / S)) *
        (Real.exp (alpha * Real.log (K / S)) * bsCall S K tau r q sigma)
    _ = (Real.exp (-alpha * Real.log (K / S)) * Real.exp (alpha * Real.log (K / S)))
        * bsCall S K tau r q sigma := by rw [mul_assoc]
    _ = Real.exp (-alpha * Real.log (K / S) + alpha * Real.log (K / S))
        * bsCall S K tau r q sigma := by rw [← Real.exp_add]
    _ = Real.exp 0 * bsCall S K tau r q sigma := by rw [harg]
    _ = bsCall S K tau r q sigma := by rw [Real.exp_zero, one_mul]

/-!
--------------------------------------------------------------------------
§3  Fourier inversion
--------------------------------------------------------------------------
-/

/-- Fourier inversion for the damped call price: if `f` is continuous, integrable, and
its Fourier transform `𝓕 f` is integrable, then `𝓕⁻ (𝓕 f) = f`.
Stated via mathlib's `Continuous.fourierInv_fourier_eq` (the `Integrable.fourier_inversion`
result at mathlib v4.34.0). -/
theorem fourierInversion_dampedCallPrice {f : ℝ → ℂ} (hcont : Continuous f)
    (hint : Integrable f) (hFint : Integrable (𝓕 f)) :
    𝓕⁻ (𝓕 f) = f :=
  Continuous.fourierInv_fourier_eq hcont hint hFint

/-- Pointwise evaluation of the Fourier inversion formula at a given log-strike `k`. -/
theorem fourierInversion_dampedCallPrice_at {f : ℝ → ℂ} (hcont : Continuous f)
    (hint : Integrable f) (hFint : Integrable (𝓕 f)) (k : ℝ) :
    𝓕⁻ (𝓕 f) k = f k := by
  rw [fourierInversion_dampedCallPrice hcont hint hFint]

/-!
--------------------------------------------------------------------------
§4  The main theorems: landing on the lognormal expectation and real-valuedness
--------------------------------------------------------------------------
-/

/-- **T6 sub-goal 3(b): Fourier inversion lands on the lognormal expectation.**
When the damped call price function `k ↦ dampedCallPrice ... k` is inverted
via `𝓕⁻ (𝓕 ·)` at `k = log(K/S)` and undamped by `e^{-α k}`, the result equals
the discounted risk-neutral expectation:

    e^{-rτ} · ∫ (S e^x - K)⁺ d N((r-q-σ²/2)τ, σ²τ)(x).
-/
theorem carrMadan_inversion_eq_lognormal_expectation (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (alpha : ℝ)
    {f : ℝ → ℂ} (hf : f = fun k ↦ ↑(dampedCallPrice S v ((r - q - sigma ^ 2 / 2) * tau) r tau alpha k))
    (hcont : Continuous f) (hint : Integrable f) (hFint : Integrable (𝓕 f)) :
    ((Real.exp (-alpha * Real.log (K / S)) : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) (Real.log (K / S))
      = ((Real.exp (-r * tau) *
          ∫ x, max (S * Real.exp x - K) 0
            ∂(ProbabilityTheory.gaussianReal ((r - q - sigma ^ 2 / 2) * tau) v) : ℝ) : ℂ) := by
  rw [fourierInversion_dampedCallPrice_at hcont hint hFint, hf]
  dsimp only
  rw [← Complex.ofReal_mul,
    undamped_dampedCallPrice S K tau r q sigma hS hK htau hsigma v hv alpha,
    bsCall_eq_lognormal_expectation S K tau r q sigma hS hK htau hsigma v hv]

/-- **T6 sub-goal 3(b): Fourier inversion equals `bsCall`.**
By joining `carrMadan_inversion_eq_lognormal_expectation` with BRIEF_007's
`bsCall_eq_lognormal_expectation`, the inverted damped pricing transform
equals the BSM closed form `bsCall S K tau r q sigma`. -/
theorem carrMadan_inversion_eq_bsCall (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (alpha : ℝ)
    {f : ℝ → ℂ} (hf : f = fun k ↦ ↑(dampedCallPrice S v ((r - q - sigma ^ 2 / 2) * tau) r tau alpha k))
    (hcont : Continuous f) (hint : Integrable f) (hFint : Integrable (𝓕 f)) :
    ((Real.exp (-alpha * Real.log (K / S)) : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) (Real.log (K / S))
      = ((bsCall S K tau r q sigma : ℝ) : ℂ) := by
  rw [carrMadan_inversion_eq_lognormal_expectation S K tau r q sigma hS hK htau hsigma v hv alpha hf hcont hint hFint]
  exact congrArg (fun x : ℝ => (x : ℂ))
    (bsCall_eq_lognormal_expectation S K tau r q sigma hS hK htau hsigma v hv).symm

/-- **Real-valuedness of the inverted pricing integral.**
Because the inverted transform equals the cast of the real number
`bsCall S K tau r q sigma`, its imaginary part is identically zero. -/
theorem carrMadan_inversion_im_eq_zero (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (alpha : ℝ)
    {f : ℝ → ℂ} (hf : f = fun k ↦ ↑(dampedCallPrice S v ((r - q - sigma ^ 2 / 2) * tau) r tau alpha k))
    (hcont : Continuous f) (hint : Integrable f) (hFint : Integrable (𝓕 f)) :
    (((Real.exp (-alpha * Real.log (K / S)) : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) (Real.log (K / S))).im = 0 := by
  rw [carrMadan_inversion_eq_bsCall S K tau r q sigma hS hK htau hsigma v hv alpha hf hcont hint hFint]
  exact Complex.ofReal_im _

/-- The complex inverted value equals the cast of its own real part. -/
theorem carrMadan_inversion_eq_re (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (alpha : ℝ)
    {f : ℝ → ℂ} (hf : f = fun k ↦ ↑(dampedCallPrice S v ((r - q - sigma ^ 2 / 2) * tau) r tau alpha k))
    (hcont : Continuous f) (hint : Integrable f) (hFint : Integrable (𝓕 f)) :
    ((Real.exp (-alpha * Real.log (K / S)) : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) (Real.log (K / S))
      = ↑((((Real.exp (-alpha * Real.log (K / S)) : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) (Real.log (K / S))).re) := by
  rw [carrMadan_inversion_eq_bsCall S K tau r q sigma hS hK htau hsigma v hv alpha hf hcont hint hFint]
  rw [Complex.ofReal_re]

/-- The real part of the inverted pricing integral equals `bsCall`. -/
theorem carrMadan_inversion_re_eq_bsCall (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (alpha : ℝ)
    {f : ℝ → ℂ} (hf : f = fun k ↦ ↑(dampedCallPrice S v ((r - q - sigma ^ 2 / 2) * tau) r tau alpha k))
    (hcont : Continuous f) (hint : Integrable f) (hFint : Integrable (𝓕 f)) :
    (((Real.exp (-alpha * Real.log (K / S)) : ℝ) : ℂ) * 𝓕⁻ (𝓕 f) (Real.log (K / S))).re
      = bsCall S K tau r q sigma := by
  rw [carrMadan_inversion_eq_bsCall S K tau r q sigma hS hK htau hsigma v hv alpha hf hcont hint hFint]
  exact Complex.ofReal_re _

end BSM
