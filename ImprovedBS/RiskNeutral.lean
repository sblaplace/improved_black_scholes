/-
  ImprovedBS/RiskNeutral.lean — BRIEF_007: T6 sub-goal 3(a), the GBM instance
  of "the Fourier price agrees with the risk-neutral expectation".

  What this file proves, in one line each:

    bsCall S K τ r q σ = e^{-rτ} · ∫ max (S·e^{(r-q-σ²/2)τ + σ√τ·z} - K) 0 · φ(z) dz
    bsPut  S K τ r q σ = e^{-rτ} · ∫ max (K - S·e^{(r-q-σ²/2)τ + σ√τ·z}) 0 · φ(z) dz

  for `0 < S`, `0 < K`, `0 < τ`, `0 < σ`, together with the same identity read
  against mathlib's probability measures: the standard normal law
  `gaussianReal 0 1` of the driving noise (`bsCall_eq_gaussianReal_expectation`)
  and the lognormal law `gaussianReal ((r-q-σ²/2)τ) (σ²τ)` of `log S_T`
  (`bsCall_eq_lognormal_expectation`). The closed form of `Core.lean` IS the
  discounted risk-neutral expectation `e^{-rτ} E[(S_T - K)⁺]`, and the
  martingale/drift condition `E[S_T] = S e^{(r-q)τ}` is a theorem too
  (`integral_spot_mul_phi_eq_forward`).

  Why this is the GBM instance of T6(3) and not T6(3) itself: docs/03 §D1
  states T6 as "the Carr–Madan integral is absolutely convergent (BRIEF_005),
  real-valued, and agrees with `e^{-rτ} E[(S_T - K)⁺]`". The agreement claim has
  two halves. This file establishes the right-hand side — the pricing
  expectation as a concrete, machine-checked integral against the law of the
  log-price — and shows the closed form equals it. The left-hand side, Fourier
  inversion of the damped call transform back onto that expectation, is
  sub-goal 3(b) and is deliberately out of scope here (see the brief).

  Why `phi`/`Phi` are NOT migrated to mathlib's Gaussian. BRIEF_006 left the
  migration as a T6 question. The answer taken here is a *bridge*, not a
  migration: `phi_eq_gaussianPDFReal`, `Phi_eq_gaussianReal_Iic` and
  `integral_gaussianReal_eq_integral_mul_phi` identify the repository's `phi`
  and `Phi` with `gaussianPDFReal 0 1` and `gaussianReal 0 1 (Iic ·)` once and
  for all, so that every T1–T5 statement keeps the definitions it was pinned
  against (`tests/golden_statements.json`) while every probabilistic statement
  from here on can be written against mathlib's measures. Rewriting the
  definitions would have moved 60 pinned statements to say something nominally
  different; proving the bridge moves nothing.

  Design rules inherited from BRIEF_003–006 and applied here:
  * the numeric route was checked in Python before any Lean was written
    (ledger C4): the four identities below hold to 1e-14 on the oracle grid, and
    with `σ < 0` the closed form is `-bsPut`, not the expectation — which is
    why `0 < σ` (not `σ ≠ 0`) is the hypothesis;
  * every mathlib name below was read in the v4.34.0 source before pushing
    (ledger C3); the file is CI-compiled only, this tree has no toolchain;
  * pointwise identities are stated as explicit `∀ z, …` facts and moved under
    the integral with `integral_congr_ae`/`setIntegral_congr_fun`, never by
    rewriting under a binder; `mul_comm`/`mul_add` are given their arguments.

  The route (each step is one lemma):
    §1  the Gaussian bridge: `phi = gaussianPDFReal 0 1`, `Phi = gaussianReal 0 1 (Iic ·)`,
        `∫ f ∂N(0,1) = ∫ f·phi`, `∫ phi = 1`.
    §2  tilted Gaussian integrals: `e^{sz} phi z = e^{s²/2} phi (z - s)` (the T3
        tilting identity `phi_add` in lognormal form), hence
        `∫ e^{sz} phi = e^{s²/2}` and `∫_{(a,∞)} e^{sz} phi = e^{s²/2} Phi (s - a)`.
    §3  the payoff: `S e^{m + sz} - K = K (e^{s(z + d2)} - 1)` where
        `s·d2 = log (S/K) + m`, so `(S e^{m+sz} - K)⁺ φ` is the indicator of the
        exercise region `{z > -d2}` times `(S e^{m+sz} - K) φ`.
    §4  the theorems: split the half-line integral, evaluate both pieces with §2,
        and recognise `e^{-rτ} S e^{m} e^{s²/2} = S e^{-qτ}` and
        `s - (-d2) = d1` (T1). The put follows from the call by parity (T2) and
        `(K - x)⁺ = (x - K)⁺ - x + K`.
-/
import ImprovedBS.Core

noncomputable section

namespace BSM

open MeasureTheory

/-!
--------------------------------------------------------------------------
§1  The Gaussian bridge
--------------------------------------------------------------------------
-/

/-- **The density bridge**: the repository's `phi` is mathlib's standard-normal
density `gaussianPDFReal 0 1`. Unfold both sides; with `μ = 0`, `v = 1` mathlib's
`(√(2πv))⁻¹ exp (-(x-μ)²/(2v))` is `phi` up to `a / b = b⁻¹ * a`. -/
theorem phi_eq_gaussianPDFReal (x : ℝ) : phi x = ProbabilityTheory.gaussianPDFReal 0 1 x := by
  unfold phi ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  ring

/-- **The distribution-function bridge**: `Phi x` is the `gaussianReal 0 1`-measure
of `(-∞, x]`. `gaussianReal_apply_eq_integral` writes that measure as
`ENNReal.ofReal (∫_{(-∞,x]} gaussianPDFReal 0 1)`; the integral is nonnegative, so
`toReal` undoes `ofReal`, and `Phi_eq_integral_Iic` plus the density bridge finish. -/
theorem Phi_eq_gaussianReal_Iic (x : ℝ) :
    Phi x = (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal := by
  have h0 : 0 ≤ ∫ u in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 u :=
    setIntegral_nonneg measurableSet_Iic
      fun u _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 u
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 (one_ne_zero : (1 : NNReal) ≠ 0)
      (Set.Iic x),
    ENNReal.toReal_ofReal h0, Phi_eq_integral_Iic]
  exact setIntegral_congr_fun measurableSet_Iic fun u _ => phi_eq_gaussianPDFReal u

/-- **The expectation bridge**: an integral against the standard normal law is a
Lebesgue integral against `phi`. This is the lemma that lets every statement below
be read as a statement about `gaussianReal 0 1` without touching `Core.lean`. -/
theorem integral_gaussianReal_eq_integral_mul_phi (f : ℝ → ℝ) :
    ∫ z, f z ∂(ProbabilityTheory.gaussianReal 0 1) = ∫ z, f z * phi z := by
  have hpw : ∀ z : ℝ, ProbabilityTheory.gaussianPDFReal 0 1 z • f z = f z * phi z := by
    intro z
    rw [smul_eq_mul, phi_eq_gaussianPDFReal, mul_comm (ProbabilityTheory.gaussianPDFReal 0 1 z) (f z)]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpw)

/-- `∫ phi = 1`: `phi` is a probability density. Through the bridge, this is
mathlib's `integral_gaussianPDFReal_eq_one`. -/
theorem integral_phi : ∫ z, phi z = 1 := by
  have hfun : phi = ProbabilityTheory.gaussianPDFReal 0 1 := funext phi_eq_gaussianPDFReal
  rw [hfun]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (one_ne_zero : (1 : NNReal) ≠ 0)

/-!
--------------------------------------------------------------------------
§2  Tilted Gaussian integrals
--------------------------------------------------------------------------
-/

/-- **The tilting identity in lognormal form**: `e^{sz} phi z = e^{s²/2} phi (z - s)`.
This is `phi_add` (the identity behind T3 and T4) read at `u = z - s`, `a = s`. -/
theorem exp_mul_phi_eq (s z : ℝ) :
    Real.exp (s * z) * phi z = Real.exp (s ^ 2 / 2) * phi (z - s) := by
  have h := phi_add (z - s) s
  rw [sub_add_cancel] at h
  have hexp : Real.exp (s ^ 2 / 2) * Real.exp (s * (z - s) + s ^ 2 / 2) = Real.exp (s * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← h, ← mul_assoc, hexp]

/-- `e^{sz} phi z` is integrable for every real `s`: it is a constant times a
translate of `phi`. -/
theorem integrable_exp_mul_phi (s : ℝ) :
    Integrable (fun z : ℝ => Real.exp (s * z) * phi z) := by
  refine ((phi_integrable.comp_sub_right s).const_mul (Real.exp (s ^ 2 / 2))).congr ?_
  exact Filter.Eventually.of_forall fun z => (exp_mul_phi_eq s z).symm

/-- **The lognormal moment**: `∫ e^{sz} phi z dz = e^{s²/2}` — the moment generating
function of the standard normal law, obtained by translation invariance of
Lebesgue measure from `∫ phi = 1`. -/
theorem integral_exp_mul_phi (s : ℝ) :
    ∫ z, Real.exp (s * z) * phi z = Real.exp (s ^ 2 / 2) := by
  have hI : ∫ z, Real.exp (s * z) * phi z = ∫ z, Real.exp (s ^ 2 / 2) * phi (z - s) :=
    integral_congr_ae (Filter.Eventually.of_forall (exp_mul_phi_eq s))
  rw [hI, integral_const_mul, integral_sub_right_eq_self phi s, integral_phi, mul_one]

/-- `∫_{(a,∞)} phi = Phi (-a)`: reflect the half-line (`integral_comp_neg_Ioi`, `phi`
is even) and read `Phi_eq_integral_Iic`. -/
theorem integral_phi_Ioi (a : ℝ) : ∫ z in Set.Ioi a, phi z = Phi (-a) := by
  have h := integral_comp_neg_Ioi a phi
  simp only [phi_neg] at h
  rw [h, Phi_eq_integral_Iic]

/-- `∫_{(a,∞)} phi (z - s) dz = Phi (s - a)`. Reflect `z ↦ -z` (so the translate
`phi (z - s) = phi (s - z)` becomes `phi (s + w)` on `(-∞, -a]`) and translate with
`integral_comp_add_right_Iic`. -/
theorem integral_phi_sub_Ioi (a s : ℝ) : ∫ z in Set.Ioi a, phi (z - s) = Phi (s - a) := by
  have h1 : ∫ z in Set.Ioi a, phi (z - s)
      = ∫ z in Set.Ioi a, (fun w : ℝ => phi (s + w)) (-z) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
    show phi (z - s) = phi (s + -z)
    rw [← phi_neg (z - s), neg_sub, sub_eq_add_neg]
  rw [h1, integral_comp_neg_Ioi a (fun w : ℝ => phi (s + w))]
  show ∫ x in Set.Iic (-a), phi (s + x) = Phi (s - a)
  have h2 : ∫ x in Set.Iic (-a), phi (s + x) = ∫ x in Set.Iic (-a), phi (x + s) :=
    setIntegral_congr_fun measurableSet_Iic fun x _ => by rw [add_comm s x]
  have h3 : -a + s = s - a := by ring
  rw [h2, integral_comp_add_right_Iic phi (-a) s, h3, Phi_eq_integral_Iic]

/-- **The lognormal partial expectation**:
`∫_{(a,∞)} e^{sz} phi z dz = e^{s²/2} Phi (s - a)`. This is the one Gaussian
computation in Black–Scholes; everything else is bookkeeping. -/
theorem integral_exp_mul_phi_Ioi (a s : ℝ) :
    ∫ z in Set.Ioi a, Real.exp (s * z) * phi z = Real.exp (s ^ 2 / 2) * Phi (s - a) := by
  have h : ∫ z in Set.Ioi a, Real.exp (s * z) * phi z
      = ∫ z in Set.Ioi a, Real.exp (s ^ 2 / 2) * phi (z - s) :=
    setIntegral_congr_fun measurableSet_Ioi fun z _ => exp_mul_phi_eq s z
  rw [h, integral_const_mul, integral_phi_sub_Ioi]

/-!
--------------------------------------------------------------------------
§3  The payoff
--------------------------------------------------------------------------
-/

/-- `σ√τ · d2 = log (S/K) + (r - q - σ²/2) τ`: `d2` cleared of its denominator.
The same fact is the first step inside `d2_exponent`; it is exposed here because
§3 needs it as a hypothesis in the abstract form `s * d = log (S/K) + m`. -/
theorem sigma_sqrt_tau_mul_d2 (S K tau r q sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    sigma * Real.sqrt tau * d2 S K tau r q sigma
      = Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau := by
  have hne : sigma * Real.sqrt tau ≠ 0 := mul_ne_zero hsigma (Real.sqrt_pos.mpr htau).ne'
  have h1 : Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau
      = d2 S K tau r q sigma * (sigma * Real.sqrt tau) := by
    apply (div_eq_iff hne).mp
    rfl
  rw [h1, mul_comm (sigma * Real.sqrt tau) (d2 S K tau r q sigma)]

/-- **The payoff in exercise-region form**: if `s·d = log (S/K) + m` then
`S e^{m + sz} - K = K (e^{s(z + d)} - 1)`. Stated with the drift `m`, the scale `s`
and the threshold `d` abstracted, and the only relation the algebra needs as a
hypothesis — the T5 idiom (`d_tau_quotient_eq`). In use, `m = (r - q - σ²/2)τ`,
`s = σ√τ`, `d = d2`. -/
theorem spot_sub_strike_eq (S K m s d z : ℝ) (hS : 0 < S) (hK : 0 < K)
    (hd : s * d = Real.log (S / K) + m) :
    S * Real.exp (m + s * z) - K = K * (Real.exp (s * (z + d)) - 1) := by
  have hKS : K * (S / K) = S := by
    rw [← mul_div_assoc, mul_comm K S, mul_div_assoc, div_self hK.ne', mul_one]
  have h3 : K * Real.exp (s * d) = S * Real.exp m := by
    rw [hd, Real.exp_add, Real.exp_log (div_pos hS hK), ← mul_assoc, hKS]
  rw [mul_add s z d, Real.exp_add, Real.exp_add]
  linear_combination (-Real.exp (s * z)) * h3

/-- **The call payoff is an indicator**: for `s > 0`,
`(S e^{m + sz} - K)⁺ φ(z) = 𝟙_{(-d, ∞)}(z) · (S e^{m + sz} - K) φ(z)`.
The exercise region is `{z : e^{s(z + d)} ≥ 1} = {z > -d}` by `spot_sub_strike_eq`;
on it the `max` is the left argument, off it the right. -/
theorem max_spot_sub_strike_mul_phi (S K m s d : ℝ) (hS : 0 < S) (hK : 0 < K) (hs : 0 < s)
    (hd : s * d = Real.log (S / K) + m) (z : ℝ) :
    max (S * Real.exp (m + s * z) - K) 0 * phi z
      = Set.indicator (Set.Ioi (-d)) (fun z => (S * Real.exp (m + s * z) - K) * phi z) z := by
  have hpay := spot_sub_strike_eq S K m s d z hS hK hd
  by_cases hz : z ∈ Set.Ioi (-d)
  · rw [Set.indicator_of_mem hz]
    have hnn : 0 ≤ S * Real.exp (m + s * z) - K := by
      rw [hpay]
      have hz' : -d < z := Set.mem_Ioi.mp hz
      have hzd : 0 ≤ s * (z + d) := mul_nonneg hs.le (by linarith)
      have h1 : 1 ≤ Real.exp (s * (z + d)) := Real.one_le_exp hzd
      exact mul_nonneg hK.le (sub_nonneg.mpr h1)
    rw [max_eq_left hnn]
  · rw [Set.indicator_of_notMem hz]
    have hnp : S * Real.exp (m + s * z) - K ≤ 0 := by
      rw [hpay]
      have hz' : z ≤ -d := not_lt.mp (fun h => hz (Set.mem_Ioi.mpr h))
      have hzd : s * (z + d) ≤ 0 := by
        have := mul_nonneg hs.le (by linarith : 0 ≤ -(z + d))
        linarith
      have h1 : Real.exp (s * (z + d)) ≤ 1 := Real.exp_le_one_iff.mpr hzd
      have := mul_nonneg hK.le (sub_nonneg.mpr h1)
      linarith
    rw [max_eq_right hnp, zero_mul]

/-- `(b - a)⁺ = (a - b)⁺ - a + b`: the put payoff in terms of the call payoff. -/
theorem max_sub_swap_eq (a b : ℝ) : max (b - a) 0 = max (a - b) 0 - a + b := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

/-!
--------------------------------------------------------------------------
§4  The theorems
--------------------------------------------------------------------------
-/

/-- The (undiscounted) terminal spot along a standard-normal draw,
`S e^{(r-q-σ²/2)τ + σ√τ z} φ(z)`, is integrable — for every real parameter set. -/
theorem integrable_spot_mul_phi (S tau r q sigma : ℝ) :
    Integrable (fun z : ℝ =>
      S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z) := by
  have hpw : ∀ z : ℝ, S * Real.exp ((r - q - sigma ^ 2 / 2) * tau)
      * (Real.exp (sigma * Real.sqrt tau * z) * phi z)
      = S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z := by
    intro z
    rw [Real.exp_add]
    ring
  exact ((integrable_exp_mul_phi (sigma * Real.sqrt tau)).const_mul
    (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau))).congr (Filter.Eventually.of_forall hpw)

/-- **The martingale (drift) condition**: `E[S_T] = S e^{(r-q)τ}` — the risk-neutral
drift `(r - q - σ²/2)τ` is exactly the one that makes the discounted, dividend-adjusted
spot a martingale. This is `integral_exp_mul_phi` at `s = σ√τ` and
`(σ√τ)²/2 = σ²τ/2`. -/
theorem integral_spot_mul_phi_eq_forward (S tau r q sigma : ℝ) (htau : 0 ≤ tau) :
    ∫ z, S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z
      = S * Real.exp ((r - q) * tau) := by
  have hpw : ∀ z : ℝ,
      S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z
        = S * Real.exp ((r - q - sigma ^ 2 / 2) * tau)
          * (Real.exp (sigma * Real.sqrt tau * z) * phi z) := by
    intro z
    rw [Real.exp_add]
    ring
  have hI : ∫ z, S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z
      = ∫ z, S * Real.exp ((r - q - sigma ^ 2 / 2) * tau)
          * (Real.exp (sigma * Real.sqrt tau * z) * phi z) :=
    integral_congr_ae (Filter.Eventually.of_forall hpw)
  have harg : (r - q - sigma ^ 2 / 2) * tau + sigma ^ 2 * tau / 2 = (r - q) * tau := by ring
  rw [hI, integral_const_mul, integral_exp_mul_phi, mul_pow, Real.sq_sqrt htau, mul_assoc,
    ← Real.exp_add, harg]

/-- The call payoff `(S_T - K)⁺` has finite risk-neutral expectation: through
`max_spot_sub_strike_mul_phi` it is the indicator of `(-d2, ∞)` times an integrable
function. -/
theorem integrable_max_spot_sub_strike_mul_phi (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    Integrable (fun z : ℝ =>
      max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0
        * phi z) := by
  have hs : 0 < sigma * Real.sqrt tau := mul_pos hsigma (Real.sqrt_pos.mpr htau)
  have hd := sigma_sqrt_tau_mul_d2 S K tau r q sigma htau hsigma.ne'
  have hpw : ∀ z : ℝ, S * Real.exp ((r - q - sigma ^ 2 / 2) * tau)
      * (Real.exp (sigma * Real.sqrt tau * z) * phi z) - K * phi z
      = (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) * phi z := by
    intro z
    rw [Real.exp_add]
    ring
  -- state the difference in lambda form first (the `Integrable (f - g)` Pi-form
  -- is accepted against a lambda-typed `have`, cf. `hg_int` in Fourier.lean),
  -- so that `.congr` below compares two lambdas and nothing else
  have h0 : Integrable (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau)
      * (Real.exp (sigma * Real.sqrt tau * z) * phi z) - K * phi z) :=
    ((integrable_exp_mul_phi (sigma * Real.sqrt tau)).const_mul
      (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau))).sub (phi_integrable.const_mul K)
  have h1 : Integrable (fun z : ℝ =>
      (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) * phi z) :=
    h0.congr (Filter.Eventually.of_forall hpw)
  exact (h1.indicator measurableSet_Ioi).congr (Filter.Eventually.of_forall fun z =>
    (max_spot_sub_strike_mul_phi S K ((r - q - sigma ^ 2 / 2) * tau) (sigma * Real.sqrt tau)
      (d2 S K tau r q sigma) hS hK hs hd z).symm)

/-- **T6(3a), the call.** The Black–Scholes closed form is the discounted
risk-neutral expectation of the call payoff:

    bsCall S K τ r q σ = e^{-rτ} ∫ (S e^{(r-q-σ²/2)τ + σ√τ z} - K)⁺ φ(z) dz.

Proof: the integrand is `𝟙_{(-d2,∞)} · (S e^{m+sz} - K) φ` (`max_spot_sub_strike_mul_phi`);
split it as `S e^{m} (e^{sz} φ) - K φ` on the half-line; the first piece is
`S e^{m} e^{s²/2} Phi (s + d2) = S e^{m} e^{s²/2} Phi d1` (`integral_exp_mul_phi_Ioi`, T1),
the second is `K Phi d2` (`integral_phi_Ioi`); finally `e^{-rτ} e^{m} e^{s²/2} = e^{-qτ}`.

The hypotheses are the honest ones: `0 < S`, `0 < K` for the logarithm, `0 < τ` for
`√τ`, and `0 < σ` because with `σ < 0` the closed form evaluates to `-bsPut` while the
expectation is unchanged (checked numerically before this file was written). -/
theorem bsCall_eq_riskNeutral_expectation (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    bsCall S K tau r q sigma
      = Real.exp (-r * tau) *
        ∫ z, max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0
          * phi z := by
  have hs : 0 < sigma * Real.sqrt tau := mul_pos hsigma (Real.sqrt_pos.mpr htau)
  have hd := sigma_sqrt_tau_mul_d2 S K tau r q sigma htau hsigma.ne'
  have hd1 : d1 S K tau r q sigma = d2 S K tau r q sigma + sigma * Real.sqrt tau := by
    have := t1_d1_minus_d2 S K tau r q sigma htau hsigma.ne'
    linarith
  have hs2 : (sigma * Real.sqrt tau) ^ 2 = sigma ^ 2 * tau := by
    rw [mul_pow, Real.sq_sqrt htau.le]
  -- Step 1: the integrand is the indicator of the exercise region `{z > -d2}`.
  have hind : ∫ z, max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0
        * phi z
      = ∫ z, Set.indicator (Set.Ioi (-(d2 S K tau r q sigma)))
          (fun z => (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K)
            * phi z) z :=
    integral_congr_ae (Filter.Eventually.of_forall
      (max_spot_sub_strike_mul_phi S K ((r - q - sigma ^ 2 / 2) * tau) (sigma * Real.sqrt tau)
        (d2 S K tau r q sigma) hS hK hs hd))
  -- Step 2: on the half-line, `(S e^{m+sz} - K) φ = S e^{m} (e^{sz} φ) - K φ`.
  have hsplit : ∫ z in Set.Ioi (-(d2 S K tau r q sigma)),
        (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) * phi z
      = ∫ z in Set.Ioi (-(d2 S K tau r q sigma)),
        (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau) * (Real.exp (sigma * Real.sqrt tau * z) * phi z)
          - K * phi z) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
    show (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) * phi z
      = S * Real.exp ((r - q - sigma ^ 2 / 2) * tau) * (Real.exp (sigma * Real.sqrt tau * z) * phi z)
        - K * phi z
    rw [Real.exp_add]
    ring
  have hA : IntegrableOn (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau)
      * (Real.exp (sigma * Real.sqrt tau * z) * phi z)) (Set.Ioi (-(d2 S K tau r q sigma))) :=
    ((integrable_exp_mul_phi (sigma * Real.sqrt tau)).const_mul
      (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau))).integrableOn
  have hB : IntegrableOn (fun z : ℝ => K * phi z) (Set.Ioi (-(d2 S K tau r q sigma))) :=
    (phi_integrable.const_mul K).integrableOn
  -- Step 3: the two Gaussian integrals, and the arguments of `Phi`.
  have hPhi1 : Phi (sigma * Real.sqrt tau - -(d2 S K tau r q sigma)) = Phi (d1 S K tau r q sigma) := by
    congr 1
    linarith
  have hPhi2 : Phi (-(-(d2 S K tau r q sigma))) = Phi (d2 S K tau r q sigma) := by
    rw [neg_neg]
  have hexp : Real.exp (-r * tau) * (Real.exp ((r - q - sigma ^ 2 / 2) * tau)
      * Real.exp ((sigma * Real.sqrt tau) ^ 2 / 2)) = Real.exp (-q * tau) := by
    rw [hs2, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hind, integral_indicator measurableSet_Ioi, hsplit, integral_sub hA hB, integral_const_mul,
    integral_const_mul, integral_exp_mul_phi_Ioi, integral_phi_Ioi, hPhi1, hPhi2]
  unfold bsCall
  linear_combination (-(S * Phi (d1 S K tau r q sigma))) * hexp

/-- **T6(3a), the put.** By parity (T2) and `(K - x)⁺ = (x - K)⁺ - x + K`:

    bsPut S K τ r q σ = e^{-rτ} ∫ (K - S e^{(r-q-σ²/2)τ + σ√τ z})⁺ φ(z) dz.

The three integrals on the right of the pointwise identity are the call
expectation, the forward `S e^{(r-q)τ}` (`integral_spot_mul_phi_eq_forward`) and
`K ∫ φ = K`; discounting the forward gives `S e^{-qτ}`, which is parity. -/
theorem bsPut_eq_riskNeutral_expectation (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    bsPut S K tau r q sigma
      = Real.exp (-r * tau) *
        ∫ z, max (K - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)) 0
          * phi z := by
  have hpt : ∀ z : ℝ,
      max (K - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)) 0 * phi z
        = (max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0
              * phi z
            - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z)
          + K * phi z := by
    intro z
    rw [max_sub_swap_eq (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)) K]
    ring
  have hcall := integrable_max_spot_sub_strike_mul_phi S K tau r q sigma hS hK htau hsigma
  have hspot := integrable_spot_mul_phi S tau r q sigma
  have hKphi : Integrable (fun z : ℝ => K * phi z) := phi_integrable.const_mul K
  have hsub : Integrable (fun z : ℝ =>
      max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0 * phi z
        - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z) :=
    hcall.sub hspot
  have hI : ∫ z, max (K - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)) 0
        * phi z
      = ∫ z, (max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0
              * phi z
            - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z)
          + K * phi z :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hint : ∫ z, max (K - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)) 0
        * phi z
      = ((∫ z, max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0
            * phi z)
          - ∫ z, S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) * phi z)
        + ∫ z, K * phi z := by
    rw [hI, integral_add hsub hKphi, integral_sub hcall hspot]
  have harg : -r * tau + (r - q) * tau = -q * tau := by ring
  have hF : Real.exp (-r * tau) * (S * Real.exp ((r - q) * tau)) = S * Real.exp (-q * tau) := by
    rw [mul_left_comm, ← Real.exp_add, harg]
  rw [hint, integral_spot_mul_phi_eq_forward S tau r q sigma htau.le, integral_const_mul,
    integral_phi, mul_one, t2_put_call_parity,
    bsCall_eq_riskNeutral_expectation S K tau r q sigma hS hK htau hsigma]
  linear_combination hF

/-- **T6(3a) against mathlib's standard normal law.** The same identity with the
integral taken against the probability measure `gaussianReal 0 1` of the driving
noise `Z`: `bsCall = e^{-rτ} E[(S e^{(r-q-σ²/2)τ + σ√τ Z} - K)⁺]`. -/
theorem bsCall_eq_gaussianReal_expectation (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    bsCall S K tau r q sigma
      = Real.exp (-r * tau) *
        ∫ z, max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) - K) 0
          ∂(ProbabilityTheory.gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_mul_phi]
  exact bsCall_eq_riskNeutral_expectation S K tau r q sigma hS hK htau hsigma

/-- **T6(3a) against the lognormal law of `log S_T`.** Under the risk-neutral
measure `log (S_T / S) ~ N((r-q-σ²/2)τ, σ²τ)`, and

    bsCall = e^{-rτ} ∫ (S e^{x} - K)⁺ d N((r-q-σ²/2)τ, σ²τ)(x).

The variance enters as `v : ℝ≥0` with `(v : ℝ) = σ²τ` because `gaussianReal` takes
its variance in `ℝ≥0`. The law is obtained from `gaussianReal 0 1` by the two
affine maps `z ↦ σ√τ z` and `x ↦ (r-q-σ²/2)τ + x` (`gaussianReal_map_const_mul`,
`gaussianReal_map_const_add`), and `integral_map` pulls the integral back to the
standard normal, where `bsCall_eq_gaussianReal_expectation` applies. This is the
form sub-goal 3(b) will invert. -/
theorem bsCall_eq_lognormal_expectation (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma)
    (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) :
    bsCall S K tau r q sigma
      = Real.exp (-r * tau) *
        ∫ x, max (S * Real.exp x - K) 0
          ∂(ProbabilityTheory.gaussianReal ((r - q - sigma ^ 2 / 2) * tau) v) := by
  have hw : (⟨(sigma * Real.sqrt tau) ^ 2, sq_nonneg _⟩ * 1 : NNReal) = v := by
    apply NNReal.eq
    rw [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one, hv, mul_pow, Real.sq_sqrt htau.le]
  have hmean : sigma * Real.sqrt tau * 0 + (r - q - sigma ^ 2 / 2) * tau
      = (r - q - sigma ^ 2 / 2) * tau := by ring
  -- the law of `m + s·Z` for `Z ~ N(0,1)` is `N(m, s²)`
  have hlaw : ((ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => sigma * Real.sqrt tau * z)).map
        (fun x : ℝ => (r - q - sigma ^ 2 / 2) * tau + x)
      = ProbabilityTheory.gaussianReal ((r - q - sigma ^ 2 / 2) * tau) v := by
    rw [ProbabilityTheory.gaussianReal_map_const_mul, ProbabilityTheory.gaussianReal_map_const_add,
      hw, hmean]
  -- `fun_prop` first; the explicit terms are the same proofs spelled out, kept as
  -- the fallback because this file is compiled by CI only
  have hmeas1 : Measurable (fun z : ℝ => sigma * Real.sqrt tau * z) := by
    first
      | fun_prop
      | exact (continuous_const.mul continuous_id).measurable
  have hmeas2 : Measurable (fun x : ℝ => (r - q - sigma ^ 2 / 2) * tau + x) := by
    first
      | fun_prop
      | exact (continuous_const.add continuous_id).measurable
  have hcont1 : Continuous (fun x : ℝ => max (S * Real.exp x - K) 0) := by
    first
      | fun_prop
      | exact ((continuous_const.mul Real.continuous_exp).sub continuous_const).max continuous_const
  have hcont2 : Continuous (fun x : ℝ => max (S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + x) - K) 0) := by
    first
      | fun_prop
      | exact ((continuous_const.mul (continuous_const.add continuous_id).rexp).sub
          continuous_const).max continuous_const
  rw [← hlaw, integral_map hmeas2.aemeasurable hcont1.aestronglyMeasurable,
    integral_map hmeas1.aemeasurable hcont2.aestronglyMeasurable]
  exact bsCall_eq_gaussianReal_expectation S K tau r q sigma hS hK htau hsigma

end BSM
