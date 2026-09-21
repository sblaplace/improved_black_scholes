/-
  ImprovedBS/Skeleton.lean — BRIEF_009: the model-free skeleton.

  What this file proves, in one line each:

    modelFreeCall μ X K r tau - modelFreePut μ X K r tau
      = e^{-r*tau} * ((∫ s, X s ∂μ) - K)                   -- model_free_parity_gap
    ∫ s, X s ∂μ = S e^{(r-q)*tau}  →
      modelFreeCall - modelFreePut = S e^{-q*tau} - K e^{-r*tau}
                                                   -- model_free_put_call_parity
    0 ≤ X, 0 ≤ K, drift  →  max (S e^{-q*tau} - K e^{-r*tau}) 0 ≤ modelFreeCall
                            ≤ S e^{-q*tau}            -- model_free_call_bounds
      and the mirrored put bounds through parity      -- model_free_put_bounds

  for ANY probability measure `μ` on `ℝ` and ANY terminal-spot map `X : ℝ → ℝ`
  -- no Gaussian, no density, no closed form. Parity is `max_sub_swap_eq`
  (BRIEF_007's pointwise payoff identity) integrated; the bounds are
  `le_max_left`/`le_max_right` integrated. The drift condition is the only
  market hypothesis, and it is load-bearing in exactly one place: it turns the
  unfixed gap `e^{-r*tau}(E[S_T] - K)` into the forward spread.

  Why this exists before the increment law is widened. T2/T4 as landed are
  theorems about `bsCall`/`bsPut`, the closed forms. The tempered-stable law of
  docs/03 §D1 has no closed form -- its price IS the expectation/Fourier
  integral -- so a skeleton expressed only through `bsCall` cannot be preserved
  by a law that never meets one. Lifted to the expectation layer once, parity
  and the bounds become instantiation: a future law supplies `Integrable X`,
  the drift condition and `0 ≤ X`, and inherits T2/T4 (BSM-2 item 5).

  And the abstraction is graded for vacuity at the only law we have: §5
  instantiates everything at the GBM law `gaussianReal 0 1` with the lognormal
  spot map (written inline, syntactically identical to
  `bsCall_eq_gaussianReal_expectation`'s integrand -- no wrapper def, per
  BRIEF_006's unapplied-def elaboration cost), and §6 re-derives T2′ and T4
  through the layer as `t2_spread_via_skeleton` / `t4_call_bounds_via_skeleton`,
  which must cite the model-free parents and must NOT cite the closed-form
  proofs (the `[SKELETON]` route check in scripts/lean_lint.py). A mistyped
  operator or a wrong drift condition cannot survive that re-derivation.

  Design rules inherited from BRIEF_003--008 and applied here:
  * the numeric route was checked in Python before any Lean was written
    (ledger C4): tests/test_bs.py::test_model_free_skeleton asserts every
    identity here at hand-built NON-lognormal discrete laws, with a wrong-drift
    canary proving the drift hypothesis load-bearing (the `0 < sigma`
    discipline of BRIEF_007, one layer up);
  * every mathlib name below was read at the v4.34.0 source or marked with its
    expected route in a comment before pushing (ledger C3); the file is
    CI-compiled only, this tree has no toolchain;
  * the put is never defined from the call and parity is never assumed
    (`[INDEPENDENCE]`): `modelFreePut` has its own body, and the put's
    integrability is derived through `max_sub_swap_eq`, which IS the parity
    identity in embryo.

  The route (each step is one lemma):
    §1  the operators: `modelFreeCall`/`modelFreePut`, price by expectation.
    §2  payoff integrability from `Integrable X` (mono over `|X| + |K|`;
        the put via `max_sub_swap_eq` and `Integrable.sub`/`.add`).
    §3  parity: `max_sub_swap_eq` under the integral (unfixed form), the
        drift condition (forward form).
    §4  bounds: `le_max_right` (nonneg), `le_max_left` + drift (lower),
        `X ≥ 0` + `integral_mono_ae` (upper); put bounds via parity + `linarith`
        exactly as `t4_put_bounds` rides on `t4_call_bounds` + T2.
    §5  the GBM instance: the integrability twin of BRIEF_007's
        `integral_gaussianReal_eq_integral_mul_phi`, then items 3--4 at
        `gaussianReal 0 1`.
    §6  the re-derivations: §5 + `bsCall_eq_gaussianReal_expectation` /
        `bsPut_eq_riskNeutral_expectation` land on T2′/T4's exact statements.
-/
import ImprovedBS.RiskNeutral

noncomputable section

namespace BSM

open MeasureTheory

/-!
---------------------------------------------------------------------------
§1  The operators: price by expectation, no model
---------------------------------------------------------------------------
-/

/-- **The model-free call value**: `e^{-r*tau} E[(X - K)^+]` against the
terminal-spot law `(μ, X)`. The put has its own definition below -- it is NOT
the call minus anything (`[INDEPENDENCE]`), just as `bsPut` is not `bsCall`
minus anything. -/
noncomputable def modelFreeCall (μ : Measure ℝ) (X : ℝ → ℝ) (K r tau : ℝ) : ℝ :=
  Real.exp (-r * tau) * ∫ s, max (X s - K) 0 ∂μ

/-- **The model-free put value**: `e^{-r*tau} E[(K - X)^+]`, independently
derived (its own payoff, its own integral). -/
noncomputable def modelFreePut (μ : Measure ℝ) (X : ℝ → ℝ) (K r tau : ℝ) : ℝ :=
  Real.exp (-r * tau) * ∫ s, max (K - X s) 0 ∂μ

/-!
---------------------------------------------------------------------------
§2  Payoff integrability
---------------------------------------------------------------------------
-/

/-- The call payoff of an integrable spot is integrable: pointwise
`|max (X s - K) 0| ≤ |X s| + |K|`, and `Integrable.mono` over `|X| + |K|`. -/
theorem integrable_call_payoff {μ : Measure ℝ} (X : ℝ → ℝ) (K : ℝ)
    (hX : Integrable X μ) : Integrable (fun s => max (X s - K) 0) μ := by
  have hbound : ∀ s : ℝ, ‖max (X s - K) 0‖ ≤ ‖X s‖ + ‖K‖ := by
    intro s
    have h0 : 0 ≤ max (X s - K) 0 := le_max_right _ _
    calc ‖max (X s - K) 0‖ = max (X s - K) 0 := Real.norm_of_nonneg h0
      _ ≤ |X s - K| := max_le (le_abs_self _) (abs_nonneg _)
      _ = |X s + -K| := congrArg abs (sub_eq_add_neg _ _)
      _ ≤ |X s| + |-K| := abs_add _ _
      _ = ‖X s‖ + ‖K‖ := by rw [abs_neg, Real.norm_eq_abs, Real.norm_eq_abs]
  -- `Integrable.norm` and `MeasureTheory.integrable_const` (auto-param
  -- finiteness at the tag) give `fun s => ‖X s‖ + ‖K‖`; measurability of the
  -- payoff is `fun_prop` on the concrete shape (BRIEF_007 experience).
  exact MeasureTheory.Integrable.mono (hX.norm.add (MeasureTheory.integrable_const))
    (Filter.Eventually.of_forall hbound)
    (hX.aestronglyMeasurable.sub (MeasureTheory.aestronglyMeasurable_const _)).max
      (MeasureTheory.aestronglyMeasurable_const _)

/-- The put payoff of an integrable spot is integrable -- derived through
`max_sub_swap_eq`, the pointwise identity `(K - X)^+ = (X - K)^+ - X + K`.
This is parity in embryo: the same identity, integrated, is §3. -/
theorem integrable_put_payoff {μ : Measure ℝ} (X : ℝ → ℝ) (K : ℝ)
    (hX : Integrable X μ) : Integrable (fun s => max (K - X s) 0) μ := by
  have hpt : ∀ s : ℝ, max (K - X s) 0 = max (X s - K) 0 - X s + K := fun s =>
    max_sub_swap_eq (X s) K
  have heq : (fun s : ℝ => max (K - X s) 0) = fun s => max (X s - K) 0 - X s + K :=
    funext hpt
  rw [heq]
  have h1 : Integrable (fun s : ℝ => max (X s - K) 0 - X s) μ :=
    (integrable_call_payoff X K hX).sub hX
  have h2 : (fun s : ℝ => max (X s - K) 0 - X s + K) = fun s => (max (X s - K) 0 - X s) + K :=
    funext (fun _ => rfl)
  rw [h2]
  exact h1.add (MeasureTheory.integrable_const)

/-!
---------------------------------------------------------------------------
§3  Parity -- the model-free skeleton, parity half
---------------------------------------------------------------------------
-/

/-- **Model-free parity, unfixed form**: the call minus the put is the
discounted mean spread, for EVERY law -- wrong drift included. This is
`max_sub_swap_eq` (put payoff = call payoff − spot + strike) integrated; the
drift condition plays no part, which is why it has no hypothesis here. The
numeric shadow is `test_model_free_skeleton`'s gap identity, asserted at
non-lognormal laws. -/
theorem model_free_parity_gap {μ : Measure ℝ} [IsProbabilityMeasure μ] (X : ℝ → ℝ)
    (K r tau : ℝ) (hX : Integrable X μ) :
    modelFreeCall μ X K r tau - modelFreePut μ X K r tau
      = Real.exp (-r * tau) * ((∫ s, X s ∂μ) - K) := by
  have hpt : ∀ s : ℝ, max (K - X s) 0 = max (X s - K) 0 - X s + K := fun s =>
    max_sub_swap_eq (X s) K
  have hcallI := integrable_call_payoff X K hX
  have hputI := integrable_put_payoff X K hX
  have hKint : ∫ s : ℝ, K ∂μ = K := by simp [MeasureTheory.integral_const]
  have hput : ∫ s, max (K - X s) 0 ∂μ = (∫ s, max (X s - K) 0 ∂μ - ∫ s, X s ∂μ) + K := by
    have ha : ∫ s, max (K - X s) 0 ∂μ = ∫ s, (max (X s - K) 0 - X s) + K ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun s => hpt s))
    have hb : ∫ s, (max (X s - K) 0 - X s) + K ∂μ
        = ∫ s, max (X s - K) 0 - X s ∂μ + ∫ s, K ∂μ :=
      integral_add (hcallI.sub hX) (MeasureTheory.integrable_const)
    have hc : ∫ s, max (X s - K) 0 - X s ∂μ = ∫ s, max (X s - K) 0 ∂μ - ∫ s, X s ∂μ :=
      integral_sub hcallI hX
    rw [ha, hb, hc, hKint]
  unfold modelFreeCall modelFreePut
  rw [hput]
  ring

/-- **T2 at the model-free layer** (traded form): under the drift condition
`E[S_T] = S e^{(r-q)*tau}` the gap is the forward spread
`S e^{-q*tau} - K e^{-r*tau}`. `t2_put_call_parity_spread` is this identity at
the closed forms; the `*_via_skeleton` re-derivation of §6 is the wire test
that the two layers agree. -/
theorem model_free_put_call_parity {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (S K tau r q : ℝ) (X : ℝ → ℝ) (hX : Integrable X μ)
    (hE : ∫ s, X s ∂μ = S * Real.exp ((r - q) * tau)) :
    modelFreeCall μ X K r tau - modelFreePut μ X K r tau
      = S * Real.exp (-q * tau) - K * Real.exp (-r * tau) := by
  rw [model_free_parity_gap X K r tau hX, hE, mul_sub]
  have harg : -r * tau + (r - q) * tau = -q * tau := by ring
  have hF : Real.exp (-r * tau) * (S * Real.exp ((r - q) * tau)) = S * Real.exp (-q * tau) := by
    rw [mul_left_comm, ← Real.exp_add, harg]
  linear_combination hF

/-!
---------------------------------------------------------------------------
§4  Bounds -- the model-free skeleton, bounds half
---------------------------------------------------------------------------
-/

/-- **Nonnegativity of the model-free call** -- a nonneg integrand has a
nonneg integral, with no integrability hypothesis and no drift condition. The
statement deliberately has none: `0 ≤ (X - K)^+` is pointwise. -/
theorem model_free_call_nonneg {μ : Measure ℝ} (X : ℝ → ℝ) (K r tau : ℝ) :
    0 ≤ modelFreeCall μ X K r tau := by
  unfold modelFreeCall
  apply mul_nonneg (Real.exp_pos _).le
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall (fun s => le_max_right (X s - K) 0))

/-- **T4 at the model-free layer**: the no-arbitrage bounds
`max (S e^{-q*tau} - K e^{-r*tau}) 0 ≤ call ≤ S e^{-q*tau}` for any law with
nonnegative spots and the drift condition. Pointwise content:
`X - K ≤ (X - K)^+` gives the lower bound after the drift is substituted;
`(X - K)^+ ≤ X` (which needs `0 ≤ X` and `0 ≤ K` -- at `X s < 0` the upper
bound is false, which is why `hX0` is a hypothesis) gives the upper. -/
theorem model_free_call_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (S K tau r q : ℝ) (X : ℝ → ℝ) (hX : Integrable X μ)
    (hE : ∫ s, X s ∂μ = S * Real.exp ((r - q) * tau))
    (hK : 0 ≤ K) (hX0 : ∀ᵐ s ∂μ, 0 ≤ X s) :
    max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0
      ≤ modelFreeCall μ X K r tau ∧
    modelFreeCall μ X K r tau ≤ S * Real.exp (-q * tau) := by
  have hcallI := integrable_call_payoff X K hX
  -- the drift algebra, in the two directions the bounds need
  have harg : -r * tau + (r - q) * tau = -q * tau := by ring
  have hF : Real.exp (-r * tau) * (S * Real.exp ((r - q) * tau)) = S * Real.exp (-q * tau) := by
    rw [mul_left_comm, ← Real.exp_add, harg]
  -- upper: (X - K)^+ ≤ X a.e. from hX0, hK, then monotonicity and the drift
  have hupper_pt : ∀ᵐ s ∂μ, max (X s - K) 0 ≤ X s := by
    refine hX0.mono (fun s hs => ?_)
    rcases le_total K (X s) with h | h
    · rw [max_eq_left (sub_nonneg.mpr h)]
      linarith
    · rw [max_eq_right (sub_nonpos.mpr h)]
      exact hs
  have hmon : ∫ s, max (X s - K) 0 ∂μ ≤ ∫ s, X s ∂μ :=
    MeasureTheory.integral_mono_ae hcallI hX hupper_pt
  have hhi : modelFreeCall μ X K r tau ≤ S * Real.exp (-q * tau) := by
    unfold modelFreeCall
    rw [← hF, ← hE]
    exact mul_le_mul_of_nonneg_left hmon (Real.exp_pos _).le
  -- lower: X - K ≤ (X - K)^+ pointwise; the left side integrates to the drift − K
  have hlower_pt : ∀ᵐ s ∂μ, X s - K ≤ max (X s - K) 0 :=
    Filter.Eventually.of_forall (fun s => le_max_left _ _)
  have hKint : ∫ s : ℝ, K ∂μ = K := by simp [MeasureTheory.integral_const]
  have hsub : ∫ s, X s - K ∂μ = ∫ s, X s ∂μ - K := by
    rw [MeasureTheory.integral_sub hX (MeasureTheory.integrable_const), hKint]
  have hmon2 : ∫ s, X s - K ∂μ ≤ ∫ s, max (X s - K) 0 ∂μ :=
    MeasureTheory.integral_mono_ae (hX.sub (MeasureTheory.integrable_const)) hcallI hlower_pt
  have hlo : S * Real.exp (-q * tau) - K * Real.exp (-r * tau)
      ≤ modelFreeCall μ X K r tau := by
    unfold modelFreeCall
    have h : Real.exp (-r * tau) * (∫ s, X s ∂μ - K)
        = S * Real.exp (-q * tau) - K * Real.exp (-r * tau) := by
      rw [hE, mul_sub]
      linear_combination hF
    rw [← h, ← hsub]
    exact mul_le_mul_of_nonneg_left hmon2 (Real.exp_pos _).le
  have hcall0 : 0 ≤ modelFreeCall μ X K r tau := model_free_call_nonneg X K r tau
  exact ⟨max_le hlo hcall0, hhi⟩

/-- **T4′ at the model-free layer**: the mirrored put bounds, obtained from the
call bounds by parity (`model_free_put_call_parity`) and `linarith` only — the
exact route of `t4_put_bounds` over `t4_call_bounds` + T2. The `[SKELETON]`
check requires the parity cite: the put bounds are a corollary, not an
independent analytic claim. -/
theorem model_free_put_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (S K tau r q : ℝ) (X : ℝ → ℝ) (hX : Integrable X μ)
    (hE : ∫ s, X s ∂μ = S * Real.exp ((r - q) * tau))
    (hK : 0 ≤ K) (hX0 : ∀ᵐ s ∂μ, 0 ≤ X s) :
    max (K * Real.exp (-r * tau) - S * Real.exp (-q * tau)) 0
      ≤ modelFreePut μ X K r tau ∧
    modelFreePut μ X K r tau ≤ K * Real.exp (-r * tau) := by
  obtain ⟨hlo, hhi⟩ := model_free_call_bounds S K tau r q X hX hE hK hX0
  have hpar := model_free_put_call_parity S K tau r q X hX hE
  have h0 : 0 ≤ modelFreeCall μ X K r tau := le_trans (le_max_right _ _) hlo
  have h1 : S * Real.exp (-q * tau) - K * Real.exp (-r * tau) ≤ modelFreeCall μ X K r tau :=
    le_trans (le_max_left _ _) hlo
  exact ⟨max_le (by linarith) (by linarith), by linarith⟩

/-!
---------------------------------------------------------------------------
§5  The GBM instance
---------------------------------------------------------------------------
-/

/-- The integrability twin of BRIEF_007's `integral_gaussianReal_eq_integral_mul_phi`:
against the standard normal law, integrability is integrability against
`phi`. Route: `gaussianReal_of_var_ne_zero` at variance 1, the withDensity
integrability transfer (`MeasureTheory.integrable_withDensity_iff`, expected
at the tag with an AEMeasurable hypothesis -- re-verify per C3), and
`toReal_gaussianPDF` + `phi_eq_gaussianPDFReal` + `mul_comm` pointwise. -/
theorem integrable_gaussianReal_iff (f : ℝ → ℝ) :
    Integrable f (ProbabilityTheory.gaussianReal 0 1)
      ↔ Integrable (fun z : ℝ => f z * phi z) := by
  have hw : AEMeasurable (ProbabilityTheory.gaussianPDF 0 1) volume :=
    (ProbabilityTheory.measurable_gaussianPDF 0 1).aemeasurable
  have hpw : ∀ z : ℝ,
      (ProbabilityTheory.gaussianPDF 0 1 z).toReal • f z = f z * phi z := by
    intro z
    rw [ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul, phi_eq_gaussianPDFReal z]
    ring
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    MeasureTheory.integrable_withDensity_iff hw]
  exact ⟨fun h => h.congr (Filter.Eventually.of_forall hpw),
    fun h => h.congr (Filter.Eventually.of_forall (fun z => (hpw z).symm))⟩

/-- **Parity instantiated at the GBM law** — and the statement is where
model-free parity shows it is strictly stronger than the closed-form
identities: `htau : 0 ≤ tau` and nothing else. No `0 < S`, no `0 < K`, no
`0 < sigma`: the lognormal spot map is integrable and at the drift for every
real parameter set with `0 ≤ tau`. -/
theorem lognormal_parity_gap (S K tau r q sigma : ℝ) (htau : 0 ≤ tau) :
    modelFreeCall (ProbabilityTheory.gaussianReal 0 1)
        (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
        K r tau
    - modelFreePut (ProbabilityTheory.gaussianReal 0 1)
        (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
        K r tau
      = S * Real.exp (-q * tau) - K * Real.exp (-r * tau) := by
  have hX : Integrable
      (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
      (ProbabilityTheory.gaussianReal 0 1) :=
    (integrable_gaussianReal_iff _).2 (integrable_spot_mul_phi S tau r q sigma)
  have hE : ∫ z,
        S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)
        ∂(ProbabilityTheory.gaussianReal 0 1) = S * Real.exp ((r - q) * tau) := by
    rw [integral_gaussianReal_eq_integral_mul_phi]
    exact integral_spot_mul_phi_eq_forward S tau r q sigma htau
  exact model_free_put_call_parity S K tau r q _ hX hE

/-- **T4 instantiated at the GBM law.** `hS : 0 ≤ S` discharges the
nonnegative-spots hypothesis (`Real.exp_pos`); `sigma` is again arbitrary. The
put instance is `model_free_put_bounds` at the same data and is deliberately
not restated -- the put side is already generic through parity, and its GBM
instance would add a pin, not a claim. -/
theorem lognormal_call_bounds (S K tau r q sigma : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (htau : 0 ≤ tau) :
    max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0
      ≤ modelFreeCall (ProbabilityTheory.gaussianReal 0 1)
          (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
          K r tau ∧
    modelFreeCall (ProbabilityTheory.gaussianReal 0 1)
        (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
        K r tau
      ≤ S * Real.exp (-q * tau) := by
  have hX : Integrable
      (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
      (ProbabilityTheory.gaussianReal 0 1) :=
    (integrable_gaussianReal_iff _).2 (integrable_spot_mul_phi S tau r q sigma)
  have hE : ∫ z,
        S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)
        ∂(ProbabilityTheory.gaussianReal 0 1) = S * Real.exp ((r - q) * tau) := by
    rw [integral_gaussianReal_eq_integral_mul_phi]
    exact integral_spot_mul_phi_eq_forward S tau r q sigma htau
  have hX0 : ∀ᵐ z ∂(ProbabilityTheory.gaussianReal 0 1),
      0 ≤ S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z) :=
    Filter.Eventually.of_forall
      (fun z => mul_nonneg hS (Real.exp_pos ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)).le)
  exact model_free_call_bounds S K tau r q _ hX hE hK hX0

/-!
---------------------------------------------------------------------------
§6  The closed-form re-derivations -- the vacuity guard
---------------------------------------------------------------------------
-/

/-- **T2′ through the skeleton.** `t2_put_call_parity_spread`'s exact
statement, re-derived from `lognormal_parity_gap` + the BRIEF_007 identities
(`bsCall_eq_gaussianReal_expectation`, `bsPut_eq_riskNeutral_expectation`) —
and NOT from `t2_put_call_parity`/`_spread`, which `[SKELETON]` forbids.
Honesty note: T2′ is hypothesis-free and this twin inherits `0 < S`,
`0 < K`, `0 < tau`, `0 < sigma` from the expectation bridge — same identity,
stronger hypotheses, different route, and the route is the point. -/
theorem t2_spread_via_skeleton (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    bsCall S K tau r q sigma - bsPut S K tau r q sigma
      = S * Real.exp (-q * tau) - K * Real.exp (-r * tau) := by
  have hX : Integrable
      (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
      (ProbabilityTheory.gaussianReal 0 1) :=
    (integrable_gaussianReal_iff _).2 (integrable_spot_mul_phi S tau r q sigma)
  have hE : ∫ z,
        S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)
        ∂(ProbabilityTheory.gaussianReal 0 1) = S * Real.exp ((r - q) * tau) := by
    rw [integral_gaussianReal_eq_integral_mul_phi]
    exact integral_spot_mul_phi_eq_forward S tau r q sigma htau.le
  have hc : bsCall S K tau r q sigma
      = modelFreeCall (ProbabilityTheory.gaussianReal 0 1)
          (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
          K r tau := by
    rw [bsCall_eq_gaussianReal_expectation S K tau r q sigma hS hK htau hsigma]
    rfl
  have hp : bsPut S K tau r q sigma
      = modelFreePut (ProbabilityTheory.gaussianReal 0 1)
          (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
          K r tau := by
    rw [bsPut_eq_riskNeutral_expectation S K tau r q sigma hS hK htau hsigma]
    show Real.exp (-r * tau) *
        ∫ z, max (K - S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)) 0
          * phi z
      = modelFreePut (ProbabilityTheory.gaussianReal 0 1)
          (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
          K r tau
    unfold modelFreePut
    rw [integral_gaussianReal_eq_integral_mul_phi]
  rw [hc, hp]
  exact model_free_put_call_parity S K tau r q _ hX hE

/-- **T4 through the skeleton.** `t4_call_bounds`'s exact statement,
re-derived from `lognormal_call_bounds` + `bsCall_eq_gaussianReal_expectation`
— not from `t4_call_bounds`, `bsCall_nonneg`, `bsPut_nonneg` or
`Phi_le_exp_mul_Phi_add` (`[SKELETON]`'s must-not-cite list). The T4′ twin is
`linarith` of this with `t2_spread_via_skeleton` and is not separately
declared — `t4_put_bounds`'s own route, one level up. -/
theorem t4_call_bounds_via_skeleton (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0
      ≤ bsCall S K tau r q sigma ∧
    bsCall S K tau r q sigma ≤ S * Real.exp (-q * tau) := by
  have hc : bsCall S K tau r q sigma
      = modelFreeCall (ProbabilityTheory.gaussianReal 0 1)
          (fun z : ℝ => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z))
          K r tau := by
    rw [bsCall_eq_gaussianReal_expectation S K tau r q sigma hS hK htau hsigma]
    rfl
  rw [hc]
  exact lognormal_call_bounds S K tau r q sigma hS.le hK.le htau.le

end BSM
