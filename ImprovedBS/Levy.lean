/-
  ImprovedBS.Levy — BRIEF_004 / T6 sub-goal 1: the moment obstruction.

  docs/03 §D1 and the T6 comment block in ImprovedBS/Core.lean both record, in
  prose, that a PURE alpha-stable log-increment cannot be a risk-neutral
  log-price, because it has no finite exponential moment:

      P(X > x) ~ c x^(-alpha)   =>   E[exp X] = ∫ exp x dP = ∞.

  This module turns that claim into a theorem. Everything in §1 is analysis —
  no option-pricing vocabulary appears in it — and §2 contains the modelling
  claim that consumes it, as a separate theorem, so a reader can accept the
  analysis and still argue with the finance.

  WHAT THE FINANCE NEEDS FROM §1, IN ONE LINE

  The obstruction is at the MOMENT step, not the KERNEL step. The Carr–Madan /
  Lewis contour has to sit in a moment strip `{u : E[exp (u X)] < ∞}`, and a
  polynomial tail lower bound makes that strip empty on the side that matters:
  the risk-neutral condition `E[S_T] = S_0 exp((r - q) tau)` cannot be met at
  any drift, so there is no equivalent martingale measure inside the
  exponential-Lévy ansatz.

  THE PROOF IDEA, AND WHY IT IS NOT A `lintegral` SLOG

  Non-integrability is proved through the layer that is easiest to bound: the
  half-lines that carry the tail hypothesis. For a level `x`,

      ∫⁻ y, ofReal (exp (y + d)) ∂μ  ≥  exp (x + d) · μ (Ici x)
                                      ≥  exp (x + d) · ofReal (c x^(-alpha)).

  So a single level `x` already gives a lower bound, and the levels are free to
  choose. Taking `x = 2 ^ k` and letting `k → ∞`, the right-hand side is
  `c · exp d · exp (2^k) · (2^k)^(-alpha)`, which diverges for EVERY real
  `alpha`, because `exp u / u ^ s → ∞` at `+∞` (mathlib:
  `Real.tendsto_exp_div_rpow_atTop`). The lintegral is then `⊤`, and an
  integrable function has a finite lower integral (`Integrable.lintegral_lt_top`)
  — contradiction.

  TWO CORRECTIONS TO THE BRIEF, AND WHY THEY ARE STRENGTHENINGS

  BRIEF_004 asked for

      (halpha : 0 < alpha) (halpha2 : alpha < 2) ... : ¬ Integrable (fun x => exp x) μ

  1. `alpha < 2` is not needed, and the brief's own sanity check for it is
     wrong. The check reads: "with `alpha ≥ 2`-like Gaussian tails the
     exponential moment is finite, so a proof that never uses `alpha < 2` has
     proved something false". But a Gaussian tail is `e^{-x²/2}`, which is not
     a power law at all: it is eventually *below* `c x^(-alpha)` for every
     `alpha`, so it never satisfies the hypothesis. For a power tail the
     conclusion holds at every index — a tail that decays like `x^(-3)` still
     has infinite exponential moment. The real dichotomy is polynomial versus
     exponential decay, not `alpha < 2` versus `alpha ≥ 2`, and the theorem
     below is stated for every real `alpha`, which is the machine-checked form
     of that statement.
  2. `0 < alpha` is not a proof ingredient either, for the same reason: the
     divergence is in `exp` versus `rpow`, and the rpow index never enters.
     It is a *regime* hypothesis, not a proof step: for `alpha ≤ 0` the tail
     lower bound is unsatisfiable for a probability measure — it forces
     `c ≤ μ (Ici x)` for all large `x`, while `μ (Ici x) → 0` — so `alpha > 0`
     is exactly the range in which the hypothesis is *about* something. That
     makes it a statement-level remark (recorded in benchmarks/LEDGER.md C7 and
     docs/03 §D1), not a binder: keeping a hypothesis the proof never touches
     is the vacuity shape this repository rejects.

  Both corrections are recordable findings of the brief, not silent edits: see
  benchmarks/LEDGER.md C7 and the correction record at the top of
  briefs/BRIEF_004_stable_moment_obstruction.md.

  WHAT IS *NOT* MACHINE-CHECKED

  The specialization to a symmetric alpha-stable law is not formalized, because
  mathlib v4.34.0 has no such law. The brief permits this explicitly and
  requires it be said out loud rather than faked, so: §2 uses the tail bound
  `μ (Ici x) ≥ c x^(-alpha)` as its hypothesis and a caller must supply it from
  the literature. For the symmetric alpha-stable law with `alpha ∈ (0, 2)` the
  bound holds with `c = F(-alpha)` (the tail of the Zolotarev S1 representation,
  see docs/03 §D1) — that citation, not this file, is where the specialization
  lives.
-/

-- `import Mathlib` deliberately, matching ImprovedBS/Core.lean: narrow imports
-- can only be validated with a toolchain, and this tree is authored in
-- environments that have none.
import Mathlib

noncomputable section

namespace BSM

open MeasureTheory Filter
open scoped ENNReal Topology

/-!
--------------------------------------------------------------------------
§1  Analysis: a polynomial tail lower bound kills the exponential moment
--------------------------------------------------------------------------

Nothing in this section mentions a price, a strike or a payoff. That is
deliberate: the obstruction is a theorem about measures on `ℝ`, and mixing it
with option vocabulary would make it unreviewable as analysis.
-/

/-- **The one-step bound.** If the half-line `[x, ∞)` carries measure at least
`c x^(-alpha)`, then the lower integral of `exp (· + d)` is already at least
`exp (x + d) · c x^(-alpha)`.

This is the whole measure-theoretic content of the obstruction: on `[x, ∞)` the
integrand is bounded below by its value at the endpoint (`Real.exp_le_exp`), the
integral of a constant over a set is the constant times the measure
(`setLIntegral_const`), and restricting the domain can only lower an integral
(`setLIntegral_le_lintegral`). No hypothesis on the sign of `alpha` or on
whether `μ` is a probability measure is needed here — it is a bound, not a
limit. -/
theorem ofReal_mul_tail_le_lintegral_exp_add (μ : Measure ℝ) (d α c x : ℝ)
    (htail : ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)) :
    ENNReal.ofReal (Real.exp (x + d) * (c * x ^ (-α)))
      ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (y + d)) ∂μ := by
  have hset : MeasurableSet (Set.Ici x) := measurableSet_Ici
  calc ENNReal.ofReal (Real.exp (x + d) * (c * x ^ (-α)))
      = ENNReal.ofReal (Real.exp (x + d)) * ENNReal.ofReal (c * x ^ (-α)) :=
        ENNReal.ofReal_mul (Real.exp_pos _).le
    _ ≤ ENNReal.ofReal (Real.exp (x + d)) * μ (Set.Ici x) :=
        mul_le_mul_right htail _
    _ = ∫⁻ y in Set.Ici x, ENNReal.ofReal (Real.exp (x + d)) ∂μ :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in Set.Ici x, ENNReal.ofReal (Real.exp (y + d)) ∂μ :=
        setLIntegral_mono' hset fun y hy =>
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (add_le_add_right (show x ≤ y from hy) d))
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (y + d)) ∂μ :=
        setLIntegral_le_lintegral _ _

/-- **The divergence.** A probability measure whose upper tail is bounded below
by `c x^(-alpha)` has infinite exponential moment — indeed its lower integral of
`exp (· + d)` is `⊤`, for every real drift `d`.

The proof chooses the levels `x = 2 ^ k`. Each one contributes at least
`exp (2^k + d) · c · (2^k)^(-alpha) = c · exp d · (exp (2^k) / (2^k)^alpha)`,
and that sequence diverges because `exp u / u ^ s → ∞` for every real `s`
(`Real.tendsto_exp_div_rpow_atTop`), composed with `(2 ^ k) → ∞`
(`tendsto_pow_atTop_atTop_of_one_lt`). A lower integral at least as large as an
unbounded sequence of reals is `⊤` (`ENNReal.eq_top_of_forall_nnreal_le`). -/
theorem lintegral_exp_add_eq_top_of_tail_lower_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (α c x₀ d : ℝ) (hc : 0 < c)
    (htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (y + d)) ∂μ = ⊤ := by
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hseq : Tendsto
      (fun k : ℕ => Real.exp ((2 : ℝ) ^ k + d) * (c * ((2 : ℝ) ^ k) ^ (-α)))
      atTop atTop := by
    have hfun : (fun k : ℕ => Real.exp ((2 : ℝ) ^ k + d) * (c * ((2 : ℝ) ^ k) ^ (-α)))
        = fun k : ℕ =>
            (c * Real.exp d) * (Real.exp ((2 : ℝ) ^ k) / ((2 : ℝ) ^ k) ^ α) := by
      funext k
      rw [Real.exp_add, Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k),
        div_eq_mul_inv]
      ring
    rw [hfun]
    exact ((tendsto_exp_div_rpow_atTop α).comp hpow).const_mul_atTop
      (mul_pos hc (Real.exp_pos d))
  have hstep : ∀ k : ℕ, x₀ ≤ (2 : ℝ) ^ k →
      ENNReal.ofReal (Real.exp ((2 : ℝ) ^ k + d) * (c * ((2 : ℝ) ^ k) ^ (-α)))
        ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (y + d)) ∂μ :=
    fun k hk => ofReal_mul_tail_le_lintegral_exp_add μ d α c ((2 : ℝ) ^ k) (htail _ hk)
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  obtain ⟨k, hkM, hk0⟩ :=
    ((Filter.tendsto_atTop.1 hseq (r : ℝ)).and
      (Filter.tendsto_atTop.1 hpow x₀)).exists
  exact le_trans (le_of_eq (ENNReal.ofReal_coe_nnreal r).symm)
    ((ENNReal.ofReal_le_ofReal hkM).trans (hstep k hk0))

/-- The `d = 0` case of `lintegral_exp_add_eq_top_of_tail_lower_bound`: the
lower integral of `exp` itself is `⊤`. -/
theorem lintegral_exp_eq_top_of_tail_lower_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (α c x₀ : ℝ) (hc : 0 < c)
    (htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)) :
    ∫⁻ y, ENNReal.ofReal (Real.exp y) ∂μ = ⊤ := by
  simpa using lintegral_exp_add_eq_top_of_tail_lower_bound μ α c x₀ 0 hc htail

/-- **Drift does not repair the obstruction.** For every additive log-drift `d`,
`exp (· + d)` is not integrable — so no choice of drift makes the shifted
increment integrable. Equivalently (§2): in the exponential-Lévy ansatz a change
of drift acts on the exponent, and multiplying an infinite moment by
`exp d ≠ 0` leaves it infinite.

This is the form the finance needs, and it is why the obstruction cannot be
answered by "just drift it": the risk-neutral drift is exactly such a shift. -/
theorem exp_moment_infinite_add_of_tail_lower_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (α c x₀ d : ℝ) (hc : 0 < c)
    (htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)) :
    ¬ Integrable (fun y => Real.exp (y + d)) μ := by
  have htop := lintegral_exp_add_eq_top_of_tail_lower_bound μ α c x₀ d hc htail
  intro hf
  exact (ne_top_of_lt hf.lintegral_lt_top) htop

/-- **The obstruction (T6, sub-goal 1).** A probability measure on `ℝ` whose
upper tail decays no faster than a power law has no finite exponential moment.

Tail hypothesis: `μ (Ici x) ≥ c x^(-alpha)` for all `x ≥ x₀`, with `c > 0` and
any real `alpha`. The conclusion is `¬ Integrable (fun x => Real.exp x) μ`,
i.e. `E[exp X] = ∞` for `X ~ μ`.

This is the cheapest theorem in the research tier and the one that disciplines
the rest: every heavier-tailed candidate for T6 has to get past it, and it is
the reason the direction is viable only in *tempered* form (CGMY /
Boyarchenko–Levendorskii), where an `e^{-λ|x|}` damping of the Lévy measure
restores a non-empty moment strip. See docs/03 §D1. -/
theorem exp_moment_infinite_of_tail_lower_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (α c x₀ : ℝ) (hc : 0 < c)
    (htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)) :
    ¬ Integrable (fun y => Real.exp y) μ := by
  simpa using exp_moment_infinite_add_of_tail_lower_bound μ α c x₀ 0 hc htail

/-!
--------------------------------------------------------------------------
§2  The modelling claim: `E[S_T] = ∞`, hence no EMM in the ansatz
--------------------------------------------------------------------------

The theorems here consume §1 and add exactly one idea: a spot process written
as `S_T = S_0 exp X` has a first moment proportional to `E[exp X]`, so an
infinite exponential moment is an infinite price moment. The separation is
deliberate — §1 is checkable analysis, §2 is the modelling claim, and a reader
should be able to accept one while doubting the other.

`μ` here is the *law* of the log-increment `X`. The hypothesis on `μ` is the
same tail bound, so the whole content of the modelling step is the scaling, not
a second divergence argument.
-/

/-- **The spot has infinite first moment.** If the log-increment's law carries
the power tail bound, then `S_0 · E[exp X] = ∞` for every `S_0 > 0`, so the
risk-neutral expectation `E[S_T] = S_0 exp((r - q) tau)` cannot even be formed.
A positive constant rescales the moment, it does not create one. -/
theorem spot_not_integrable_of_tail_lower_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (α c x₀ S₀ : ℝ) (hS : 0 < S₀) (hc : 0 < c)
    (htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)) :
    ¬ Integrable (fun x => S₀ * Real.exp x) μ := by
  intro h
  refine exp_moment_infinite_of_tail_lower_bound μ α c x₀ hc htail ?_
  have hscale : (fun x : ℝ => S₀⁻¹ * (S₀ * Real.exp x)) = fun x : ℝ => Real.exp x := by
    funext x
    rw [← mul_assoc, inv_mul_cancel₀ hS.ne', one_mul]
  rw [← hscale]
  exact h.const_mul S₀⁻¹

/-- **No equivalent martingale measure inside the exponential-Lévy ansatz.**
For every additive log-drift `d`, the drifted spot `S_0 exp (X + d)` has
infinite first moment.

A change of drift in that ansatz is a shift of the log-increment — equivalently
a translation of the exponent — which is multiplication by `exp d > 0`. There is
therefore no `d` at which the martingale condition `E[S_T] = S_0 exp((r - q) tau)`
holds: the obstruction is a property of the *tail index*, and drift is not a
parameter that can move it. This is the negative result that makes the tempered
(CGMY) hypothesis in docs/03 §D1 earned rather than convenient. -/
theorem no_drift_makes_spot_integrable (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (α c x₀ S₀ d : ℝ) (hS : 0 < S₀) (hc : 0 < c)
    (htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)) :
    ¬ Integrable (fun x => S₀ * Real.exp (x + d)) μ := by
  intro h
  refine exp_moment_infinite_add_of_tail_lower_bound μ α c x₀ d hc htail ?_
  have hscale : (fun x : ℝ => S₀⁻¹ * (S₀ * Real.exp (x + d)))
      = fun x : ℝ => Real.exp (x + d) := by
    funext x
    rw [← mul_assoc, inv_mul_cancel₀ hS.ne', one_mul]
  rw [← hscale]
  exact h.const_mul S₀⁻¹

end BSM
