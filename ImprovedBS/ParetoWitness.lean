/-
  ImprovedBS/ParetoWitness.lean — BRIEF_015: the Pareto witness for the tail
  hypothesis of ImprovedBS/Levy.lean (ledger C13 finding 3).

  What this file proves, in one line:

      (∃ probability law with  μ[x, ∞) ≥ c · x^(−α)  eventually, c > 0)  ↔  0 < α.

  WHY IT EXISTS

  Every theorem in Levy.lean — the moment obstruction that makes the tempered
  (CGMY) direction earned rather than convenient — carries the hypothesis

      htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)

  and until this module nothing in the tree had ever discharged it. Statement
  pins catch a claim being weakened; they do not catch a claim whose hypothesis
  is empty. This file closes that gap in both directions:

  * §1–§3: mathlib's own `ProbabilityTheory.paretoMeasure t r` has the exact
    tail `μ[x, ∞) = t^r · x^(−r)` for `x ≥ t`, so it meets `htail` WITH
    EQUALITY at `c = t^r`, `α = r`, `x₀ = t`, for every `r > 0`. The Levy.lean
    obstruction is then instantiated at it BY CITATION (the `[PARETO]` lint
    check) — no hypothesis is left over.
  * §3: ledger C7's prose remark — `htail` is unsatisfiable for `α ≤ 0` — is
    now a theorem (`levy_tail_hypothesis_unsatisfiable_of_nonpos`), so the
    headline is an `↔`, a characterization rather than one example.
  * §4: the discriminator. A green `←` would also be green if `htail` were
    trivially true of every law, so the module exhibits a law (the Dirac mass
    at `0`) that FAILS `htail` and HAS a finite exponential moment. The
    mechanism is polynomial versus exponential decay — Levy.lean correction 1.

  The law is NOT hand-rolled (BRIEF_015 finding F1): a second density would be
  a second specification to pin and trust, and the upstream one is reviewed.
  `isProbabilityMeasure_paretoMeasure` is a lemma, not an instance, hence the
  local `have`s below.

  WHAT IS STILL NOT MACHINE-CHECKED

  No α-stable law: mathlib has none. The witness shows the hypothesis CAN be
  met; that stable laws meet it remains the Zolotarev citation in Levy.lean.
-/

import Mathlib
import ImprovedBS.Levy

noncomputable section

namespace BSM

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-!
--------------------------------------------------------------------------
§1  The tail — the only new analysis
--------------------------------------------------------------------------
-/

/-- **The Pareto tail.** For `x ≥ t`, `μ[x, ∞) = t^r · x^(−r)`. The route is the
shape of mathlib's `lintegral_paretoPDF_eq_one` with the lower limit moved from
`t` to `x`: density on `Ici x ⊆ Ici t`, Bochner integral, and
`integral_Ioi_rpow_of_lt`. -/
theorem paretoMeasure_Ici {t r : ℝ} (ht : 0 < t) (hr : 0 < r) {x : ℝ} (hx : t ≤ x) :
    paretoMeasure t r (Set.Ici x) = ENNReal.ofReal (t ^ r * x ^ (-r)) := by
  have hx0 : 0 < x := lt_of_lt_of_le ht hx
  have hcongr : ∫⁻ y in Set.Ici x, paretoPDF t r y
      = ∫⁻ y in Set.Ici x, ENNReal.ofReal (r * t ^ r * y ^ (-(r + 1))) :=
    setLIntegral_congr_fun measurableSet_Ici (fun y hy => paretoPDF_of_le (le_trans hx hy))
  have hint : IntegrableOn (fun y : ℝ => r * t ^ r * y ^ (-(r + 1))) (Set.Ici x) := by
    have h := integrableOn_Ioi_rpow_of_lt (by linarith : -(r + 1) < -1) hx0
    have hIci : IntegrableOn (fun y : ℝ => y ^ (-(r + 1))) (Set.Ici x) := by
      exact (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr h
    exact hIci.const_mul (r * t ^ r)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici x)]
      fun y : ℝ => r * t ^ r * y ^ (-(r + 1)) := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    filter_upwards with y hy
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hy
    show (0 : ℝ) ≤ r * t ^ r * y ^ (-(r + 1))
    positivity
  rw [paretoMeasure, withDensity_apply _ measurableSet_Ici, hcongr,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -(r + 1) < -1) hx0]
  have h1 : -(r + 1) + 1 = -r := by ring
  rw [h1]
  have hr0 : r ≠ 0 := hr.ne'
  calc r * t ^ r * (-x ^ (-r) / -r) = t ^ r * x ^ (-r) * (r / r) := by ring
    _ = t ^ r * x ^ (-r) := by rw [div_self hr0, mul_one]

/-- Sanity corollary: all of the mass sits on `[t, ∞)`. -/
theorem paretoMeasure_Ici_self {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    paretoMeasure t r (Set.Ici t) = 1 := by
  rw [paretoMeasure_Ici ht hr le_rfl, ← Real.rpow_add ht]
  simp

/-!
--------------------------------------------------------------------------
§2  The discharge — the hypothesis stops being empty
--------------------------------------------------------------------------
-/

/-- **`htail` at Pareto**, syntactically Levy.lean's hypothesis with
`c := t ^ r`, `α := r`, `x₀ := t`, so it is passed with no restatement. -/
theorem pareto_tail_lower_bound {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∀ x ≥ t, ENNReal.ofReal (t ^ r * x ^ (-r)) ≤ paretoMeasure t r (Set.Ici x) :=
  fun _ hx => (paretoMeasure_Ici ht hr hx).ge

/-- The tail constant is positive. -/
theorem pareto_tail_const_pos {t r : ℝ} (ht : 0 < t) : 0 < t ^ r :=
  Real.rpow_pos_of_pos ht r

/-!
--------------------------------------------------------------------------
§3  The instantiations and the headline
--------------------------------------------------------------------------
-/

/-- **The obstruction at a real law.** Pareto has no finite exponential moment
— proved THROUGH `exp_moment_infinite_of_tail_lower_bound`, not re-derived. -/
theorem pareto_exp_moment_infinite {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ¬ Integrable (fun y => Real.exp y) (paretoMeasure t r) := by
  have := isProbabilityMeasure_paretoMeasure ht hr
  exact exp_moment_infinite_of_tail_lower_bound (paretoMeasure t r) r (t ^ r) t
    (pareto_tail_const_pos ht) (pareto_tail_lower_bound ht hr)

/-- **No drift repairs it at Pareto** — through `no_drift_makes_spot_integrable`. -/
theorem pareto_no_drift_makes_spot_integrable {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (S₀ d : ℝ) (hS : 0 < S₀) :
    ¬ Integrable (fun x => S₀ * Real.exp (x + d)) (paretoMeasure t r) := by
  have := isProbabilityMeasure_paretoMeasure ht hr
  exact no_drift_makes_spot_integrable (paretoMeasure t r) r (t ^ r) t S₀ d hS
    (pareto_tail_const_pos ht) (pareto_tail_lower_bound ht hr)

/-- **C7 correction 1 at a concrete law** (BRIEF_015 F3): a tail like `x^(−3)`
— outside the stable range `α < 2` — still has infinite exponential moment. -/
theorem pareto_three_exp_moment_infinite :
    ¬ Integrable (fun y => Real.exp y) (paretoMeasure 1 3) :=
  pareto_exp_moment_infinite one_pos (by norm_num)

/-- **Ledger C7, now a theorem.** For `α ≤ 0` the tail hypothesis is
unsatisfiable by any probability measure: it forces `μ[x, ∞) ≥ c` for all large
`x`, while the cdf tends to `1`. -/
theorem levy_tail_hypothesis_unsatisfiable_of_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α c x₀ : ℝ} (hα : α ≤ 0) (hc : 0 < c) :
    ¬ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x) := by
  intro htail
  have hlim : Tendsto (cdf μ) atTop (𝓝 1) := tendsto_cdf_atTop μ
  obtain ⟨y₀, hy₀⟩ :=
    Filter.eventually_atTop.1 ((tendsto_order.1 hlim).1 (1 - c) (by linarith))
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = max x₀ (max 1 (y₀ + 1)) := ⟨_, rfl⟩
  have hx₀ : x₀ ≤ x := by rw [hxdef]; exact le_max_left _ _
  have hx1 : 1 ≤ x := by rw [hxdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hxy : y₀ + 1 ≤ x := by rw [hxdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hpow : 1 ≤ x ^ (-α) := Real.one_le_rpow hx1 (by linarith)
  have hcx : c ≤ c * x ^ (-α) := le_mul_of_one_le_right hc.le hpow
  have hd : 1 - c < cdf μ (x - 1) := hy₀ _ (by linarith)
  have hdisj : Disjoint (Set.Ici x) (Set.Iic (x - 1)) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : x ≤ z := hz1
    have h2 : z ≤ x - 1 := hz2
    linarith
  have hsum : ENNReal.ofReal c + ENNReal.ofReal (cdf μ (x - 1)) ≤ 1 := by
    calc ENNReal.ofReal c + ENNReal.ofReal (cdf μ (x - 1))
        ≤ μ (Set.Ici x) + μ (Set.Iic (x - 1)) :=
          add_le_add ((ENNReal.ofReal_le_ofReal hcx).trans (htail x hx₀))
            (ofReal_cdf μ (x - 1)).le
      _ = μ (Set.Ici x ∪ Set.Iic (x - 1)) := (measure_union hdisj measurableSet_Iic).symm
      _ ≤ 1 := prob_le_one
  rw [← ENNReal.ofReal_add hc.le (cdf_nonneg μ _), ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff zero_le_one] at hsum
  linarith

/-- **The headline (BRIEF_015).** Levy.lean's tail hypothesis is satisfiable by
some probability law on `ℝ` exactly when `α > 0`: `→` is C7 as a theorem, `←`
is the Pareto law at scale `1` (C13's original `[1, ∞)` normalization, where
the constant is `1^α = 1`). -/
theorem levy_tail_hypothesis_satisfiable_iff (α : ℝ) :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∃ c x₀ : ℝ, 0 < c ∧ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x))
    ↔ 0 < α := by
  constructor
  · rintro ⟨μ, hμ, c, x₀, hc, htail⟩
    have := hμ
    by_contra hα
    exact levy_tail_hypothesis_unsatisfiable_of_nonpos μ (not_lt.1 hα) hc htail
  · intro hα
    refine ⟨paretoMeasure 1 α, isProbabilityMeasure_paretoMeasure one_pos hα, 1, 1,
      one_pos, ?_⟩
    intro x hx
    have h := pareto_tail_lower_bound (t := 1) (r := α) one_pos hα x hx
    rwa [Real.one_rpow] at h

/-!
--------------------------------------------------------------------------
§4  The discriminator — the check that could have been red
--------------------------------------------------------------------------
-/

/-- The Dirac mass at `0` fails the tail hypothesis for every `c > 0`, `α`, `x₀`:
at `x = max x₀ 1 > 0` its upper tail is `0`. -/
theorem dirac_tail_hypothesis_fails {α c x₀ : ℝ} (hc : 0 < c) :
    ¬ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ (Measure.dirac (0 : ℝ)) (Set.Ici x) := by
  intro htail
  have hx1 : (1 : ℝ) ≤ max x₀ 1 := le_max_right _ _
  have hpos : 0 < c * (max x₀ 1) ^ (-α) :=
    mul_pos hc (Real.rpow_pos_of_pos (by linarith) _)
  have hnot : ¬ (max x₀ 1 ≤ 0) := not_le.2 (by linarith)
  have hzero : (Measure.dirac (0 : ℝ)) (Set.Ici (max x₀ 1)) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Ici]
    simp [hnot]
  have h := htail (max x₀ 1) (le_max_left _ _)
  exact (not_le.2 (ENNReal.ofReal_pos.2 hpos)) (h.trans_eq hzero)

/-- ... and the Dirac mass at `0` has a finite exponential moment. Together with
`dirac_tail_hypothesis_fails`, `htail` is shown to discriminate. -/
theorem dirac_exp_integrable :
    Integrable (fun y => Real.exp y) (Measure.dirac (0 : ℝ)) := by
  exact (integrable_const (Real.exp 0)).congr (ae_eq_dirac (fun y => Real.exp y)).symm

end BSM
