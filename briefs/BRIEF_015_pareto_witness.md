# BRIEF_015 — the Pareto witness: the obstruction's tail hypothesis, satisfied (ledger C13 finding 3)

- **Status:** **LANDED GREEN** @ `df470d1` — lean run 36119639468 (oracle lane run
  36119639528), PR [#23](https://github.com/sblaplace/improved_black_scholes/pull/23):
  `lake build` (`Built ImprovedBS.ParetoWitness`) + the `#print axioms` audit on
  all 237 entries (the 226 previous plus this brief's 11 theorems, every one on
  `[propext, Classical.choice, Quot.sound]`) + **statement pins (elab, all
  268)** + `lint` (incl. `[PARETO]`, 44 lint mutants, 5 controls) + `oracle`
  (incl. `test_pareto_witness`, mutants M24/M25) all green, on the 3rd lean run
  (`benchmarks/LEDGER.md` row 15 and its CI history). Issued in the same PR
  (documentation commit `259462a`).
- **What this is.** The first of the two **repair briefs** ledger C13 queued
  after the BSM-2 kit. The other one, the Haug / term-structure external
  anchor (C13 finding 4), stays queued and gets its number when it is issued.
  C13's provisional "BRIEF_013 = Pareto witness" label was superseded by the
  kit ordering. BRIEF_013's numbering note recorded that, and this brief takes
  the next free number.
- **Why this one next.** Three reasons, and each one can be checked in the tree:
  1. **It repairs the repository's founding rule where the rule is weakest.**
     `ImprovedBS/Levy.lean` §1–§2 is the flagship negative result: pure stable
     laws admit no martingale measure inside the exponential-Lévy ansatz. That
     result is what makes the tempered (CGMY) direction *earned rather than
     convenient*. Right now every theorem in the module carries a hypothesis
     that nothing in the tree has ever discharged:
     `htail : ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)`.
     C7 already proved in prose that `htail` is **unsatisfiable** for
     `α ≤ 0`. So satisfiability is known to matter, and it is still left as
     prose. Pins catch a statement being weakened. They do not catch a
     statement whose hypothesis is empty. C13's own words: *"the witness is the
     cheap defense for the node the thesis leans on hardest."*
  2. **It is cheap, and cheaper than C13 thought.** C13 described building the
     law by hand, as `Measure.withDensity` against Lebesgue on `[1, ∞)` with
     density `α·x^(−(α+1))`. Mathlib already ships that law at the pinned rev
     (finding F1 below). So the work is one tail integral plus citations. There
     is no `cpow`, no contour, and no limit in `Y`.
  3. **It consumes landed machinery instead of building new machinery.** The
     instantiation goes *through* `exp_moment_infinite_of_tail_lower_bound` and
     `no_drift_makes_spot_integrable` by citation (the `[PARETO]` route check).
     That is the same pattern as `[SKELETON]` and `[NONUNIQ]`.
- **Prerequisites:** BRIEF_004 (`ImprovedBS/Levy.lean`) is merged. The brief is
  **append-only**: one new module plus grading wiring. No existing declaration
  is edited, and no pre-existing pin may move.
- **Skills:** Lean 4 + mathlib at `v4.34.0` (rev `5ed2965`):
  `ProbabilityTheory.paretoMeasure`, `withDensity_apply`, `setLIntegral_congr_fun`,
  `integral_Ioi_rpow_of_lt`, `Real.rpow` algebra (`rpow_add`, `rpow_neg`,
  `div_rpow`), and `ProbabilityTheory.cdf` for the `α ≤ 0` half.
- **Budget:** one CI-only lane, since there is no local Lean toolchain. The
  mathematics is fixed and route-checked below. The expected failure mode is
  API shape at the tag (`rpow` normal forms, `ENNReal.ofReal` bookkeeping), not
  wrong mathematics.

## Findings recorded at issue

**F1. Mathlib already has the law.** Checked against the source at the pinned
rev `5ed2965256430c3649e86755f9576b54eca72435` (the `lake-manifest.json` rev for
input `v4.34.0`), `Mathlib/Probability/Distributions/Pareto.lean` provides:

    noncomputable def paretoPDFReal (t r x : ℝ) : ℝ :=
      if t ≤ x then r * t ^ r * x ^ (-(r + 1)) else 0
    noncomputable def paretoPDF (t r x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (paretoPDFReal t r x)
    noncomputable def paretoMeasure (t r : ℝ) : Measure ℝ := volume.withDensity (paretoPDF t r)
    lemma isProbabilityMeasure_paretoMeasure (ht : 0 < t) (hr : 0 < r) :
        IsProbabilityMeasure (paretoMeasure t r)
    lemma lintegral_paretoPDF_eq_one (ht : 0 < t) (hr : 0 < r) : ∫⁻ x, paretoPDF t r x = 1
    lemma paretoPDF_of_le (hx : t ≤ x) : paretoPDF t r x = ENNReal.ofReal (r * t ^ r * x ^ (-(r + 1)))
    lemma paretoPDF_of_lt (hx : x < t) : paretoPDF t r x = 0

The witness **must use `ProbabilityTheory.paretoMeasure`**. A hand-rolled
density would be a second specification that has to be pinned, audited and
trusted. The upstream one is already reviewed.

Two details are easy to trip on:

- `isProbabilityMeasure_paretoMeasure` is a **lemma, not an instance**. It
  needs `haveI := isProbabilityMeasure_paretoMeasure ht hr` before a `Levy.lean`
  theorem can be applied, because those theorems take
  `[IsProbabilityMeasure μ]`.
- Mathlib has **no tail lemma**: no `paretoMeasure (Ici x)` closed form and no
  survival function. That tail is the one genuinely new proof in this brief.

**F2. The witness decides the question exactly: the hypothesis is satisfiable
if and only if `α > 0`.** Pareto with scale `t` and shape `r` has the tail
`μ[x, ∞) = (t/x)^r = t^r · x^(−r)` for `x ≥ t`. So `htail` holds **with
equality** at `c = t^r`, `α = r`, `x₀ = t`, and that works for every `r > 0`.
Together with C7's `α ≤ 0` argument, which this brief turns into a theorem,
the result is a characterization, not just one example. The headline is
therefore an `↔` (§3 below). That is stronger than C13 asked for, and it costs
one short extra lemma.

**F3. The witness also puts C7 correction 1 on record at a concrete law.**
C7 recorded that `Levy.lean` is stated for every real `α` and needs no
`α < 2`. The witness applies at `r = 3` as well as at `r ∈ (0, 2)`. The module
should include one instance at `r = 3` (`pareto_three_exp_moment_infinite`), so
that "a tail like `x^(−3)` still has infinite exponential moment" is a checked
statement and not just a remark in a docstring.

## The mathematics to land

The new module is `ImprovedBS/ParetoWitness.lean`, in `namespace BSM`, with
`open ProbabilityTheory MeasureTheory`. Throughout, `0 < t` and `0 < r`.

**§1 The tail (the only new analysis).**

    theorem paretoMeasure_Ici (ht : 0 < t) (hr : 0 < r) {x : ℝ} (hx : t ≤ x) :
        paretoMeasure t r (Set.Ici x) = ENNReal.ofReal (t ^ r * x ^ (-r))

Route. `withDensity_apply _ measurableSet_Ici` gives the set lintegral of
`paretoPDF` over `Ici x`. On `Ici x ⊆ Ici t` the density is
`ofReal (r * t^r * y^(-(r+1)))` (`setLIntegral_congr_fun` + `paretoPDF_of_le`).
Pass to the Bochner integral with `ofReal_integral_eq_lintegral_ofReal`, or with
`integral_eq_lintegral_of_nonneg_ae`, which is the direction
`lintegral_paretoPDF_eq_one` already uses at the tag. Then use
`integral_Ici_eq_integral_Ioi`, `integral_const_mul` and
`integral_Ioi_rpow_of_lt (by linarith : -(r+1) < -1) (by linarith : 0 < x)`,
which gives `−x^(−r)/(−r)`. Finally `r * t^r * (x^(−r)/r) = t^r * x^(−r)` by
`field_simp`. **Copy the shape of `lintegral_paretoPDF_eq_one`'s proof.** It is
exactly this computation with `x := t`, and it is known to elaborate at the tag.

    theorem paretoMeasure_Ici_self (ht : 0 < t) (hr : 0 < r) :
        paretoMeasure t r (Set.Ici t) = 1        -- sanity corollary: t^r * t^(-r) = 1

**§2 The discharge.** This section is where the hypothesis stops being empty.

    theorem pareto_tail_lower_bound (ht : 0 < t) (hr : 0 < r) :
        ∀ x ≥ t, ENNReal.ofReal (t ^ r * x ^ (-r)) ≤ paretoMeasure t r (Set.Ici x)

It must be **syntactically** `Levy.lean`'s `htail` with `c := t ^ r`, `α := r`,
`x₀ := t`, so that it can be passed as an argument with no restatement. The
proof is `(paretoMeasure_Ici ht hr hx).ge`.

    theorem pareto_tail_const_pos (ht : 0 < t) : 0 < t ^ r   -- Real.rpow_pos_of_pos

**§3 The instantiations and the headline.** Each item below **cites** its
`Levy.lean` parent. None of them re-proves a divergence.

    theorem pareto_exp_moment_infinite (ht : 0 < t) (hr : 0 < r) :
        ¬ Integrable (fun y => Real.exp y) (paretoMeasure t r)
      -- cites exp_moment_infinite_of_tail_lower_bound
    theorem pareto_no_drift_makes_spot_integrable (ht : 0 < t) (hr : 0 < r) (S₀ d : ℝ) (hS : 0 < S₀) :
        ¬ Integrable (fun x => S₀ * Real.exp (x + d)) (paretoMeasure t r)
      -- cites no_drift_makes_spot_integrable
    theorem pareto_three_exp_moment_infinite :
        ¬ Integrable (fun y => Real.exp y) (paretoMeasure 1 3)          -- F3

    theorem levy_tail_hypothesis_unsatisfiable_of_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ]
        {α c x₀ : ℝ} (hα : α ≤ 0) (hc : 0 < c) :
        ¬ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x)       -- C7, now a theorem

Route for the `α ≤ 0` half. For `x ≥ max x₀ 1` we have `x^(−α) ≥ 1`
(`Real.one_le_rpow_of_pos_of_le_one_of_nonpos` or `one_le_rpow` after
`neg_nonneg`), so `ofReal c ≤ μ (Ici x)`. But
`μ (Ici x) ≤ μ (Iic (x−1))ᶜ = 1 − ofReal (cdf μ (x−1))` (`prob_compl_eq_one_sub`
and `ofReal_cdf`), and `tendsto_cdf_atTop` sends that to `0`. Pick `x` with
`cdf μ (x − 1) > 1 − c`. All three names were read in
`Mathlib/Probability/CDF.lean` at the pinned rev. **Do not** reach for a
`tendsto_measure_Ici_atTop`-style lemma. No such name was found at the tag, and
the CDF route avoids needing one.

The headline states that the hypothesis is non-vacuous at exactly the indices
the obstruction is about:

    theorem levy_tail_hypothesis_satisfiable_iff (α : ℝ) :
        (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
          ∃ c x₀ : ℝ, 0 < c ∧ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x))
        ↔ 0 < α

`→` is `levy_tail_hypothesis_unsatisfiable_of_nonpos` by contraposition.
`←` is `⟨paretoMeasure 1 α, isProbabilityMeasure_paretoMeasure one_pos h, 1, 1, one_pos, …⟩`.
Using `t = 1` gives `c = 1^α = 1` (`Real.one_rpow`), which is C13's original
`[1, ∞)` normalization.

**§4 The discriminator.** This is the check that could have come out red.
Without it, the headline's `←` direction would also pass if `htail` were
trivially true of every law. So the module has to show a law that **fails**
`htail` and **does** have a finite exponential moment:

    theorem dirac_tail_hypothesis_fails {α c x₀ : ℝ} (hc : 0 < c) :
        ¬ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ (Measure.dirac (0 : ℝ)) (Set.Ici x)
    theorem dirac_exp_integrable : Integrable (fun y => Real.exp y) (Measure.dirac (0 : ℝ))

For the failure, take `x = max x₀ 1 > 0`. Then `dirac 0 (Ici x) = 0` (by
`Measure.dirac_apply'` and `0 ∉ Ici x`), while `c * x^(−α) > 0`. The
integrability half is `integrable_dirac`, or `Integrable.of_finite` on a
finite measure with a bounded function. The mechanism is polynomial versus
exponential decay, which is `Levy.lean` correction 1. Record that in the
module header.

## The numeric route-check (measured before the Lean, per ledger C4)

The route-check was run as a scratch script before this brief was written. It
used log-spaced trapezoid quadrature, with the analytic tail added beyond `10⁶t`.
The oracle has no Pareto primitive yet (see grading wiring). Grid:
`t ∈ {0.5, 1, 2}` × `r ∈ {0.5, 1, 1.5, 3}`.

| check | lands as | result |
|---|---|---|
| `∫ density = 1` on the grid (12 laws) | upstream `lintegral_paretoPDF_eq_one` | worst residual `3.6e-9` |
| tail closed form `μ[x,∞) = (t/x)^r` vs. quadrature, 96 points `x = 1.37·t·2^k` | `paretoMeasure_Ici` | worst relative residual `5.7e-8` |
| `htail` margin with `c = t^r, α = r, x₀ = t`, 2400 points | `pareto_tail_lower_bound` | worst `\|μ[x,∞) − c x^{−α}\| = 2.2e-16`, i.e. **equality** (F2) |
| divergence lower bound `e^x (t/x)^r` at `x = 2^k`, `k = 1..6` | the `Levy.lean` route, cited | `r = 0.5`: `5.2 → 7.8e26`; `r = 3`: `0.92, 0.85, 5.8 → 2.4e22`. It dips at small `k` and then diverges (F3) |
| partial moments `∫_1^R e^x · pdf(1, 1.5)` for `R = 5, 10, 20, 40` | `pareto_exp_moment_infinite` | `9.9, 152, 4.7e5, 3.7e13`, unbounded |
| **canary**: exponential law, rate `λ ∈ {2, 5}` | §4's species | `E[e^X] = λ/(λ−1)` is finite (`2`, `1.25`); `tail / x^{−3}` at `x = 10, 50, 100` is `2e-6 → 1e-81`, so `htail` fails for every `c > 0` |
| **canary**: standard Gaussian | §4's species | `tail / x^{−10}` at `x = 10, 20` is `7.6e-14`, `2.8e-76`, so `htail` fails |
| **mutant**: density exponent `−(r+1) → −r` | oracle M24 | mass `≈ 3.0 ≠ 1` at `(1, 1.5)` (and infinite for `r ≤ 1`) |
| **mutant**: tail constant `c = t^r → 2·t^r` | oracle M25 | `htail` gap `−1.0` at `x = t`, violated |
| **mutant**: tail index `α = r → r − 1` | `[PARETO]` clause 2 | gap `−0.089` at `(2, 1.5)`, `x = 10³`, violated |
| **weak mutant**: `c = t^r → t^(−r)` | (found, recorded) | at `t = 2` the inequality **still holds** (gap `+0.875`) |

The last row is why the oracle test has to assert the tail **with equality**
at a sample of points with `t ≠ 1`, and not only the inequality `htail`. The
inequality alone does not catch the `t^(−r)` mutant when `t > 1`. When M25 is
seeded as `t^r → t^(−r)` it has to be killed by the equality assertion, and the
test's docstring should say so.

## Grading wiring (the repo changes)

* **`scripts/lean_lint.py`.** All new declarations go in `REQUIRED` **and**
  `PROTECTED`. That is 11 theorems and no defs, because the law is upstream,
  so the audit list goes `226 → 237`. Add a new **`[PARETO]` check** with four
  clauses:
  1. `pareto_exp_moment_infinite`, `pareto_no_drift_makes_spot_integrable` and
     `pareto_three_exp_moment_infinite` must **cite**
     `exp_moment_infinite_of_tail_lower_bound` or
     `no_drift_makes_spot_integrable`. The cheat this blocks is a fresh
     divergence argument (`tendsto_exp_div_rpow_atTop` inside the new module).
  2. `pareto_tail_lower_bound`'s statement must contain `t ^ r` as the constant
     and `x ^ (-r)` as the power, not a renamed or shifted index. The cheat is
     proving the bound at a weaker index than the law's shape.
  3. The module must use `paretoMeasure` and must **not** contain
     `withDensity` in a `def`. The cheat is a hand-rolled second law (F1).
  4. `levy_tail_hypothesis_satisfiable_iff` must be an `↔` whose right-hand
     side is `0 < α`. The cheat is weakening the headline to the `←` direction,
     which drops the C7 half.

  Seed one lint mutant per clause in `tests/test_lint.py`, so the count goes
  `40 → 44` mutants with 5 controls. House rule: each mutant must be killed
  **by name**, and the counts in the README and here must move with them.
* **`experiments/black_scholes.py` + `tests/test_bs.py`.** Add two primitives,
  `pareto_pdf(t, r, x)` and `pareto_tail(t, r, x)`, plus a committed
  `test_pareto_witness` that asserts the route-check table: normalization on
  the grid, the tail closed form against quadrature, `htail` **with equality**
  at `t ∈ {0.5, 2}`, the divergence of the lower-bound sequence, and both
  canaries' rejection.
* **`tests/test_mutants.py`.** Add **M24** (density exponent `−(r+1) → −r`) and
  **M25** (tail constant `t^r → t^(−r)`, the weak mutant). Each one must be
  killed by `test_pareto_witness` alone.
* **`tests/golden_statements.json`.** Append-only, both layers, with the 257
  pre-existing entries **byte-identical**, so pins go `257 → 268`. The `elab`
  layer for the new names bootstraps red on the first CI run by design, and the
  printed `elab_delta` is merged verbatim (`added 11, changed 0`).
* **`ImprovedBS.lean`:** one import line plus a blurb.
  **`ImprovedBS/Levy.lean`: no edit.** Its "WHAT IS *NOT* MACHINE-CHECKED"
  block stays true, because stable laws are still not in the tree. Its
  pointer to the witness goes in `docs/03`, not in a pinned file.
* **`benchmarks/LEDGER.md`:** a row when CI grades it, plus C7's status line
  ("`α ≤ 0` unsatisfiable") marked as proved by
  `levy_tail_hypothesis_unsatisfiable_of_nonpos`. **`docs/03` §D1 and
  `docs/04`'s queue** get the landed status.

## Done looks like (acceptance, machine-graded)

1. `lake build` is green at the pinned tag, and `#print axioms` on the new
   section shows `[propext, Classical.choice, Quot.sound]` and never `sorryAx`.
2. `levy_tail_hypothesis_satisfiable_iff` is a theorem, and its elaborated pin
   shows the `↔`, the `IsProbabilityMeasure` conjunct and `0 < α`.
3. `pareto_exp_moment_infinite` and `pareto_no_drift_makes_spot_integrable`
   are proved **through** `Levy.lean` (`[PARETO]` clause 1), so the obstruction
   theorem is exercised at a real law with no hypothesis left over.
4. `dirac_tail_hypothesis_fails` and `dirac_exp_integrable` are proved, so the
   hypothesis is shown to discriminate.
5. `lint` is green including `[PARETO]`, and each of its four mutants is red
   under mutation and killed by name.
6. The `oracle` lane is green including `test_pareto_witness`, and the mutation
   harness is green with M24 and M25 each killed by that test alone.
7. No pinned statement outside `ImprovedBS/ParetoWitness.lean` has moved, and
   `deferred: {}` is untouched.

## Explicitly out of scope

* **No α-stable law.** Mathlib still has none, and the Zolotarev tail constant
  stays a citation (`Levy.lean` header). The witness shows that the hypothesis
  *can* be met. It does not show that stable laws meet it. That gap is
  recorded, not closed.
* **The Haug / term-structure anchor** (C13 finding 4) is the other repair
  brief. It gets its number when issued.
* **No CGMY law construction.** That is the shared blocker for the
  expectation-level versions of kit items 3, 5 and 6. It needs its own
  feasibility brief, and nothing here moves it.
* **No pricing at Pareto.** The theorem is negative: no martingale measure in
  the ansatz. Pricing a Pareto-tailed asset is not a goal.

## Name-check status (ledger C3)

Read at rev `5ed2965` via the GitHub API: everything in F1, plus
`integral_Ioi_rpow_of_lt` / `integrableOn_Ioi_rpow_of_lt`
(`Analysis/SpecialFunctions/ImproperIntegrals.lean`), `tendsto_cdf_atTop`,
`ofReal_cdf` and `cdf_le_one` (`Probability/CDF.lean`). `withDensity_apply`,
`setLIntegral_congr_fun`, `integral_Ici_eq_integral_Ioi` and
`integral_eq_lintegral_of_nonneg_ae` are verified *in use* inside `Pareto.lean`
at the same rev. The following were **not** individually verified and should
be treated as CI's first name check: `prob_compl_eq_one_sub`,
`Measure.dirac_apply'`, `integrable_dirac`, and the exact `rpow` monotonicity
lemma for `x^(−α) ≥ 1`. For that last one, the fallback is
`Real.rpow_le_rpow_of_exponent_le` with base `x ≥ 1`.
