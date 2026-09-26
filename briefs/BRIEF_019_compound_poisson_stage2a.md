# BRIEF_019 — the compound-Poisson law, and the truncated CGMY jump law (BRIEF_017's Stage 2, first half)

- **Status:** **ISSUED** — PR [#26](https://github.com/sblaplace/improved_black_scholes/pull/26)
  (documentation plus a numeric route-check run at issue, no committed test).
  It changes no `.lean` file, no pin, no lint rule, no workflow; `deferred: {}`
  is untouched.
- **What this is.** Stage 2's machinery, landed as one module: the
  **compound-Poisson law** of a *probability* jump measure `ρ` at rate `λ` —
  the Poisson mixture of convolution powers `∑ₙ pₙ ρ^{*n}` — and its
  **characteristic function** `exp(λ(φ_ρ(t) − 1))`; then the tree's first
  **general-`Y` probability laws**: the **truncated CGMY jump law**
  `ν_ε/λ_ε` built from the landed `cgmyLevyDensity`, and its
  compound-Poisson marginal, whose exponent is the honest Bochner integral
  `∫_{x ∈ {|x| ≥ ε}} (e^{ivx} − 1) ν(dx)`. That is **BRIEF_017's F5
  sub-goals (i) and (ii)**, and it fixes the two conventions the rest of
  Stage 2 is written against — the truncation is **symmetric**, the
  compensation is **none** — each with a measurement behind it (F2, F3).
  It is not the CGMY law: the `ε ↓ 0` limit, its tightness and its
  identification are the *next* brief's, and this one lands the object that
  limit is taken on. Name fixed here: `ImprovedBS/CompoundPoisson.lean`.
- **Prerequisites:** BRIEF_011 (the CGMY exponent, the Lévy density
  `cgmyLevyDensity`, and `cgmy_levy_far_moment` — the far-field integrability
  this brief's mass theorem consumes), BRIEF_013 / BRIEF_014 (the Esscher and
  corner vocabulary the *next* brief needs, not this one), BRIEF_017 (the F5
  route call this brief implements the first half of), BRIEF_018 (the `Y = 0`
  member whose corner this brief's route-check cross-checks against), and
  mathlib at the pinned rev `5ed2965` (`v4.34.0`) — read at the tag, see the
  name-check section. All landed; CI-only for the Lean half.
- **Budget:** the implementation is one Lean module plus one oracle test. The
  skills it needs, named rather than waved at: a `Measure.sum`-valued mixture
  and its `Measure.sum_apply` mass; the sum/integral exchange
  (`integral_sum_measure` / `hasSum_integral_measure`) plus
  `Measure.smul_apply` for the scalar bookkeeping; `charFun_conv` induction
  for the convolution powers; `NormedSpace.expSeries_div_hasSum_exp` to close
  the tsum — the *same* lemma mathlib's own Poisson `charFun` proof closes with
  (F1); and `withDensity` + `Measure.restrict` + `lintegral` bookkeeping to
  build the truncated jump measure and prove its mass finite and positive.
  Nothing here estimates a date: the repo's only clock is the CI run.

## Findings recorded at issue

**F1. mathlib ships every rung of the mixture, and one of them is the exact
proof template.** Read at the pinned rev: `ProbabilityTheory.poissonMeasure
(r : ℝ≥0) : Measure ℕ` with `IsProbabilityMeasure`, the weights
`poissonPMFReal r n = exp (-r) * r ^ n / n!` and their exact normalisation
`hasSum_one_poissonMeasure : HasSum (fun n ↦ exp (-r) * r ^ n / n!) 1`;
`integral_poissonMeasure` and `hasSum_integral_poissonMeasure` (the
sum-over-ℕ exchange at that law); and `charFun_map_cast_poissonMeasure`, whose
proof is the template this brief's headline follows line for line —

    ∑' a, (rexp (-r) * r ^ a / a!) * cexp ((a * t) * I)
      = rexp (-r) * ∑' a, ((r * cexp (t * I)) ^ a / a!)      -- mul_pow
      = rexp (-r) * cexp (r * cexp (t * I))                  -- expSeries_div_hasSum_exp
      = cexp (r * (cexp (t * I) - 1))

— i.e. `NormedSpace.expSeries_div_hasSum_exp` is the closing lemma, and it is
*imported*, not re-derived. The measure-level pieces are equally shipped:
`Measure.sum` with `sum_apply` (`Measure/Sum.lean`), the additive convolution
`Measure.conv` (the `to_additive` twin of `Measure.mconv`, with `charFun_conv`
stated on it at the tag: `charFun (μ ∗ ν) t = charFun μ t * charFun ν t`), and
`Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean` — `integrable_sum_measure`,
`hasSum_integral_measure`, `integral_sum_measure`. So the CF identity is
**consume-shaped**: no new analysis, one sum/integral exchange and one tsum
identity. `Measure.smul_apply` (the ENNReal scalar) is the other bookkeeping
lemma. Residual API risk, named: the ENNReal bridge from
`∑' n, ofReal (pₙ)` to `ofReal (∑' n, pₙ)` on the mass row (the `ofReal_tsum`
family was **not** located at the tag); the route is `hasSum_lintegral_measure`
or `Measure.sum_apply` plus an `NNReal`/`ENNReal` `HasSum` bridge, and the
implementation must find it at the tag rather than guess (the BRIEF_012
precedent: an unmitigated risk is recorded, not hidden).

**F2. The truncation is SYMMETRIC, and that is load-bearing — a one-sided
truncation has no limit.** The route is the classical one: `ν_ε := ν` restricted
to `|x| ≥ ε` is a *finite* measure (`λ_ε = ν_ε(ℝ)`), so `ρ_ε := ν_ε/λ_ε` is a
probability law and the compound-Poisson marginal at time `τ` has CF

    exp (τ · A_ε(v)),    A_ε(v) = ∫_{|x| ≥ ε} (e^{ivx} − 1) ν(dx).

Measured for `(C, G, M) = (0.5, 5, 10)`, `τ = 0.25`, three `ε`: the error
`|τ A_ε − τ ψ_Y|` against the landed `cgmyExponent` decays like `ε^{2−Y}`
(log-log slopes **1.4904** at `Y = 1/2`, predicted `1.5`; **0.4947** at
`Y = 3/2`, predicted `0.5`) — no drift, no centering, no compensator. Truncate
**one side only** and it breaks exactly where the theory says: at `Y = 1/2` the
error still decays (slope `+0.4929`), at `Y = 3/2` it *grows* like `ε^{1−Y}`
(slope **−0.4798**), because the near-zero `i v x` piece has no partner on the
other side. The symmetric truncation is the only one whose two sides cancel
that piece, and it is the only one that can converge to the tree's exponent.
The module therefore defines `cgmyTruncatedExponent` over `{|x| ≥ ε}` and
**never** over a half-line; the `[CPoisson]` R4 clause holds it (F6).

**F3. BRIEF_017's F5(iv) says the identification is "by dominated
convergence". It cannot be — no dominating integrable function exists.** Near
zero, `|e^{ivx} − 1| ν ≤ 2ν` and `∫_{(0,δ]} ν = ∞` for every `δ > 0`, since the
density is `C x^{−1−Y}`: the truncation mass diverges, `λ_ε → ∞`, measured to
grow like `2C/Y · ε^{−Y}` (`Y = 1/2`: last-decade slope **0.546475**,
`λ_{1e−4} = 190.5817` against the asymptote `200.0000`; `Y = 3/2`: slope
**1.507914**, `λ_{1e−4} = 665216.6196` against `666666.6667`). So the `ε ↓ 0`
step is a **conditional-convergence** argument — the two sides' `i v x` pieces
cancel, the remainder is `O(x^{1−Y})` and dominated, the far field is dominated
by the tempered exponential — and it is *not* a one-line DCT. That is why this
brief lands the truncated exponent as a Bochner integral (absolutely
convergent *because* of the truncation) and leaves the limit to the next brief
with the hypothesis pinned: the correctness of the limit rests on the
*symmetric* cancellation, and the oracle test asserts the one-sided failure as
its canary (F2's row).

**F4. The truncation rate is `ε^{2−Y}`: at `Y → 2` it degenerates, so the limit
must be stated along a sequence — and the corner is not claimed.** `2 − Y → 0`
means the convergence is arbitrarily slow at the `Y ↑ 2` end, where BRIEF_014's
corner needs the *normalized* scale `C_Y = (σ²/2)(2−Y)` because a bare
`Y → 2` hits the Γ pole. This brief therefore names the `ε`-ladder as a
sequence (`εₙ = 2^{−n}`, the index mathlib's `isTightMeasureSet_of_tendsto_charFun`
and `ProbabilityMeasure.tendsto_of_tendsto_charFun` are stated for) and says out
loud that **no** law-level corner statement is claimed at `Y ↑ 2` — item 6's
expectation-level twin stays gated, as BRIEF_017 recorded, and the reason is
now quantitative rather than programmatic.

**F5. The corner consistency is measurable today, at a witness, and it is the
cross-check between the two halves of the program.** At `ε = 1e−4`, the same
truncation route at small `Y` meets BRIEF_018's landed `Y = 0` member: the gap
`|A_ε − ψ₀|` (against the oracle's `cgmy_zeroth_exponent`, the VG corner of the
landed `vgLaw`) is `O(Y)`, with `|A_ε − ψ₀|/Y` settling to **0.037511** at
`v = 0.5` and **0.158055** at `v = 2.0`. Two independently built objects — a
truncated compound-Poisson exponent and a difference-of-Gammas law — agree to
the corner rate BRIEF_017 measured. The next brief's law must reproduce this at
the `Y ↓ 0` end as a *limit of laws*, and this is the numeric shape of the
statement it will land.

**F6. The compensator is a *different* exponent, not a bookkeeping convention.**
Compensating everywhere (`e^{ivx} − 1 − ivx`) is the other standard convention,
and it lands on `ψ_Y(v) − i v m^∞` with
`m^∞ = C Γ(1−Y)(M^{Y−1} − G^{Y−1})` — verified at the oracle's own
`cgmy_exponent_one_sided_compensated` to `≤ 1.2e−15` (`m^∞ = −1.641663919` at
`Y = 3/2`, `(C, G, M) = (0.5, 5, 10)`). That is the tree's exponent *translated*
by a drift, i.e. a different law; the landed `cgmyExponent` is the
uncompensated conditionally-convergent integral (BRIEF_011's route-check and
`test_cgmy_contour` already pin the one-sided compensated closed form, which is
what this identity is assembled from). A compensator slipped into the truncated
exponent would therefore change the target silently, with no type error — the
`[CPoisson]` R4 clause forbids it in the definition's body, and the oracle test
asserts both conventions against their own closed forms so neither can drift
into the other.

**F7. mathlib ships `Measure.tilted`, and it is the route to item 3 at general
`Y`.** `Measure/Tilted.lean` has `Measure.tilted (μ) (f)`, `tilted_apply`,
`lintegral_tilted`, `setIntegral_tilted`, `integral_tilted`, `tilted_tilted`,
`tilted_comm` and `isProbabilityMeasure_tilted` — a law-level tilt with the
normalisation built in. Not used by this brief (the tilt at the general-`Y` law
is the brief after next), recorded here because it also gives the landed
`vgTilt` a bridge lemma worth having: `vgTilt = vgLaw.tilted (θ * ·)` is the
identity between the tree's `withDensity`-shaped tilt (BRIEF_018's `[VGLaw]`
R4) and mathlib's own. That bridge is *not* in this brief's scope; it is named
so the later brief consumes `Measure.tilted` instead of re-deriving the tilt
layer.

## The mathematics to land

Fix nothing yet: §1 is a general theorem about a probability measure on `ℝ`.

### §1 The compound-Poisson law and its characteristic function

    convPow ρ 0     = Measure.dirac 0
    convPow ρ (n+1) = Measure.conv (convPow ρ n) ρ          -- additive convolution

    cpLaw λ ρ       = Measure.sum (fun n ↦
                        ENNReal.ofReal (poissonPMFReal λ n) • convPow ρ n)

with `λ : ℝ≥0` (the rate, matching `poissonPMFReal`'s and `poissonMeasure`'s
type) and `ρ : Measure ℝ`. Then, for `IsProbabilityMeasure ρ`:

* `convPow ρ n` is a finite measure (the `Measure.conv` of two finite measures
  is finite: `finite_of_finite_mconv`'s additive twin, or by unfolding — the
  map of a product of finite measures is finite) and a *probability* measure;
* `charFun (convPow ρ n) t = (charFun ρ t)^n` by induction on `n`, consuming
  `charFun_conv` (and `charFun_dirac` at `n = 0`; `charFun_apply_real` is the
  `Measure ℝ` form: `charFun μ t = ∫ x, exp (t * x * I) ∂μ`);
* `(cpLaw λ ρ) Set.univ = 1` (the mass identity: `Measure.sum_apply` at
  `univ`, the scalar `Measure.smul_apply`, `(convPow ρ n) Set.univ = 1`, and
  `hasSum_one_poissonMeasure`) — so `IsProbabilityMeasure (cpLaw λ ρ)`;
* **the headline:** `charFun (cpLaw λ ρ) t = cexp (λ * (charFun ρ t − 1))`.

The headline's route, in the order the lemmas are needed: `Integrable` of
`x ↦ cexp (t*x*I)` w.r.t. `Measure.sum` (every summand is a finite measure and
`‖cexp (t x I)‖ = 1`, so `integrable_sum_measure` applies with the summable
majorant `∑' n, pₙ = 1`); `integral_sum_measure` to exchange sum and integral;
`Measure.smul_apply`/`integral_smul_measure` to pull out `pₙ`; `charFun_conv`
induction for the powers; and `NormedSpace.expSeries_div_hasSum_exp` (with
`tsum_mul_left`) to close `∑' n, pₙ z^n = exp (λ (z − 1))` — the same closing
line as mathlib's `charFun_map_cast_poissonMeasure`, which is why that lemma is
a *citation*, not a citation of the thing being proved: it is the `ρ = δ₁`
instance (F1's numeric canary asserts they agree).

### §2 The truncated CGMY jump law, and its marginal

    cgmyJumpMeasure C G M Y ε   = (volume.restrict {x | ε ≤ |x|}).withDensity
                                    (fun x ↦ ENNReal.ofReal (cgmyLevyDensity C G M Y x))
    cgmyJumpLaw C G M Y ε       = (cgmyJumpMeasure … Set.univ)⁻¹ • cgmyJumpMeasure …
    cgmyTruncatedExponent C G M Y ε v
                                = ∫ x in {x | ε ≤ |x|},
                                    (cexp (v * x * I) - 1) * (cgmyLevyDensity C G M Y x : ℂ)

For `0 < C`, `0 < G`, `0 < M`, `0 < Y`, `0 < ε`:

* the truncated measure has **finite** mass (`cgmyJumpMass_lt_top`): on
  `[ε, 1]` the density is bounded by `C ε^{−1−Y}`; on `[1, ∞)` the far-field
  bound is the landed `cgmy_levy_far_moment` at `u = 0`, and its mirror on
  `(−∞, −1]` is the same lemma at `G`;
* the mass is **nonzero** (`cgmyJumpMass_pos`), so `cgmyJumpLaw` is a
  probability measure (`cgmyJumpLaw_isProbabilityMeasure`) and its
  characteristic function is the normalised truncated integral;
* `cgmyTruncatedExponent` is **Bochner-integrable** on `{|x| ≥ ε}`
  (`cgmyTruncatedExponent_integrable`): `|e^{ivx} − 1| ≤ 2` and `ν` is finite
  *because of the truncation* — this is the honest reason the truncation is the
  right construction (F3), and it is why the def is a plain `∫` and not an
  improper integral;
* `cgmyTruncatedExponent C G M Y ε 0 = 0` (the sanity the CF needs: the
  marginal's CF at `t = 0` is `exp 0 = 1`);
* **the bridge:** at rate `τ · λ_ε` and jump law `ν_ε/λ_ε`, §1's headline
  becomes
  `charFun (cpLaw (τ λ_ε) (cgmyJumpLaw C G M Y ε)) t = cexp (τ * cgmyTruncatedExponent C G M Y ε (t : ℂ))`
  — the tree's first general-`Y` compound-Poisson marginal, with its exponent
  written as the integral the next brief takes to `cgmyExponent`.

## The numeric route-check (run at issue, per ledger C4)

Scratch script, Python 3 stdlib only, through the router's own oracle
(`cgmy_exponent`, `cgmy_gamma_neg`, `cgmy_exponent_one_sided_compensated`,
`cgmy_zeroth_exponent`, `_simpson`, `_expm1_complex`,
`_expm1_minus_z_complex`). Witness unless stated: `(C, G, M) = (0.5, 5, 10)`,
`τ = 0.25`. The mixture side is a *truncated* tsum in the script (the Lean
statement is a `tsum`), so every row carries its Poisson tail bound; the
quadrature is dyadic-graded from `ε` to 1 plus Simpson on `[1, x_max]`.

| check | lands as | result |
|---|---|---|
| mixture identity at `ρ = δ₁` (the answer is mathlib's `charFun_map_cast_poissonMeasure`, `exp (λ (e^{it} − 1))`), `λ = 0.5, 2.5`, `t = 0.3, 1.7, −2.2` | `charFun_cpLaw` (the `δ₁` instance) | worst residual `3.5e−16`, inside the Poisson tail bound — the machinery's identity, checked against a *shipped* CF |
| mixture identity at the truncated CGMY jump law, `Y = 0.7, 1.5`, `ε = 1e−2, 1e−3`, `v = 0.5, 2.0` | `charFun_cgmyCpLaw` | worst residual `1.35e−12` at `λ_ε = 20656.1127` (floating-point summation over 20656 terms), inside the tail bound — the identity is exact in the measure and does not degrade with the rate |
| `λ_ε` growth (asymptote `2C/Y · ε^{−Y}`) | BRIEF_020's ladder | last-decade slopes `0.546475` (`Y = 1/2`), `1.507914` (`Y = 3/2`); `λ_{1e−4} = 190.5817 / 665216.6196` against `200.0000 / 666666.6667` |
| `\|τ A_ε − τ ψ_Y\|` decay, predicted `ε^{2−Y}` | BRIEF_020's limit | slopes `1.4904` (`Y = 1/2`, `v = 0.5, 2.0`), `0.4947` (`Y = 3/2`) — the exponent of the *symmetric* truncation, no centering |
| **canary**: the ONE-SIDED truncation | R4's measured cheat | `Y = 1/2`: error decays (slope `+0.4929`); `Y = 3/2`: error **grows** (slope `−0.4798` = `ε^{1−Y}`) — the forbidden version, and the reason `{|x| ≥ ε}` is the only truncation the module may write |
| compensating everywhere (the other convention) | F6, the route not taken | matches `ψ_Y − i v m^∞` to `1.2e−15`; `m^∞ = −0.116083169` (`Y = 1/2`), `−1.641663919` (`Y = 3/2`) — a *translated* law, i.e. a silently different target |
| corner consistency vs BRIEF_018's landed `vgLaw` (`cgmy_zeroth_exponent`), `ε = 1e−4` | BRIEF_020's `Y ↓ 0` end | `\|A_ε − ψ₀\|/Y → 0.037511` (`v = 0.5`), `0.158055` (`v = 2.0`) at `Y = 1e−3` — `O(Y)`, the corner rate |
| **mutants** at `(Y, ε, v) = (1.5, 1e−3, 1)` | M34–M38 | log-scale separations: `1/n!` dropped `47757.20`; jump law not normalised `106663583.68`; the `−1` dropped `5164.03`; tempering legs swapped `0.74` vs `0.38`; one-sided truncation `7.98` |

Two rows deserve their own line. First, the **canary row**: the failing route is
not an approximation error, it is a *different family* (a half-line truncation),
and the test must assert the divergence (the `Y = 3/2` growth) rather than a
mismatch of values. Second, the **mass row**: it is the reason F3 exists — a
`λ_ε → ∞` at a rate `ε^{−Y}` is what makes "dominated convergence" impossible
and the conditional-convergence argument necessary, and the test asserts the
growth against its closed form so a later "simplification" of the truncation
cannot quietly restore a DCT-shaped (and false) proof.

## What the implementation must land

* **Lean, `ImprovedBS/CompoundPoisson.lean`** (name fixed here), in
  `namespace BSM`, all declarations in `REQUIRED` + `PROTECTED`: **5 defs** —
  `convPow`, `cpLaw`, `cgmyJumpMeasure`, `cgmyJumpLaw`,
  `cgmyTruncatedExponent` — and **12 theorems**: `convPow_isFiniteMeasure`,
  `convPow_isProbabilityMeasure`, `charFun_convPow`, `cpLaw_isProbabilityMeasure`,
  `cpLaw_apply_univ`, `charFun_cpLaw`, `cgmyJumpMass_lt_top`,
  `cgmyJumpMass_pos`, `cgmyJumpLaw_isProbabilityMeasure`,
  `cgmyTruncatedExponent_integrable`, `cgmyTruncatedExponent_zero`,
  `charFun_cgmyCpLaw`. Pins move `292 → 309`, the audit list `256 → 268`
  (theorems only, the repo's convention); no pre-existing entry may move. If
  the landed count differs, the ledger records it the way C21 did.
* **Lint, a `[CPoisson]` check with four clauses** (one lint mutant each;
  lint mutants `48 → 52`, the five must-stay-green controls untouched):
  * **R1 the mixture is the mixture.** `cpLaw`'s RHS cites `Measure.sum`,
    `poissonPMFReal` and `convPow`; it does **not** cite `withDensity` or
    `Measure.map` — the cheat is a hand-rolled density law, or the Poisson law
    pushed forward, which is right only for `ρ = δ₁` and is not the
    construction.
  * **R2 the CF consumes the shipped exchange.** `charFun_cpLaw`'s body cites
    `charFun_conv` **and** one of `integral_sum_measure` /
    `hasSum_integral_measure`; it does **not** cite
    `charFun_map_cast_poissonMeasure` (that is the `δ₁` instance the
    route-check uses as a numeric canary, not the proof of the general
    theorem).
  * **R3 the jump law is built from the landed density.** `cgmyJumpMeasure`'s
    body cites `cgmyLevyDensity` and the truncation set `{x | ε ≤ |x|}`;
    `cgmyJumpMass_lt_top` cites the landed `cgmy_levy_far_moment` — the
    far-field integrability is inherited, not re-derived; no second density
    function may appear in the module.
  * **R4 symmetric truncation, no compensator.** No declaration in the module
    may truncate a half-line (`Ioi ε`, `Ici ε`, `Iic (−ε)`, `{ε ≤ x}` as a
    set-builder on one side, …), and `cgmyTruncatedExponent`'s body must not
    carry a compensation term (`- v * x * I` and its spellings). Both are
    *measured* cheat classes (F2's divergence row, F6's translated target),
    not stylistic rules.
* **Oracle + tests:** primitives `poisson_weights` (log-space — the rate runs
  into the thousands), `poisson_tail`, `cp_law_cf_mixture`,
  `cp_law_cf_closed`, `cgmy_jump_mass`, `cgmy_jump_cf`,
  `cgmy_truncated_exponent`, `cgmy_law_cf`; the committed
  `tests/test_bs.py::test_compound_poisson` asserting the route-check table
  above (the two mixture rows against their independent sides, the two growth
  rows against closed forms, the one-sided canary, the compensation row, the
  corner row); and mutants **M34–M38**, each killed by that test alone.
  Counts: oracle tests `24 → 25`, oracle mutants `34 → 39`.
* **Docs:** `docs/03` §D1 item 4/6's "gated on a law construction" sentence
  gets the Stage-2 split (2a landed here, 2b named); `docs/04`'s queue row
  and the item-6 line get the same; `README`'s CGMY-law note gets the
  Stage-1 → Stage-2a progress; `benchmarks/LEDGER.md` gets the row.
* **Corrections to record if measurement repeats:** F3 (BRIEF_017's F5(iv)
  "by dominated convergence" is not available) and F6 (the compensator is a
  translation, not a convention) are the two that change what a reader of
  BRIEF_017 would otherwise implement.

## Done looks like (acceptance, machine-graded)

1. `lake build` green at the tag; every new constant on
   `[propext, Classical.choice, Quot.sound]`; no `sorryAx`; `deferred: {}`
   untouched.
2. Statement pins move by exactly the landed count in **both** layers with the
   292 pre-existing entries byte-identical; `lint` green including `[CPoisson]`
   with its four cheats killed by name and nothing else; `oracle` green
   including `test_compound_poisson` and M34–M38, each killed by that test
   alone.
3. `cpLaw` is the Poisson mixture of convolution powers (R1), the CF headline
   consumes the shipped sum/integral exchange and `charFun_conv` (R2), the jump
   law is `cgmyLevyDensity`-built and its mass is finite by the landed
   far-field moment (R3), and the truncated exponent is symmetric with no
   compensator (R4).
4. The expectation-level statements that need a *general-`Y` law* still do not
   exist — this brief lands the laws' machinery and the truncated family, and
   says so; item 6's expectation-level twin stays gated on the next brief.
5. A row in `benchmarks/LEDGER.md` when CI grades it, and the docs queue
   updated: Stage 2a landed, Stage 2b and G1 still open with their names.

## Explicitly out of scope

* **The `ε ↓ 0` limit and the CGMY law itself** (Stage 2b): no
  `Tendsto` of `cgmyTruncatedExponent` to `cgmyExponent`, no tightness, no
  `isTightMeasureSet_of_tendsto_charFun`, no `ProbabilityMeasure.tendsto_of_tendsto_charFun`,
  no `Measure.ext_of_charFun` identification, no law named `cgmyLaw`. That
  brief is the next number, and F3/F4 above are its specification.
* **The complex-rate Γ integral (G1)** and the one-sided tempered integral
  identity: the `ε ↓ 0` argument needs the closed form of
  `∫_0^∞ (e^{ivx} − 1) e^{−Mx} x^{−1−Y} dx`, which is where G1 (or an
  equivalent conditional-convergence argument) enters. Not needed to *state*
  §1–§2, so not here.
* **The mgf on the strip, the Esscher tilt at the law, and items 3/5 at
  general `Y`** (the brief after next): `Measure.tilted` (F7) and the landed
  `esscher_cgmy_shift` are the pieces, and they are not this module's.
* **Item 6's expectation-level twin** at `Y ↑ 2` (F4: the normalized corner),
  and any law-level corner statement.
* **Any change to `ImprovedBS/CGMY.lean`, `VGLaw.lean`, `Esscher.lean`,
  `Corner.lean`, `Skeleton.lean`, `Pricing.lean` or any landed pin**; the
  landed CGMY density and far-field moment are consumed, not re-derived.

## Name-check status (ledger C3)

Every mathlib name in F1–F2 and §1–§2 was read at the pinned rev `5ed2965`
through the GitHub API (`gh api …/contents/<path>?ref=<rev> --jq .content |
base64 -d`): `Probability/Distributions/Poisson/Basic.lean` (the whole file,
including the `charFun_map_cast_poissonMeasure` proof F1 quotes),
`MeasureTheory/Measure/Sum.lean` (`Measure.sum`, `sum_apply`),
`MeasureTheory/Integral/Bochner/SumMeasure.lean` (`integrable_sum_measure`,
`hasSum_integral_measure`, `integral_sum_measure`),
`MeasureTheory/Group/Convolution.lean` (`Measure.mconv` and its `to_additive`
twin `Measure.conv`; the file header states both), the convolution lemmas'
attribute shape (`@[to_additive]`, no explicit names — so the additive twins'
*generated* names are to be confirmed by `#check` at implementation, which is
the one residual naming risk this issue could not close),
`MeasureTheory/Measure/CharacteristicFunction/Basic.lean` (`charFun_apply_real`,
`charFun_conv`, `charFun_dirac`, `Measure.ext_of_charFun`),
`MeasureTheory/Measure/Module.lean` (`Measure.smul_apply`),
`MeasureTheory/Measure/Map.lean` (`map_apply`), and
`MeasureTheory/Measure/Typeclasses/Probability.lean` (`isProbabilityMeasure_map`).
The two analytical risks are named rather than hidden: the ENNReal `tsum`
bridge on the mass row (F1's residual), and the `withDensity`/`lintegral`
bookkeeping when the truncated mass is shown finite — the same class of failure
the landed briefs hit and recorded.
