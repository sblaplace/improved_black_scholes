# BRIEF_017 — the CGMY law: feasibility, the reachable core, and the route (the audit the note asked for)

- **Status:** **ISSUED** — PR [#25](https://github.com/sblaplace/improved_black_scholes/pull/25),
  documentation plus a numeric route-check run at issue (no committed test).
  This is the **feasibility brief** the queue asked for before any law
  construction: it audits mathlib at the pinned rev, prices the candidate
  routes, makes the route call, and specifies the first implementation brief.
  It changes no `.lean` file, no pin, no lint rule, no workflow; `deferred: {}`
  is untouched.
- **What this is.** The tree has no CGMY **law**: every CGMY declaration that
  exists is about the characteristic **exponent**, its strip, its decay, its
  Esscher shift and its `Y ↑ 2` corner. The expectation-level twins of three
  kit items are gated on a `Measure ℝ` that the tree cannot name:
  - **item 3** (Esscher drift): "the expectation-level drift
    `∫ S e^x dμ^θ = S e^{(r−q)τ}` against an actual tilted measure"
    (`briefs/BRIEF_013_esscher_drift.md` §"explicitly out of scope");
  - **item 5** (the model-free skeleton): landed *for any law* with the drift
    condition (`ImprovedBS/Skeleton.lean`), but never instantiated at a
    non-Gaussian family member;
  - **item 6** (CGMY → GBM): the corner is a limit of *exponents*, not of
    laws, so the law-level corner statement does not exist either
    (`ImprovedBS/Corner.lean`, BRIEF_014).
  This brief decides which of those a first law can discharge, and by what
  construction.
- **Prerequisites:** BRIEF_011 (the concrete exponent and strip),
  BRIEF_013 (Esscher), BRIEF_014 (the `Y ↑ 2` corner). No new toolchain: the
  route-check below ran in the router's stdlib-only oracle.
- **Budget:** this brief is CI-only and documentation-only. The *implementation*
  it specifies is one Lean module plus one oracle test and is scoped to the
  reachable core (Stage 1). Nothing here estimates a date: the repo's only clock
  is the CI run.

## Findings recorded at issue

**F1. The general theorem is not in mathlib, and its absence is load-bearing.**
At the pinned rev `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`) the tree
contains **no** Lévy–Khintchine representation, **no** infinitely divisible
measures, **no** stable laws, **no** subordinators or convolution semigroups,
and **no** Bochner/positive-definite-function theorem. The two files whose names
suggest otherwise are about convergence: `MeasureTheory/Measure/LevyConvergence.lean`
and `MeasureTheory/Measure/LevyProkhorovMetric.lean`. So "there exists a law
with this characteristic exponent" cannot be cited; the law has to be **built**.

**F2. What *is* in mathlib, and it is more than the first pass of the review
assumed — four layers, all read at the tag:**

1. **A real probability law with a density**, `Mathlib/Probability/Distributions/Gamma.lean`:
   `gammaPDFReal a r x = r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))` on
   `0 ≤ x` (zero below), `gammaPDF`, and
   `gammaMeasure a r = volume.withDensity (gammaPDF a r)` with
   `isProbabilityMeasure_gammaMeasure (0 < a) (0 < r)`. This is the only
   CGMY-family marginal mathlib ships.
2. **The Γ-integral identity that makes its mgf computable**,
   `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`:
   `integral_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (0 < a) (0 < r) :
   ∫ t in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a`
   (real rate, real exponent), `Complex.Gamma_eq_integral`,
   `integral_cpow_mul_exp_neg_mul_Ioi` (real rate, **complex** exponent),
   `Real.Gamma_add_one (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s`, and the
   pole conventions `Real.Gamma_zero : Gamma 0 = 0`,
   `Real.Gamma_neg_nat_eq_zero : Gamma (-n) = 0`.
3. **The moment-generating machinery**, `Mathlib/Probability/Moments/`:
   `mgf X μ t = μ[fun ω ↦ exp (t * X ω)]`, `cgf`,
   `integrableExpSet`, `analyticOn_mgf`, `iteratedDeriv_mgf`
   (`n`-th derivative at `t` is `μ[X^n * exp (tX)]`), `hasDerivAt_mgf`; and
   `complexMGF X μ z = μ[fun ω ↦ cexp (z * X ω)]` with
   `analyticOn_complexMGF` / `differentiableOn_complexMGF` on the strip
   `{z | z.re ∈ interior (integrableExpSet X μ)}` and the recorded fact that
   on the imaginary axis `complexMGF` **is** the characteristic function. This
   is the layer that makes the expectation-level twins statements about
   integrals rather than about a new branch of analysis.
4. **The convergence layer**, `MeasureTheory/Measure/CharacteristicFunction/Basic.lean`,
   `IntegralCharFun.lean`, `LevyConvergence.lean`, `Prokhorov.lean`:
   `charFun`, `charFun_conv` (the CF of `MeasureTheory.mconv` is the product),
   `charFun_prod`, `Measure.ext_of_charFun` (a finite measure is determined by
   its CF), `measureReal_abs_gt_le_integral_charFun` (a quantitative tail bound
   from an integral of `1 − charFun`), `isTightMeasureSet_of_tendsto_charFun`
   (**tightness** from pointwise CF convergence),
   `ProbabilityMeasure.tendsto_of_tendsto_charFun` (**Lévy's continuity
   theorem**), and `isCompact_closure_of_isTightMeasureSet` (**Prokhorov**).
   Plus `MeasureTheory.mconv` (`MeasureTheory/Group/Convolution.lean`).

**F3. The family's `Y ↓ 0` corner is the Variance-Gamma law, and its building
block is exactly `gammaMeasure`.** As `Y ↓ 0`, with `C` fixed,
`Γ(−Y) ~ −1/Y` and `((M−iv)^Y − M^Y) → Y·log((M−iv)/M)`, so the landed
exponent (`ImprovedBS/CGMY.lean`'s `cgmyExponent`) has a finite limit

    ψ₀(v) = C·[log (M/(M − iv)) + log (G/(G + iv))].

That is the CF of `X = Z_M − Z_G`, two **independent Gamma laws**
`Z_M ~ Gamma(shape Cτ, rate M)`, `Z_G ~ Gamma(shape Cτ, rate G)` — the classical
Madan–Seneta difference-of-Gammas representation of the Variance-Gamma model,
which is the CGMY family at `Y = 0` (the Lévy density `C e^{−M x} x^{−1}` on
the positive side). Consequences, all measured in the route-check below:

- the mgf is `E[e^{uX}] = (M/(M−u))^{Cτ} · (G/(G+u))^{Cτ}` on the open strip
  `−G < u < M` — **the same strip** the landed `cgmyCumulant` / `cgmyExponent_strip`
  work uses, with `u = 1` finite exactly when `1 < M` (the landed numéraire
  condition `cgmy_numeraire_strip`);
- the Esscher tilt is the same `(G, M) ↦ (G+θ, M−θ)` map, and the landed
  zero-drift parameter `θ₀ = (M−G−1)/2` is the exact zero of the `Y = 0` drift;
- **the limit is elementary in Lean**: `Real.Gamma_add_one` at `s = −Y` gives
  `Gamma (−Y) * Y = −Gamma (1 − Y)`, so `Γ(−Y)·Y → −Γ(1) = −1` by continuity —
  no reflection formula, no new Γ analysis. The companion limit
  `((M−iv)^Y − M^Y)/Y → log((M−iv)/M)` is the derivative of `Y ↦ cexp` at `0`;
- the same parameters are the **external anchor's** parameters: BRIEF_016
  pins Carr–Madan (1999) Case 4, whose VG law this is, under the map
  `C = 1/ν`, `s = √(θ² + 2σ²/ν)`, `G, M = (s ± θ)/σ²` (BRIEF_016 finding F3).
  So the first CGMY-family law the tree can build is a **published** one.

**F4. `Y = 0` and `Y = 1` are silent, not loud — and that is the trap.**
`Real.Gamma 0 = 0` and `Real.Gamma (−1) = 0` at the tag, so the raw formula
`cgmyExponent C G M 0 v` is **`0` for every `v`**, i.e. the degenerate Dirac
law (a deterministic forward), and `Y = 1` is the same silent collapse. This is
the C17 pattern again, one corner over: at `Y = 2` the false bare statement
"the limit is the value" is wrong but still typechecks; here the false bare
statement is *identically zero*. The corner **must** be a limit statement
(`Tendsto … (𝓝[>] 0) …`), never an evaluation. The oracle is already loud where
Lean is silent (`cgmy_gamma_neg` raises for `Y ∉ (0,2)` and for `Y = 1`), which
is the correct split to keep.

**F5. The general-`Y` law is reachable, but it is a program, not a corner.**
The construction that matches the tooling mathlib actually has is the classical
one: truncate the Lévy measure to `|x| ≥ ε` (a **finite** measure), form the
**compound-Poisson** law of the truncated jumps, and let `ε ↓ 0`; identify the
limit by its CF, which converges pointwise to `exp(τ ψ_CGMY(v))`; the limit
exists by **tightness** (`isTightMeasureSet_of_tendsto_charFun`) plus
**Prokhorov compactness** (`isCompact_closure_of_isTightMeasureSet`) and is
unique by **CF uniqueness** (`Measure.ext_of_charFun`). What is missing is not
a theorem of analysis but the *construction*: (i) the compound-Poisson law as a
`Measure`-valued series over convolution powers (`MeasureTheory.mconv` exists;
the Poisson mixture and its summability do not), (ii) the CF of that mixture as
`exp(λ(∫ e^{ivx} dρ̂ − 1))` (needs `charFun_conv` plus a sum/integral exchange),
(iii) the CF limit of the truncation family at the concrete CGMY exponent (the
truncated Lévy-density integrals), and (iv) the identification of the limit's
CF with `cgmyExponent` by dominated convergence. Each is a brief-sized piece;
together they are the research tier, and none of them is needed for Stage 1.

**F6. The routes that do not work at the tag, so no brief is written against
them.** (a) *Cite a general existence theorem* (Lévy–Khintchine / Bochner):
absent (F1); carrying it as a hypothesis would be the "unbacked premise" the
tree's acceptance rules forbid. (b) *Subordination* (Brownian motion under a
tempered-stable subordinator): the subordinator's own law is a tempered-stable
law, which is the thing being built — circular; and for general `G ≠ M` the
CGMY process is not a one-factor Brownian subordination anyway.
(c) *Closed-form density*: CGMY has no elementary density at general `Y` (the
`Y = 0` density is already a modified-Bessel expression; nothing at `Y = 1`).
(d) *Evaluate the exponent at `Y = 0`*: F4 — silently the Dirac law.

## The route call (decided here, as the queue asked)

**Two stages. Stage 1 is the brief that gets written next; Stage 2 is specified
and queued behind it.**

- **Stage 1 — land the family's `Y = 0` member as a real probability measure.**
  New module (proposed `ImprovedBS/VGLaw.lean`), built **only** from
  `ProbabilityTheory.gammaMeasure` and the Γ-integral identity of F2:
  1. `vgLaw (C τ G M) : Measure ℝ` — the law of `Z_M − Z_G`, i.e. the product
     of the two Gamma laws mapped through `p ↦ p.1 − p.2`; `IsProbabilityMeasure`;
  2. `mgf id (gammaMeasure a r) u = (r / (r − u)) ^ a` for `u < r` (consuming
     `integral_rpow_mul_exp_neg_mul_Ioi`), and `vgLaw`'s mgf on `−G < u < M` —
     the same strip the landed cumulant work uses;
  3. `vg_corner : Tendsto (fun Y ↦ cgmyExponent C G M Y v) (𝓝[>] 0) (𝓝 (ψ₀ v))`
     — the corner as a limit, with `Real.Gamma_add_one` doing the pole work
     (F3), so the family's `Y = 0` member is *named* by the exponent the tree
     already owns;
  4. the **Esscher tilt at the law level**: `withDensity` of the exponential
     over its mgf, the tilted mgf re-derived, the `(G, M) ↦ (G+θ, M−θ)` closure
     at the level of mgf values, and the numéraire statement `1 < M − θ`;
  5. the **expectation-level instantiations** of items 3 and 5 at this law:
     the drift identity `∫ S_T dμ^θ = S e^{(r−q)τ}` at the `θ` that solves the
     landed drift equation (at `Y = 0` the range is not bounded — see the
     route-check row), and the model-free parity/bounds of
     `ImprovedBS/Skeleton.lean` instantiated at a concrete **non-Gaussian**
     martingale law.

  Why Stage 1 first: it is the only place where the family's law is already in
  mathlib, the corner's analytic spine is two lines of landed Γ material, the
  result is the **published** law of BRIEF_016's external anchor (so the two
  briefs cross-check each other by construction), and it is the `Y ↑ 2` pattern
  of BRIEF_014 mirrored — corner first, factor work second, law when the corner
  admits one. It is also honest about what it is: *one member of the family*
  (`Y = 0`), not "the CGMY law".
- **Stage 2 — the general-`Y` law, by the F5 construction.** Its four named
  sub-goals (Poisson mixture, its CF, the truncation CF limit, the
  identification) go in the queue as their own brief, priced by that brief's own
  route-check. It is the piece that item 6's expectation-level twin actually
  needs (a limit *of laws* at `Y ↑ 2` requires laws at general `Y`), and it is
  the piece that turns "one member" into "the family".
- **Explicitly not unblocked by Stage 1:** item 6's expectation-level twin
  (needs Stage 2); the law-level CF and the measure-level tilt equality (needs
  the sub-goal below); and every pricing statement at the law (the tree prices
  from the exponent, and Stage 1 does not change that).
- **Named sub-goal G1 (isolated, deferred):** the *complex-rate* Γ integral —
  `∫ t in Ioi 0, (t:ℂ)^(a−1) * cexp (−(z t)) = z⁻ᵃ Γ(a)` for `0 < z.re` — is not
  in mathlib (the shipped lemma has a **real** rate). It is not needed for
  Stage 1 (the `mgf` is real on the strip, which is where items 3/5 live), but
  it is the direct route to `charFun` of these laws and hence, with
  `Measure.ext_of_charFun`, to law-level identifications. The alternative route
  — `complexMGF`'s analyticity (F2.3) plus analytic continuation from the real
  mgf — is probably cheaper and should be the first thing the Stage 2 brief
  tries.

## The numeric route-check (run at issue, per ledger C4)

Scratch script, Python 3 stdlib only, through the router's own oracle
(`cgmy_exponent`, `cgmy_gamma_neg`, `esscher_drift_map`, `esscher_theta_zero`,
`esscher_drift_bound`, `bs_call`). Unless stated, `C = 0.5, G = 5, M = 10`,
`τ = 0.25`, and `u_max`-free (all checks are closed-form or one-dimensional
quadrature).

| check | lands as | result |
|---|---|---|
| corner: `\|ψ_Y(v) − ψ₀(v)\| / Y` at `Y = 1/2 … 1/128`, `v = 1, 3` | `vg_corner` | finite limits (`0.0764`, `0.2527` at `C=.5,G=5,M=10`; `0.1734`, `0.6659` at `C=1,G=3,M=6`) — i.e. `O(Y)`, exponent-right, not an artifact |
| the law's mgf vs the **published** VG CF on 10 strip points, at Carr–Madan Case 4's `(C,G,M) = (½, 2.7081…, 5.9081…)` | `vgLaw_mgf` | worst relative gap `3.4e−15` |
| the map check: `C(1/M − 1/G) = θ` and `C(1/M² + 1/G²) = σ² + νθ²` | (comment) | `−0.1000000000` vs `−0.1`; `0.0825000000` vs `0.0825` |
| Γ mgf identity by quadrature, 11 cases incl. the shape `Cτ = 0.125` | `integral_rpow_mul_exp_neg_mul_Ioi` (consumed) | worst relative gap `1.1e−13` |
| drift map: `esscher_drift_map` at `θ = ½` for `Y ↓ 0` vs the `Y = 0` closed form | law-level drift | `−0.1332 → −0.0682 → −0.0586 → −0.0565` vs `−0.05583` |
| `θ₀ = (M−G−1)/2` zeroes the `Y = 0` drift | `esscherThetaZero` at the law | `−5.6e−17` (exact at `θ₀ = 2`) |
| the `Y = 0` drift strictly increasing on `(−G, M−1)` | tilt uniqueness at the law | monotone on all 200 sampled points |
| tilted law's mgf = mgf at `(G+θ, M−θ)`; `1 < M − θ` | law-level Esscher | worst relative gap `2.2e−16`; numéraire holds |
| **the edge is not the general-`Y` edge:** `H_Y` as `Y ↓ 0` | (recorded) | `H = 100.5, 1000.5, 10000.5` at `Y = 10⁻², 10⁻³, 10⁻⁴`, i.e. `H_Y ~ C/Y → ∞`. At `Y = 0` there is **no in-range/out-of-range split**: every finite `r − q` solves (the `Y = 0` drift solves `g₀(θ) = 5` at `θ = 8.9937`) |
| **canary**: the Dirac the raw formula would price | (kills a `Y = 0` evaluation) | `ψ ≡ 0` ⇒ `bs_call(S,K,τ,r,q,0) = 0.49502543252569353`, against any real CGMY price — the assertion is `≠`, not an approximation |
| **mutant**: corner sign flip `ψ₀ → −C[log(M/(M−iv)) + log(G/(G+iv))]` | M30 | the mgf at `u = 1` moves to `1/0.9840` from `0.9840`, i.e. `O(1)` |
| **mutant**: shape/rate transposition `(M/(M−u))^{Cτ} → (M/(M−u))^{C}` | M31 | at `τ = 0.25` the mgf at `u = 1` becomes `1.0581` vs `0.9840` |
| **mutant**: tilt map `(G, M) ↦ (G+θ, M−θ)` → `(M+θ, G−θ)` | M32 | the tilted mgf at `u = 1` moves by `O(1)`; the numéraire flips |
| **mutant**: drift sign `1/M − 1/G → 1/G − 1/M` | M33 | the solved `θ` moves to the wrong side of `θ₀`; the drift identity fails at `O(1)` |

Two of these deserve their own line in the brief's record. First, the
**`H_Y → ∞` row**: the landed `esscher_exists_unique_of_mem_range` has an
in-range/out-of-range split, and at `Y = 0` that split degenerates — a
statement carried over to the corner must say `∀ target, ∃ θ`, not
`∃ θ ↔ |target| < H`, and the oracle test should assert both facts (the
degeneration and the general-`Y` bound) so neither is silently assumed.
Second, the **canary row**: the trap of F4 is not an error of approximation, it
is a *different model*, and the test must assert inequality against the
deterministic price.

## What the Stage-1 implementation must land (its own brief, numbered at issue)

The Stage-1 brief is to be written next and takes the next free number. Its
shape, so it can be reviewed against this brief:

* **Lean, `ImprovedBS/VGLaw.lean` (name to be fixed at issue):** ~16
  declarations, all in `REQUIRED` + `PROTECTED` — `vgLaw` (1 def),
  `vgCornerExponent`/`vg_cumulant` as needed (defs), the theorem list of the
  route call: `vgLaw_isProbabilityMeasure`, `gammaLaw_mgf`, `vgLaw_mgf`,
  `vgLaw_mgf_one` (the numéraire), `vgLaw_cgf`/`vgLaw_mean`, `vg_corner`
  (the `𝓝[>] 0` limit), `vg_tilt` + `vg_tilt_mgf` + `vg_tilt_numeraire`,
  `vg_drift_identity` (the expectation-level item-3 twin), and the
  `modelFreeCall`/`modelFreePut` instantiation with parity and bounds (the
  item-5 twin). Statement pins 268 → 268 + k, audit list 237 → 237 + k with the
  exact `k` fixed by the brief that lands; no pre-existing entry may move.
* **Lint, a `[VGLaw]` check with four clauses** (the cheats named, one lint
  mutant each; lint mutants 44 → 48, controls stay 5):
  R1 the corner must be a `Tendsto … (𝓝[>] 0)` statement **and** the module
  must never evaluate the family at `Y = 0` — the whole-file ban is the point
  (F4: the evaluation is silent). R2 the law must be built from
  `gammaMeasure`, with no `def` using `withDensity` — the cheat is a hand-rolled
  VG density, which the tree cannot justify and which would not be the
  published law. R3 the mgf theorem must **cite**
  `integral_rpow_mul_exp_neg_mul_Ioi` (or the `GammaIntegral` family) rather
  than re-derive the Γ integral. R4 the tilt must be `Measure.withDensity` of
  `θx` over the mgf value, and the drift headline must carry `1 < M − θ` and
  land on `rexp ((r − q) * τ)`.
* **Oracle + tests:** primitives `gamma_mgf`, `vg_mgf`, `vg_corner_exponent`,
  `vg_esscher_solve`; a committed `test_vg_law` asserting the route-check table
  above (the corner's `O(Y)` ratios, the `3.4e−15` law-vs-published-CF identity,
  the Γ integral to `1e−13`, the tilt identity, the degenerate edge, and both
  canaries); and mutants **M30–M33**. **Numbering note:** the numbers assume
  BRIEF_016 (the anchor) lands first — it holds M26–M29 (its own C-map,
  ν-scaling, ω-sign and θ-sign mutants); if the order flips, the Stage-1
  mutants take whichever range is free and the ledger records it.
* **Primitive reconciliation, recorded now:** BRIEF_016's implementation
  specifies a `vg_char_exponent` in the **`(σ, ν, θ)`** parametrisation for its
  pricing test; this brief's corner primitive is the **`(C, G, M)`** exponent.
  They are the same object under BRIEF_016 F3's map; whichever lands second
  must *consume* the first rather than shadow it, and the Stage-1 brief must
  say which name survives.
* **Docs:** `docs/03` §D1 item 3's "gated on a law construction" sentence gets
  the landing reference; `docs/04`'s queue row and the item-6 line get the same;
  `README`'s CGMY-law note gets the Stage-1/Stage-2 split; `benchmarks/LEDGER.md`
  gets the row.

## Done looks like (acceptance, machine-graded)

1. `lake build` green at the tag; every new constant on
   `[propext, Classical.choice, Quot.sound]`; no `sorryAx`; `deferred: {}`
   untouched.
2. Statement pins move by exactly the landed count in **both** layers with the
   268 pre-existing entries byte-identical; `lint` green including `[VGLaw]`
   with its four cheats killed by name and nothing else; `oracle` green
   including `test_vg_law` and M30–M33, each killed by that test alone.
3. The module contains no evaluation of the CGMY family at `Y = 0` (R1), the
   law is `gammaMeasure`-built (R2), the mgf consumes the Γ integral (R3), and
   the tilt carries the numéraire condition (R4).
4. The two expectation-level statements exist as **theorems about an actual
   `Measure ℝ`**: the drift identity at the tilted `vgLaw`, and the model-free
   parity/bounds at it — the first non-Gaussian law in the tree that discharges
   BRIEF_009's hypotheses by construction.
5. A row in `benchmarks/LEDGER.md` when CI grades it, and the docs queue
   updated: Stage 1 landed, Stage 2 and G1 still open with their names.

## Explicitly out of scope

* **The general-`Y` law** (Stage 2): no Poisson-mixture construction, no
  truncation limit, no Prokhorov/Lévy-continuity work in Stage 1. Stage 1 is
  the `Y = 0` member.
* **The complex-rate Γ integral and law-level CF statements** (G1): the
  `mgf` on the strip is the interface Stage 1 needs; `Measure.ext_of_charFun`
  identifications wait for G1.
* **Item 6's expectation-level twin**: a limit *of laws* at `Y ↑ 2` needs Stage
  2. Stage 1 does not claim it.
* **Pricing at the law**: the tree's Carr–Madan route is exponent-level; Stage 1
  adds no pricing theorem and changes no price.
* **Any change to `ImprovedBS/CGMY.lean`, `Esscher.lean`, `Corner.lean`,
  `Skeleton.lean` or any landed pin**; the Esscher numbers at `Y = 0` are
  consumed, not re-derived.

## Name-check status (ledger C3)

Every mathlib name in F1–F3 was read at the pinned rev `5ed2965` through the
GitHub API (`gh api …/contents/<path>?ref=<rev> --jq .content | base64 -d`):
`Probability/Distributions/Gamma.lean`, `Analysis/SpecialFunctions/Gamma/Basic.lean`,
`Probability/Moments/{Basic,ComplexMGF,MGFAnalytic}.lean`,
`MeasureTheory/Measure/CharacteristicFunction/Basic.lean`,
`MeasureTheory/Measure/IntegralCharFun.lean`,
`MeasureTheory/Measure/LevyConvergence.lean`,
`MeasureTheory/Measure/Prokhorov.lean`,
`MeasureTheory/Group/Convolution.lean`, plus a recursive tree listing for the
absences in F1. The two analytical risks are named rather than hidden: the
`(cpow)` slope limit `((M−iv)^Y − M^Y)/Y → log((M−iv)/M)` (derivative of
`Y ↦ cexp` at `0`, with the `Complex.log` branch fixed by `Re > 0` on the
strip), and the `withDensity`/`IntegrableOn`/`ENNReal.ofReal` bookkeeping when
unfolding `gammaMeasure` — the same class of failure the landed briefs hit and
recorded.
