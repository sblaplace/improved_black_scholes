# BRIEF_018 — the variance-gamma law: the first CGMY-family probability measure in the tree (BRIEF_017 Stage 1)

- **Status:** **ISSUED** — PR [#24](https://github.com/sblaplace/improved_black_scholes/pull/24)
  (the third brief on the one branch and its one cumulative PR: BRIEF_016 the
  anchor, BRIEF_017 the feasibility audit, this one the Stage-1 contract —
  separate commits, in that order), documentation plus a numeric route-check run
  at issue (no committed test). It changes no `.lean` file, no pin, no lint
  rule, no workflow; `deferred: {}` is untouched.
- **What this is.** BRIEF_017's route call, made concrete and checkable: the
  implementation brief for **`ImprovedBS/VGLaw.lean`** (name fixed here). It
  lands the family's `Y = 0` member — the **variance-gamma law** — as an actual
  `Measure ℝ` built **only** from mathlib's `ProbabilityTheory.gammaMeasure`,
  proves the mgf on the landed strip `(−G, M)`, names it by the exponent the
  tree already owns (the `Y ↓ 0` corner as a *limit*, never an evaluation),
  takes its Esscher tilt at the law level, and lands the **expectation-level
  twins of kit items 3 and 5** at a concrete non-Gaussian martingale law. It
  fixes the declaration list, the statements, the counts, the four `[VGLaw]`
  lint clauses, the four oracle primitives, the committed test and the four
  mutants its implementation must land.
- **Prerequisites:** BRIEF_011 (`cgmyExponent`, `cgmyExponent_strip`,
  `cgmy_numeraire_strip`), BRIEF_013 (`cgmyCumulant`, `cgmyCumulant_eq_strip`,
  `esscherDriftMap`, `esscherThetaZero`, `esscher_tilted_numeraire`,
  `esscher_cgmy_shift`, `esscher_drift_factor`), BRIEF_014 (the `Y ↑ 2` pattern
  this brief mirrors at `Y ↓ 0`), BRIEF_016's **implementation** (the oracle's
  `(σ, ν, θ)` VG exponent and `cgmy_zeroth_exponent`, and the published Case-4
  literals — §"primitive reconciliation" below) and BRIEF_017 (the audit, the
  route call, the traps). All LANDED or landed; CI-only, no local toolchain.
- **Budget:** the implementation is one Lean module plus one oracle test. The
  skills it needs are named rather than waved at: a `withDensity`/`ENNReal.ofReal`
  unfold of `gammaMeasure` against `integral_rpow_mul_exp_neg_mul_Ioi`; the
  product-measure factorisation of an mgf (`integral_prod_mul`); the Γ pole
  cancellation `Γ(−Y) = −Γ(2−Y)/(Y(1−Y))` through two `Real.Gamma_add_one`; the
  slope limit `(z^Y − M^Y)/Y → log (z/M)` for `Re > 0` bases
  (`HasDerivAt.tendsto_slope_zero_right` at `Y ↦ cexp (Y * log (z/M))`); and the
  `Measure.withDensity` tilt with its mgf re-derived. Nothing here estimates a
  date: the repo's only clock is the CI run.

## Findings recorded at issue

**F1. mathlib ships the Gamma *law* at the tag — and not one mgf lemma for
it.** Read at the pinned rev `5ed2965256430c3649e86755f9576b54eca72435`
(`v4.34.0`), `Mathlib/Probability/Distributions/Gamma.lean` (153 lines) has
`gammaPDFReal a r x = r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))` on
`0 ≤ x` (zero below), `gammaPDF`, and
`gammaMeasure a r = volume.withDensity (gammaPDF a r)` with
`isProbabilityMeasure_gammaMeasure (ha : 0 < a) (hr : 0 < r)` (and two `cdf`
lemmas). A code search at the tag for an mgf of `gammaMeasure` returns nothing;
the shipped Γ integral is
`Real.integral_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
  ∫ t in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a`
— a **real** rate only (the complex-rate version is BRIEF_017's G1, deferred).
So `gammaMeasure_mgf` is new work, and it is the module's one hard rung: the
rest of the module is *application* of that rung.

**F2. The `Y = 0` member is the difference of two independent Gamma laws — and
that is the representation to build, not the normal variance-mean mixture.**
Two classical representations exist: (i) `X_τ = θ G + σ √G Z` with
`G ~ Gamma(τ/ν, 1/ν)` (the subordination form the paper states), and (ii) the
difference of the two Gamma laws of the *gamma-difference* (Madan–Carr–Chang)
form. Stage 1 lands (ii):

    vgLaw C G M τ := ((gammaMeasure (C*τ) M).prod (gammaMeasure (C*τ) G)).map
                       (fun p : ℝ × ℝ ↦ p.1 − p.2),

because (ii) is two lines from `Measure.prod`/`Measure.map`, its mgf factors by
`integral_prod_mul` into the two Γ integrals F1 owns, and its mgf *is* the
published factor: with `C = 1/ν`, `G = (s+θ)/σ²`, `M = (s−θ)/σ²` the map
BRIEF_016 fixed (and verified against the paper: `C(1/M − 1/G) = θ`,
`C(1/M² + 1/G²) = σ² + νθ²` to `1e−12`),

    (1 − θνu − ½σ²νu²)^(−τ/ν) = (M/(M−u))^{Cτ} (G/(G+u))^{Cτ}

**exactly** (both sides are `½σ²ν (M−u)(G+u)` raised to `−τ/ν` with
`MG = 2/(σ²ν)`), measured below at `3.4e−16`. Route (i) would need the Gaussian
law as a *kernel* over `gammaMeasure` plus a density-level identification that
the tree does not have; it is not needed for Stage 1 and is named here only so
the choice is on the record.

**F3. Three martingale-shaped laws, and only one of them is the tree's
Esscher measure. Do not conflate them.** At the same `(σ, ν, θ) ↔ (C, G, M)`:

* **(a) the corner law** (`vgLaw`, what Stage 1 lands): the *untilted* member,
  mgf `(M/(M−u))^{Cτ}(G/(G+u))^{Cτ}` on `(−G, M)`, CF `exp(τ ψ₀(v))` with
  `ψ₀(v) = C[log(M/(M−iv)) + log(G/(G+iv))]` — the `Y ↓ 0` corner of the landed
  `cgmyExponent`. Not a martingale law: `κ₀(1) = ψ₀(−i)` is the mean-rate
  `C[log(M/(M−1)) + log(G/(G+1))]`, and at witness A it equals
  `−0.0644164359214842` — **exactly `−ω`**, the paper's own martingale
  correction. That identity is the bridge between the two normalizations;
* **(b) the published martingale law** (Carr–Madan §5, and the landed
  `cgmy_zeroth_forward_exponent`): (a) **translated** by
  `(r − q − κ₀(1))τ`, i.e. `exp(τ Ψ₀)` with `Ψ₀(v) = ψ₀(v) + i(r−q−κ₀(1))v`.
  BRIEF_016's anchor prices at *this* law; its three published put prices are
  the external anchor, and Stage 1 **prices nothing**;
* **(c) the Esscher-tilted law** (`vgTilt`, the tree's `π^θ`): the exponential
  tilt of (a) at the drift solution `θ*`. By `esscher_cgmy_shift` its
  characteristic factor is the family member with rates `(G+θ*, M−θ*)` — a
  **different** law from (b), with the same `E[e^{X_τ}] = e^{(r−q)τ}` but mean
  `(r−q)τ` rather than (b)'s `(r−q+ω+θ)τ`. Only (c) is `esscherExponent`'s
  measure, and only (c) is *in* the landed strip family with no translation —
  so items 3 and 5 land at (c), and the brief says so out loud.

Measured witness A: `mgf_(a)(1) = 0.984025`, while (b) and (c) both carry
`E[e^{X_τ}] = e^{0.005} = 1.005012520859401`. The three agree only in the
degenerate `θ = 0`, `r = q` limit.

**F4. The `Y = 0` drift geometry degenerates — every `r − q` is admissible,
and `θ*` is not small.** BRIEF_013/014's split ("exactly one `θ` for
`|r−q| < H`, none outside") collapses at the corner, where
`H_Y ~ C/Y → ∞`: at `(C, G, M) = (0.5, 5, 10)`, `H_Y = 50.2580, 500.2545,
5000.2541, 50000.2541` at `Y = 10⁻², 10⁻³, 10⁻⁴, 10⁻⁵` (so `H_Y·Y → C`). There
is **no** out-of-range case to prove at `Y = 0` and no `esscher_no_solution`
twin; what replaces it is that `θ*` can be large — at witness A,
`θ* = 1.463508761` against `θ₀ = (M−G−1)/2 = 1.1`, i.e. on the far side of the
zero-drift point. The numéraire condition is a **citation**, not a hypothesis:
`esscher_tilted_numeraire (hθ : θ ∈ Ioo (−G) (M − 1)) : 1 < M − θ` is landed
and holds at both witnesses (`4.4446`, `6.9040`).

**F5. The `Y = 0` cumulant is a separate definition, and the corner is what
names it.** `cgmyCumulant C G M 0 u` is `Γ(0)·0`: not the corner, and not
evaluable. Stage 1 defines the real-section cumulant

    vgCumulant C G M u := C * (Real.log (M / (M − u)) + Real.log (G / (G + u)))

and proves it is the corner's real section two ways: as a limit of the landed
`cgmyCumulant` (`vg_corner_cumulant`) and as the real part of the complex
corner target (`vgCumulant_eq_corner_re`). No statement in the module may
contain `cgmyExponent … 0 …`: `Real.Gamma 0 = 0`, so a raw evaluation is
*silently* the Dirac law (BRIEF_017's canary — the deterministic value
`0.49502543252569353` at `S = K = 100`, `τ = 0.25`, `r = 0.05`, `q = 0.03`).

## The mathematics to land

Fix `0 < C`, `0 < τ`, `0 < G`, `0 < M`, `1 < G + M` (the landed strip scale;
`M > 1` is the numéraire). All quantities below live on the closed strip
`[−G, M]` and its open interior, the same sets `cgmyExponent_strip` uses.

**The law.** `vgLaw C G M τ` is the pushforward of the product of the two Gamma
laws `Gamma(Cτ, M)` and `Gamma(Cτ, G)` under `p ↦ p.1 − p.2`. It is a
probability measure because a product of probability measures is one
(mathlib's `Measure.prod.instIsProbabilityMeasure`) and `Measure.map` of one is
one (the `IsProbabilityMeasure (map f μ)` instance). It is **not** symmetric:
the rate `M` sits on the positive side (`M − iv` in the exponent), which is why
`1 < M` is the numéraire condition and `−G > −∞` is not.

**The mgf.** For `u ∈ (−G, M)`,

    mgf id (gammaMeasure a r) u          = (r / (r − u)) ^ a          (a = Cτ),
    mgf id (vgLaw C G M τ) u             = rexp (τ * vgCumulant C G M u),

with the second obtained from the first by `mgf_id_map` + `integral_prod_mul`:
the product integral splits into `mgf_1(u) · mgf_2(−u)` and
`(G/(G+u))^a = mgf_2(−u)`. `Integrable` is proved too, not inherited from the
value: `mgf` returns `0` on non-integrable functions, so `vgLaw_mgf` alone
would be a *silent* statement at the strip's edge — the integrability lemmas
(`gammaMeasure_exp_integrable`, `vgLaw_exp_integrable`) are what make the
item-5 instantiation honest.

**The corner.** Two `Real.Gamma_add_one` give
`Γ(−Y) = −Γ(2−Y)/(Y(1−Y))` for `0 < Y < 1`; `Γ(2−Y) → Γ(2) = 1`; and

    ((M − iv)^Y − M^Y)/Y = M^Y · (((M − iv)/M)^Y − 1)/Y → Complex.log ((M − iv)/M)

by `HasDerivAt.tendsto_slope_zero_right` applied to
`Y ↦ Complex.cexp (Y * Complex.log ((M − iv)/M))` at `0`. Therefore, for every
`v : ℂ`,

    Tendsto (fun Y ↦ cgmyExponent C G M Y v) (𝓝[>] 0) (𝓝 (vgCornerExponent C G M v)),

    vgCornerExponent C G M v :=
      C * (Complex.log ((M : ℂ) / ((M : ℂ) − (v : ℂ) * I))
           + Complex.log ((G : ℂ) / ((G : ℂ) + (v : ℂ) * I))),

the same shape as the oracle's `cgmy_zeroth_exponent`, with the branch fixed by
`Re ((M − iv)/M) = 1 > 0` (so `Complex.arg ≠ π` and every `log` splits the way
the algebra needs). The one-sided filter is the point (`𝓝[>] 0`): the two-sided
limit does not exist, and an evaluation at `Y = 0` is the F5 trap.

**The tilt.** `vgTilt C G M τ θ` is `(vgLaw C G M τ).withDensity` of
`x ↦ ENNReal.ofReal (rexp (θ * x) / mgf id (vgLaw C G M τ) θ)`. Its mgf is the
ratio `mgf (u + θ)/mgf (θ)`, and the algebraic identity

    vgCumulant C G M (u + θ) − vgCumulant C G M θ = vgCumulant C (G+θ) (M−θ) u

(three `Real.log_div`/`Real.log_mul` rewrites, `M − θ − u > 0`, `G + θ + u > 0`)
makes the tilted law a *family member at the shifted rates* — the law-level
image of `esscher_cgmy_shift`, consumed rather than re-derived.

**Items 3 and 5, at that law.** With `θ ∈ Ioo (−G) (M−1)` solving
`vgDriftMap C G M θ = r − q` (where `vgDriftMap C G M θ := vgCumulant C G M (θ+1)
− vgCumulant C G M θ`),

    ∫ x, S * rexp x ∂(vgTilt C G M τ θ) = S * rexp ((r − q) * τ),         (item 3)

because the left side is `S · mgf id (vgTilt …) 1 = S · rexp (τ * vgDriftMap … θ)`
and the right side substitutes; and with `X := fun x ↦ S * rexp x`,
`μ := vgTilt C G M τ θ`, the landed `model_free_call_bounds` /
`model_free_put_bounds` / `model_free_put_call_parity` are then **instantiated**
(item 5) — the first non-Gaussian law in the tree that discharges BRIEF_009's
hypotheses by construction: probability measure (the tilt is one), integrability
(`vgLaw_exp_integrable` at `u = 1 + θ`), the drift hypothesis (item 3), and
`0 ≤ S·rexp` a.e. (everywhere).

## The Lean work to land (the contract)

New module `ImprovedBS/VGLaw.lean`, namespace `BSM`, imported from
`ImprovedBS.lean` with its doc bullet (the `[SPINE]` check). Planned **5 defs +
17 audited theorems = 22 declarations**, all in `REQUIRED` + `PROTECTED`; the
landed count is what CI pins, and any deviation is recorded in the ledger row
(the BRIEF_014 precedent):

    -- defs
    vgLaw (C G M τ : ℝ) : Measure ℝ
    vgCumulant (C G M u : ℝ) : ℝ
    vgDriftMap (C G M θ : ℝ) : ℝ
    vgCornerExponent (C G M : ℝ) (v : ℂ) : ℂ
    vgTilt (C G M τ θ : ℝ) : Measure ℝ

    -- the Γ rung (the only new analysis)
    gammaMeasure_mgf            : mgf id (gammaMeasure a r) u = (r/(r−u)) ^ a     [0 < a, 0 < r, u < r]
    gammaMeasure_exp_integrable : Integrable (fun x ↦ rexp (u * x)) (gammaMeasure a r)
    -- the law
    vgLaw_isProbabilityMeasure  : IsProbabilityMeasure (vgLaw C G M τ)
    vgLaw_exp_integrable        : Integrable (fun x ↦ rexp (u * x)) (vgLaw C G M τ)   [−G < u < M]
    vgLaw_mgf                   : mgf id (vgLaw C G M τ) u = rexp (τ * vgCumulant C G M u)
    vgLaw_cgf                   : cgf id (vgLaw C G M τ) u = τ * vgCumulant C G M u
    vgLaw_mgf_one               : mgf id (vgLaw C G M τ) 1 = rexp (τ * vgCumulant C G M 1)   [1 < M]
    vgCumulant_hasDerivAt       : HasDerivAt (vgCumulant C G M)
                                    (C * (1/(M−u) − 1/(G+u))) u                              [−G < u < M]
    -- the corner
    vgCumulant_eq_corner_re     : vgCumulant C G M u = (vgCornerExponent C G M (−(u:ℂ)*I)).re
    vg_corner_cumulant          : Tendsto (fun Y ↦ cgmyCumulant C G M Y u) (𝓝[>] 0) (𝓝 (vgCumulant C G M u))
    vg_corner                   : Tendsto (fun Y ↦ cgmyExponent C G M Y v) (𝓝[>] 0) (𝓝 (vgCornerExponent C G M v))
    -- the tilt
    vgTilt_isProbabilityMeasure : IsProbabilityMeasure (vgTilt C G M τ θ)                      [θ ∈ Ioo (−G) (M−1)]
    vg_tilt_numeraire           : 1 < M − θ                       (via `esscher_tilted_numeraire`, cited)
    vg_tilt_mgf                 : mgf id (vgTilt C G M τ θ) u
                                    = mgf id (vgLaw C G M τ) (u + θ) / mgf id (vgLaw C G M τ) θ
    vg_tilt_cumulant_shift      : vgCumulant C G M (u+θ) − vgCumulant C G M θ = vgCumulant C (G+θ) (M−θ) u
    -- items 3 and 5
    vg_drift_identity           : ∫ x, S * rexp x ∂(vgTilt C G M τ θ) = S * rexp ((r − q) * τ)  [vgDriftMap … θ = r − q]
    vg_modelFree_call_bounds    : the T4 pair at (vgTilt …, fun x ↦ S * rexp x)
    vg_modelFree_put_bounds     : the put twin
    vg_modelFree_parity         : the parity identity at the same law

Boundary discipline, stated once and checked by the test: `(−G, M)` for every
mgf, `(−G, M−1)` for every tilt, `1 < M − θ` after every tilt, and the exponent
`exp(τ · vgCumulant … u)` never written as `(…)^τ` with a negative base.

## The numeric contract (fixed witnesses)

* **Witness A** — the anchor's own map: `(σ, ν, θ) = (0.25, 2.0, −0.10)` →
  `(C, G, M) = (0.5, 2.708131845707604, 5.908131845707604)`, `τ = 0.25`,
  `r = 0.05`, `q = 0.03`, `S = K = 100`. `κ₀(1) = −ω = −0.0644164359214842`,
  `θ* = 1.463508761`, `M − θ* = 4.4446…`.
* **Witness B** — the corner's own witness from BRIEF_017: `(C, G, M) =
  (0.5, 5, 10)`, `τ = 0.25`, same `r, q, S, K`; `θ* = 3.095836730`,
  `M − θ* = 6.9041…`.
* **The pinned quadrature** for everything priced: the landed
  `carr_madan_by_exponent` defaults `α = 1.5`, `u_max = 2000`, `n = 80000`
  (never re-tuned here; the F4 grid of BRIEF_016 governs).

## The numeric route-check (run at issue, per ledger C4)

Scratch script, Python 3 stdlib only, through the router's own oracle
(`cgmy_zeroth_corner_map`, `cgmy_zeroth_exponent`, `carr_madan_by_exponent`,
`bs_call`); no `numpy`, no `scipy`.

| check | lands as | result |
|---|---|---|
| `∫₀^∞ x^(a−1) e^(−x) dx = Γ(a)`, Simpson with `z = x^a` (which removes the `a = 0.125` singularity), shapes `0.125, 0.25, 1, 2.5, 7`; the rate is exact scaling | `gammaMeasure_mgf` (consuming `integral_rpow_mul_exp_neg_mul_Ioi`) | worst relative gap `9.3e−11` |
| the law's mgf vs the **published** no-drift factor `(1 − θνu − ½σ²νu²)^(−τ/ν)`, witness A, 11 strip points | `vgLaw_mgf` | worst relative gap `3.4e−16` |
| the corner: `\|ψ_Y(v) − ψ₀(v)\|/Y` at `Y = 1/2 … 1/128` | `vg_corner` | `0.1343 → 0.0764` and `0.4480 → 0.2527` (`C=.5,G=5,M=10`, `v = 1, 3`); `0.2796 → 0.1734` and `1.0808 → 0.6659` (`C=1,G=3,M=6`) — finite, i.e. `O(Y)` |
| the drift solve `vgDriftMap (θ) = r − q` | `vgDriftMap`, `vgTilt` | witness A `θ* = 1.463508761` (`θ₀ = 1.1`); witness B `3.095836730`; residual `≤ 2e−15`; `1 < M − θ*` at both |
| `mgf id (vgTilt …) 1` | `vg_drift_identity` | `1.005012520859401` vs `rexp (τ(r−q)) = 1.005012520859401` (gap `≤ 2.2e−16`) |
| the closure `κ(θ+1) − κ(θ) = κ_{(G+θ,M−θ)}(1)` | `vg_tilt_cumulant_shift` | residual `5.6e−17` (A) / `9.0e−17` (B) |
| call at the tilted law, **item 5**, pinned grid | `vg_modelFree_call_bounds` | A `2.749188832359`, B `1.705678682076`, both inside `[0.4950254325, 99.2528050227]` |
| the put through parity at the same law | `vg_modelFree_put_bounds` | A `2.254163399833`, B `1.210653249550`, both inside `[0, 98.7577796468]` |
| **canary**: the Dirac the raw `Y = 0` evaluation prices | R1 + the test's canary | `bs_call(S,K,τ,r,q,1e−12) = 0.49502543252569353 = S e^{−qτ} − K e^{−rτ}`; at `K = 90`, `10.370803437464502` — asserted as *equality with the intrinsic*, so a `Y = 0` evaluation cannot pass it |
| **mutant** M30 — corner sign, in the landed `cgmy_zeroth_exponent` (`C * (…) → −C * (…)`) | M30 | the bridge `rexp (τ · ψ₀(−i))` moves `0.984025 → 1.016234` |
| **mutant** M31 — `vg_cumulant`'s `τ` dropped in the mgf (`rexp (τ * κ) → rexp κ`) | M31 | the mgf at `u = 1` moves `0.984025 → 0.937614` |
| **mutant** M32 — the tilt's rates swapped (`(G+θ, M−θ) → (M+θ, G−θ)`) | M32 | the tilted mgf at `1` moves `0.984025 → 0.946021`; the strip point `u = 1` is no longer the same point |
| **mutant** M33 — the cumulant reflected (`u ↦ −u`, i.e. `1/M − 1/G → 1/G − 1/M` in the mean) | M33 | the solved `θ` moves across `θ₀` to `−1.736491239`, where the *true* drift is `−0.283720` instead of `0.02` — an `O(1)` kill |

## Grading wiring (the repo motion)

* **Lean, `ImprovedBS/VGLaw.lean`:** the 22 declarations above, all in
  `REQUIRED` + `PROTECTED`, on `[propext, Classical.choice, Quot.sound]` and
  never `sorryAx`; `ImprovedBS.lean` gains the import and its doc bullet.
  Statement pins `268 → 268 + 22` (the landed count rules) in **both** layers
  with the 268 pre-existing entries byte-identical; audit list `237 → 237 + 22`
  modulo the same landing rule; `deferred: {}` untouched.
* **Lint, a `[VGLaw]` check with four clauses**, one lint mutant each, named:
  **R1** no evaluation of the family at `Y = 0` anywhere in the module (the
  whole file is the scope — the evaluation is *silent*), and the corner is a
  `Tendsto … (𝓝[>] 0)` statement; cheat: an in-module `cgmyExponent C G M 0 v`.
  **R2** the law is `gammaMeasure`-built: `vgLaw`'s body mentions
  `gammaMeasure` and contains no `withDensity`; cheat: a hand-rolled VG density.
  **R3** the mgf theorem cites `integral_rpow_mul_exp_neg_mul_Ioi` (the Γ
  integral is consumed, not re-derived); cheat: a local re-derivation.
  **R4** the tilt is `Measure.withDensity` of the exponential `θx` over its own
  mgf value, and the numéraire condition `1 < M − θ` appears as a conclusion
  (via `esscher_tilted_numeraire`), never as a hypothesis; cheat: the tilt
  defined by a shifted `gammaMeasure` without the density, and/or a drift
  statement with `1 < M − θ` assumed. Lint mutants `44 → 48`, controls stay 5.
* **Oracle + tests:** new primitives (no published literals in the oracle,
  BRIEF_016's rule) `gamma_mgf(a, r, u)`, `vg_cumulant(C, G, M, u)`,
  `vg_mgf(C, G, M, τ, u)`, `vg_drift_map(C, G, M, θ)`,
  `vg_tilted_cumulant(C, G, M, θ, u)`, `vg_esscher_solve(C, G, M, target,…)`;
  the committed `tests/test_bs.py::test_vg_law` asserting the route-check table
  above (the Γ gap `≤ 1e−9` at one shape, the published-factor identity
  `≤ 1e−12`, the corner ratios and their bands, the drift solve, the tilt
  identity and the closure, the two Carr–Madan numbers with the bounds and
  parity, and the two canaries); mutants **M30–M33**, each killed by the new
  test (M30 also by `test_term_structure_anchor`, which is recorded, not
  avoided). Tests `23 → 24`, mutants `30 → 34`.
* **Primitive reconciliation, decided here:** BRIEF_016's implementation landed
  `cgmy_zeroth_exponent` — *the* complex corner target. This brief does **not**
  shadow it with a `vg_corner_exponent`: `vgCornerExponent` is the Lean-side
  definition of that same function, and the test consumes
  `cgmy_zeroth_exponent` directly. `cgmy_zeroth_corner_map` stays the only
  `(σ, ν, θ) ↔ (C, G, M)` translation, and `carr_madan_by_exponent` stays the
  only contour quadrature.
* **Docs:** `docs/03` §D1 items 3 and 5 lose their "gated on a law
  construction" sentence and gain the landing reference; `docs/04` gets the row
  (ISSUED → LANDED GREEN with its run); `README`'s CGMY-law paragraph says
  Stage 1 landed and Stage 2/G1 remain open; `benchmarks/LEDGER.md` gets row 17.

## Done looks like (acceptance, machine-graded)

1. `lake build` green at the tag; every new constant on
   `[propext, Classical.choice, Quot.sound]`; no `sorryAx`; `deferred: {}`.
2. Statement pins move by exactly the landed count in both layers with the 268
   pre-existing entries byte-identical; `lint` green including `[VGLaw]` with
   its four cheats killed by name (44 → 48) and nothing else; `oracle` green
   including `test_vg_law` and M30–M33, each killed by that test.
3. The module contains no `Y = 0` evaluation (R1), `vgLaw` is built from
   `gammaMeasure` and no hand-rolled density appears (R2), the mgf consumes the
   Γ integral (R3), and the tilt carries the derived numéraire condition (R4).
4. The two expectation-level statements exist as **theorems about an actual
   `Measure ℝ`**: `∫ x, S * rexp x ∂(vgTilt …) = S * rexp ((r − q)τ)` (item 3),
   and the model-free parity/bounds at it (item 5) — the first non-Gaussian law
   in the tree that discharges BRIEF_009's hypotheses by construction.
5. A row in `benchmarks/LEDGER.md` and the docs queue updated: Stage 1 landed,
   Stage 2 and G1 still open with their names.

## Explicitly out of scope

* **The general-`Y` law** (Stage 2): no Poisson mixture, no truncation limit,
  no Prokhorov/Lévy-continuity work. Stage 1 is the family's `Y = 0` member.
* **The complex-rate Γ integral and law-level CF statements** (G1): the real
  mgf on the strip is the interface items 3 and 5 need. No
  `Measure.ext_of_charFun` identification, no measure-level tilt equality, no
  law-level CF.
* **Item 6's expectation-level twin**: a limit *of laws* at `Y ↑ 2` needs Stage
  2. Not claimed here.
* **Pricing at the law**: the tree's Carr–Madan route is exponent-level and
  BRIEF_016's anchor owns the only published numbers. Stage 1 prices nothing,
  and its `2.749188832359` is a *check on the bounds*, not a new quote — it is
  the tilted (Esscher) law, not the published (translated) one (F3).
* **Landed modules touched:** none. `ImprovedBS/CGMY.lean`,
  `Esscher.lean`, `Corner.lean`, `Skeleton.lean` and every landed pin are
  consumed by citation only.
* **The normal variance-mean mixture representation** (F2 route (i)): recorded,
  not built.

## Name-check status (ledger C3)

Read at the pinned rev `5ed2965` through the GitHub API
(`gh api …/contents/<path>?ref=<rev> --jq .content | base64 -d`):
`Probability/Distributions/Gamma.lean` (F1, and the *absence* of any mgf lemma,
confirmed by a code search at the tag), `Analysis/SpecialFunctions/Gamma/Basic.lean`
(`Real.Gamma_add_one`, `Real.Gamma_one`, `Real.Gamma_pos_of_pos`,
`Real.integral_rpow_mul_exp_neg_mul_Ioi` — statement quoted in F1),
`MeasureTheory/Integral/Prod.lean`
(`integral_prod_mul {L} [RCLike L] (f : α → L) (g : β → L) :
  ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν` — no integrability
hypothesis: the non-integrable case is handled by `integral_undef`),
`MeasureTheory/Measure/Prod.lean` (`prod.instIsProbabilityMeasure`),
`MeasureTheory/Measure/Typeclasses/Probability.lean` (the `IsProbabilityMeasure
(map f μ)` instance), `Probability/Moments/Basic.lean` (`mgf_map`, `mgf_id_map`),
`Analysis/Calculus/Deriv/Slope.lean`
(`HasDerivAt.tendsto_slope_zero_right : Tendsto (fun t ↦ t⁻¹ • (f (x + t) − f x))
  (𝓝[>] 0) (𝓝 f')`), `Analysis/SpecialFunctions/Complex/Log.lean`
(`Complex.log_inv (x) (hx : x.arg ≠ π) : log x⁻¹ = −log x`, and
`log_mul_ofReal`), `Analysis/SpecialFunctions/Pow/Complex.lean` (`Complex.cpow`).
Two risks are named rather than hidden, both in the F1 rung: the
`withDensity`/`ENNReal.ofReal`/`toReal` unfold of `gammaMeasure` against
`integral_rpow_mul_exp_neg_mul_Ioi` (the same class of bookkeeping the landed
briefs hit and recorded), and the branch condition `x.arg ≠ π` in
`Complex.log_inv` at `x = (M − iv)/M`, discharged from `Re x = 1 > 0` — if the
branch rewrite resists, the corner statement can be *stated* in the `−C·log`
form and the `M/(M−iv)` shape recovered by an explicit `Complex.log_inv`
corollary; either way the oracle's `cgmy_zeroth_exponent` is the pinned shape
and the test checks the bridge.
