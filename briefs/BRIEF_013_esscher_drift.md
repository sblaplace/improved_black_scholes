# BRIEF_013 — the Esscher drift: BSM-2 kit item 3, the named pricing measure at CGMY

- **Status:** **ISSUED** 2026-09-24 — not yet implemented; nothing in
  `ImprovedBS/Esscher.lean` exists yet and no pin has moved. This is **item 3**
  of the BSM-2 kit in `docs/03` §D1 and the successor `docs/04`'s queue names
  once item 7 landed: *"item 7 went first deliberately … so item 3 can now be
  written against a proved requirement rather than an assertion."* That
  requirement is now proved — BRIEF_012's
  `static_skeleton_does_not_select_measure` (row 12) — and this brief supplies
  the name it obliges: **the Esscher transform**. One line of scope: the
  exponent shift `ψ^θ(v) = ψ(v − iθ) − ψ(−iθ)` is algebra on what BRIEF_011
  landed, the drift condition picks `θ`, and the strip theorem says when such a
  `θ` exists — and the route-check (§"The numeric route-check") measured all
  three before this brief was written.
- **Numbering note.** Ledger C13's repair queue provisionally assigned
  "BRIEF_013" to the Pareto witness for `Levy.lean`'s tail hypothesis and
  "BRIEF_014" to the Haug/term-structure anchor. The queue in `docs/04`
  supersedes that numbering for the kit: BRIEF_012 took the witness slot (item
  7), this brief takes 013 (item 3), item 6 (the GBM corner) takes the next
  number, and C13's two repair briefs stay queued after the kit, to be numbered
  at issue. Recorded here rather than edited into C13.
- **Prerequisite PRs:** BRIEF_011 (`ImprovedBS/CGMY.lean` — the exponent, the
  strip `cgmyExponent_strip`, the decay constants, and
  `cgmy_cmPriceKernel_integrable`) and BRIEF_012
  (`ImprovedBS/NonUniqueness.lean` — the proved requirement) merged. **No edit
  to any existing declaration** anywhere in the tree, and no pre-existing pin
  may move: the brief is append-only in both pin layers.
- **Skills:** Lean 4 + mathlib at the pinned tag v4.34.0: the Γ recurrence
  (`Real.Gamma_add_one`) for `Γ(−Y)·Y(Y−1) = Γ(2−Y)`, real `rpow` derivatives
  (`hasDerivAt_rpow_const`) on the *real* section of the strip (no new `cpow`
  work — the Esscher analysis lives where `cgmyExponent_strip` says the
  exponent is real), strict convexity from a positive second derivative
  (`StrictMonoOn.strictConvexOn_of_deriv`, `strictMonoOn_of_deriv_pos`), and
  the intermediate value theorem on the closed strip. No new mathematics: every
  ingredient is calculus plus one `push_cast; ring` algebra identity.
- **Budget:** one CI-only lane (no local Lean toolchain). As for BRIEF_012, the
  mathematics is fixed and route-checked first (§"The numeric route-check"), so
  the expected failure mode is API shape at the tag, not wrong estimates —
  budget for elaboration rounds, not for rediscovery. Every mathlib name this
  brief relies on was read at the v4.34.0 tag before issue (§"Mathlib name
  check at the tag"), which is the mitigation BRIEF_012 could not run.

## Background, in order

1. `docs/03` §D1 item 3 is the requirement, verbatim: *"The drift is fixed* ***at
   a named pricing measure***, *and `E[S_T] = S·e^{(r−q)τ}` is proved at the new
   law under that measure (the CGMY twin of `integral_spot_mul_phi_eq_forward`).
   The martingale condition alone does not select the measure — see item 7; the
   choice (Esscher, minimal-entropy, calibrated, …) is part of the model, and
   the price is a claim* ***at the chosen measure***.*"* Items 1–2 of the kit
   landed as BRIEF_011, item 7 as BRIEF_012; item 3 is what this brief issues.
2. **What BRIEF_011 supplies.** `cgmyExponent` and `cgmyCharFactor` (the closed
   form `ψ(v) = C Γ(−Y)[(M − iv)^Y − M^Y + (G + iv)^Y − G^Y]`, affine in τ);
   the moment strip `cgmyExponent_strip` — on `v = −iu`, `u ∈ (−G, M)`, both
   bases become positive reals and `ψ(−iu)` is the *real* number
   `C Γ(−Y)[(M−u)^Y − M^Y + (G+u)^Y − G^Y]`, the closed form of
   `E[e^{uX_τ}] = exp(τψ(−iu)) < ∞`; the numéraire instance
   `cgmy_numeraire_strip` (`u = 1` needs `1 < M`); and the pricing-machine
   instance `cgmy_cmPriceKernel_integrable` (continuity + (H-decay) on the
   contour `u ↦ u − i(α+1)`, condition `α + 1 < M`). Everything item 3 needs
   is either one of these statements or calculus on the real section they open.
3. **What BRIEF_012 proved, and why it shapes this brief.**
   `static_skeleton_does_not_select_measure` says the static skeleton — parity,
   bounds, the drift condition — leaves a whole segment of mutually equivalent
   martingale laws pricing the same call differently. So any theorem of the form
   "the drift condition fixes the measure" is false; the most a law can claim is
   "the drift condition fixes the measure ***relative to a named selection
   principle***". This brief names Esscher. And it lands the complementary half
   of C13's finding 2, which BRIEF_012 quotes as a constraint — *"within a
   single exponential-Lévy model the Esscher martingale equation is strictly
   monotone in the parameter (the cumulant is strictly convex), so
   non-uniqueness lives* ***across*** *selection principles, not within the
   Esscher family"*: BRIEF_012 needed that remark to be true to rule out
   intra-family witnesses; BRIEF_013 makes it a theorem
   (`cgmyCumulant_strictConvex` + `esscher_exists_unique_of_mem_range`:
   at most one Esscher parameter delivers a given drift, and the strip edge
   values decide whether one exists).
4. **The Esscher transform, concretely.** For a law with exponent `ψ`, the
   `e^{θx}`-tilt (density `e^{θx}/E[e^{θX}]`) has exponent
   `ψ^θ(v) := ψ(v − iθ) − ψ(−iθ)` — the shift the user-facing one-line of this
   brief names. For CGMY this is *internal*: the shift just moves the tempering
   rates, `(G, M) ↦ (G+θ, M−θ)` (§1 below), so the whole of BRIEF_011 — strip,
   decay, kernel integrability — applies to the tilted law by parameter
   substitution. The drift delivered by tilt `θ` is
   `g(θ) := κ(θ+1) − κ(θ)` where `κ(u) := ψ(−iu)` on the strip, and the
   martingale condition is the **Esscher equation** `g(θ) = r − q`.

## Re-scope note — the named measure lands at the exponent level (honesty item)

Item 3's second clause asks for the drift "proved at the new law under that
measure", as an expectation. The tree has **no CGMY law as a `Measure ℝ`** —
BRIEF_011 landed the exponent and the Lévy *density*, and its header labels the
Lévy–Khintchine representation itself as prose (mathlib v4.34.0 has no such
theorem). Constructing the tilted law `dQ^θ ∝ e^{θx} dP` would need `P` first.
So this brief lands item 3's drift at the level the tree can carry — the
characteristic factor — and says so in the module header:

* the Esscher parameter `θ*` is defined and its existence/uniqueness proved
  from the closed form and the strip;
* the drift condition is proved as the factor identity
  `cgmyCharFactor C (G+θ*) (M−θ*) Y τ (−I) = exp(τ(r−q))`
  (`esscher_drift_factor`), which *is* `E^{θ*}[e^{X_τ}] = e^{(r−q)τ}` once the
  factor is read as the tilted law's transform;
* the identification "factor = expectation" stays in the same labelled-prose
  class as BRIEF_011's Lévy–Khintchine caveat, route-checked numerically. The
  expectation-level twin of `integral_spot_mul_phi_eq_forward` is gated on a
  law construction and is **explicitly out of scope** — recorded here so the
  acceptance bar below cannot be read as having silently dropped it.

This is the same move BRIEF_010 made ("re-scoped": the pricing identity proved
at any strip law, the law abstracted behind a hypothesis), one level down.

## The mathematics to land

New module `ImprovedBS/Esscher.lean`, `namespace BSM`, importing
`ImprovedBS.CGMY` (and through it `ImprovedBS.Pricing`). Five sections.

**§1 The Esscher shift — algebra on BRIEF_011.**

    def esscherExponent (ψ : ℂ → ℂ) (θ : ℝ) (v : ℂ) : ℂ :=
      ψ (v - (θ : ℂ) * Complex.I) - ψ (-(θ : ℂ) * Complex.I)

    theorem cgmyExponent_zero : cgmyExponent C G M Y 0 = 0

    theorem esscher_cgmy_shift :          -- the shift stays inside the family
      esscherExponent (cgmyExponent C G M Y) θ =
        cgmyExponent C (G + θ) (M - θ) Y

    theorem esscher_tilt_factorization :   -- e^{τψ(v−iθ)} = e^{τψ^θ(v)} · e^{τψ(−iθ)}
      cgmyCharFactor C G M Y τ (v - (θ : ℂ) * I) =
        cgmyCharFactor C (G + θ) (M - θ) Y τ v *
          cgmyCharFactor C G M Y τ (-(θ : ℂ) * I)

`esscher_cgmy_shift` is the whole algebraic content of the Esscher transform
for CGMY: `M − i(v − iθ) = (M−θ) − iv` and `G + i(v − iθ) = (G+θ) + iv`, after
which the subtracted `ψ(−iθ)` cancels `M^Y` and `G^Y` and leaves exactly the
CGMY form at `(G+θ, M−θ)`. It is `push_cast; ring` on the cpow terms — **no
branch hypothesis needed**: the identity is term algebra, and the positivity
conditions enter only where the *shifted parameters* are then consumed by
BRIEF_011's theorems. Note the anti-vacuity shape: `esscherExponent` is defined
by the shift for a *general* `ψ`, so `esscher_cgmy_shift` is a theorem relating
two independent expressions — defining `esscherExponent` *as* the shifted CGMY
form would make the theorem `rfl` and hollow it (the C1 failure mode; the
`[ESSCHER]` lint check below guards the definition body).

**§2 The cumulant and its strict convexity — real analysis on the strip.**

    def cgmyCumulant (C G M Y u : ℝ) : ℝ :=
      C * Real.Gamma (-Y) * ((M - u) ^ Y - M ^ Y + (G + u) ^ Y - G ^ Y)

    theorem cgmyCumulant_eq_strip        -- cites cgmyExponent_strip, not re-proved:
      -- ψ(−iu) = ↑(cgmyCumulant … u) for u ∈ (−G, M)
    theorem cgmyCumulant_continuousOn    -- on Icc (−G) M, for 0 < Y (0^Y = 0 at the edges)
    theorem cgmyCumulant_hasDerivAt      -- κ'(u) = CΓ(−Y)·Y·((G+u)^{Y−1} − (M−u)^{Y−1})
    theorem cgmyGamma_two_sub_eq         -- Γ(−Y)·Y·(Y−1) = Γ(2−Y), via Real.Gamma_add_one twice
    theorem cgmyCumulant_hasDerivAt2     -- κ''(u) = C·Γ(2−Y)·((M−u)^{Y−2} + (G+u)^{Y−2})
    theorem cgmyCumulant_second_deriv_pos -- 0 < κ''(u) on (−G, M): Γ(2−Y) > 0, both rpows > 0
    theorem cgmyCumulant_deriv_strictMono -- κ' strictly increasing on (−G, M)
    theorem cgmyCumulant_strictConvex     -- StrictConvexOn ℝ (Ioo (−G) M) cgmyCumulant

Two things worth saying about the route. First, the Γ rewrite: the second
derivative of `κ` carries `Γ(−Y)·Y(Y−1)`, and `Real.Gamma_add_one` (verified at
the tag, takes `s ≠ 0`) applied twice gives `Γ(2−Y) = (1−Y)(−Y)Γ(−Y)` — so the
curvature constant is `Γ(2−Y)`, positive for `Y ∈ (0,2)` by
`Real.Gamma_pos_of_pos`, with **no case split on `Y ≷ 1`** (the pole at `Y = 1`
is excluded as everywhere in BRIEF_011, and `2−Y > 0` keeps the positivity
argument one-line). Second, everything here is real `rpow` on positive bases —
the strip theorem is what buys that; no `cpow` estimate from BRIEF_011 §4 is
redone. The measured closed form of `κ''` is in the route-check table.

**§3 The Esscher equation, and the strip decides solvability.**

    def esscherDriftMap (C G M Y θ : ℝ) : ℝ :=
      cgmyCumulant C G M Y (θ + 1) - cgmyCumulant C G M Y θ

    def esscherThetaZero (G M : ℝ) : ℝ := (M - G - 1) / 2

    def esscherDriftBound (C G M Y : ℝ) : ℝ :=
      |C * Real.Gamma (-Y)| * |(G + M) ^ Y - (G + M - 1) ^ Y - 1|

`esscherDriftMap` is the drift `g(θ) = κ(θ+1) − κ(θ)` the tilt at `θ` delivers;
the martingale condition is `esscherDriftMap … θ = r − q`, and `θ` must place
both `θ` and `θ+1` in the strip `(−G, M)`, i.e. **`θ ∈ Ioo (−G) (M−1)` — the
admissible interval, nonempty exactly when `1 < G + M`** (a hypothesis the docs
do not yet carry and the first implementation attempt will meet immediately:
`G = 0.3, M = 0.5` gives `(−0.3, −0.5)`).

The three structural facts, all measured before issue:

    theorem esscherDriftMap_reflect :    -- antisymmetry about θ₀ = (M−G−1)/2
      esscherDriftMap C G M Y (M - G - 1 - θ) = - esscherDriftMap C G M Y θ
    theorem esscherDriftMap_zero :
      esscherDriftMap C G M Y (esscherThetaZero G M) = 0
    theorem esscherDriftMap_bound_eq :   -- the boundary values are ± the bound
      esscherDriftMap C G M Y (-G) = - esscherDriftBound C G M Y ∧
      esscherDriftMap C G M Y (M - 1) = esscherDriftBound C G M Y

`reflect` is the engine: writing `x = M − θ`, `s = G + M`, the map is
`CΓ(−Y)[(x−1)^Y + (s−x+1)^Y − x^Y − (s−x)^Y]`, and `x ↦ s+1−x` swaps the
bracket's halves and negates it — `ring` on rpow terms. Its corollaries are the
two sharpest statements of the brief: the **zero-drift Esscher parameter is
exactly `θ₀ = (M−G−1)/2`** — independent of `Y` — with the tilt's rates
`((G+M−1)/2, (G+M+1)/2)`; and the attainable drift interval is **symmetric,
`(−H, H)`, with `H` a function of `(C, Y, G+M)` alone**.

    theorem esscherDriftBound_pos        -- H > 0 for 0 < C, 0 < Y < 2, Y ≠ 1, 1 < G+M:
      -- s^Y − (s−1)^Y − 1 has the sign of Y − 1 (MVT / monotone-derivative, both regimes)
    theorem esscherDriftMap_strictMono : -- StrictMonoOn on Ioo (−G) (M−1)
      -- g'(θ) = κ'(θ+1) − κ'(θ) > 0 because κ' is strictly increasing (§2)
    theorem esscherDriftMap_mem_range :  -- values stay strictly inside the edge values
      θ ∈ Ioo (-G) (M-1) →
        - esscherDriftBound C G M Y < esscherDriftMap C G M Y θ ∧
        esscherDriftMap C G M Y θ < esscherDriftBound C G M Y

and the headline pair — **"the strip theorem tells you when `θ` exists"**:

    theorem esscher_exists_unique_of_mem_range
      (hC hG hM hY hY₂ hY₁ hGM)          -- 0<C, 0<G, 0<M, 0<Y<2, Y≠1, 1 < G+M
      (hd : |r - q| < esscherDriftBound C G M Y) :
      ∃! θ ∈ Ioo (-G) (M - 1), esscherDriftMap C G M Y θ = r - q

    theorem esscher_no_solution_of_outside_range
      (hd : esscherDriftBound C G M Y ≤ |r - q|) :
      ¬ ∃ θ ∈ Ioo (-G) (M - 1), esscherDriftMap C G M Y θ = r - q

Existence is IVT on the continuous extension of `g` to `[−G, M−1]`
(`cgmyCumulant_continuousOn`, with `0^Y = 0` at the edges — the `Y > 0`
continuity of rpow at 0 is the one leaf lemma flagged in §"Mathlib name check"),
uniqueness is `esscherDriftMap_strictMono`; the negative half is
`esscherDriftMap_mem_range` contraposed. Together they say the martingale
condition selects **exactly one** Esscher parameter when the target drift lies
strictly inside the strip's edge values, and **none** otherwise — no third case.

**§4 The drift condition at the named measure.**

    theorem esscher_theta_zero_unique :  -- the exact anchor
      -- the unique zero-drift solution is esscherThetaZero G M
    theorem esscherExponent_neg_I_eq (hθ : θ ∈ Ioo (-G) (M - 1)) :
      esscherExponent (cgmyExponent C G M Y) θ (-I) =
        ↑(esscherDriftMap C G M Y θ)     -- via cgmyExponent_strip twice: θ, θ+1 ∈ (−G, M)
    theorem esscher_drift_factor         -- item 3's deliverable, at factor level
      (hθ : θ ∈ Ioo (-G) (M - 1)) (hE : esscherDriftMap C G M Y θ = r - q) :
      cgmyCharFactor C (G + θ) (M - θ) Y τ (-I) =
        Complex.exp (↑τ * ↑(r - q))
    theorem esscher_tilted_numeraire (hθ : θ ∈ Ioo (-G) (M - 1)) :
      1 < M - θ                          -- θ+1 < M, the numéraire point in the TILTED strip

`esscher_drift_factor` is the re-scoped item-3 statement (§"Re-scope note"):
`exp(τψ^θ*(−i)) = exp(τ(r−q))`, read as `E^{θ*}[e^{X_τ}] = e^{(r−q)τ}`, i.e.
`E^{θ*}[S_T] = S·e^{(r−q)τ}` — the CGMY twin of
`integral_spot_mul_phi_eq_forward` at the exponent level. Note
`esscher_tilted_numeraire`: the strip containment that makes `θ` admissible
*simultaneously* puts the numéraire point inside the tilted strip — one
hypothesis doing two jobs, which is why the drift condition and the moment
condition never separate in this family.

**§5 Pricing at the Esscher measure — consuming BRIEF_010/011, not re-proving.**

    theorem esscher_correction_invariant :
      cgmyTemperedCorrection C (G + θ) (M - θ) Y =
        cgmyTemperedCorrection C G M Y   -- c' carries M + G; ring
    theorem esscher_cmPriceKernel_integrable
      (hθ : θ ∈ Ioo (-G) (M - 1)) (hα : 0 < α) (hcontour : α + 1 < M - θ)
      (hC hY hY₂ hY₁ hτ) :
      Integrable (cmPriceKernel (cgmyCharFactor C (G + θ) (M - θ) Y τ) α)

The second is `cgmy_cmPriceKernel_integrable` **cited at the shifted parameters
`(G+θ, M−θ)`** — the tilt's own pricing-line condition is `α + 1 < M − θ`
(C14 at shifted rates: `G+θ` does not constrain the line), and everything else —
continuity, the decay rate `r = 2C|Γ(−Y)cos(πY/2)|`, the correction `c'`, the
threshold — is inherited. The invariance theorem records *why* the decay
survives the tilt unchanged to leading order: `r` depends only on `(C, Y)` and
`c'` only on `(C, Y, G+M)`, both tilt-invariant; only `K₀` moves. This is the
capstone that makes item 3 a pricing statement and not a measure-theoretic
curiosity: the named Esscher measure plugs straight into the item-4 machine.
`[ESSCHER]` clause 2 enforces the citation — re-deriving kernel integrability
from `cmPriceKernel_integrable` inside the new module is the cheat, exactly as
`[CGMY]` guards the same route commitment one level down.

## The numeric contract (fixed witness sets)

Unlike BRIEF_012's dyadic contract, Esscher parameters are transcendental, so
the contract is **four parameter sets plus assertions**, not exact prices.
τ = 1 throughout; solver = bisection, 200 iterations.

| set | `(C, G, M, Y)` | target `r−q` | `θ*` | attainable range `(−H, H)` | shifted rates `(G+θ*, M−θ*)` |
|---|---|---|---|---|---|
| **A** | `(1, 5, 10, 0.7)` | `0.05` | `2.381041` | `(−2.932381, 2.932381)` | `(7.381041, 7.618959)` |
| **B** | `(1, 2, 8, 1.5)` | `0.05` | `2.531499` | `(−8.561606, 8.561606)` | `(4.531499, 5.468501)` |
| **C** | `(0.5, 0.05, 1, 0.3)` | `0.05` | `−0.021865` | `(−0.848811, 0.848811)` | `(0.028135, 1.021865)` |
| **D** | `(1, 0.5, 3, 1.9)` | `0.05` | `0.752775` | `(−22.837027, 22.837027)` | `(1.252775, 2.247225)` |

Assertions the committed test carries, per set: `θ* ∈ (−G, M−1)`; residual
`|g(θ*) − (r−q)| ≤ 1e-12`; `ψ^θ*(−i)` evaluated by the *complex* oracle route
agrees with `r−q` to `1e-12` with imaginary part `< 1e-12` (the branch check:
both bases `M−θ*−1 > 0` and `G+θ*+1 > 0` are positive reals); the drift factor
agrees with `exp(τ(r−q))`; set A additionally carries `α = 1.5`, with the
tilted contour legal (`α + 1 = 2.5 < 7.618959`) and the numéraire in the
tilted strip (`1 < 7.618959`). Exact anchors that are not solver outputs:
`g((M−G−1)/2) = 0` (set A: `θ₀ = 2`), the antisymmetry
`g(θ₀ + t) = −g(θ₀ − t)`, and `H = |CΓ(−Y)|·|(G+M)^Y − (G+M−1)^Y − 1|`.

**Canaries** (committed, so the test can fail):

* **out of range:** set A, target `3.0324 > H = 2.9324` — no sign change, no
  solution; the test asserts rejection, not a solve;
* **empty domain:** `G = 0.3, M = 0.5` — the admissible interval
  `(−0.3, −0.5)` is empty because `G + M ≤ 1`; the test asserts emptiness;
* **strong tilt:** set A with target `0.4` gives `θ* = 4.8271`,
  `M − θ* = 5.1729`, so the tilted contour condition `α + 1 < M − θ*` binds at
  `α = 4.1729` — the strip gate on the *pricing* side, measured.

## The numeric route-check (measured before the brief — ledger C4)

Scratch scripts `/tmp/b13/route1.py`–`route4b.py` against the repository's own
oracle (`experiments/black_scholes.py`: `cgmy_exponent`, `cgmy_gamma_neg`,
`cgmy_tempered_rate/correction/constant`, `cgmy_decay_threshold`,
`cgmy_pricing_contour_v`), 2026-09-24. Parameter grid
`C ∈ {0.5, 1}`, `G ∈ {0.05, 0.5, 5}`, `M ∈ {1, 3, 10}`,
`Y ∈ {0.3, 0.7, 0.99, 1.3, 1.7, 1.9}` — **108 sets**, all with `G + M > 1`
(the smallest sum is `1.05`; empty-domain canaries therefore use off-grid
parameters).

| check (Lean declaration it shadows) | grid | result |
|---|---|---|
| family closure `ψ(v−iθ) − ψ(−iθ) = ψ_{C,G+θ,M−θ,Y}(v)` (`esscher_cgmy_shift`) | 108 sets × 5 θ-fracs × 7 v-points | worst rel resid **1.124e-13** |
| `κ'' = CΓ(2−Y)[(M−u)^{Y−2} + (G+u)^{Y−2}]` (`cgmyCumulant_hasDerivAt2`) | 540 strip points, numeric 2nd derivative | O(h²) convergence: resid `1.52e-4 → 1.52e-6 → 1.56e-8` for `h = 1e-3…1e-5·(G+M)`, roundoff floor `6.4e-7` at `1e-6`; **all 540 values > 0** |
| `Γ(−Y)·Y(Y−1) = Γ(2−Y)` (`cgmyGamma_two_sub_eq`) | 108 sets | worst rel resid **3.015e-15** |
| strict monotonicity of `g` on `(−G, M−1)` (`esscherDriftMap_strictMono`) | 108 sets × 400 increments | **43200 increments, most negative `0.0`** |
| boundary ordering `L < H` and `L < g(θ) < H` inside (`esscherDriftMap_mem_range`) | 108 sets × 5 θ-fracs | **0 ordering failures, worst violation `0.0`** |
| existence inside the range (`esscher_exists_unique_of_mem_range`) | targets `{−0.2, 0, 0.02, 0.05}` × 108 sets | **427 solved**, worst residual **1.268e-13**; **5 out-of-range targets correctly rejected** |
| antisymmetry `g(θ₀+t) = −g(θ₀−t)` (`esscherDriftMap_reflect`) | 540 points | worst **8.971e-14** |
| `g(θ₀) = 0` at `θ₀ = (M−G−1)/2` (`esscherDriftMap_zero`) | 108 sets | worst **5.684e-14** |
| range half-width closed form (`esscherDriftMap_bound_eq`, `esscherDriftBound`) | 108 sets | worst rel resid **4.432e-14** |
| correction invariance `c'(G+θ, M−θ) = c'(G, M)` (`esscher_correction_invariant`) | solved sets | worst rel resid **2.437e-16** |
| tilted decay on the pricing contour at `(G+θ*, M−θ*)`, `α+1 < M−θ*` (consumption in `esscher_cmPriceKernel_integrable`) | 880 probes past the shifted threshold (`u₀`, `1.7u₀`, `12u₀`, `2000`) | **0 violations** of `Re ψ ≤ −r|u|^Y + c'|u|^{Y−1} + K̃₀`, of the half-rate bound, and of the factor decay |
| drift factor at `θ*` (sets A–D) | complex route | `ψ^θ*(−i) = r−q` to 12 digits, imaginary parts `≤ 1e-16`; factor agrees with `e^{τ(r−q)}` |

**Mutation canaries measured at issue** (each becomes a committed mutant):
wrong-sign shift `ψ(v + iθ) − ψ(iθ)` vs the closure form: resid **2.251**
(O(1), kills the closure assertion); `Γ(−Y)` in place of `Γ(2−Y)` in the
curvature: resid **5.762** (O(1)); `g` flipped to `κ(θ) − κ(θ+1)`: strictly
*decreasing* everywhere sampled (kills the monotonicity assertion).

Two facts the check also pins down, BRIEF_011-style: the attainable range is
**always the symmetric interval `(−H, H)`** — a consequence of `reflect`, so a
test asserting asymmetry would be wrong, not flaky — and the solver residual
sits at `1e-13`, so the committed test's `1e-12` tolerance carries a 10×
margin while the exact-anchor assertions (`θ₀`, `H`, antisymmetry) are
tolerance-free at `1e-13` scale.

## Grading wiring (the repo motion)

* `ImprovedBS/Esscher.lean`: new module, one import line + blurb in
  `ImprovedBS.lean`; nothing else outside the module. **30 declarations
  (5 defs + 25 theorems)**, every one in `REQUIRED` **and** `PROTECTED`
  (definitions are specifications — hollowing `esscherExponent` or
  `esscherDriftBound` is a diff): defs `esscherExponent`, `cgmyCumulant`,
  `esscherDriftMap`, `esscherThetaZero`, `esscherDriftBound`; theorems
  `cgmyExponent_zero`, `esscher_cgmy_shift`, `esscher_tilt_factorization`,
  `cgmyCumulant_eq_strip`, `cgmyCumulant_continuousOn`,
  `cgmyCumulant_hasDerivAt`, `cgmyCumulant_hasDerivAt2`,
  `cgmyGamma_two_sub_eq`, `cgmyCumulant_second_deriv_pos`,
  `cgmyCumulant_deriv_strictMono`, `cgmyCumulant_strictConvex`,
  `esscherDriftMap_reflect`, `esscherDriftMap_zero`,
  `esscherDriftMap_bound_eq`, `esscherDriftBound_pos`,
  `esscherDriftMap_strictMono`, `esscherDriftMap_mem_range`,
  `esscher_exists_unique_of_mem_range`,
  `esscher_no_solution_of_outside_range`, `esscher_theta_zero_unique`,
  `esscherExponent_neg_I_eq`, `esscher_drift_factor`,
  `esscher_tilted_numeraire`, `esscher_correction_invariant`,
  `esscher_cmPriceKernel_integrable`. Statement pins **210 → 240**, audit list
  **186 → 211**, the 210 pre-existing entries byte-identical (append-only);
  the `elab` layer bootstraps red by design and is merged verbatim — the
  commit must be a pure insertion. If a statement moves during CI (as
  `cgmy_contour_continuous` did, C15), the diff is recorded as a correction,
  and only inside this module.
* `scripts/lean_lint.py`: a new **`[ESSCHER]` check** with four clauses and at
  least one mutant each:
  1. `esscherExponent` must be defined by the **shift** — its body applies
     `ψ` to `v − ↑θ·I` and subtracts `ψ` at `−↑θ·I`, and must **not** mention
     `cgmyExponent` (the cheat is defining the shift *as* the shifted CGMY form
     and making `esscher_cgmy_shift` an `rfl` tautology — C1 item 1 reloaded);
  2. `esscher_cmPriceKernel_integrable` must **cite**
     `cgmy_cmPriceKernel_integrable` and must not mention
     `cmPriceKernel_integrable` (the cheat is re-deriving integrability from
     the abstract interface — the `[CGMY]` route commitment, one level up);
  3. `esscher_exists_unique_of_mem_range` must carry `1 < G + M`, `Y ≠ 1` and
     the `esscherDriftBound` comparison, and no `min` over `G`/`M` may appear
     anywhere in the module (the C14 regression guard, extended);
  4. `esscherDriftBound`'s body must carry
     `(G + M) ^ Y - (G + M - 1) ^ Y - 1` (the closed form is the
     specification; the cheat is defining the bound as a `max` over sampled
     values, which builds and certifies nothing).
  Mutants seeded in `tests/test_lint.py`: **E1** the hollowed shift (clause 1),
  **E2** the re-derived integrability (clause 2), **E3** the dropped
  `1 < G + M` (clause 3). House rule: each killed by name; the README and this
  brief's counts move with them (**32 → 35** lint cheats, 5 controls).
* `experiments/black_scholes.py`: six new oracle functions shadowing the Lean
  definitions — `esscher_exponent` (the shift, route A), `cgmy_cumulant` (the
  real κ), `esscher_drift_map` (g), `esscher_drift_bound` (H),
  `esscher_theta_zero` (`(M−G−1)/2`), and `esscher_solve` (bisection on g,
  returning `None` without a sign change) — built only on the existing CGMY
  primitives, with the one-place contour convention of BRIEF_011 respected.
* `tests/test_bs.py`: a committed `test_esscher_drift` asserting the whole
  route-check table — the closure identity on the grid, the four witness sets
  of §"The numeric contract" with their assertions, the exact anchors
  (`θ₀`, antisymmetry, the `H` closed form), the three canaries
  (out-of-range rejection, empty domain, strong tilt), the correction
  invariance and the tilted-decay probes. **test_bs.py 19 → 20.**
* `tests/test_mutants.py`: two mutants, each killed by `test_esscher_drift`
  alone — **M20** the wrong-sign shift in `esscher_exponent`
  (`v + iθ` / `+iθ`, resid O(1) against the closure assertion) and **M21**
  the drift bound with its final factor sign-flipped
  (`(G+M−1)^Y − (G+M)^Y + 1`, which breaks the range assertions for every set
  with `Y < 1` and every set with `Y > 1` in opposite directions — one mutant,
  both regimes). **20 → 22** oracle mutants.
* `tests/golden_statements.json`: append-only, both layers, the 210
  pre-existing entries byte-identical; `elab` merged from CI verbatim.
* `benchmarks/LEDGER.md`: a row when CI grades the implementation. `docs/03`
  §D1 item 3 and `docs/04`'s queue get the issued status at issue and the
  landed status at merge.

## Mathlib name check at the tag (ledger C3, run at issue)

Unlike BRIEF_012's issue (no toolchain *and* no network), this brief's
mathlib names were read at the v4.34.0 source before issue. **Verified:**
`Real.Gamma_add_one (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s` and
`Real.Gamma_pos_of_pos` (`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`);
`StrictMonoOn.strictConvexOn_of_deriv` and `MonotoneOn.convexOn_of_deriv`
(`Mathlib/Analysis/Convex/Deriv.lean`); `hasDerivAt_rpow_const` /
`hasStrictDerivAt_rpow_const` with hypothesis `x ≠ 0 ∨ 1 ≤ p`, and the
`HasFDerivAt.rpow_const` family (`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean`);
the IVT file is `Mathlib/Topology/Order/IntermediateValue.lean`
(`intermediate_value_Icc` family; the `Ioo` variant's exact name to be
re-grepped at implementation); `exists_deriv_eq_slope` (used inside
`Mathlib/Analysis/Convex/Deriv.lean`'s proofs). **Flagged** (long-standing,
low-risk, first CI run is the name check): `strictMonoOn_of_deriv_pos`
(`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` per the docs; file not
re-read at the tag), `strictConvexOn_of_deriv2_pos` (same Deriv.lean file,
later chunk), and the continuity of `x ↦ x^Y` at `x = 0` for `0 < Y`
(`Pow/Continuity.lean` — fallback if the packaged lemma resists: prove
`Tendsto (· ^ Y)` at `0` from `Real.tendsto_rpow_atTop`-style estimates, or
state `cgmyCumulant_continuousOn` on `Ioo` and carry the two boundary values
as separate `rpow`-at-`0` evaluations, which changes nothing downstream since
the IVT only needs continuity on the closed interval via those endpoint
values).

## Done looks like (acceptance — machine-graded)

1. `lake build` green at the pinned tag, with `#print axioms` on the new
   `-- BRIEF_013:` section showing `[propext, Classical.choice, Quot.sound]`
   and never `sorryAx`.
2. `esscher_exists_unique_of_mem_range` and
   `esscher_no_solution_of_outside_range` are theorems, not `sorry` and not
   `True`: the elaborated pins must show the `1 < G + M` domain condition, the
   `Y ≠ 1` exclusion, and the `esscherDriftBound` comparison on both sides.
   The pair — existence exactly inside `(−H, H)`, no solution at and beyond —
   *is* "the strip theorem tells you when `θ` exists", and a one-sided
   version certifies only half the item.
3. `esscher_cgmy_shift` is proved at the general `esscherExponent` definition
   (the definition body carries the shift, the theorem carries the family
   closure — not the other way around), and `esscher_drift_factor` is proved
   consuming it plus `cgmyExponent_strip`, so the drift condition is a
   calculation on BRIEF_011's landed objects.
4. `esscher_cmPriceKernel_integrable` cites `cgmy_cmPriceKernel_integrable` at
   the shifted parameters with the tilted condition `α + 1 < M − θ` — the
   `[ESSCHER]` check reads the citation, and mutant E2 seeds the re-derivation.
5. `lint` green including `[ESSCHER]`, with E1/E2/E3 red under mutation and
   killed by name; `oracle` lane green including `test_esscher_drift`, with
   M20/M21 killed by that test alone.
6. No pinned statement outside `ImprovedBS/Esscher.lean` moved; `deferred: {}`
   untouched; T1–T6 and BRIEF_004–012 statements unchanged.

## Explicitly out of scope

* **The expectation-level drift** — `∫ S e^x dμ^θ = S e^{(r−q)τ}` against an
  actual tilted measure — per §"Re-scope note": there is no CGMY law as a
  `Measure ℝ` in the tree, so the factor-level statement is the honest
  deliverable and the LK caveat is inherited, not reopened.
* **The tilted law's skeleton instantiation** (item 5 at the Esscher measure:
  supplying `Integrable X`, the drift and `0 ≤ X` to
  `model_free_put_call_parity`/`model_free_call_bounds`). Same gate: needs the
  law. When a law construction lands, both this item and the skeleton instance
  come with it.
* **Other selection principles** — minimal-entropy, mean-correcting,
  calibrated. Item 3 says the choice is part of the model; this brief makes
  Esscher's choice a theorem and leaves the comparison to later briefs.
  BRIEF_012's witness already says no principle can claim uniqueness across
  principles; nothing here should be read as evidence for Esscher over the
  alternatives.
* **Item 6** (the GBM corner `Y → 2`): `Γ(−Y)` has its pole there and the
  corner needs its own normalization, as `docs/04`'s queue says.
* **The compound-Poisson Esscher version** (ties item 3 to the Lévy line the
  way BRIEF_012 noted for item 7): genuinely more work — an infinite-state
  law — and not here.
* **No stochastic integral, no hedging.** The Esscher measure is a
  one-marginal object; the hedging horizon stays where `docs/03`'s "Beyond
  BSM-2" puts it.

## Why this is worth a brief (and shaped this way)

Because item 3 is where the program's honesty machinery pays its bill. The
widening has an exponent (items 1–2), a pricing machine that consumes it
(item 4), a skeleton that survives it (item 5), and — since BRIEF_012 — a
*proof that no price it produces is "the" price without a named measure*
(item 7). Until item 3 lands, that proof points at an empty chair: the kit
demands a selection principle and the tree contains none. The Esscher
transform is the cheapest honest occupant — the shift is algebra on landed
definitions, the drift equation is one real function whose strict convexity is
a second derivative, and existence is an IVT on the strip BRIEF_011 already
proved — and the route-check measured every claim before this sentence was
written. The two things a reviewer should check are the two the guards watch:
the shift must be *derived, not defined* (clause 1 — the C1 tautology class),
and the pricing integrability must be *consumed from BRIEF_011, not re-proved*
(clause 2 — the route-commitment class) — because a green build that defines
the answer into the question, or quietly rebuilds the machine it claims to
instantiate, is exactly the green build that certifies nothing.
