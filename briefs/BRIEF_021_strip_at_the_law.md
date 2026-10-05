# BRIEF_021 — the strip at the law: the mgf on `(−G, M)`, the Esscher tilt at `cgmyLaw`, and items 3/5/4 at general `Y`

- **Status:** **ISSUED** — documentation plus a numeric route-check run at issue
  (no committed test, no PR yet). It changes no `.lean` file, no pin, no lint
  rule, no workflow; `deferred: {}` is untouched.
- **What this is.** The brief BRIEF_020 deferred in its own out-of-scope
  section ("the mgf on the strip, the Esscher tilt at the law, and items 3/5
  at general `Y` … the pieces" — README, `docs/03`), made concrete and
  checkable: the implementation brief for **`ImprovedBS/CgmyStrip.lean`**
  (name fixed here). It lands (1) the mgf `mgf id (cgmyLaw …) u =
  e^{τ·κ(u)}` for `−G < u < M` — BRIEF_020's CF at **real** `v` upgraded to
  the mgf line and the complex strip; (2) the Esscher tilt of the law itself
  (`Measure.tilted`, BRIEF_019 F7's name); (3) the expectation-level twins of
  kit **items 3 and 5** at general `Y` (drift identity and skeleton at the
  tilted law, `VGLaw`'s statements re-run at `cgmyTilt`); (4) the first
  **pricing statement at `cgmyLaw`** — BRIEF_010's triangle instantiated at
  the law. It fixes the declaration list, the statements, the counts, the five
  `[CgmyStrip]` lint clauses, the oracle primitives, the committed test and
  the five mutants M44–M48 its implementation must land.
- **Prerequisites:** BRIEF_009 (the skeleton, item 5), BRIEF_010 (the pricing
  identity), BRIEF_011 (`cgmyExponent`, `cgmy_numeraire_strip`,
  `cgmy_levy_far_moment`, `cgmy_contour_continuous`, `cgmy_contour_decay`),
  BRIEF_013 (`cgmyCumulant`, `cgmyCumulant_eq_strip`, `esscherDriftMap` and
  its solvers, `esscher_tilted_numeraire`, `esscher_exponent`,
  `esscher_cgmy_shift`), BRIEF_016 (the oracle's `carr_madan_by_exponent`),
  BRIEF_017 (the audit: F7 named `Measure.tilted`, F3 the mgf question),
  BRIEF_018 (`VGLaw` — the tilt/skeleton template this brief mirrors),
  BRIEF_019 (`cpLaw`, `charFun_cpLaw`, `charFun_convPow`), BRIEF_020
  (`cgmyCpProbability`, `cgmyLaw`, `charFun_cgmyLaw_eq_cgmyCharFactor`,
  the decomposition and its two monotone limits, the drift identity at real
  rate). All LANDED green; CI-only, no local toolchain.
- **Budget:** one Lean module plus one oracle test. The skills it needs are
  named rather than waved at:
  * the **truncation sandwich** that passes the mgf through the weak limit:
    bounded-continuous test functions of the weak topology
    (`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` applied to
    `x ↦ min (e^{u x}) K`) + a Markov tail under a **stricter** moment
    `u′ > u` + a uniform sup along BRIEF_020's ladder;
  * the **identity theorem in the complex variable** `z` mirroring mathlib's
    own `eqOn_complexMGF_of_mgf'` proof (`analyticAt_complexMGF` +
    `convex_integrableExpSet` + agreement on the real axis), with the target
    analytic by `differentiableAt_id.cpow` — the pattern already green at
    `CGMYLaw.lean:1040`;
  * the **`Measure.tilted` algebra** character for character from `VGLaw`
    (`isProbabilityMeasure_tilted`, `integral_exp_tilted`);
  * a **real-variable IBP** for the one-sided mgf forms, anchored on the
    shipped real-rate Γ lemma — strictly easier than BRIEF_020's (no `I`, no
    branch);
  * the **cpLaw mgf series** mirroring the landed `charFun_cpLaw` (the same
    `expSeries` sum), with `mgf_conv` as the three-line mirror of
    `charFun_conv` at `integral_conv`;
  * **instantiating** `carrMadan_eq_modelFreeCall` from four discharged
    hypotheses (`gbm_carrMadan_eq_bsCall` is the consumption precedent).
  Nothing here estimates a date: the repo's only clock is the CI run.

## Findings recorded at issue

All numbers below were run at issue through the repo's own oracle
(`experiments/black_scholes.py`, Python stdlib) on the witness
`(C, G, M) = (0.5, 5, 10)`, `τ = 0.25`, `r = 0.05`, `q = 0.02`
(`r − q = 0.03`), `S = 100`, `K = 110`, pricing horizon `1`, `α = 1.5`,
ladder `εₙ = 2⁻ⁿ`.

**F1. The mgf line is a value of the *landed* truncated exponent — and the
landed *theorems* about it stop at real `v`.** `cgmyTruncatedExponent`
takes `v : ℂ` natively (`CompoundPoisson.lean:462`), so at `v = −I·u` it *is*
`∫_{|x|≥ε} (e^{u x} − 1) ν` — no new integral is needed. But the landed
`decomp`/`tendsto`/integrand lemmas all carry `(v : ℝ)` hypotheses with
coercions (`CGMYLaw.lean:475,621`), and the dominators there use
`‖e^{ivx} − 1 − ivx‖ ≤ 3(vx)²` — a real-`v` bound. §1 therefore re-runs the
decomposition and the two monotone limits **at the line as real analysis**
(dominators `(u²x²/2)·1 + 2·1` on the ball, `e^{|u|x} + 1` off it — simpler
than BRIEF_020's, no `I`). Measured: the composite limit
`B̃₀(u) + u·d₀` agrees with `cgmy_cumulant` to **2.757e−12** (`Y = ½`, worst
over `u ∈ {−4.5, −2, 0.5, 4, 7, 9.5}`) and **2.657e−11** (`Y = 3⁄2`), with
imaginary part exactly `0`; the ladder converges at slopes **1.44 / 0.95 /
0.47** for `Y = ½, 1, 3⁄2` against the predicted `2 − Y` (errors at
`ε = 2⁻¹⁴`, `u = 4`: `6.36e−7`, `1.22e−4`, `3.13e−2`).

**F2. At `Y = 1` the mgf exists and the closed form does not carry it — so
the closed-form statements carry `Y ≠ 1`.** The ladder still converges
(slope `0.95`, predicted `1`), and the composite is finite and real:
`3.6777706672` at `u = −4.5` (and `9.5`), `1.0208380857` at `u = −2` (and
`7`), `−0.1548269490` at `u = 0.5`, `−0.2737312404` at `u = 4` — symmetric
about `(M − G)/2 = 2.5`. What does **not** exist there is `cgmyCumulant`:
it evaluates to `C · Real.Gamma (−1) · 0 = 0` under mathlib's `Γ(−1) = 0`
convention (BRIEF_017's F2 trap), and the oracle raises
(`cgmy_gamma_neg` refuses `Y = 1`). So `cgmyLaw_mgf` and its complex twin
carry `hY₁ : Y ≠ 1` — exactly as `esscherDriftMap_strictMono`,
`cgmyDrift_identity` and BRIEF_020's `cgmyLKExponent_eq_cgmyExponent`
already do. The `Y = 1` mgf *as a theorem of the composite* is measured
above and recorded, not claimed.

**F3. The strip's right edge belongs to the mgf domain only when `Y < 1` —
and the statements never go there.** At `u = M` the ladder converges for
`Y = ½` (`2.5442 → 2.5745` over `ε = 2⁻⁶ … 2⁻¹⁴`, the `0.129` gap to the
closed form being the `x_max = 60` tail `≈ 60^{−Y}/(2Y)`) and **diverges**
for `Y = 3⁄2` (`12.053 → 16.510 → 17.678`, rate `ε^{1−Y}`): at the edge the
near-zero jump integral `∫ (e^{Mx}−1)e^{−Mx} x^{−1−Y}` is finite exactly
when `Y < 1`. The closed form `ψ(−iM)` is finite for `Y ≠ 1` regardless —
so the edge is honest precisely where the strict hypotheses `-G < u`, `u < M`
exclude it. All statements keep `Ioo`; mutant M48 (§"Mutants") is the
refusal row.

**F4. The limit passage is a truncation sandwich in the weak topology — no
dominated convergence, no Portmanteau required.** The only convergence
theorem the sandwich needs is a *defining property* of the weak topology at
the tag: `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` binds
`∀ f : Ω →ᵇ ℝ`, so it applies to `f_K = min (e^{u·}, K)` (bounded,
continuous, nonnegative), giving `∫ f_K dμₙ → ∫ f_K dμ`. The two
directions are then:
`∫ f dμ = sup_K ∫ f_K dμ = sup_K lim ∫ f_K dμₙ ≤ liminf ∫ f dμₙ`, and
`∫ f dμ ≥ ∫ f_K dμ = lim ∫ f_K dμₙ ≥ liminf (∫ f dμₙ − tailₙ(K))` with the
**marginal** tail `tailₙ(K) ≤ K^{1 − u′/u} · supₘ Eₘ[e^{u′X}]` for any `u`
and `u′` deeper in the strip (Markov at `u′`, pointwise
`e^{ux} ≤ e^{(u−u′)t₀} e^{u′x}` past `t₀ = ln K / u` — two sign cases).
The uniform sup comes from the F1 ladder (a convergent sequence is bounded;
no packaged lemma is assumed — `tendsto_norm` + `Iio_mem_nhds` + a finite
head sup). Measured ingredients: `supₙ M_ε(u′)` over the ladder is
`1.718594` / `1.569021` (`Y = ½`) and `70.850003` / `52.695428`
(`Y = 3⁄2`) at `u′ = −4.9 / +9.7` (limits `1.718607 / 1.569024` and
`77.889934 / 57.602045`); the tail bound at `u = 4`, `u′ = 9.7` is
`3.06e−3` at `K = 10³` and `1.62e−7` at `K = 10⁶`, against the **constant**
`57.602045` the `u′ = u` mutant would produce (the bound stops decaying).
Portmanteau's set forms are shipped as the fallback if the truncated-function
route balks — `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`,
`ProbabilityMeasure.le_liminf_measure_open_of_tendsto` — also read at the
tag.

**F5. The complex extension is one identity theorem, and mathlib's own
proof shows the shape.** `analyticAt_complexMGF` /
`analyticOn_complexMGF` ship with hypothesis `z.re ∈ interior
(integrableExpSet id μ)`; `eqOn_complexMGF_of_mgf'` runs the continuation on
`convex_integrableExpSet.interior.linear_preimage reLm` with
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, agreement on the real
axis via `complexMGF_ofReal`, and `frequently_iff_seq_forall`. §2 mirrors
that proof with the target
`z ↦ cexp (τ * cgmyExponent … (−I * z))` = `cexp (τ·C·Γ(−Y)·[(M − z)^Y +
(G + z)^Y − M^Y − G^Y])` — on the open strip both bases sit in the right
half-plane (`Re (M − z) > 0`, `Re (G + z) > 0`), off the branch cut, and
`differentiableAt_id.cpow` is the rung already green in-tree
(`CGMYLaw.lean:1040`). Agreement on the reals is `complexMGF_ofReal` +
`cgmyCumulant_eq_strip` (latter landed, real `u`). Note for whoever goes
looking: **`eqOn_complexMGF_of_mgf` is not directly usable** — it compares
*two* random variables and we have no partner; the one-variable continuation
is the point. Measured: the composite `B₀(v) + iv·d₀` matches `ψ(v)` on the
complex strip to **7.010e−13** (`Y = ½`) / **9.284e−12** (`Y = 3⁄2`) over
five points including `z = 7 + i`; the ladder at `ε = 2⁻¹⁴` gives
`5.09e−7 … 1.61e−6` (`Y = ½`) and `2.50e−2 … 7.93e−2` (`Y = 3⁄2`) over
`z ∈ {0.5+0.5i, 0.5+2i, 4+0.5i, 4−1.5i}` at rate `ε^{2−Y}`.

**F6. The tilt is the `VGLaw` proof, character for character.**
`Measure.tilted`, `isProbabilityMeasure_tilted` and `integral_exp_tilted`
are all green in `VGLaw.lean` — §3 defines `cgmyTilt C G M Y τ θ :=
(cgmyLaw …).tilted (fun x ↦ θ * x)` and re-runs `vgTilt_isProbabilityMeasure`
/ `vg_tilt_mgf` / `vg_drift_identity` with §1's `cgmyLaw_mgf` in place of
`vgLaw_mgf`. The numéraire is a *citation* (`esscher_tilted_numeraire`:
`θ ∈ Ioo (−G) (M−1)` says `θ + 1 < M`), never a hypothesis. Item 3 is
`S · M(θ+1) / M(θ) = S · e^{τ·g(θ)}` against the **def body** of
`esscherDriftMap` (`κ(θ+1) − κ(θ)`). Measured at the solved `θ*`
(`2.689658466` at `Y = ½`, `2.046326895` at `Y = 3⁄2`, residuals
`0.030000000000`): the composite-level ratio equals `e^{τ(r−q)} =
1.0075281954` to **1.33e−14 / 1.35e−14**; the ladder-level ratio's worst
error at `ε = 2⁻¹⁴` is `1.38e−3` (`Y = ½`) / `5.03e−3` (`Y = 3⁄2`) — the
test asserts the composite row tightly and the ladder row at rate.

**F7. The raw law is not risk-neutral — pricing does not need it to be, and
the skeleton therefore lands at the tilt.** `κ(1) = −0.090650566`
(`Y = ½`) / `−1.307099676` (`Y = 3⁄2`): `e^{τκ(1)} = 0.9775922 / 0.7212461`
against the forward `e^{τ(r−q)} = 1.0075282`. Two consequences, both in the
statements below: **(a)** items 3/5 land at `cgmyTilt` (drift by
construction — `VGLaw`'s precedent, BRIEF_018 F3's law (c)); **(b)** the
pricing identity needs no drift at all — `carrMadan_eq_modelFreeCall` is a
transform statement whose four hypotheses discharge from landed + §1:
continuity and decay of `contourCharFun` on the line come from
`cgmy_charFactor_contour_continuous` / `cgmy_contour_decay` once §2's
corollary identifies the line, the tail moment `Integrable (e^{(α+1+δ)x})`
is §1 at `u = α + 1 + δ` with `α + 1 + δ < M`, and `hX` is §1 at `u = 1`
with `1 < M` from `cgmy_numeraire_strip`. The tilted Carr–Madan price
measured through `esscher_exponent` is `5.24603314` (`Y = ½`) and
`28.43523097` (`Y = 3⁄2`), inside the bounds `[0, 98.01986733]`, with the
drift check `ψ^θ(−i) − (r − q) = 6.83e−16 / 6.19e−15`.

**F8. Quadrature ceiling in the `eps = 0` composite at large `|v|` —
recorded, not fixed.** `_expm1_minus_z_complex`'s Taylor stops at `k = 59`
and its docstring claims it "converges in one pass for `|z|` far beyond the
cutoff"; measured, it does not: the composite on the pricing line at
`v = 30 − 2.5i` errs by **3.396e+02**, at `v = 60 − 2.5i` by **2.690e+20**,
with `n_panel` 400 → 8000 changing nothing (the series, not the mesh). No
landed row is affected — landed `v`'s never exceed `|z| ≲ 2` — and the
**ladder** path (`_expm1_complex`, exact `cmath.exp` branch) has no such
limit (on the line it was run to `ε = 2⁻¹⁶`). This brief's `eps = 0`
composite rows therefore stay at `|v| ≤ 10` on the line, where the worst
residual against `ψ` is **5.702e−11** (`Y = 3⁄2`, `u = 10`). A guarded
fallback (`cmath.exp(z) − 1 − z` above `|z| > 25`) is the obvious repair;
out of scope here (and recorded as correction **C28** below).

## The mathematics to land

### §1 The mgf on the strip, at the marginals and at the law

Throughout: `hC : 0 < C`, `hG : 0 < G`, `hM : 0 < M`, `hY : 0 < Y`,
`hY₂ : Y < 2`, `hτ : 0 < τ`, `hY₁ : Y ≠ 1` where the closed form enters;
the ladder is BRIEF_020's `εₙ = 2⁻ⁿ`.

1. **Marginal mgf.** For the jump law `ρ_ε` (`cgmyJumpLaw`), the mgf
   `mgf id ρ_ε u` is finite on the strip by the far-field moment in both
   directions (positive side `cgmy_levy_far_moment` at `u < M`; negative side
   its `integral_comp_neg_Ioi` mirror at `u > −G`), and the compound-Poisson
   marginal satisfies

   ```lean
   theorem cgmyCpProbability_mgf … (hu₁ : -G < u) (hu₂ : u < M) :
       mgf id (cgmyCpProbability C G M Y τ ε hC hG hM hY hε : Measure ℝ) u =
         Real.exp (τ * (cgmyTruncatedExponent C G M Y ε (-(Complex.I * u))).re)
   ```

   by the mirror of the landed `charFun_cpLaw`: `mgf_conv` (three lines at
   `integral_conv`, the mirror of `charFun_conv`), `mgf_convPow`
   (the landed `charFun_convPow` induction), the `expSeries` sum (same
   `NormedSpace.expSeries_div_hasSum_exp` shape as the landed ℂ proof —
   route through `complexMGF` at real `z` and `complexMGF_ofReal` if the `ℝ`
   instantiation balks; see name-check), assembled through
   `integral_sum_measure`.

2. **The decomposition at the line** — the real-exponential twin of
   `cgmyTruncatedExponent_decomp`:

   ```lean
   theorem cgmyMgfTruncatedExponent_decomp … (ε : ℝ≥0) (hε : 0 < ε) (hε₁ : ε ≤ 1) (u : ℝ) :
       (cgmyTruncatedExponent C G M Y ε (-(Complex.I * u))).re
         = (∫ x in {x | (ε:ℝ) ≤ |x|},
             (Real.exp (u * x) - 1 - Set.indicator (Icc (-1) 1) (fun y ↦ u * y) x)
               * (cgmyLevyDensity C G M Y x : ℝ))
           + u * (∫ x in Ioc (ε:ℝ) 1, cgmyDriftIntegrand C G M Y x)
   ```

   (the indicator's coefficient is `u`, not `I·v`, because `i·(−I·u) = u`).
   The implementation may instead introduce a real def
   `cgmyMgfTruncatedExponent` with a bridge lemma to the landed complex one —
   in which case the def count below is +1 and the theorem count −0/−1.

3. **The limit to `κ`.** `Tendsto (fun n ↦ … εₙ …) atTop (𝓝 ((κ u : ℝ) : ℂ))`
   by the two `tendsto_setIntegral_of_monotone`s BRIEF_020 ran (same
   index, same monotone-in-`ε` sets; the compensator dominated on the ball by
   `(u²x²/2)·1 + 2·1`, off it by `(e^{|u|x} + 1)·ν`), the identification
   `B̃₀(u) + u·d₀ = κ(u)` by the real-variable IBP mirroring
   `cgmyOneSidedExponent_eq` (`integral_Ioi_mul_deriv_eq_deriv_mul` per side,
   or the `Y`-split F5 of BRIEF_020 used, anchored on the shipped
   **real-rate** `integral_cpow_mul_exp_neg_mul_Ioi` — no complex rate, no
   `G1`), and the landed `cgmyDrift_identity` for `d₀`.

4. **The sandwich and the two headlines** (F4's route):

   ```lean
   theorem cgmyLaw_exp_integrable … (hY₁ : Y ≠ 1) (hu₁ : -G < u) (hu₂ : u < M) :
       Integrable (fun x => Real.exp (u * x)) (cgmyLaw C G M Y τ hC hG hM : Measure ℝ)

   theorem cgmyLaw_mgf … (hY₁ : Y ≠ 1) (hu₁ : -G < u) (hu₂ : u < M) :
       mgf id (cgmyLaw C G M Y τ hC hG hM) u =
         Real.exp (τ * cgmyCumulant C G M Y u)
   ```

   plus the small set lemma `Ioo (-G) M ⊆ interior (integrableExpSet id
   (cgmyLaw …))` §2 consumes. Internal helpers (bounded-continuous
   truncation convergence; the Markov tail at `u′`; the ladder's uniform
   bound) are counted in §"What the implementation must land".

### §2 The complex strip: `complexMGF` and `contourCharFun`

```lean
theorem complexMGF_cgmyLaw … (hY₁ : Y ≠ 1) (hz₁ : -G < z.re) (hz₂ : z.re < M) :
    complexMGF id (cgmyLaw C G M Y τ hC hG hM) z =
      Complex.exp (τ * cgmyExponent C G M Y (-(Complex.I * z)))

theorem contourCharFun_cgmyLaw … (hY₁ : Y ≠ 1) (hv₁ : -M < v.im) (hv₂ : v.im < G) :
    contourCharFun (cgmyLaw C G M Y τ hC hG hM) v =
      cgmyCharFactor C G M Y τ v
```

Proof: both sides `AnalyticOnNhd` on the open strip (LHS
`analyticAt_complexMGF` + §1's interior lemma; RHS `Complex.exp` composed
with the `cpow` target — F5), preconnected by convexity, agreeing on the
real axis (`complexMGF_ofReal` + `cgmyLaw_mgf` + `cgmyCumulant_eq_strip`),
frequently at `z₀ = 0` (`frequently_iff_seq_forall`, sequence `1/n`) —
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, the pattern of
BRIEF_020's R4 and of mathlib's own `eqOn_complexMGF_of_mgf'` (F5). The
corollary converts `z = I·v` through `contourCharFun μ v = complexMGF id μ
(I * v)` (the `rfl` pattern `Pricing.lean:64` already uses) and `−I·(I·v) =
v`; note `−M < v.im < G` is *the same set* as `−G < (I v).re < M`, and the
pricing line `v = u − I(α+1)` sits in it exactly when `α + 1 < M` (C14).

### §3 The Esscher tilt at the law — item 3 at general `Y`

```lean
noncomputable def cgmyTilt (C G M Y τ θ : ℝ) : Measure ℝ :=
  (cgmyLaw C G M Y τ …).tilted (fun x => θ * x)   -- Measure.tilted, F7's name

theorem cgmyTilt_isProbabilityMeasure … (hθ : θ ∈ Ioo (-G) (M - 1)) :
    IsProbabilityMeasure (cgmyTilt … θ)

theorem cgmy_tilt_numeraire (G M θ : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1)) :
    1 < M - θ := esscher_tilted_numeraire G M θ hθ

theorem cgmy_tilt_mgf … (hθ : θ ∈ Ioo (-G) (M - 1))
    (hu₁ : -(G + θ) < u) (hu₂ : u < M - θ) :
    mgf id (cgmyTilt … θ) u =
      mgf id (cgmyLaw …) (u + θ) / mgf id (cgmyLaw …) θ

theorem cgmy_drift_identity … (hθ : θ ∈ Ioo (-G) (M - 1))
    (hdrift : esscherDriftMap C G M Y θ = r - q) :
    ∫ x, S * Real.exp x ∂(cgmyTilt … θ) = S * Real.exp ((r - q) * τ)
```

`VGLaw` verbatim, with one simplification: because `cgmyTilt` is defined
*as* `Measure.tilted` (R3 reads that off the RHS), the bridge
`vgTilt` needed by `unfold vgTilt Measure.tilted mgf` is definitional here.
`isProbabilityMeasure_tilted` is fed §1's `Integrable (e^{θ·})`,
`integral_exp_tilted` gives the ratio, then the calc
`S · mgf(tilt) 1 = S · mgf(law)(1+θ)/mgf(law) θ = S · e^{τ(κ(θ+1) − κ(θ))} =
S · e^{τ·esscherDriftMap θ} = S · e^{(r−q)τ}` — the middle difference *is*
the def body of `esscherDriftMap`, no shift lemma needed (F6).

### §4 Item 5 at the tilted law, and pricing at `cgmyLaw` — item 4's twin

```lean
theorem cgmy_modelFree_parity … (hθ : θ ∈ Ioo (-G) (M - 1)) … :
    modelFreeCall (cgmyTilt … θ) (fun x => S * Real.exp x) K r tau -
      modelFreePut (cgmyTilt … θ) (fun x => S * Real.exp x) K r tau
      = S * Real.exp (-q * tau) - K * Real.exp (-r * tau)

theorem cgmy_modelFree_call_bounds … (hK : 0 ≤ K) (hS : 0 ≤ S) :
    max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0 ≤
        modelFreeCall (cgmyTilt … θ) (fun x => S * Real.exp x) K r tau ∧
      modelFreeCall (cgmyTilt … θ) (fun x => S * Real.exp x) K r tau ≤
        S * Real.exp (-q * tau)

theorem cgmy_modelFree_put_bounds … :   -- parity corollary, the VGLaw route
    …

theorem cgmy_carrMadan_eq_modelFreeCall (hS : 0 < S) (hK : 0 < K) (hα : 0 < α)
    (hcontour : α + 1 < M) … :
    ↑(Real.exp (-α * Real.log (K / S))) *
        cmPriceIntegral (contourCharFun (cgmyLaw …)) α r tau S (Real.log (K / S))
      = ↑(modelFreeCall (cgmyLaw …) (fun x => S * Real.exp x) K r tau)
```

The skeleton trio discharges BRIEF_009's three facts at `cgmyTilt` the way
`vg_modelFree_*` does: probability (§3), `Integrable (S·e^x)` by
`integrable_tilted_iff` + §1 at `θ + 1` (`θ + 1 < M` — the numéraire
citation), drift (§3), `0 ≤ S·eˣ` pointwise. The pricing theorem is an
*instantiation* of the landed `carrMadan_eq_modelFreeCall` with the four
discharged hypotheses of F7(b) — continuity/decay through §2's corollary and
the landed `cgmy_charFactor_contour_continuous` / `cgmy_contour_decay`
(signature carries the same `α`, `Y`, `hG`/`hα` shape; C14's `α + 1 < M`
enters as `hcontour`), tail moment and `hX` from §1 — never a re-proof of
the triangle (`gbm_carrMadan_eq_bsCall` is the consumption precedent).

## The numeric route-check (run at issue, per ledger C4)

Python stdlib through the router oracle; the committed
`tests/test_bs.py::test_cgmy_strip` asserts the table. New oracle
primitives: `cgmy_mgf_exponent(C, G, M, Y, u)` — the composite `B̃₀(u) +
u·d₀` at `eps = 0` with its analytic tail (via
`cgmy_compensated_exponent(…, −I·u)` + `cgmy_paired_drift`), defined for
all `0 < Y < 2`; `cgmy_mgf(C, G, M, Y, tau, u) = exp(tau *
cgmy_mgf_exponent(…))` **refusing `u` outside the open strip** (the
`gamma_mgf` refusal precedent — F3/M48); `cgmy_complex_mgf(C, G, M, Y,
tau, z) = exp(tau * cgmy_exponent(…, −I z))` (F5's target).

| # | claim shadowed | row (witness above) | measured |
|---|---|---|---|
| 1 | `cgmyLaw_mgf` composite | `\|cgmy_mgf_exponent − cgmy_cumulant\|`, `Y = ½, 3⁄2`, six `u` | `≤ 2.76e−12` / `≤ 2.66e−11`, imag `0` |
| 2 | the ladder `Tendsto` | slope of `\|A_ε(4) − composite\|`, `ε = 2⁻⁴…2⁻¹¹` | `1.44 / 0.95 / 0.47` vs `2 − Y`; err@`2⁻¹⁴`: `6.36e−7 / 1.22e−4 / 3.13e−2` |
| 3 | `Y ≠ 1` is load-bearing (F2) | composite at `Y = 1`: `u = −4.5, −2, 0.5, 4, 7, 9.5` | `3.6777706672, 1.0208380857, −0.1548269490, −0.2737312404, …`; `cgmy_cumulant` refuses |
| 4 | open strip (F3/M48) | ladder at `u = M`: `Y = ½` vs `Y = 3⁄2` | `2.5442→2.5745` finite; `12.053→17.678` diverging |
| 5 | `complexMGF_cgmyLaw` | `\|A_ε(z) − ψ(−Iz)\|` at four strip points, `ε = 2⁻¹⁴`; composite at five | `5.09e−7…1.61e−6` / `2.50e−2…7.93e−2`; composite `≤ 7.01e−13` / `≤ 9.28e−12` |
| 6 | F4's uniform moment | `supₙ M_ε(u′)`, `u′ = −4.9, 9.7` | `1.7186 / 1.5690`; `70.8500 / 52.6954` (limits `1.7186 / 1.5690`; `77.8899 / 57.6020`) |
| 7 | F4's tail bound | `u = 4, u′ = 9.7`: bound at `K = 10³, 10⁶`, and the `u′ = u` value | `3.06e−3, 1.62e−7` vs constant `57.602045` |
| 8 | `cgmy_drift_identity` (item 3) | composite ratio `M(θ*+1)/M(θ*)` vs `e^{τ(r−q)}`; ladder worst at `2⁻¹⁴` | `1.0075281954` to `1.33e−14` / `1.35e−14`; ladder `1.38e−3 / 5.03e−3` |
| 9 | `cgmy_modelFree_*` (item 5) | tilted Carr–Madan call in the bounds; drift check `ψ^θ(−i)` | `5.24603314 / 28.43523097` in `[0, 98.01986733]`; `\|residual\| 6.83e−16 / 6.19e−15` |
| 10 | F7, why the tilt | raw law: `κ(1)`, `e^{τκ(1)}`, raw call | `−0.0907 / −1.3071`; `0.9776 / 0.7212` vs `1.0075282`; call `1.83672700 / 0.66582913` |
| 11 | `contourCharFun_cgmyLaw` on the pricing line | composite at `u = 0, 2, 10` vs `ψ` (`\|v\| ≤ 10`, F8); ladder at `ε = 2⁻⁸, 2⁻¹², 2⁻¹⁶` | `≤ 5.70e−11`; ladder `1.24e−7…2.11e−6` (`Y = ½`), `2.44e−2…4.15e−1` (`Y = 3⁄2`) |
| 12 | the `Y ↓ 0` corner of the mgf (against BRIEF_018's `vg_mgf`) | `\|κ_Y − κ_VG\|/Y` at `u = 0.5, 4`, `Y = 1e−2 → 1e−3` | `0.033605→0.033309`, `0.059296→0.058772` (mgf-level `0.008355→0.008282`, `0.014681→0.014552`) |

Canary (unchanged role): the `cgmy_mgf` refusal at `u ∈ {−G, M, M + 1}` and
`cgmy_cumulant`'s `Y = 1` refusal are asserted as `ValueError`s — the
guards that keep F2/F3 honest.

### Mutants (M44–M48, each killed by `test_cgmy_strip` alone)

| id | seeded in | corruption | separation (assert scale) |
|---|---|---|---|
| M44 | `cgmy_mgf_exponent` | the strip point is reflected: `u → −u` (the cumulant's argument flips sign) | `\|κ(4) − κ(−4)\| = 13.808910` (`Y = 3⁄2`) |
| M45 | `cgmy_mgf_exponent` | the paired drift term `u·d₀` is dropped from the composite | `6.564529` (`= \|4·d₀\|`) |
| M46 | `cgmy_mgf` | the `τ` factor drops out of the exponent | `\|e^{τκ} − e^{κ}\| = 0.450642` |
| M47 | `cgmy_complex_mgf` | the conjugate line: `ψ(−Iz) → ψ(Iz)` | `21.370699` |
| M48 | `cgmy_mgf`'s strip refusal | `<` → `≤` (the closed strip is accepted) | the refusal assertions fail; documented by row 4 (`83.051856` vs `91.586680` at `Y = 3⁄2`, `ε = 2⁻¹⁴`) |

## What the implementation must land

* **Lean, `ImprovedBS/CgmyStrip.lean`** (name fixed here), `namespace BSM`,
  imports `Mathlib` + `ImprovedBS.Pricing` + `ImprovedBS.CGMYLaw` +
  `ImprovedBS.Esscher`, all declarations in `REQUIRED` + `PROTECTED`:
  **2 defs** — `cgmyTilt`, plus `cgmyMgfTruncatedExponent` if §1's bridge
  route is chosen (otherwise 1) — and **23 theorems**: §1
  `mgf_conv`, `mgf_convPow`, `cgmyJumpLaw_exp_integrable`,
  `cgmyCpProbability_mgf`, `cgmyMgfTruncatedExponent_decomp`,
  `cgmyMgfTruncatedExponent_tendsto`, `cgmyMgfOneSided_eq` (and its
  compensated twin — merge to one two-case theorem and the count is 22),
  `cgmyMgf_uniformBound` (the ladder's `sup`, F4), `cgmyMgf_markovTail`
  (the `u′` tail, F4), `cgmyLaw_exp_integrable`, `cgmyLaw_mgf`,
  `openStrip_subset_integrableExpSet`; §2 `cgmyStrip_target_analyticOnNhd`
  (may inline), `complexMGF_cgmyLaw`, `contourCharFun_cgmyLaw`; §3
  `cgmyTilt_isProbabilityMeasure`, `cgmy_tilt_numeraire`,
  `cgmy_tilt_mgf`, `cgmy_drift_identity`; §4 `cgmy_modelFree_parity`,
  `cgmy_modelFree_call_bounds`, `cgmy_modelFree_put_bounds`,
  `cgmy_carrMadan_eq_modelFreeCall`. Pins move `333 → 358` in both layers
  (def count 1 → `357`), the audit list `286 → 309` (theorems only, the
  repo's convention); no pre-existing entry may move. If the landed count
  differs, the ledger records it the way C21 did.
* **Lint, a `[CgmyStrip]` check with five clauses** (one lint mutant each;
  lint mutants `56 → 61`, the five must-stay-green controls untouched):
  * **R1 the law's mgf is a theorem of the weak limit.** `cgmyLaw_mgf`'s
    body cites `cgmyCpProbability_mgf` and the tendsto machinery of F4
    (`cgmyCpProbability_tendsto_cgmyLaw` or `cgmyLaw_unique`'s `Tendsto`);
    it does **not** cite `withDensity`, `Measure.map`, `Classical.choose`,
    or `mgf_undef` — the cheat is a law-level mgf with no ladder behind it
    (`mgf_undef` would make the statement `0 = e^{τκ}`-shaped, but the
    clause forbids the detour regardless).
  * **R2 the strip is open.** `cgmyLaw_mgf`, `complexMGF_cgmyLaw` and
    `cgmyMgfTruncatedExponent_tendsto` carry `h₁ : -G < u` and `h₂ : u < M`
    (resp. `z.re` versions) — never `≤` (F3: the edge is a different
    theorem, and only for `Y < 1`).
  * **R3 the tilt is `Measure.tilted` over the mgf and the numéraire is
    cited.** `cgmyTilt`'s RHS cites `Measure.tilted` (no `withDensity`
    hand-roll), `cgmy_tilt_mgf`'s body cites `integral_exp_tilted`, and
    `cgmy_tilt_numeraire` cites `esscher_tilted_numeraire` — the numéraire
    is never re-proved or assumed.
  * **R4 the complex extension is the identity theorem on the landed CF.**
    `complexMGF_cgmyLaw`'s body cites `analyticAt_complexMGF` (or
    `analyticOn_complexMGF`) **and** one of `AnalyticOnNhd.eqOn_of_
    preconnected_of_frequently_eq` / `eqOn_of_preconnected_of_eventuallyEq`
    **and** `cgmyLaw_mgf` — it does not cite
    `charFun_cgmyLaw_eq_cgmyCharFactor` as a pointwise substitution at
    "imaginary arguments" (the CF's type has no imaginary arguments), and
    does not re-prove §1 inside §2.
  * **R5 pricing consumes the landed triangle.**
    `cgmy_carrMadan_eq_modelFreeCall`'s body cites
    `carrMadan_eq_modelFreeCall` **and** `contourCharFun_cgmyLaw`; it does
    not cite `gbm_*` and does not inline a Fourier inversion.
* **Oracle + tests:** primitives `cgmy_mgf_exponent`, `cgmy_mgf` (strip
  refusal, F3), `cgmy_complex_mgf` (F5); the committed
  `tests/test_bs.py::test_cgmy_strip` asserting the twelve-row route-check
  table above plus the canary refusals; mutants **M44–M48** as tabled, each
  killed by that test alone. Counts: oracle tests `26 → 27`, oracle mutants
  `44 → 49`. Rows 9–11 also consume landed primitives
  (`esscher_exponent`, `esscher_solve`, `carr_madan_by_exponent`,
  `cgmy_truncated_exponent` — the ladder path, exact per F8); row 12
  consumes `vg_mgf`/`vg_cumulant`.
* **Docs:** the issue-time half is done by this brief itself — the `docs/04`
  queue row above, marked **ISSUED** (the `README`/`docs/03` "next brief"
  wording stays accurate and is deliberately left unchanged). At landing:
  the queue row flips to **LANDED GREEN** with the CI links and its item-6
  line names BRIEF_021 as landed, `docs/03` §D1 item 3's "the brief after
  this one" and `README`'s CGMY-law note ("are the next brief") get the
  landed status, and `benchmarks/LEDGER.md` gets the row.
* **Corrections to record if measurement repeats:** **C28** —
  `_expm1_minus_z_complex`'s docstring ("converges in one pass for `|z|`
  far beyond the cutoff") is false for `|z| ≳ 25`: measured `3.396e+02`
  error on the pricing line at `|v| = 30.1` and `2.690e+20` at `|v| = 60.1`,
  independent of `n_panel` (F8).

## Done looks like (acceptance, machine-graded)

1. `lake build` green at the tag; every new constant on
   `[propext, Classical.choice, Quot.sound]`; no `sorryAx`;
   `deferred: {}` untouched.
2. Statement pins move by exactly the landed count in **both** layers with
   the 333 pre-existing entries byte-identical; `lint` green including
   `[CgmyStrip]` with its five cheats killed by name and nothing else;
   `oracle` green including `test_cgmy_strip` and M44–M48, each killed by
   that test alone.
3. `mgf id (cgmyLaw …) u = e^{τ·κ(u)}` on `−G < u < M` for `Y ≠ 1` is a
   theorem of the weak limit (R1) with the strip open (R2), and
   `complexMGF id (cgmyLaw …) z = cexp (τ ψ(−Iz))` / its `contourCharFun`
   corollary is the identity theorem on the landed CF (R4).
4. `∫ S e^x ∂(cgmyTilt θ) = S e^{(r−q)τ}` at `esscherDriftMap θ = r − q`
   (item 3, numéraire cited — R3) and the skeleton bounds hold at
   `cgmyTilt` (item 5); `cgmy_carrMadan_eq_modelFreeCall` instantiates the
   landed triangle at `cgmyLaw` (item 4's twin — R5).
5. A row in `benchmarks/LEDGER.md` when CI grades it, and the docs queue
   updated: strip/tilt/items 3+5+4 landed; item 6's `Y ↑ 2` twin is now
   unblocked and names BRIEF_021 as its prerequisite.

## Explicitly out of scope

* **Item 6's expectation-level twin at `Y ↑ 2`** (and any law-level corner
  statement at either end): §2 unblocks it — the `Y ↑ 2` comparison of
  `contourCharFun (cgmyLaw … Y …)` against `gbmCharFactor` is the brief
  after this one (BRIEF_022's candidate), not this one.
* **The `Y = 1` closed-form mgf** and any `cgmyCumulant` evaluation at
  `Y = 1` (F2: the composite exists, `Γ(−1) = 0` does not carry it); the
  same for edge-inclusive strip statements at `Y < 1` (F3: measured, not
  claimed).
* **The `_expm1_minus_z_complex` repair** (F8): recorded as C28, not taken;
  this brief's rows stay inside the measured-valid region.
* **Pricing at the tilted law** (a complex-mgf theorem for the tilt) and
  `esscher_tilt_cumulant_shift`'s general-`Y` twin: the tilt's §3 lands the
  real-mgf algebra item 3 needs; the complex tilt can follow later.
* **Any change to `ImprovedBS/CGMY.lean`, `CompoundPoisson.lean`,
  `CGMYLaw.lean`, `Esscher.lean`, `Skeleton.lean`, `Pricing.lean`,
  `VGLaw.lean` or any landed pin** — all are consumed, not re-derived, and
  no landed oracle primitive is edited (F8's fix is out of scope precisely
  because it edits one).
* **A general Lévy–Khintchine theorem**, a general weak-limit mgf theorem
  (the sandwich is proved for this ladder, not packaged), and any statement
  about laws outside the CGMY family.

## Name-check status (ledger C3)

Every name below was read at the pinned rev `5ed296525643`
(`v4.34.0`) through the GitHub API (`gh api repos/leanprover-community/
mathlib4/contents/<path>?ref=<rev> --jq .content | base64 -d`):

* `Mathlib/Probability/Moments/Basic.lean` — `mgf (X : Ω → ℝ) (μ) (t : ℝ)
  : ℝ := ∫ ω, exp (t * X ω)`, `cgf`, `mgf_undef`, `mgf_pos`,
  `integrableExpSet`.
* `Mathlib/Probability/Moments/ComplexMGF.lean` — `complexMGF (X : Ω → ℝ)
  (μ) (z : ℂ) : ℂ := ∫ ω, cexp (z * X ω)`; `complexMGF_ofReal`,
  `complexMGF_id_mul_I : complexMGF id μ (t * I) = charFun μ t`,
  `norm_complexMGF_le_mgf`, `hasDerivAt_complexMGF`,
  `differentiableOn_complexMGF`, `analyticOnNhd_complexMGF`,
  `analyticOn_complexMGF`, `analyticAt_complexMGF` (hypothesis
  `z.re ∈ interior (integrableExpSet X μ)`), `eqOn_complexMGF_of_mgf'` /
  `eqOn_complexMGF_of_mgf` (F5: the pattern; not directly usable),
  `convex_integrableExpSet`, `Measure.ext_of_complexMGF_eq`.
* `Mathlib/MeasureTheory/Measure/FiniteMeasure.lean` +
  `…/ProbabilityMeasure.lean` — `tendsto_iff_forall_integral_tendsto`
  (binds `∀ f : Ω →ᵇ ℝ`, both classes), `tendsto_iff_forall_lintegral_tendsto`
  (`Ω →ᵇ ℝ≥0`), `tendsto_iff_forall_integral_rclike_tendsto` (`Ω →ᵇ 𝕜`),
  `tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds`.
* `Mathlib/MeasureTheory/Measure/Portmanteau.lean` — fallback set forms
  (F4): `FiniteMeasure.limsup_measure_closed_le_of_tendsto`,
  `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`,
  `ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, plus the
  integral forms `integral_le_liminf_integral_of_forall_isOpen_measure_
  le_liminf_measure` (`Ω →ᵇ ℝ`, `0 ≤ f`).
* `Mathlib/MeasureTheory/Measure/Tilted.lean` — `Measure.tilted`,
  `tilted_apply`, `isProbabilityMeasure_tilted`,
  `integral_exp_tilted`, `tilted_tilted`, `integrable_tilted_iff` (the
  last two consumed via their green use in `VGLaw.lean`).
* `Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean` —
  `charFun_conv` (its body is `integral_conv` + `Complex.exp_add`: the
  `mgf_conv` mirror), `charFun_apply_real`.
* `Mathlib/Analysis/Normed/Algebra/Exponential.lean` —
  `NormedSpace.expSeries_div_hasSum_exp (x : 𝔸)` over a general normed
  `𝕂`-algebra (the landed uses are at `ℂ`; the `ℝ` instantiation for
  `mgf_cpLaw` is the one name to confirm at implementation — the fallback
  is the `complexMGF` route + `complexMGF_ofReal`, which needs no new name).
* `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` —
  `integral_cpow_mul_exp_neg_mul_Ioi` / `integral_rpow_mul_exp_neg_mul_Ioi`
  (the shipped **real-rate** Γ integrals §1's identification is anchored
  on), `Real.Gamma` at nonpositive integers (`Γ(−1) = 0`, F2's trap).
* In-tree, green at the tag (no API risk, cited as precedent):
  `differentiableAt_id.cpow` (`CGMYLaw.lean:1040`),
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` (BRIEF_020 R4,
  mathlib's own `eqOn_complexMGF_of_mgf'`),
  `tendsto_setIntegral_of_monotone`, `continuousAt_of_dominated`,
  `integral_Ioi_mul_deriv_eq_deriv_mul`, `integral_comp_neg_Ioi`,
  `cgmyDrift_identity`, `cgmy_charFactor_contour_continuous`,
  `cgmy_contour_decay`, `esscher_tilted_numeraire`,
  `carrMadan_eq_modelFreeCall`, `gbm_carrMadan_eq_bsCall`,
  `model_free_call_bounds` and friends, `isProbabilityMeasure_tilted`,
  `integral_exp_tilted`, `integrable_tilted_iff`.

Not located and named as risks rather than assumed: a packaged
"convergent sequence is bounded" lemma for F4's uniform sup (the step is
elementary — `tendsto_norm` + `Iio_mem_nhds` + a finite head — and no name
is assumed); a `mgf_conv`/`complexMGF_convPow` (searched: absent at the
tag — §1 proves them by the `charFun_conv` mirror); and the exact `ℝ`
instantiation of `expSeries_div_hasSum_exp` (above).
