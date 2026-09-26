# BRIEF_020 — the CGMY law: the `ε ↓ 0` limit, tightness, Lévy continuity and the identification `charFun μ_τ v = cexp (τ ψ_Y(v))` (BRIEF_017's Stage 2, second half), with G1 as its analytic engine

- **Status:** **ISSUED** — documentation plus a numeric route-check run at
  issue, no committed test. It changes no `.lean` file, no pin, no lint rule,
  no workflow; `deferred: {}` is untouched.
- **What this is.** The brief that turns BRIEF_019's truncated family into
  *the* law. Three things, in the order they are provable: **(§1)** the
  `ε ↓ 0` limit of the landed `cgmyTruncatedExponent`, along the ladder
  `εₙ = 2⁻ⁿ`, to a **Lévy–Khintchine exponent** `L(v)` written as two
  *absolutely* convergent integrals — the conditional convergence BRIEF_019 F3
  named, made unconditional by a decomposition the route-check measures to
  `≤ 7.3e−15`; **(§2)** the law itself: tightness of the compound-Poisson
  marginals (`isTightMeasureSet_of_tendsto_charFun`), a limit law by
  Prokhorov + subsequence + CF uniqueness (mathlib has no Bochner theorem, so
  the limit is *constructed*, not cited), `cgmyLaw` as that limit, its CF
  `cexp (τ L(v))`, and its weak convergence from the truncated family
  (`ProbabilityMeasure.tendsto_of_tendsto_charFun`); **(§3)** the
  identification `L(v) = cgmyExponent C G M Y v` for `Y ≠ 1`, which is where
  **G1** — the complex-rate Γ integral — enters, and only there. §1–§2 need
  no G1 and hold on **all** of `0 < Y < 2`, including `Y = 1` (F2); §3 is
  severable (F6). Name fixed here: `ImprovedBS/CGMYLaw.lean`.
- **Prerequisites:** BRIEF_019 (`cgmyTruncatedExponent`, `cgmyJumpLaw`,
  `cpLaw`, `charFun_cgmyCpLaw` — every object this brief takes a limit of),
  BRIEF_011 (`cgmyExponent`, `cgmyLevyDensity`, `cgmy_levy_far_moment`),
  BRIEF_018 (the `Y = 0` member the `Y ↓ 0` end is cross-checked against, F7),
  BRIEF_017 (the F5 route this brief closes), and mathlib at the pinned rev
  `5ed2965` (`v4.34.0`) — read at the tag, see the name-check section. All
  landed; CI-only for the Lean half.
- **Budget:** one Lean module plus one oracle test. The skills, named:
  `tendsto_setIntegral_of_monotone` on two monotone families of sets (the
  limit); the reflection `integral_comp_neg_Ioi` and `integral_sub` (the
  pairing); `continuousAt_of_dominated` (the limit exponent is continuous at
  `0`); `isTightMeasureSet_of_tendsto_charFun`,
  `isCompact_closure_of_isTightMeasureSet`, `IsCompact.tendsto_subseq`,
  `ProbabilityMeasure.tendsto_iff_tendsto_charFun`, `tendsto_nhds_unique`,
  `Filter.limUnder` / `tendsto_nhds_limUnder` and `Measure.ext_of_charFun`
  (the law); `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
  `DifferentiableOn.analyticOnNhd`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` against the shipped
  real-rate `integral_cpow_mul_exp_neg_mul_Ioi` (G1); and
  `integral_Ioi_mul_deriv_eq_deriv_mul` twice (the identification). Nothing
  here estimates a date: the repo's only clock is the CI run.

## Findings recorded at issue

**F1. The conditional convergence is two absolute convergences in disguise,
and the decomposition is an identity at every `ε > 0` — no limit is taken to
state it.** For `0 < ε ≤ 1` and real `v`, split the truncated exponent on the
unit ball:

    A_ε(v) = ∫_{|x|≥ε} (e^{ivx} − 1) ν(dx)
           = ∫_{|x|≥ε} (e^{ivx} − 1 − ivx·1_{|x|≤1}) ν(dx)   +   iv · d_ε ,
             ────────────── B_ε(v) ──────────────
    d_ε    = ∫_{ε≤|x|≤1} x ν(dx)  =  C ∫_ε^1 x^{−Y} (e^{−Mx} − e^{−Gx}) dx .

Both `∫_{ε≤x≤1} x ν` and `∫_{−1≤x≤−ε} x ν` are finite for `ε > 0`, so the
pairing is a plain `integral_sub` after `integral_comp_neg_Ioi` folds the
negative side onto `(ε, 1]`; nothing conditional happens at fixed `ε`.
Measured at `(C, G, M) = (0.5, 5, 10)`, `Y ∈ {½, 1, 3⁄2}`, `v ∈ {0.5, 2}`,
`ε ∈ {10⁻¹, 10⁻², 10⁻³}`: `|A_ε − (B_ε + iv d_ε)| ≤ 7.3e−15` (worst at
`Y = 3⁄2`, `ε = 10⁻³`, `v = 2`, where `|A_ε| ≈ 3.2`). What the split buys is
that **each piece now has an integrable dominator on all of `ℝ ∖ {0}`**:
`|e^{ivx} − 1 − ivx 1_{|x|≤1}| ≤ (v²x²/2) 1_{|x|≤1} + 2·1_{|x|>1}`, and
`x² · C|x|^{−1−Y} = C|x|^{1−Y}` is integrable at `0` for every `Y < 2`; the
paired drift integrand is `≤ C|M − G| x^{1−Y}` near `0` because
`|e^{−Mx} − e^{−Gx}| ≤ |M − G| x`. The far field is the landed
`cgmy_levy_far_moment` on both tails. So `B_ε → B_0` and `d_ε → d_0` are two
instances of `tendsto_setIntegral_of_monotone` (the sets `{2⁻ⁿ ≤ |x|}` and
`Ioc 2⁻ⁿ 1` increase to `{0}ᶜ` and `Ioc 0 1`), both at rate `ε^{2−Y}`:
measured slopes **1.4996** (`Y = ½`), **0.9997** (`Y = 1`), **0.4998**
(`Y = 3⁄2`) for *both* pieces — the rate BRIEF_019 measured for `A_ε` itself
(1.4904 / 0.4947), now attributed piece by piece. The limit is

    L(v) := B_0(v) + iv · d_0 ,   d_0 = C ∫_0^1 x^{−Y}(e^{−Mx} − e^{−Gx}) dx ,

the Lévy–Khintchine form with the unit-ball compensator and the drift `d_0`.
**The drift is not zero and it is load-bearing**: `d_0 = −0.11546` (`Y = ½`),
`−0.34600` (`Y = 1`), `−1.64113` (`Y = 3⁄2`). BRIEF_019 F3 / ledger C22 said
the two sides' `ivx` pieces "cancel"; they do not — they *pair* into this
finite drift, and dropping it is mutant M2 below with a separation of
`1.6411` at `Y = 3⁄2`. Recorded as correction **C25**.

**F2. `Y = 1` is a pole of the *formula*, not of the *law*.** `L(v)` is
defined and finite for every `0 < Y < 2` — nothing in F1 divides by
`Γ(−Y)` or `1 − Y`. At `Y = 1` the route-check gives
`L(0.5) = −0.018727 − 0.172975 i`, `L(2) = −0.294325 − 0.674259 i`, and the
landed closed form approaches it from both sides:
`|ψ_{1±δ}(v) − L_1(v)| = 4.42e−4 / 4.40e−4` at `δ = 10⁻³`, `v = 0.5`
(`1.88e−3 / 1.88e−3` at `v = 2`), i.e. `O(δ)`. So §1–§2 — the limit, the
tightness, the law and its CF `cexp (τ L(v))` — are stated on `0 < Y < 2`
**without** `Y ≠ 1`, and only the identification §3 carries the `Y ≠ 1`
hypothesis the landed `cgmyExponent` needs. The tree gains a law at `Y = 1`
whose CF is an honest integral, which is more than the closed form can say.

**F3. Existence of the limit law is a construction, not a citation.** mathlib
at the tag has `ProbabilityMeasure.tendsto_of_tendsto_charFun` — but its
statement *takes* the limit `μ₀`; it does not produce one (there is no Bochner
theorem at the tag). The route that exists: `isTightMeasureSet_of_tendsto_charFun`
needs the pointwise CF limit `f(t) = cexp (τ L(t))` and `ContinuousAt f 0`
(from `continuousAt_of_dominated` on `L`, dominator `(x² ∧ 2)·ν` uniform for
`|t| ≤ 1`); Prokhorov (`isCompact_closure_of_isTightMeasureSet`) makes the
closure of the range compact in `ProbabilityMeasure ℝ`;
`IsCompact.tendsto_subseq` extracts a convergent subsequence with limit `μ₀`;
`ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp` along that subsequence
plus `tendsto_nhds_unique` identifies `charFun μ₀ = f`; then
`tendsto_of_tendsto_charFun` gives the **whole** sequence `→ μ₀`, and
`Measure.ext_of_charFun` makes `μ₀` the unique law with that CF. The module
therefore *defines* `cgmyLaw` as `Filter.limUnder atTop (fun n ↦ μₙ)` in
`ProbabilityMeasure ℝ` (T2, so `tendsto_nhds_limUnder` is the only lemma
needed to use it), and its CF is a theorem, not a definition. The tightness
mechanism is measurable: mathlib's own proof bounds
`sup_n μₙ(|X| > R) ≤ (R/2) ∫_{−2/R}^{2/R} (1 − Re φₙ(t)) dt`; along
`εₙ = 2⁻ⁿ`, `n ∈ {1, 3, 6, 9, 12}`, that bound is monotone in `n` and
converges to its value at the limit — `0.00471` (`Y = ½`, `R = 2`),
`0.00076` (`R = 5`); `0.10771` (`Y = 3⁄2`, `R = 2`), `0.01788` (`R = 5`) —
uniform in `n` and decreasing in `R`, which is what tightness says.

**F4. G1 is one identity-theorem argument, and mathlib ships every rung of
it.** The complex-rate Γ integral

    ∫ x in Ioi 0, (x:ℂ)^(s−1) · cexp (−z x) = Γ(s) · z^(−s)     (0 < s, 0 < Re z)

is *not* at the tag (`integral_cpow_mul_exp_neg_mul_Ioi` has a **real** rate
`r`), but the route needs no contour: the left side is differentiable in `z`
on the open right half-plane by `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(derivative `−∫ x^s e^{−zx}`, dominated on `Re z ≥ δ` by `x^s e^{−δx}`), hence
`AnalyticOnNhd` there by `DifferentiableOn.analyticOnNhd`; the right side is
analytic away from the branch cut; the half-plane is convex
(`convex_halfSpace_re_gt`) hence preconnected; and the two agree on the
positive reals — which accumulate at `z = 1` — by the shipped real-rate lemma,
so `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` closes it. Measured
by quadrature at `z = M − iv`: `|∫ − Γ(s) z^{−s}| ≤ 2.9e−11` for
`s ∈ {½, 3⁄2}`, `v ∈ {0.5, 2}` (the real-rate anchor at `z = M` has the same
`2.96e−11`, i.e. the residual is the quadrature's, not the identity's).

**F5. The identification is G1 plus integration by parts — once for `Y < 1`,
twice for `Y > 1` — and a real-rate drift identity that needs no G1 at all.**
Write `z = M − iv` for the `M` leg (`G + iv` for the mirror). For `0 < Y < 1`,
one `integral_Ioi_mul_deriv_eq_deriv_mul` with `u = x^{−Y}/(−Y)` and
`v' = e^{−zx} − e^{−Mx}` turns `∫_0^∞ (e^{−zx} − e^{−Mx}) x^{−1−Y} dx` into
`(−1/Y)[z Γ(1−Y) z^{Y−1} − M Γ(1−Y) M^{Y−1}] = Γ(−Y)(z^Y − M^Y)` (two G1
instances at `s = 1 − Y` and `Real.Gamma_add_one`) — the landed
`cgmy_exponent_one_sided` closed form, reproduced to `2.7e−15`. For
`1 < Y < 2`, two parts with `f(x) = e^{−zx} − e^{−Mx} − ivx e^{−Mx}` (note
`f(0) = f'(0) = 0`, which is what kills both boundary terms) reduce to
`∫ f''(x) x^{1−Y} dx / (Y(Y−1))`, three G1 instances at `s = 2 − Y` and
`s = 3 − Y`, and land on `Γ(−Y)[z^Y − M^Y + ivY M^{Y−1}]` — the landed
`cgmy_exponent_one_sided_compensated`, reproduced to `3.0e−14`. That is the
*fully* compensated exponent; the tree's `cgmyExponent` differs from it by
`iv m^∞` (BRIEF_019 F6), and F1's `L` differs from it by `iv (d_0 + d_far)`
with `d_far = ∫_{|x|>1} x ν(dx)`. So the identification `L = ψ_Y` for `Y > 1`
is exactly the **drift identity**

    C ∫_0^∞ x^{−Y} (e^{−Mx} − e^{−Gx}) dx  =  C Γ(1−Y) (M^{Y−1} − G^{Y−1})  =  m^∞ ,

a *real*-rate, Frullani-type statement (one integration by parts and the
shipped `integral_rpow_mul_exp_neg_mul_Ioi` at `s = 2 − Y`, then
`Real.Gamma_add_one`), measured to `3.0e−10` at `Y = 3⁄2` and `1.5e−10` at
`Y = ½` (where each leg converges on its own and the identity is the
difference of two `Γ(1−Y)` integrals). Assembled: `|L − ψ_Y| ≤ 6.2e−10` at
`Y ∈ {½, 3⁄2}`, `v ∈ {0.5, 2}` — the quadrature floor.

**F6. §3 is severable, and the brief says how.** Nothing in §1–§2 cites G1,
`cgmyExponent`, or `Y ≠ 1`; §3 cites all three. If the implementation lands
§1–§2 green and §3 stalls, the ledger row records `cgmyLaw` with CF
`cexp (τ L(v))` as landed and §3 moves to the next number *unchanged* — its
statement is fixed here (`cgmyLKExponent_eq_cgmyExponent`, below), and
BRIEF_019's F5 corner row and BRIEF_018's `vgLaw` remain the numeric
cross-checks. The route-check already separates the two: F1–F3's rows never
call `cgmy_exponent`; F4–F5's rows never call `cgmy_truncated_exponent`.

**F7. The `Y ↓ 0` end reproduces BRIEF_019 F5 at the limit exponent.**
`|L(v; Y) − ψ₀(v)| / Y` against the oracle's `cgmy_zeroth_exponent` (the VG
corner of the landed `vgLaw`) settles to **0.037518** at `v = 0.5` and
**0.158082** at `v = 2` by `Y = 10⁻³` — BRIEF_019 measured `0.037511` /
`0.158055` at `A_{10⁻⁴}`; the difference is the truncation error
`O(ε^{2−Y})` that `L` no longer carries. Two independently built objects (a
limit of compound-Poisson exponents and a difference-of-Gammas cumulant) agree
to the corner rate. No law-level corner statement at `Y ↓ 0` is claimed (it
would need `Y` as a parameter of a *sequence of laws*; item 6's twin at
`Y ↑ 2` stays gated as BRIEF_019 F4 recorded).

**F8. The CF-level convergence is Lipschitz in the exponent, so no second
estimate is needed.** Both `A_ε` and `L` have real part `≤ 0` (measured
`max Re A_ε ≤ −8.7e−4` along the ladder), and on the closed left half-plane
`|e^a − e^b| ≤ |a − b|`; measured `|e^{τA_ε} − e^{τL}| / (τ|A_ε − L|) ≤ 0.9990`
over `n = 1..14`. The implementation does not need the bound — `Tendsto.cexp`
(continuity of `Complex.exp`) turns §1's limit into the CF limit directly —
but the row pins that the CF convergence is no slower than the exponent's
(`|A_{2⁻¹⁴} − L| = 4.0e−7` at `Y = ½`, `1.96e−2` at `Y = 3⁄2`: the `Y ↑ 2`
degeneration of BRIEF_019 F4, in numbers).

## The mathematics to land

Throughout `0 < C`, `0 < G`, `0 < M`, and `0 < Y < 2`; `Y ≠ 1` **only** in §3.
`εₙ := (2⁻¹ : ℝ≥0) ^ n`, the index type `ℕ` that mathlib's Lévy lemmas are
stated for.

### §1 The decomposition and the limit exponent

    cgmyCompensatedIntegrand (v x : ℝ) : ℂ :=
        cexp (v * x * I) - 1 - Set.indicator (Icc (-1) 1) (fun x ↦ v * x * I) x
    cgmyDriftIntegrand (C G M Y : ℝ) (x : ℝ) : ℝ :=
        C * x ^ (-Y) * (rexp (-M * x) - rexp (-G * x))
    cgmyLKExponent (C G M Y : ℝ) (v : ℝ) : ℂ :=
        (∫ x, cgmyCompensatedIntegrand v x * (cgmyLevyDensity C G M Y x : ℂ))
        + v * I * (∫ x in Ioc 0 1, cgmyDriftIntegrand C G M Y x : ℝ)

* `cgmyCompensatedIntegrand_integrable`: `Integrable (fun x ↦ … * ν x)`
  w.r.t. `volume` — dominator `(v²x²/2) 1_{|x|≤1} + 2·1_{|x|>1}` times the
  density, near zero `C|x|^{1−Y}` (`integrableOn_Ioo_rpow_iff`, `1 − Y > −1`),
  far field the landed `cgmy_levy_far_moment` at `u = 0` on both tails (the
  `G` tail after `integral_comp_neg_Ioi`).
* `cgmyDriftIntegrand_integrableOn`: `IntegrableOn … (Ioc 0 1)` — dominator
  `C|M − G| x^{1−Y}` from `|e^{−Mx} − e^{−Gx}| ≤ |M − G| x` on `x ≥ 0`.
* `cgmyTruncatedExponent_decomp` (F1's identity, for `0 < ε ≤ 1`, real `v`):
  `cgmyTruncatedExponent C G M Y ε v = (∫ x in {ε ≤ |x|}, compensated·ν) + v I ∫ x in Ioc ε 1, drift`.
  The `ivx 1_{|x|≤1}` piece is integrable on `{ε ≤ |x|}` for `ε > 0`, so this
  is `integral_add`/`integral_sub` plus the reflection — no limit.
* `cgmyTruncatedExponent_tendsto`:
  `Tendsto (fun n ↦ cgmyTruncatedExponent C G M Y (εₙ) v) atTop (𝓝 (cgmyLKExponent C G M Y v))`
  — two `tendsto_setIntegral_of_monotone`s (`{εₙ ≤ |x|} ↑ {0}ᶜ`, whose
  integral is the full integral because `volume {0} = 0`; `Ioc εₙ 1 ↑ Ioc 0 1`)
  through the decomposition.
* `cgmyLKExponent_zero`: `cgmyLKExponent C G M Y 0 = 0`.
* `cgmyLKExponent_continuous`: `Continuous (cgmyLKExponent C G M Y)` —
  `continuous_of_dominated` will not do (its bound must be uniform in `v`);
  use `continuousAt_of_dominated` at each `v₀` with the dominator for
  `|v| ≤ |v₀| + 1`. Only `ContinuousAt … 0` is consumed, by §2.

### §2 The law

    cgmyCpProbability (C G M Y : ℝ) (τ : ℝ≥0) (ε : ℝ≥0) (h…) : ProbabilityMeasure ℝ :=
        ⟨cpLaw (τ * (cgmyJumpMeasure C G M Y ε univ).toNNReal) (cgmyJumpLaw C G M Y ε),
         cpLaw_isProbabilityMeasure _ _ (cgmyJumpLaw_isProbabilityMeasure …)⟩
    cgmyLaw (C G M Y : ℝ) (τ : ℝ≥0) (h…) : ProbabilityMeasure ℝ :=
        Filter.limUnder atTop (fun n ↦ cgmyCpProbability C G M Y τ (εₙ) h…)

* `charFun_cgmyCpProbability_tendsto`: for every real `t`,
  `Tendsto (fun n ↦ charFun (cgmyCpProbability … (εₙ)) t) atTop (𝓝 (cexp (τ * cgmyLKExponent C G M Y t)))`
  — `charFun_cgmyCpLaw` rewrites each term, then §1's limit under
  `Tendsto.cexp` (F8: no estimate needed).
* `cgmyCpProbability_isTight`: `IsTightMeasureSet (Set.range (fun n ↦ (cgmyCpProbability … (εₙ) : Measure ℝ)))`
  — `isTightMeasureSet_of_tendsto_charFun` with `ContinuousAt` from
  `cgmyLKExponent_continuous` and `Complex.continuous_exp`.
* `cgmyLaw_exists` (F3's construction, the theorem that makes `limUnder`
  honest): `∃ μ₀ : ProbabilityMeasure ℝ, Tendsto (fun n ↦ cgmyCpProbability … (εₙ)) atTop (𝓝 μ₀)`
  — Prokhorov, `IsCompact.tendsto_subseq`, the CF along the subsequence via
  `ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp` and `tendsto_nhds_unique`,
  then `ProbabilityMeasure.tendsto_of_tendsto_charFun` for the full sequence.
* `cgmyCpProbability_tendsto_cgmyLaw`: `Tendsto (fun n ↦ cgmyCpProbability … (εₙ)) atTop (𝓝 (cgmyLaw …))`
  — `tendsto_nhds_limUnder cgmyLaw_exists`.
* **the headline of §2:** `charFun_cgmyLaw`:
  `charFun (cgmyLaw C G M Y τ h… : Measure ℝ) t = cexp (τ * cgmyLKExponent C G M Y t)`
  — `ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp` on the previous line
  and `tendsto_nhds_unique` against `charFun_cgmyCpProbability_tendsto`.
* `cgmyLaw_unique`: any `μ : Measure ℝ` with `IsProbabilityMeasure μ` and
  `∀ t, charFun μ t = cexp (τ * cgmyLKExponent C G M Y t)` equals `cgmyLaw` —
  `Measure.ext_of_charFun`. This is what lets a *later* brief replace the
  `limUnder` by any other construction without touching the CF layer.

### §3 G1 and the identification (`Y ≠ 1` from here on)

    gammaIntegralComplexRate (s : ℝ) (z : ℂ) : ℂ :=
        ∫ x in Ioi 0, (x : ℂ) ^ ((s : ℂ) - 1) * cexp (-(z * x))

* **G1**, `integral_cpow_mul_cexp_neg_mul_Ioi`: for `0 < s` and `0 < z.re`,
  `gammaIntegralComplexRate s z = (Real.Gamma s : ℂ) * z ^ (-(s : ℂ))` — F4's
  identity-theorem route: `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  (on the ball `Re z > δ`, dominator `x^s e^{−δx}`, integrable by the real
  lemma at `s + 1`), `DifferentiableOn.analyticOnNhd` on
  `{z | 0 < z.re}` (open: `isOpen_lt continuous_const Complex.continuous_re`;
  preconnected: `(convex_halfSpace_re_gt 0).isPreconnected`), the right side
  analytic there (`z ↦ z ^ (−s)` is `DifferentiableOn` off the slit, which the
  half-plane avoids), agreement on `Ioi 0 ⊂ ℝ` by
  `integral_cpow_mul_exp_neg_mul_Ioi` (with `(1/r)^s = r^{−s}`), `frequently`
  at `z = 1` from `Ioi 0` accumulating there, and
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. The only lemma in the
  module whose proof touches complex analysis, and the one G1 the queue named.
* `cgmyDrift_identity` (F5, real rate, all `0 < Y < 2`, `Y ≠ 1`):
  `C * ∫ x in Ioi 0, x ^ (-Y) * (rexp (-M * x) - rexp (-G * x)) = C * Real.Gamma (1 - Y) * (M ^ (Y - 1) - G ^ (Y - 1))`
  — `integral_Ioi_mul_deriv_eq_deriv_mul` with `u = x^{1−Y}/(1−Y)`, both
  boundary terms `0` (`x^{1−Y}·O(x) → 0` at `0`, exponential decay at `∞`),
  then the shipped `integral_rpow_mul_exp_neg_mul_Ioi` at `s = 2 − Y` twice
  and `Real.Gamma_add_one` (`Γ(2−Y) = (1−Y)Γ(1−Y)`). The `Y < 1` case is
  the same lemma; it may alternatively split into two convergent legs.
* `cgmyOneSidedExponent_eq` (F5, `0 < Y < 1`) and
  `cgmyOneSidedCompensated_eq` (F5, `1 < Y < 2`): the two one-sided closed
  forms, from G1 by one and two `integral_Ioi_mul_deriv_eq_deriv_mul`s. Their
  *statements* are the integrals BRIEF_011's oracle already pins
  (`cgmy_exponent_one_sided`, `cgmy_exponent_one_sided_compensated`,
  `test_cgmy_contour`); this is the first time they are theorems.
* **the headline of §3:** `cgmyLKExponent_eq_cgmyExponent`:
  `cgmyLKExponent C G M Y v = cgmyExponent C G M Y (v : ℂ)` for `Y ≠ 1` —
  `B_0` split into its two legs, the legs into the one-sided closed forms
  (`Y < 1`: uncompensated, with the unit-ball `ivx` moved to the drift;
  `Y > 1`: fully compensated, with `∫_{|x|>1} x ν` moved to the drift), and
  the drift closed by `cgmyDrift_identity`.
* **the identification:** `charFun_cgmyLaw_eq_cgmyCharFactor`:
  `charFun (cgmyLaw C G M Y τ h… : Measure ℝ) v = cgmyCharFactor C G M Y τ v`
  for `Y ≠ 1` — `charFun_cgmyLaw` and the line above; the tree's pricing
  factor is, from here on, the CF of a law in the tree.

## The numeric route-check (run at issue, per ledger C4)

Scratch script, Python 3 stdlib only, through the router's own oracle
(`cgmy_truncated_exponent`, `cgmy_exponent`, `cgmy_exponent_one_sided`,
`cgmy_exponent_one_sided_compensated`, `cgmy_gamma_neg`,
`cgmy_zeroth_exponent`, `cgmy_jump_mass`, `_simpson`, `_expm1_complex`,
`_expm1_minus_z_complex`). Witness: `(C, G, M) = (0.5, 5, 10)`, `τ = 0.25`.
Quadrature: dyadic panels from `ε` (or `2⁻⁶⁰` for the limits, with the
analytic `O(inner^{2−Y})` tail added) to `1`, Simpson on `[1, 60]`; the
compensated integrand goes through `_expm1_minus_z_complex` so the innermost
panels keep their `x²` behaviour. Run time 11 s.

| check | lands as | result |
|---|---|---|
| **decomposition** `A_ε = B_ε + iv d_ε`, `Y ∈ {½, 1, 3⁄2}`, `v ∈ {0.5, 2}`, `ε ∈ {10⁻¹, 10⁻², 10⁻³}` | `cgmyTruncatedExponent_decomp` | worst `7.3e−15` (18 rows), an identity at every `ε` |
| `B_ε → B_0`, `d_ε → d_0` along `εₙ = 2⁻ⁿ`, `n = 2..14` | `cgmyTruncatedExponent_tendsto` | slopes `1.4996 / 0.9997 / 0.4998` at `Y = ½ / 1 / 3⁄2`, both pieces (predicted `2 − Y`); `d_0 = −0.115465 / −0.346002 / −1.641132` |
| `L = B_0 + iv d_0` against the landed `cgmyExponent` | `cgmyLKExponent_eq_cgmyExponent` | `7.5e−11`, `3.1e−10` (`Y = ½`); `1.5e−10`, `6.2e−10` (`Y = 3⁄2`) |
| **`Y = 1`**: `L_1` finite, `ψ_{1±δ} → L_1` | F2 (the law's range is `0 < Y < 2`) | `L_1(0.5) = −0.018727 − 0.172975 i`; `|ψ_{1±δ} − L_1| = 4.42e−4 / 4.40e−4` at `δ = 10⁻³` (`O(δ)`) |
| **G1** `∫ x^{s−1} e^{−zx} = Γ(s) z^{−s}`, `z = M − iv`, `s ∈ {½, 3⁄2}` | `integral_cpow_mul_cexp_neg_mul_Ioi` | `≤ 2.9e−11`; the real-rate anchor at `z = M` gives `2.96e−11` (quadrature floor) |
| the IBP chains from G1 | `cgmyOneSidedExponent_eq`, `cgmyOneSidedCompensated_eq` | `2.7e−15` against `cgmy_exponent_one_sided` (`Y = ½`); `3.0e−14` against `cgmy_exponent_one_sided_compensated` (`Y = 3⁄2`) |
| **drift identity** `C∫_0^∞ x^{−Y}(e^{−Mx} − e^{−Gx}) = m^∞` | `cgmyDrift_identity` | `1.5e−10` (`Y = ½`, `m^∞ = −0.116083169`), `3.0e−10` (`Y = 3⁄2`, `m^∞ = −1.641663919`); and `L − (fully compensated) − iv m^∞ ≤ 6.2e−10` |
| CF ladder: `|e^{τA_ε} − e^{τL}| ≤ τ|A_ε − L|`, `Re A_ε ≤ 0`, `n = 1..14` | `charFun_cgmyCpProbability_tendsto` | ratio `≤ 0.9990`; `max Re A_ε = −8.7e−4`; `|A_{2⁻¹⁴} − L| = 4.0e−7` (`Y = ½`), `1.96e−2` (`Y = 3⁄2`) |
| tightness proxy `(R/2)∫_{−2/R}^{2/R}(1 − Re φₙ)` over `n ∈ {1,3,6,9,12}` | `cgmyCpProbability_isTight` | monotone in `n`, `→` the limit's value: `0.00471` / `0.00076` (`Y = ½`, `R = 2 / 5`), `0.10771` / `0.01788` (`Y = 3⁄2`) |
| the `Y ↓ 0` end vs BRIEF_018's `vgLaw` (`cgmy_zeroth_exponent`) | F7 | `|L − ψ₀|/Y → 0.037518` (`v = 0.5`), `0.158082` (`v = 2`) at `Y = 10⁻³` |
| **mutants** at `(Y, v) = (3⁄2, 1)`, reference `|L − ψ| = 3.1e−10` | M39–M43 | unpaired drift leg **diverges** (slope `−0.5267`, `d^M_{2⁻¹⁴} = 122.5`); drift dropped `1.641132`; fully compensated without `m^∞` `1.641664`; drift sign flipped `3.282264`; `Γ(1−Y) → Γ(−Y)` in `m^∞` `2.736107`; ball radius `2` in `B` vs `1` in `d` `5.30e−4` |

Two rows deserve their own line. The **decomposition row** is the whole
argument: it is exact at every `ε`, and the two things it separates are each
dominated — that is what replaces the DCT BRIEF_017 F5(iv) asked for and C22
withdrew. The **unpaired-drift mutant** is the one that matters for the
implementer: the `M` leg of the drift alone, `C∫_ε^1 x^{−Y} e^{−Mx} dx`, is
`122.5` at `ε = 2⁻¹⁴` and growing like `ε^{1−Y}`; only the *paired* integrand
`x^{−Y}(e^{−Mx} − e^{−Gx})` is integrable at `0` for `Y ≥ 1`. The
`[CGMYLAW]` R2 clause below holds it.

## What the implementation must land

* **Lean, `ImprovedBS/CGMYLaw.lean`** (name fixed here), in `namespace BSM`,
  all declarations in `REQUIRED` + `PROTECTED`: **6 defs** —
  `cgmyCompensatedIntegrand`, `cgmyDriftIntegrand`, `cgmyLKExponent`,
  `cgmyCpProbability`, `cgmyLaw`, `gammaIntegralComplexRate` — and
  **18 theorems**: §1 `cgmyCompensatedIntegrand_integrable`,
  `cgmyDriftIntegrand_integrableOn`, `cgmyTruncatedExponent_decomp`,
  `cgmyTruncatedExponent_tendsto`, `cgmyLKExponent_zero`,
  `cgmyLKExponent_continuous`; §2 `charFun_cgmyCpProbability_tendsto`,
  `cgmyCpProbability_isTight`, `cgmyLaw_exists`,
  `cgmyCpProbability_tendsto_cgmyLaw`, `charFun_cgmyLaw`, `cgmyLaw_unique`;
  §3 `integral_cpow_mul_cexp_neg_mul_Ioi`, `cgmyDrift_identity`,
  `cgmyOneSidedExponent_eq`, `cgmyOneSidedCompensated_eq`,
  `cgmyLKExponent_eq_cgmyExponent`, `charFun_cgmyLaw_eq_cgmyCharFactor`
  (`cgmyOneSidedExponent_eq`/`cgmyOneSidedCompensated_eq` may merge into one
  two-case theorem, in which case 17). Pins move `309 → 333` in both layers
  (`332` if merged), the audit list `268 → 286` (`285`; theorems only, the
  repo's convention); no pre-existing entry may move. If the landed count
  differs, the ledger records it the way C21 did. If §3 is severed (F6), the
  module lands with §1–§2's 5 defs + 12 theorems (pins `309 → 326`, audit
  `268 → 280`) and the row says so.
* **Lint, a `[CGMYLaw]` check with four clauses** (one lint mutant each; lint
  mutants `52 → 56`, the five must-stay-green controls untouched):
  * **R1 the law is the limit, not a density.** `cgmyLaw`'s RHS cites
    `Filter.limUnder` and `cgmyCpProbability`; it does **not** cite
    `withDensity`, `Measure.map`, or `Classical.choose` — the cheat is a law
    written down by hand (there is no closed-form density to write, which is
    the point) or a bare choice with no `Tendsto` behind it.
  * **R2 the drift is paired.** `cgmyDriftIntegrand`'s body contains both
    `rexp (-M * x)` and `rexp (-G * x)` inside one integrand (the difference),
    and no declaration in the module integrates `x ^ (-Y) * rexp (-M * x)` or
    `x ^ (-Y) * rexp (-G * x)` alone over a set containing a neighbourhood of
    `0` (`Ioc 0 _`, `Ioo 0 _`) — the measured divergent mutant.
  * **R3 the CF is a theorem of the limit.** `charFun_cgmyLaw`'s body cites
    `ProbabilityMeasure.tendsto_iff_tendsto_charFun` (or
    `tendsto_of_tendsto_charFun`) **and** `tendsto_nhds_unique`; it does
    **not** cite `cgmyExponent` — the CF at the law is `cexp (τ L)` first, and
    becomes `cexp (τ ψ_Y)` only through `cgmyLKExponent_eq_cgmyExponent`
    (which is where `Y ≠ 1` enters, F2).
  * **R4 G1 is the identity theorem, anchored on the shipped real-rate
    lemma.** `integral_cpow_mul_cexp_neg_mul_Ioi`'s body cites
    `integral_cpow_mul_exp_neg_mul_Ioi` **and** one of
    `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` /
    `eqOn_of_preconnected_of_eventuallyEq`; it does **not** restate the real
    Γ integral from `Complex.GammaIntegral` — the closed form is inherited, not
    re-derived.
* **Oracle + tests:** primitives `cgmy_compensated_exponent` (`B_ε`, with
  `eps=0` meaning the limit with its tail), `cgmy_paired_drift` (`d_ε`),
  `cgmy_lk_exponent` (`L`), `gamma_integral_complex_rate` (G1 by quadrature),
  `cgmy_drift_identity_closed` (`m^∞`); the committed
  `tests/test_bs.py::test_cgmy_law` asserting the route-check table above
  (the decomposition row, the two-piece slopes, `L` vs `ψ_Y`, the `Y = 1`
  row, G1, the drift identity, the CF ladder's Lipschitz ratio, the tightness
  proxy's monotonicity, the `Y ↓ 0` row); and mutants **M39–M43** (the
  unpaired drift leg as the divergence canary, the dropped drift, the missing
  `m^∞`, the flipped drift sign, `Γ(1−Y) → Γ(−Y)`), each killed by that test
  alone. Counts: oracle tests `25 → 26`, oracle mutants `39 → 44`. The
  ball-radius mutant is *not* seeded: its separation (`5.3e−4`) is real but
  small, and a test that must resolve it would have to resolve the drift
  identity's own quadrature floor by four decades.
* **Docs:** `docs/03` §D1 item 4/6's Stage-2 sentence gets "2b issued as
  BRIEF_020, G1 inside it"; `docs/04`'s queue row and the item-6 line the
  same; `README`'s CGMY-law note gets the Stage-2b/G1 status;
  `benchmarks/LEDGER.md` gets the row and correction **C25**.
* **Corrections to record if measurement repeats:** C25 (the `ivx` pieces
  *pair* into a finite nonzero drift; they do not cancel).

## Done looks like (acceptance, machine-graded)

1. `lake build` green at the tag; every new constant on
   `[propext, Classical.choice, Quot.sound]`; no `sorryAx`; `deferred: {}`
   untouched.
2. Statement pins move by exactly the landed count in **both** layers with the
   309 pre-existing entries byte-identical; `lint` green including `[CGMYLaw]`
   with its four cheats killed by name and nothing else; `oracle` green
   including `test_cgmy_law` and M39–M43, each killed by that test alone.
3. `cgmyLaw` is `limUnder` of BRIEF_019's compound-Poisson marginals along
   `εₙ = 2⁻ⁿ` (R1), its existence is the Prokhorov construction of F3 and its
   CF `cexp (τ L)` is a theorem via Lévy continuity (R3), the drift is the
   paired integrand (R2), and G1 is the identity theorem on the shipped
   real-rate lemma (R4).
4. `charFun cgmyLaw v = cgmyCharFactor C G M Y τ v` for `Y ≠ 1` — the tree's
   pricing factor is the CF of a law in the tree — **or**, if §3 is severed,
   `charFun cgmyLaw v = cexp (τ · cgmyLKExponent v)` on all of `0 < Y < 2`
   and the row says which.
5. A row in `benchmarks/LEDGER.md` when CI grades it, and the docs queue
   updated: Stage 2b landed (in whole or as 2b-i), G1 landed or still named.

## Explicitly out of scope

* **The mgf on the strip, the Esscher tilt at the law, and items 3/5 at
  general `Y`** (the brief after this one): `Measure.tilted` (BRIEF_019 F7),
  the landed `esscher_cgmy_shift`, and `charFun_cgmyLaw_eq_cgmyCharFactor`
  extended to complex `v` on the strip are the pieces. This brief's CF is at
  **real** `v` only, which is all Lévy continuity speaks about.
* **Item 6's expectation-level twin** at `Y ↑ 2` and any law-level corner
  statement at either end (F7: measured, not claimed).
* **Any pricing statement at `cgmyLaw`**: the tree prices from the exponent,
  and this brief does not change that; the expectation-level pricing at the
  law needs the strip CF above.
* **Any change to `ImprovedBS/CGMY.lean`, `CompoundPoisson.lean`,
  `VGLaw.lean`, `Esscher.lean`, `Corner.lean` or any landed pin**; the
  truncated family, its CF, the density and the far-field moment are
  consumed, not re-derived.
* **A general Lévy–Khintchine theorem** in either direction: `L` is *this*
  measure's exponent, built from `cgmyLevyDensity`; nothing is stated for an
  arbitrary Lévy measure.

## Name-check status (ledger C3)

Every mathlib name in F3–F5 and §1–§3 was read at the pinned rev `5ed2965`
through the GitHub API (`gh api …/contents/<path>?ref=<rev> --jq .content |
base64 -d`): `MeasureTheory/Measure/LevyConvergence.lean`
(`isTightMeasureSet_of_tendsto_charFun` — its hypotheses are
`ContinuousAt f 0` and the pointwise `Tendsto` over `ℕ`;
`ProbabilityMeasure.tendsto_of_tendsto_charFun`, which *takes* `μ₀`;
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`),
`MeasureTheory/Measure/Prokhorov.lean` (`isCompact_closure_of_isTightMeasureSet`,
stated for `S : Set (ProbabilityMeasure E)` with the tightness hypothesis on
the coerced set — the coercion shape is the one bookkeeping risk in §2),
`MeasureTheory/Measure/CharacteristicFunction/Basic.lean` (`charFun_apply_real`,
`Measure.ext_of_charFun`, `norm_charFun_le_one`),
`Topology/Sequences.lean` (`IsCompact.tendsto_subseq`),
`Topology/Basic.lean` (`tendsto_nhds_limUnder`),
`Topology/Separation/Hausdorff.lean` (`tendsto_nhds_unique`),
`Topology/Defs/Filter.lean` (`Filter.limUnder`, needs `Nonempty`),
`MeasureTheory/Integral/Bochner/Set.lean` (`tendsto_setIntegral_of_monotone`,
index `ι` with `atTop` countably generated),
`MeasureTheory/Integral/Bochner/Basic.lean` (`continuousAt_of_dominated`,
`continuous_of_dominated` — the latter's bound is uniform in the parameter,
hence §1's note), `MeasureTheory/Measure/Lebesgue/Integral.lean`
(`integral_comp_neg_Ioi`, `integral_comp_neg_Iic`),
`MeasureTheory/Integral/IntervalIntegral/Basic.lean` (`integral_comp_neg`),
`MeasureTheory/Integral/IntegralEqImproper.lean`
(`integral_Ioi_mul_deriv_eq_deriv_mul`, `integral_Ioi_deriv_mul_eq_sub`,
both with the two boundary `Tendsto`s as hypotheses),
`Analysis/SpecialFunctions/Gamma/Basic.lean`
(`integral_cpow_mul_exp_neg_mul_Ioi` — complex exponent, **real** rate `r`,
RHS `(1 / r) ^ a * Gamma a`; `integral_rpow_mul_exp_neg_mul_Ioi`;
`Complex.Gamma_add_one`, `Real.Gamma_add_one`),
`Analysis/Calculus/ParametricIntegral.lean`
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`),
`Analysis/Complex/CauchyIntegral.lean` (`DifferentiableOn.analyticOnNhd`),
`Analysis/Analytic/IsolatedZeros.lean`
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`),
`Analysis/Analytic/Uniqueness.lean` (`eqOn_of_preconnected_of_eventuallyEq`),
and `Analysis/Convex/Complex.lean` (`convex_halfSpace_re_gt`). Not located
and named as risks rather than assumed: a ready-made
`|e^{−Mx} − e^{−Gx}| ≤ |M − G| x` (derive from `Real.add_one_le_exp` or the
mean value inequality), the `DifferentiableOn` of `z ↦ z ^ (−s : ℂ)` on the
half-plane in the exact form the identity theorem wants
(`DifferentiableAt.cpow` with `slitPlane` membership), and the
`Set.range`-vs-`{μ n | n}` coercion between the tightness lemma and Prokhorov.
