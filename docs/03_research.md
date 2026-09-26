# 03 — Research directions: improving the increment law

The improvement is a **wider increment law that keeps the skeleton.** Each
direction below names the exact claim, the parameters it adds relative to GBM's
single σ, and a **falsifier** that would separate it from the alternatives.
Directions are ordered by (formal tractability × strength of evidence).

Every direction is graded against docs/02 §5: **(a)** explanatory power per
parameter, and **(b)** out-of-sample prediction, not in-sample fit.

---

## D1. Tempered-stable increment (heavy tails, the hard direction)

### The claim, and the obstruction that shapes it

**Claim:** replace the Gaussian log-increment by a Lévy increment with
*algebraic* rather than exponential tails, self-similar at index 1/α with
α < 2, that is nonetheless a martingale. BS is the α = 2 corner; the smile is
the shadow of lower α on the put side.

**Obstruction — read this before proposing anything.** The naive version of
this claim is *false*, and it is worth being explicit, because it is the
attractive version. Let `X_τ` be a pure symmetric α-stable law, α < 2. Its
tails satisfy `P(X_τ > x) ~ c·x^{−α}`, so

    E[e^{X_τ}] = ∫ e^x · c·x^{−α} dx = ∞.

Therefore `S_T = S_0·e^{X_τ}` has **infinite first moment** and cannot satisfy
the risk-neutral condition `E[S_T] = S_0·e^{(r−q)τ}` (docs/01 §3, Fact B). There
is no equivalent martingale measure inside the exponential-Lévy ansatz. The
consequence is not a technicality downstream — it is immediate: the
Carr–Madan / Lewis Fourier pricing integral requires a *moment strip*
`{u : E[e^{u·X_τ}] < ∞}` containing the pricing contour, and for a pure
α-stable that strip is empty on the side that matters. There is no contour to
place.

So the failure is at the **moment** step, not the **kernel** step. Any brief
that asks for "the transport kernel survives α-stable increments" is asking for
a theorem about an object that does not exist.

**Proved versus asserted (BRIEF_004).** The moment step of this obstruction is
no longer prose. `ImprovedBS/Levy.lean` proves — no `sorry`, clean `#print
axioms` audit — that a probability measure on `ℝ` whose upper tail is bounded
below by `c·x^(−α)` has no finite exponential moment
(`BSM.exp_moment_infinite_of_tail_lower_bound`, and the shifted form
`BSM.exp_moment_infinite_add_of_tail_lower_bound`), that the spot
`S_T = S₀·e^{X_τ}` therefore has infinite first moment
(`BSM.spot_not_integrable_of_tail_lower_bound`), and that no shift of the
log-drift repairs it (`BSM.no_drift_makes_spot_integrable`): drift cannot move
a tail index. Two corrections to how this section states the obstruction,
recorded in `benchmarks/LEDGER.md` C7 and in the brief's own correction record: (the hypothesis
is now *witnessed*, not only assumed: BRIEF_015's `ImprovedBS/ParetoWitness.lean`
proves `levy_tail_hypothesis_satisfiable_iff : (∃ law, htail) ↔ 0 < α` at
mathlib's Pareto law and instantiates the obstruction there by citation):

* **The index range is not `α < 2`.** The theorem holds for every real `α`.
  The divergent object is `exp` against `rpow`, and a genuine power tail —
  `x^(−3)` as much as `x^(−1)` — has infinite exponential moment. The `α < 2`
  above is a property of the α-stable *family*, not of the obstruction; the
  obstruction itself is wider, and `α ∈ (0, 2)` — the whole range T6 cares
  about — sits inside it. Nothing that stays within that interval can escape,
  which is why the tempered (CGMY) repair has to change the tail, not the
  index.
* **`α > 0` is a satisfiability condition on the hypothesis**, not a step in
  the proof: for `α ≤ 0` no probability measure satisfies the tail lower bound.

Still asserted rather than machine-checked, and therefore still prose here: the
**specialization** to the symmetric α-stable law — mathlib v4.34.0 has no such
law, so the tail bound enters as a hypothesis and the `c = F(−α)` constant of
the Zolotarev `S1` parametrization is cited from the literature — and everything
downstream of the moment step: emptiness of the moment strip, and the tempered
repair built on it.

**The repair.** Temper the Lévy measure. In the CGMY family
(Carr–Geman–Madan–Yor) and the Boyarchenko–Levendorskii family, the Lévy density
carries an `e^{−λ|x|}` damping:

    ν(dx) = C · e^{−G|x|} / |x|^{1+Y} dx      (x < 0)
    ν(dx) = C · e^{−M|x|} / |x|^{1+Y} dx      (x > 0)

with `Y = α ∈ (0,2)` the tail index and `G, M > 0` the two tempering rates.
Tempering restores every exponential moment on the interior of the strip, so an
equivalent martingale measure exists once the drift is fixed by the usual
exponent condition; algebraic tails survive at the scale that matters for
option tenors; and the α-stable law is recovered as `G, M → 0`. The **GBM
corner** requires a different, normalized limit: `Y ↑ 2` **and**
`C_Y = (σ²/2)(2−Y)`, with the log-drift fixed separately — a bare `Y → 2`
at fixed `C` diverges because `Γ(−Y)` has a pole (BRIEF_014, ledger C17).
The price paid is parameters: GBM has one (σ), CGMY has four (C, G, M, Y).
That is exactly what falsifier (a) below is for.

### What extends

    σ (one parameter)  →  C, G, M, Y (four)
    X_{t+dt} − X_t     ~  tempered stable, drift fixed by the martingale condition

The European risk-neutral value becomes a Fourier integral over a contour
inside the moment strip — real analysis, still a transport kernel, and still a
convolution of the payoff with a transition density. (An explicit
one-dimensional integral requiring quadrature: a weaker object than BSM's
elementary function, and the difference is worth keeping in view wherever the
word "closed" appears.) What survives the widening, and what does not, is
worth stating exactly (ledger C13):

- **Survives — the static skeleton.** Put-call parity, the no-arbitrage
  bounds, and the price-as-discounted-expectation form: these hold for *any*
  terminal law with the drift condition, machine-checked in
  `ImprovedBS/Skeleton.lean`. This is the part the Fourier integral needs.
- **Does not survive — the dynamic skeleton.** A self-financing *replicating*
  portfolio, the *uniqueness* of the martingale measure, and the PDE as its
  consequence. With jumps the martingale condition is one equation and does
  not select a measure: Esscher, minimal-entropy, mean-correcting and
  calibrated choices are all arbitrage-free and price the same call
  differently. So the drift being "fixed by the martingale condition" is only
  ever fixed *relative to a named selection principle*, and the hedging
  content of the price is quadratic-error minimization, not delta
  replication. This half is now machine-checked at the smallest law that can
  carry it (`ImprovedBS/NonUniqueness.lean`, BRIEF_012, item 7 below): on
  three spots the martingale condition leaves a whole segment of measures,
  every one satisfying the static skeleton, and the call price runs over all
  of `[0, 1/3]` along it.

That is the whole point, restated honestly: **the tail moves into the
increment rather than into an elastic volatility**, so *pricing* stays a
single-martingale-measure computation — one measure, chosen and named, not
unique — and maturity-mispecification and moneyness-mispecification become one
instability instead of two hidden ones. The uniqueness loss is not a defect to
hide; it is a theorem to prove (item 7 below).

### BSM 2 — what "widened" has to mean, precisely

The repository needs a commit criterion for the word "improved", or the thesis
above stays prose. Here it is.

**BSM 1** is the tree as of BRIEF_008: one increment law — Gaussian
log-increments, constant σ — machine-checked end to end. T1–T5 are theorems
about the closed form; T6's triangle (closed form = discounted risk-neutral
expectation = inverted Carr–Madan integral) is machine-checked at the
lognormal instance; the moment obstruction for the naive widening is
machine-checked (`Levy.lean`).

**BSM 2** is a *second* concrete increment law — the tempered-stable / CGMY
one above — **in the same tree, under the same skeleton**, with all seven of:

1. **The law exists in the tree.** The concrete CGMY characteristic exponent
   (the `cpow`/branch work BRIEF_005 deferred and named), shown to arise from
   a valid Lévy measure (`∫ (1 ∧ x²) ν < ∞`) and affine in τ.
2. **Its moment strip is a theorem.** Tempering *restores*
   `E[e^{u·X_τ}] < ∞` on the interior of `(−G, M)`, and that interior contains
   the pricing contour and the numéraire point — the positive twin of
   `Levy.lean`'s obstruction theorem, and the point at which the tempered
   repair stops being asserted. (The pricing contour is the line
   `v = u − i(α+1)`, i.e. the imaginary level `−(α+1)`. In the *tilt* variable
   `u` the strip is `(−G, M)`; in the transform's own variable it is
   `−M < Im v < G` — the `G` limit is the upper one — so containment of
   `Im v = −(α+1)` is `α + 1 < M`, and the principal branch of the exponent's
   `(M − iv)^Y` term asks for the same thing, `Re(M − iv) = M − (α+1) > 0`. The
   working condition is therefore `α + 1 < M` alone; `G` constrains the *old*
   line `v = u + iα` that `Fourier.lean`'s kernel sits on
   (`Re(G + iv) = G − α`), which is what made the earlier `min(G, M)` spelling
   look plausible. The numéraire point is `u = 1`, needing `1 < M`. Ledger C12,
   C14, C15 and BRIEF_011.)
3. **The drift is fixed *at a named pricing measure*,** and
   `E[S_T] = S·e^{(r−q)τ}` is proved at the new law under that measure (the
   CGMY twin of `integral_spot_mul_phi_eq_forward`). The martingale condition
   alone does not select the measure — see item 7; the choice (Esscher,
   minimal-entropy, calibrated, …) is part of the model, and the price is a
   claim *at the chosen measure*. **Landed as BRIEF_013 (Esscher), PR #20,
   run 36072416203 (2026-09-24):**
   the shift `ψ^θ(v) = ψ(v − iθ) − ψ(−iθ)` maps CGMY to itself with
   `(G, M) ↦ (G+θ, M−θ)` (`esscher_cgmy_shift`, `esscher_tilt_factorization`);
   the drift equation `κ(θ+1) − κ(θ) = r − q` is
   strictly monotone (strict convexity of `κ` on the strip —
   `κ″ = CΓ(2−Y)[(M−u)^{Y−2} + (G+u)^{Y−2}] > 0`, the Γ rewrite
   `Γ(−Y)·Y·(Y−1) = Γ(2−Y)` keeping the curvature constant manifestly
   positive), and a unique
   `θ ∈ (−G, M−1)` exists exactly when `|r−q| < |CΓ(−Y)|·|(G+M)^Y −
   (G+M−1)^Y − 1|` — the strip's edge values decide
   (`esscher_exists_unique_of_mem_range`,
   `esscher_no_solution_of_outside_range`), with the zero-drift parameter
   the exact `θ₀ = (M−G−1)/2` (`esscher_theta_zero_unique`). Route-checked
   before issue; the deliverable landed at the factor level —
   `esscher_drift_factor` gives the tilted factor `e^{τ(r−q)}` at the
   solution, and pricing at the tilted rates consumes
   `cgmy_cmPriceKernel_integrable`. **The expectation-level twin has landed
   as BRIEF_018** (`ImprovedBS/VGLaw.lean`, `vg_drift_identity`): at the Esscher
   tilt `vgTilt` of the variance-gamma law — the family's `Y = 0` member, the
   difference of two `gammaMeasure`s — `∫ x, S · exp(x) ∂(vgTilt) = S · exp((r−q)τ)`
   whenever `vgDriftMap θ = r − q`. That is law (c) of the brief's F3, the
   tree's Esscher measure, not the published translated martingale law
   BRIEF_016 prices at. The general-`Y` law (Stage 2) and the complex-rate Γ
   integral (G1) stay open; item 6's expectation-level twin waits on the second
   half of Stage 2. **Stage 2's first half has landed as BRIEF_019**
   (`ImprovedBS/CompoundPoisson.lean`, 5 defs + 12 theorems; statement pins
   292 -> 309 in both layers with the 292 pre-existing entries byte-identical,
   audit 256 -> 268, `[CPOISSON]` R1-R4 with lint cheats 48 -> 52, oracle
   24 -> 25, mutants 34 -> 39; `briefs/BRIEF_019_compound_poisson_stage2a.md`):
   the compound-Poisson law of
   a probability jump measure at rate `λ` — the Poisson mixture of convolution
   powers, CF `exp(λ(φ−1))` — plus the truncated CGMY jump law `ν_ε/λ_ε` from
   the landed `cgmyLevyDensity` and its marginal, exponent
   `∫_{\|x\|≥ε}(e^{ivx}−1)ν`. The route-check *closes the conventions by
   measurement*: the truncation must be symmetric (two-sided error `O(ε^{2−Y})`,
   slopes 1.4904 / 0.4947 at `Y = ½, 3⁄2`; one-sided diverges like `ε^{1−Y}` for
   `Y ≥ 1`) and uncompensated (compensating everywhere lands on
   `ψ_Y − iv·m^∞`, a translated law), and it corrects F5(iv) below: the `ε ↓ 0`
   step is not dominated convergence, since `λ_ε → ∞` like `ε^{−Y}` and no
   integrable dominating function exists at zero. The limit, the tightness and
   the identification are Stage 2b; the corner cross-check against BRIEF_018's
   `vgLaw` is already measured (`\|A_ε − ψ₀\|/Y → 0.0375` at `v = 0.5`). The
   landed module stops exactly where 2b starts: no `ε ↓ 0` limit, no tightness,
   no identification — and the limit is conditional convergence, not DCT, since
   no integrable dominating function exists near zero.
4. **T6's triangle holds at the new exponent.** The Carr–Madan integral
   converges absolutely on the contour, inverts to `e^{−rτ}·E[(S_T − K)⁺]`,
   and is real-valued — the full pricing claim where no closed form exists.
   **Landed as BRIEF_010, re-scoped** (PR #16, run 35646623031; `docs/04`'s
   queue row 10): the pricing identity is proved at *any* law satisfying the
   strip conditions, and instantiated at GBM, which closes the triangle at the
   lognormal instance through the kernel route; the concrete exponent's
   continuity and decay enter as the one recorded hypothesis and are
   BRIEF_011's deliverable. Note the contour it is stated on —
   `v = u − i(α+1)`, not `φ(u + iα)`; ledger C12 records why, and what the
   difference costs.
5. **The skeleton is preserved.** Put-call parity and the no-arbitrage bounds
   hold at the new law — by *instantiation* of the model-free layer
   (`ImprovedBS/Skeleton.lean`, BRIEF_009), not by re-proof. **This item's
   machinery has landed green** (PR #11), and it is no longer GBM-only:
   parity and bounds are lifted off the closed form onto
   `e^{−rτ}·E[(S_T − K)⁺]` for any law with the drift condition, the GBM
   instance re-derives T2′ and T4 through the new layer
   (`t2_spread_via_skeleton`, `t4_call_bounds_via_skeleton`, graded to
   consume the model-free proofs and not the closed-form ones), and
   **BRIEF_018 instantiates them at the tilted variance-gamma law**
   (`vg_modelFree_call_bounds`, `vg_modelFree_put_bounds`,
   `vg_modelFree_parity`) — the first non-Gaussian law in the tree that
   discharges the three facts (`Integrable X`, the drift condition, `0 ≤ X`)
   by construction.
6. **GBM comes back at the corner — LANDED as BRIEF_014** (PR #22, lean run
   36111570530, 2026-09-25; `ImprovedBS/Corner.lean`). For
   `1 < Y < 2`, take `C_Y = (σ²/2)(2−Y)` as `Y ↑ 2`: then
   `C_Y Γ(−Y) → σ²/4` and the **uncorrected** CGMY exponent converges
   pointwise on the strip to `−(σ²/2)v² + i(σ²/2)(G−M)v`. A separately
   labelled *algebraic forward normalization* `i(r−q−κ_Y(1))v` gives the GBM
   risk-neutral exponent; at `r=q`, the **named Esscher selection**
   `θ₀=(M−G−1)/2` gives the same GBM limit and satisfies the numéraire
   condition for every `Y`. The two routes are proved separately because they
   are different selection principles: route A is `cornerForwardExponent`,
   `Ψ_Y(v) = ψ_Y(v) + i(r−q−κ_Y(1))v`, whose numéraire identity
   `Ψ_Y(−i) = r−q` is *exact at every `Y`* and consumes
   `cgmyExponent_strip`, and route B is the BRIEF_013 shift
   `esscher_cgmy_shift` consumed at the shifted rates `G′ = (G+M−1)/2`,
   `M′ = (G+M+1)/2`, with `esscherDriftMap_zero` solving the drift equation
   at `θ₀` for every `Y` — no drift correction at all, and no limiting root.
   What landed is a **one-sided** limit, `Tendsto … (𝓝[<] 2) …`: the old bare
   `Y → 2` with fixed `C` **diverges** (the `Γ(−Y)` pole), and
   `G,M → σ²/2` is **not** an alternative Gaussian limit; correction C17
   records the error and the numerical counterexample. The route-check that
   measured all of this is now a committed oracle test
   (`tests/test_bs.py::test_gbm_corner`) with seeded mutants for the doubled
   scale and the dropped drift correction. Convergence of prices, or a CGMY
   probability measure to connect this exponent to expectations, is a
   recorded deferral, not a consequence of pointwise convergence: the limit
   holds at each fixed `v`, which is not a uniform dominating bound on the
   pricing contour and does not license an interchange with the Carr–Madan
   integral.
7. **The selection principle's necessity is a theorem.** The tree contains a
   machine-checked non-uniqueness witness: two distinct probability measures,
   both satisfying the drift condition, giving *different* call prices —
   while *both* satisfy the skeleton layer's parity and bounds (item 5's
   three facts). That is the formal statement that static-skeleton
   preservation is necessary-but-not-sufficient, and it is what obliges
   item 3's "named". A one-period trinomial witness suffices (finite sums, no
   Lévy machinery); the compound-Poisson version ties it to the Lévy line.
   **LANDED** as **BRIEF_012** (ledger C13 → row 12; PR #19, lean run
   36052072620): `ImprovedBS/NonUniqueness.lean`, headline
   `static_skeleton_does_not_select_measure`. The witness is a one-period
   trinomial at spots `(1/2, 1, 2)` with the two interior martingale measures
   `(1/2, 1/4, 1/4)` and `(1/4, 5/8, 1/8)`, which price the call at `1/4` and
   `1/8` — interior to the martingale segment `p₃ = p₁/2`, `p₂ = 1 − 3p₁/2`, so
   both are fully supported and mutually equivalent (`witness_equivalent`) and
   the price difference is incompleteness rather than a support artifact. The
   sharp form is machine-checked too: `martingale_set_call_eq` — on the whole
   segment the call is exactly `p₁/2`, so every price in `[0, 1/3]` is a
   martingale price (`martingale_set_price_range`) while item 5's bounds only
   say `0 ≤ call ≤ 1`. Parity and the bounds at both measures are
   *instantiations* of item 5's theorems (the `[NONUNIQ]` lint check reads the
   citation), which is what makes this a statement about the static layer
   rather than beside it.

Items 1–3 are the new analysis. Items 4–6 are the widening being *proved*
rather than fitted. Item 7 is the honest shape of the whole enterprise: it
converts "BSM 2 = wider increment law" into "BSM 2 = wider increment law
**plus a selection principle**", which is the shape the incompleteness
literature says the problem actually has. Until all seven land, "improving
BS" is this document's
hypothesis, not the repository's theorem — and even after they land, the
falsifiers below (fitted α concentrating in `(1.3, 1.9)` and materially less
moneyness-dependent than the σ it replaces; out-of-sample hedging variance per
parameter) remain the market-facing test that separates BSM 2-as-theorem from
BSM 2-as-improvement. The formal kit is necessary and not sufficient; it is
also what makes the empirical claim falsifiable against a fixed object
instead of a moving fit.

### Falsifier (must show both)

Fit `(C, G, M, Y)` — or the reparametrized `(α, σ_α, λ)` — on an S&P 500 / FX
implied-vol panel, then:

- **(a)** it explains at least as much *out-of-sample hedging* variance per
  parameter as a GBM fitted conditionally to the smile, on held-out tenors
  (a ratio test, not a fit comparison); **and**
- **(b)** the posterior on α concentrates inside `(1.3, 1.9)`, **and** the
  fitted α is materially *less* dependent on moneyness than the GBM σ it
  replaces.

(b) is the real claim. If α has to vary with moneyness to fit, the model has
reintroduced an elastic volatility by another name and bought nothing — that is
anti-direction 1 below wearing a Lévy costume.

**Pre-registered measurement (BRIEF_016, landed).** One term-structure
falsifier for the direction, fixed before it was run. The ATM implied-vol skew
`ψ(τ) = ∂σ_BS(k,τ)/∂k` at `k = ln(K/F) = 0` was measured for two witness sets
over `τ ∈ [0.25, 5]` in a pinned quadrature (`α = 1.5`, `u_max = 2000`,
`n = 80000`, `h = 0.005`, implied vol by bisection) and fitted as `ψ ~ τ^(−a)`:
**a = 1.0857** at the published Carr–Madan (1999) Case-4 VG parameters and
**a = 0.9682** at CGMY `(1, 5, 10, 0.7)`. The market's published fits decay
like `τ^(−0.36..−0.45)` (`α ∈ (0.30, 0.50)`: El Amrani–Guyon,
Gatheral–Jaisson–Rosenbaum 2018), so the model band `[0.90, 1.15]` and the
market band are **disjoint by 0.40** — the direction, taken alone, fails this
falsifier. The order parameter is right: the asymptotic rate for
exponential-Lévy models is `O(τ^(−1))` (Figueroa-López–Forde–Jacquier), which
the measurement agrees with, and ledger **C19** corrects the reviewer's
`τ^(−1/2)` parenthetical — so the failure is one of *magnitude* (the missing
mean-reverting factor of §D2), not of the exponent's form. The measurement is a
committed test, `tests/test_bs.py::test_term_structure_anchor`, with mutants
M26–M29; the same test carries the oracle's one genuinely external anchor (the
published Carr–Madan Case-4 price table and that paper's failing VGPS row).
This is the dynamic half C13 finding 4 asked for, and it is the repository's own
statement of what the T6 direction does not buy.

### Formal target (this is T6)

Stated in `ImprovedBS/Core.lean` as a comment block; the theorem to aim at is:

> **T6.** Let `X` be a Lévy process with characteristic exponent `ψ` affine in
> `τ`, and suppose the damping strip `{u : E[e^{u·X_τ}] < ∞}` contains both the
> pricing contour and `−1` (the numéraire point, i.e. the drift is fixed so that
> `E[e^{X_τ}] = e^{rτ}`). Then the Carr–Madan integral
>
>     V = e^{−rτ}/(2π) · ∫ e^{−i·u·τ} · f̂(u + iα) · e^{τ·ψ(u + iα)} du
>
> converges absolutely, is real-valued for real payoffs, and equals
> `e^{−rτ}·E[(S_T − K)⁺]`. GBM is the case `ψ(u) = i·u·(r−q) − σ²u²/2`.

Provable sub-goals, in increasing order of commitment:

1. **The obstruction as a theorem.** For a pure α-stable exponent with α < 2,
   `E[e^{X_τ}] = ∞`, hence the moment strip excludes the pricing contour. This
   is a concrete improper-integral divergence — no finance in it — and proving
   it *earns* the tempering hypothesis instead of assuming it. It is the highest
   value-per-effort item in the whole research tier and it should be a brief on
   its own.
2. **Absolute convergence** of the Carr–Madan integrand on a contour strictly
   inside the strip, for a tempered-stable exponent.
3. **Agreement** with the risk-neutral expectation, i.e. Fourier inversion
   against the payoff transform. This splits in two (BRIEF_007):
   - **(3a) the expectation itself — LANDED GREEN** as `ImprovedBS/RiskNeutral.lean`
     (PR #9, run 35574194681): `bsCall_eq_riskNeutral_expectation` and
     `bsPut_eq_riskNeutral_expectation` prove that the T1–T5 closed form *is*
     `e^{−rτ}·E[(S_T − K)⁺]` under `log(S_T/S) ~ N((r−q−σ²/2)τ, σ²τ)`, stated
     both as a Lebesgue integral against `phi` and against mathlib's
     `gaussianReal` (standard-normal and lognormal forms), together with the
     drift condition `E[S_T] = S·e^{(r−q)τ}`. This is the GBM instance of the
     right-hand side of T6; until it existed the closed form had never been
     connected in the tree to the expectation it is supposed to be.
   - **(3b) the inversion — LANDED GREEN** (run 35578278238) as `ImprovedBS/Inversion.lean`
     (BRIEF_008): `Continuous.fourierInv_fourier_eq` /
     `Integrable.fourierInv_fourier_eq` against `carrMadanKernel`, landing on
     `bsCall_eq_lognormal_expectation`, and proving real-valuedness of the
     inverted integral (`carrMadan_inversion_im_eq_zero`). Completes the
     formalization of T6.

---

## D2. Volatility-of-volatility (skeleton-preserving, second factor)

**Claim:** keep Brownian log-increments but let σ itself diffuse, driven by a
second (correlated or independent) factor. BS is the zero-vol-of-vol corner.
This preserves the ℚ-martingale property and admits a Fourier/kernel solution —
the stochastic-volatility family, of which Heston is the affine case, i.e. the
case where the characteristic function is exponential-affine in the state and
therefore available in closed form.

**What it fixes and what it doesn't:** it produces a genuine smile and a genuine
term structure from two parameters of dynamics rather than one parameter per
strike. It does *not* produce algebraic tails — the increment stays Gaussian
conditional on the vol path, so extreme moves are still exponentially rare
conditional on the (now random) variance. If the evidence in docs/02 A2 is
taken seriously, D2 alone is incomplete; D1 and D2 are complements, not rivals,
and a combined tempered-stable-with-stochastic-volatility model is where the
literature actually lands.

**Falsifier:** a two-factor model must beat single-σ GBM by

- **(a)** matching the smile *and* the term structure *simultaneously* — in
  particular the fact that the smile's slope can change sign along tenor, which
  a single constant σ cannot express at any value of σ; and
- **(b)** producing out-of-sample hedging errors that forecast low- versus
  high-vol regimes, where the vol-of-vol is *calibrated once* rather than
  re-fitted per horizon.

---

## D3. Persistence / regime increment (the no-memory falsifier)

**Claim:** realized volatility is *temporally persistent* — GARCH-like
clustering — so the description "the increment is a Sharpe-optimal martingale
diffusion" is incomplete as a statement about a *process*: it constrains the
one-step law and says nothing about the dependence across steps.

This is the weakest of the three as a pricing direction and the strongest as a
*falsification* direction, because its test is cheap and its conclusion is
unambiguous: a Markov model of the spot cannot generate observed vol clustering,
period. Whatever replaces it must be a model of paths, not of a marginal.

**Falsifier:** the autocorrelation function of |log-return| over 1d..4w is
non-zero with statistical significance (not a point estimate — a confidence
statement), while the geometric random walk's ACF is zero by construction. Any
model that prices from the single-spot marginal alone is then ruled out as a
complete account, independent of how well it fits the surface.

**Interaction with D1/D2:** persistence is what makes the *fitted* parameters of
either model time-varying. A direction that reports a point estimate of α or of
vol-of-vol without reporting its persistence is reporting a sample statistic as
if it were a structural constant.

---

## Anti-directions

Things that "improve BS" proposals usually reach for, and why they are traps
(see docs/02):

- **Recalibrate σ per quote** ("use today's vol for today's option"). One
  parameter per print is not improvement; it is transcription of the surface.
  GBM *can* fit any smile with a strike-dependent σ — that is Dupire's local
  volatility, which is a perfectly good *calibration* and a perfectly useless
  *prediction*, because it destroys the single-martingale structure and buys no
  out-of-sample content. Fails (a) and (b) both, by construction.
- **"Just add a jump term."** A finite number of Gaussian translates still
  leaves the central-mass-to-tail ratio near Gaussian. Jumps help only if the
  jump arrivals and sizes are modelled as *informed events* with their own
  dynamics — and then you are pricing the cause of the jump, which is D2/D3
  territory, not a compound-Poisson afterthought.
- **Fit the surface and call the fit a model.** Any direction whose evidence is
  in-sample R² on the same panel it was calibrated to is disqualified on
  arrival (docs/02 §5). This is the single most common way a plausible-looking
  improvement turns out to be an expensive interpolation.

---

## The falsification loop (how a direction graduates)

For a direction → candidate → result:

1. **State** the increment-law replacement in one line: family, parameters, and
   the martingale condition that fixes its drift. A direction that cannot state
   its moment condition has not met Fact B and stops here.
2. **Fit** on an (expiry × moneyness) surface over history.
3. **Predict** out-of-sample — one tenor forward — and compare hedging error
   against the GBM hedge.
4. **Compete** on explained variance *per parameter*, not on fit.
5. **Formalize** whichever structural claim survived: the surviving identity
   becomes a node in the theorem stack, and `briefs/` gets a work order with a
   machine-graded acceptance bar.

A model whose "improvement" appears only by adding a constant per option is
disqualified at step 1.

---

## Beyond BSM-2 — aims past the current program

BSM-2 (§D1) is scoped to one widening: one replacement law, proved to preserve
the skeleton. Three aims sit past it, in decreasing order of ambition, plus
one explicit non-aim. None of them displaces the current queue: BSM-2 finishes
first, the empirical falsifiers run, and the CGMY result becomes the first
entry in the library described below — which is what retroactively validates
the framing.

### The library aim: the program as an instrument

BRIEF_009 produced something more general than the brief that commissioned it:
parity and the no-arbitrage bounds hold at the expectation level for *any*
terminal-spot law with the drift condition, so a candidate law enters the tree
by supplying three facts (`Integrable X`, the drift condition, `0 ≤ X`), not
by re-proof. The BSM-2 kit (§D1, items 1–7) is the rest of the pattern: moment
strip, drift fix, Fourier triangle, skeleton instantiation, corner recovery,
a named selection principle, empirical falsifiers. The aim past BSM-2 is to
run that kit as a standing
pipeline — a library of increment/state laws, each entering through the same
graded briefs and each exiting with a *proved domain of validity*: where the
price exists, what the drift condition is, which selection principle fixes
the pricing measure, which corner recoveries hold.
Tempered-stable is the first entry; tempered-stable-with-stochastic-volatility
(the D1+D2 combination — where the literature lands, per §D2) is the second;
a regime-switching law is a third candidate once D3's falsification question
is settled.

The deliverable shifts from "the improved Black-Scholes" to the machine that
adjudicates any proposed improvement, on both lanes: formal (the seven-item
kit) and empirical (the falsifiers of §D1). This is also the version a model-risk
function can consume: risk committees do not adopt models, they adopt
validated envelopes, and a machine-checked envelope is the one artifact a
fitted model cannot produce. `ImprovedBS/Levy.lean`'s obstruction theorem is
already that kind of object — a checked statement of where a martingale price
cannot exist. The envelope, not the fit, is the capital-facing deliverable.

### The hedging horizon: from pricing to hedging and path-dependence

Everything in the tree prices European claims from a terminal marginal. The
places model uncertainty strands capital are path-dependent and illiquid —
American and barrier structures, long-dated tails — and "improvement" there is
not a price but a hedge. And the base case matters: outside GBM there is no
replicating hedge at all — hedging under a jump law is quadratic-error
minimization (the variance-optimal hedge), so "the hedge works" is an error
*bound*, never an identity. The formal content of this aim: self-financing
strategies, discrete hedging-error bounds under the widened law, and the Snell
envelope for American payoffs. The caveat, stated now so nobody budgets it as
an ordinary brief: this is at mathlib's frontier. Its stochastic-calculus
coverage at the pinned tag is thin (no Itô formula, no stochastic integral),
so this aim partly means contributing upstream to mathlib first.

### The cheap one: the D3 falsifier as a theorem

"Under a geometric random walk, the autocorrelation of |log-returns| is zero"
is a small theorem — no new machinery, no finance — and it converts D3's
gatekeeping argument (a model that prices from the spot marginal alone is
ruled out by vol clustering) from a citation into a checked result. It is the
cheapest item on this page and it guards the framing of everything else; it
can slot as a small brief at any time.

### The non-aim: the general theory

Not adopted: arbitrary semimartingales, the fundamental theorem of asset
pricing in full generality. That is a mathlib-lifetime project and it trades
the program's actual edge — concrete laws, concrete proofs, fast graded
briefs — for generality nobody is blocked on. The library aim generalizes the
*kit*, not the mathematics.
