# BRIEF_010 — T6 at any strip law: the pricing identity, and a contour correction

- **Status:** **ISSUED** — no PR yet. This is **item 4** of the BSM-2 kit in
  `docs/03` §D1 ("What extends") — *T6's triangle holds at the new exponent* —
  worked under the re-scope option `docs/04` pre-committed for it ("abstract the
  law behind a hypothesis the way the decay bound is already abstracted, and
  record it"). Landing it also corrects a contour that `ImprovedBS/Fourier.lean`
  and `ImprovedBS/Inversion.lean` currently *describe* as the pricing contour and
  that is not one (§"The finding" below; recorded as correction C12 in
  `benchmarks/LEDGER.md`).
- **Prerequisite PRs:** BRIEF_005 (T6 sub-goal 2, `ImprovedBS/Fourier.lean`),
  BRIEF_007 (3a, `ImprovedBS/RiskNeutral.lean`), BRIEF_008 (3b,
  `ImprovedBS/Inversion.lean`) and BRIEF_009 (`ImprovedBS/Skeleton.lean`) merged.
  **No edit to any existing declaration** in `Core.lean`, `Levy.lean`,
  `Fourier.lean`, `RiskNeutral.lean`, `Inversion.lean`, `Skeleton.lean`; the
  corrections to `Fourier.lean`/`Inversion.lean` are **doc-comments only**, which
  the pin discipline strips, so no pinned statement moves. The only changes
  outside the new module are the root `import` line + blurb in `ImprovedBS.lean`,
  the doc-comment corrections, and the grading wiring (§6).
- **Skills:** Lean 4 + mathlib measure theory at the Bochner-integral level
  (`Integrable`, product measures, Fubini, dominated convergence as a continuity
  tool) and complex algebra on `Complex.exp`. **No new mathematics beyond
  calculus**: the strike transform is an elementary substitution, the inversion
  is mathlib's inversion theorem rescaled, and the only genuinely new analytic
  input is the *shape of the hypothesis* — which is where this brief deliberately
  stops (§"The decision").
- **Budget:** CI-only verification — no local Lean toolchain. Expect the two-run
  `elab` pin bootstrap as in BRIEF_007–009 (first run red by design and printing
  the block, second run merging it verbatim) plus elaboration fixes; the last
  three briefs spent 4–8 runs, most of it API shape at the tag. Every mathlib name
  this brief relies on was verified against the **pinned tag v4.34.0** before it
  was committed (ledger C3), with the file it lives in; names marked ✓ are
  verified, names marked ? are the expected route and must be re-read at the tag
  before pushing. The numeric route is checked in the oracle **before** any Lean
  is written (ledger C4) and is recorded in §"The numeric route-check".

## Background, in order

1. `docs/03` §D1, "What extends → BSM 2 — what 'widened' has to mean" — item 4 in
   full, and the paragraph that authorises this brief's shape: items 1–3 are the
   new analysis, item 4's exponent↔law connection "is the known risky step",
   items 4–6 are the widening being *proved*.
2. `docs/04` "The brief queue" — the ordering constraint and the re-scope option.
3. `benchmarks/LEDGER.md` C4 (route numerically first), C7 (hypotheses are
   load-bearing or they are wrong), C9 (a brief may reverse a documented route),
   and C1 item 1 (a theorem that is true by construction is not a theorem — the
   same instinct, applied here to an *identification* rather than a proof).
4. `ImprovedBS/Fourier.lean` — `cmDenom`, `cmDenom_u4_le`, `carrMadanKernel`,
   `carrMadanKernel_integrable`, `carrMadanPhase`, `gbmCharFactor_contour_norm`,
   and the module header's hypothesis discipline.
5. `ImprovedBS/Inversion.lean` — `carrMadanInversion`, `dampedCallPrice`,
   `fourierInversion_dampedCallPrice`, and §4's five main theorems. Note what §4
   is *about*: `𝓕⁻ (𝓕 f)` where `f := dampedCallPrice …`. `carrMadanInversion` is
   defined and proved integrable, but no theorem equates it with a price.
6. `ImprovedBS/Skeleton.lean` — `modelFreeCall`, `model_free_parity_gap`,
   `model_free_call_bounds`: the layer this brief's right-hand side lands on.
7. `experiments/black_scholes.py` — `carr_madan_denom`,
   `bs_call_by_fourier_inversion` (the oracle's contour), `_expectation`,
   `model_free_prices`, `bs_call_by_expectation`.

## The finding: the tree's kernel sits on the wrong line (and no theorem says so)

Two different contours are in play in this repository, and they are not the same
line.

* The **oracle** (`bs_call_by_fourier_inversion`, BRIEF_008, green) evaluates the
  model factor at `v = u − i(α+1)` and returns
  `e^{−rτ} · S · e^{−αk} / (2π) · ∫_ℝ e^{−iuk} φ(u − i(α+1)) / cmDenom(α,u) du`.
  It agrees with the closed form to `9.99e-16` relative at the test point
  (`S=100, K=110, τ=1, r=0.05, q=0.02, σ=0.25, α=1.5`: `7.112102348131359`), which
  is what its test asserts at `2e-11`.
* **`carrMadanKernel φ α u = φ(u + iα) · (cmDenom α u)⁻¹`** (BRIEF_005, and
  `Inversion.lean`'s `carrMadanInversion` inherits it) evaluates `φ` at
  `v = u + iα`. That is a *different* line: the two coincide only when
  `−(α+1) = α`, i.e. at `α = −1/2`, which `0 < α` excludes.

The two lines are not interchangeable, and the numbers say which one is the
pricing contour. On `u − i(α+1)` the same formula reproduces the closed form to
`9.99e-16`; on `u + iα` it returns `1.819563153701569` against `7.112102348131359`
— **74.2% relative error**. The crux identity says the same thing from the
definition side. With `f(k) := e^{αk} · e^{−rτ} · E[(S e^X − S e^k)⁺]` (this is
`dampedCallPrice`) and `φ` the lognormal factor, direct quadrature of
`∫_ℝ e^{iuk} f(k) dk` matches

    𝓕 f(u) = e^{−rτ} · S · φ(u − i(α+1)) / cmDenom(α,u)

to `1.16e-16`, `5.38e-16`, `8.16e-16` at `u = 0, 0.7, −2.0`, and misses the
tree's line by `1.28e-01`, `2.25e-01`, `5.41e-01` at the same points.

**Why it hid.** BRIEF_005's deliverable is a *conditional* integrability theorem:
its hypothesis names its own contour (`∀ u, u₀ ≤ |u| → ‖φ (↑u + ↑α·I)‖ ≤ D·exp(−c|u|^Y)`),
so the theorem is true as stated on either line — the hypothesis is a hypothesis.
And the tempered decay is **contour-independent to leading order**: for CGMY
(`C=1, G=5, M=10, Y=0.7, τ=1`) the measured `−Re ψ/|u|^Y` at `u = 2000` is
`3.731206` on the pricing line and `3.731207` on the tree's line. Nothing in the
landed stack contradicts itself; what is wrong is the *identification* in the
prose — BRIEF_005's formula `V = e^{−rτ}/(2π)·∫ e^{−iuτ} φ(u + iα)/cmDenom du`
and the module docstrings that call this kernel the pricing kernel. `Inversion.lean`
§4 never consumes `carrMadanKernel`, which is exactly why the gap survived: the
theorems it *does* prove are about `𝓕⁻ (𝓕 f)` and are correct.

**What this brief does about it.**

* It does **not** edit a landed theorem, a def body, or a pin. The correction is:
  a doc-comment correction in `Fourier.lean` and `Inversion.lean` (free under the
  pins, which strip comments), the new kernel below, an oracle mutant that pins
  the contour (§6), and a `[CONTOUR]` lint check (§6) so the identification cannot
  drift back.
* It writes the kernel on the pricing line under its own name, and it *reuses*
  BRIEF_005's theorem rather than reproving it — the shift is exact:

      cmPriceKernel φ α u = carrMadanKernel (fun v => φ (v − (2α+1)·i)) α u

  so `carrMadanKernel_integrable` applies verbatim, with the same `c, D, Y, u₀`.
  The whole cost of the correction is one pointwise identity.

## The decision: state T6 at *any* strip law, and record the exponent↔law step

`docs/04` predicted this brief's difficulty and pre-committed its fallback: item
4's exponent↔law connection "is the known risky step and inherits BRIEF_004's
re-scope option — abstract the law behind a hypothesis the way the decay bound is
already abstracted, and record it."

This brief takes that option, and it is a *strict improvement* rather than a
retreat:

* the pricing identity is **law-agnostic** — the substitution, the Fubini
  exchange, the inversion and the real-valuedness do not care what the law is,
  only that it is a probability measure with the strip conditions of §"Goal";
* stating it once, at an abstract `φ`, makes item 1's exponent a *client* of this
  theorem rather than a prerequisite: BRIEF_011 (named below) supplies the CGMY
  characteristic function and its decay, and gets item 4 by instantiation;
* the **GBM instance is proved here** (§5, `gbm_carrMadan_eq_bsCall`), closing
  T6's triangle — closed form = discounted expectation = inverted Carr–Madan
  integral — through the *kernel* route for the first time. That is the anti-vacuity
  instance BRIEF_005 required of itself, and the reason this brief is not
  bookkeeping.

What is *recorded as not machine-checked*, and said out loud in the module header
the way BRIEF_004/005 say it: that the CGMY exponent exists, is affine in `τ`, and
satisfies the decay hypothesis of §"Goal" on the pricing contour. That is item 1–2
of the kit — the `cpow`/branch work BRIEF_005 deferred and named — and it is
BRIEF_011.

## Goal

New module `ImprovedBS/Pricing.lean` (namespace `BSM`), proving for a probability
measure `μ` on `ℝ` (the law of `X = log(S_T/S)`), `0 < S`, `0 < α`, real
`r, τ, k`:

1. **The pricing kernel.** `cmPriceKernel` — the Carr–Madan kernel on the contour
   the price actually inverts from, `v = u − i(α+1)` — plus its relation to
   BRIEF_005's kernel (an exact shift) and its absolute integrability, by reuse.
2. **The strike transform**, free of any model:

       ∫_ℝ e^{iuk} · e^{αk} · (S e^x − S e^k)⁺ dk = S · e^{x(α+1+iu)} / cmDenom(α,u)

   with `cmDenom α u = (α + iu)(α + 1 + iu)` *factored* (the tree only has the
   quartic expansion; the factorization is what makes the denominator's provenance
   a theorem rather than a definition).
3. **The transform of the damped price** by Fubini:

       ∫_ℝ e^{iuk} · dampedPrice(k) dk = e^{−rτ} · S · contourCharFun μ (u − i(α+1)) / cmDenom(α,u)

   where `dampedPrice(k) = e^{αk} · e^{−rτ} · ∫ (S e^x − S e^k)⁺ ∂μ`.
4. **The inversion**, in the tree's own Carr–Madan normalization (the one the
   oracle and `carrMadanInversion` use — `(2π)⁻¹` and phase `e^{−iuk}`, *not*
   mathlib's unitary `𝓕`), obtained from `Continuous.fourierInv_fourier_eq` by the
   one-line substitution `u = −2π w`.
5. **T6's triangle at an arbitrary strip law:** the Carr–Madan integral equals the
   discounted expectation, is real-valued, and lands on BRIEF_009's model-free
   layer — so parity and the no-arbitrage bounds come free by instantiation, which
   is item 5's promise being cashed.
6. **The GBM instance through the new route**, i.e. `gbm_carrMadan_eq_bsCall`,
   re-deriving BRIEF_007/008's landing and completing the triangle at the lognormal
   law.

## Hypotheses, stated once (the re-scope, in full)

For the main theorem, with `μ` a probability measure, `S > 0`, `0 < α`:

* **(H-decay)** — the model side, BRIEF_005's hypothesis moved to the pricing line:
  `Continuous (fun u => contourCharFun μ (↑u − ↑(α+1)·I))` **and**
  `∀ u, u₀ ≤ |u| → ‖contourCharFun μ (↑u − ↑(α+1)·I)‖ ≤ D · Real.exp (−c·|u|^Y)`
  with `0 < c`, `0 < Y`, `0 ≤ D`. This is what makes the integral *absolutely*
  convergent, and it is exactly BRIEF_005's statement with the contour shifted —
  no new analysis.
* **(H-moment)** — the law side: `Integrable (fun x => Real.exp ((α+1) * x)) μ`,
  the moment at the contour's level (the "numéraire-shifted" point of `docs/03`
  §D1 item 2). It is what the Fubini exchange costs, and nothing more; the
  continuity of `u ↦ contourCharFun μ (↑u − ↑(α+1)·I)` is **proved from it**, not
  assumed.
* **(H-tail)** — `Integrable (fun x => Real.exp ((α+1+δ) * x)) μ` for some
  `δ > 0`. This is the only place a *strictly larger* moment is needed, and it is
  used for exactly one thing: the side conditions of the inversion theorem
  (`Integrable f`, `Integrable (𝓕 f)`). The implication
  `(H-tail) ⟹ Integrable (dampedPrice)` is a **lemma** in this brief, not a
  hypothesis (Hölder against `E[e^{(α+1+δ)X}]` plus Markov; the arithmetic is in §2).

Satisfiability, recorded rather than asserted: GBM satisfies (H-decay) with
`Y = 2` by BRIEF_005's `gbmCharFactor_contour_norm` at the shifted parameter (the
lemma's `α` is a free real), and satisfies (H-moment)/(H-tail) for every `α > 0`.
CGMY satisfies all three under `α + 1 < min(G, M)` — the condition under which
`(M − iv)^Y` and `(G + iv)^Y` stay in the principal branch along the whole contour
— with the measured decay in §"The numeric route-check".

## Scope (numbered)

### §1 The pricing kernel and its integrability — `ImprovedBS/Pricing.lean` (5 declarations)

1. `cmPriceKernel (φ : ℂ → ℂ) (α u : ℝ) : ℂ := φ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹`.
2. `cmPriceKernel_eq_shift (φ α u) : cmPriceKernel φ α u = carrMadanKernel (fun v => φ (v - ↑(2 * α + 1) * Complex.I)) α u` — the correction, as an identity.
3. `contourCharFun (μ : Measure ℝ) (v : ℂ) : ℂ := ∫ x, Complex.exp (Complex.I * v * ↑x) ∂μ` — the analytic continuation of the characteristic function, defined on the contour (the general-law twin of `gbmCharFactor`).
4. `gbm_contourCharFun_eq : contourCharFun (ProbabilityTheory.gaussianReal m v) w = gbmCharFactor m (v / 2) w` — the tie that lets §5 instantiate BRIEF_005/007/008 without a second convention.
5. `cmPriceKernel_integrable` — `(H-decay)` at `↑u - ↑(α+1)*I` gives `Integrable (cmPriceKernel φ α)`, obtained from `carrMadanKernel_integrable` through `cmPriceKernel_eq_shift` (the bound is in `|u|`, which the shift does not move), **plus** `gbm_cmPriceKernel_integrable` as the machine-checked instance.

### §2 The strike transform (5 declarations)

6. `cmDenom_factor (α u : ℝ) : cmDenom α u = ((α : ℂ) + ↑u * Complex.I) * ((α + 1 : ℂ) + ↑u * Complex.I)` — the factorization, by `ring`.
7. `integral_Ioi_cexp_neg_mul_eq_inv {a : ℂ} (ha : 0 < a.re) : ∫ y in Set.Ioi 0, Complex.exp (-(a * ↑y)) = a⁻¹` — the one Laplace integral the substitution needs. Route: the antiderivative `y ↦ -a⁻¹ * Complex.exp (-(a * ↑y))` with `integral_Ioi_of_hasDerivAt_of_tendsto` ✓ (`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`: `hcont`, `hderiv`, `IntegrableOn f' (Ioi a)`, `Tendsto f atTop (𝓝 m)`, conclusion `∫ x in Ioi a, f' x = m - f a`; the primed variant drops the continuity side goal) — **not** `integral_cpow_mul_exp_neg_mul_Ioi`, which at the tag takes a *real* exponent `r` and would need a second analytic-continuation argument.
8. `strikeTransform (S α x u : ℝ) : ℂ := ∫ k : ℝ, Complex.exp (Complex.I * ↑(u * k)) * ↑(Real.exp (α * k)) * ↑(max (S * Real.exp x - S * Real.exp k) 0)`.
9. `strikeTransform_eq {S x u α : ℝ} (hS : 0 ≤ S) (hα : 0 < α) : strikeTransform S α x u = ↑(S * Real.exp (x * (α + 1))) * Complex.exp (↑(x * u) * Complex.I) * (cmDenom α u)⁻¹` — substitute `k = x − y`, split the payoff, apply item 7 twice (`0 < α`, `0 < α+1`), factor by item 6.
10. `integrable_strikeTransform` — the domination `|e^{iuk} e^{αk} (S e^x − S e^k)⁺| ≤ S e^x e^{αk} 1_{k<x}`, whose `k`-integral is `S e^{(α+1)x} / α`; this is the bound §3's Fubini exchange consumes.

### §3 The damped price and its transform (5 declarations)

11. `dampedModelFreeCall (μ : Measure ℝ) (S r tau α k : ℝ) : ℝ := Real.exp (α * k) * (Real.exp (-r * tau) * ∫ x, max (S * Real.exp x - S * Real.exp k) 0 ∂μ)` — BRIEF_008's `dampedCallPrice` with the law general.
12. `dampedModelFreeCall_eq_dampedCallPrice` — at `μ = gaussianReal m v` the two agree **by definition**, which is the compatibility claim that lets §5 land on BRIEF_007/008.
13. `continuous_dampedModelFreeCall` — continuity in `k`, from `(H-moment)` by dominated convergence.
14. `integrable_dampedModelFreeCall_of_exp_moment {δ : ℝ} (hδ : 0 < δ) (h : Integrable (fun x => Real.exp ((α + 1 + δ) * x)) μ)` — `(H-tail) ⟹ Integrable (dampedModelFreeCall …)`. Proof: on `k ≤ 0` dominate by `S e^{αk} E[e^X]` (finite because `e^x ≤ 1` where `x ≤ 0` and `e^x ≤ e^{(α+1)x}` where `x > 0`, against a probability measure); on `k > 0` use Hölder against `E[e^{(α+1+δ)X}]` and Markov's `P(X > k) ≤ e^{−(α+1+δ)k} E[e^{(α+1+δ)X}]`, giving `≤ C e^{−δk}`. This lemma is the *only* consumer of `δ`.
15. `fourierDampedModelFreeCall_eq {μ} [IsProbabilityMeasure μ] (hα : 0 < α) (h : Integrable (fun x => Real.exp ((α + 1) * x)) μ) : ∫ k, Complex.exp (↑(u * k) * Complex.I) * ↑(dampedModelFreeCall μ S r tau α k) = ↑(Real.exp (-r * tau) * S) * contourCharFun μ (↑u - ↑(α + 1) * I) * (cmDenom α u)⁻¹` — write the price as an integral, exchange with `MeasureTheory.integral_integral_swap` ✓ (`Mathlib/MeasureTheory/Integral/Prod.lean`, hypothesis `Integrable (uncurry f) (μ.prod ν)`; discharge by item 10), apply `strikeTransform_eq`, and identify the `x`-integral with `contourCharFun`. **This is the theorem that was missing**: `𝓕(damped price) = the kernel`.

### §4 Inversion in the tree's normalization (3 declarations)

16. `fourierCM (f : ℝ → ℂ) (u : ℝ) : ℂ := ∫ k, Complex.exp (Complex.I * ↑(u * k)) * f k` — the non-unitary Carr–Madan transform, named so that "which convention" is never implicit again.
17. `fourierCM_eq_fourier (f u) : fourierCM f u = 𝓕 f (-u / (2 * Real.pi))` — `∫ e^{iuk} f k` vs mathlib's `∫ e^{−2πi·w·k} f k` at `w = −u/(2π)`: complex-exponential algebra and `Complex.exp` addition only.
18. `fourierCM_inversion {f : ℝ → ℂ} (hcont : Continuous f) (hint : Integrable f) (hFint : Integrable (𝓕 f)) (k : ℝ) : ((2 * Real.pi)⁻¹ : ℂ) * ∫ u, Complex.exp (-(Complex.I * ↑(u * k))) * fourierCM f u = f k` — from `Continuous.fourierInv_fourier_eq` (already in the tree) by the substitution `u = −2π w`, i.e. `MeasureTheory.Measure.integral_comp_mul_left` ✓ (`Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`: `(∫ x, g (a * x)) = |a⁻¹| • ∫ y, g y`, no side conditions) at `a = −2π`, where `|a⁻¹| = (2π)⁻¹` supplies exactly the constant. The `2π` bookkeeping is the one thing to get wrong here, so the oracle checks it numerically at the round trip (§"The numeric route-check").

### §5 T6's triangle at the general law (8 declarations)

19. `cmPriceIntegral (φ : ℂ → ℂ) (α r tau S k : ℝ) : ℂ := ↑(Real.exp (-r * tau) * S / (2 * Real.pi)) * ∫ u, Complex.exp (-(Complex.I * ↑(u * k))) * cmPriceKernel φ α u` — the pricing integral in the tree's normalization, so that item 21 is `carrMadanInversion`'s *corrected* shape and not a third convention.
20. `cmPriceIntegral_eq_damped_modelFreeCall {μ} [IsProbabilityMeasure μ]` — with `0 < α`, `(H-decay)`, `(H-tail)`:

        cmPriceIntegral (contourCharFun μ) α r τ S k = ↑(dampedModelFreeCall μ S r τ α k)

    Proof: item 15 turns the kernel into `𝓕 (damped price)`, item 18 inverts.
21. `carrMadan_eq_modelFreeCall (S K tau r q sigma …)` — the undamped form at `k = Real.log (K / S)`:

        Real.exp (-α * Real.log (K / S)) • cmPriceIntegral (contourCharFun μ) α r τ S (Real.log (K / S))
          = ↑(modelFreeCall μ (fun x => S * Real.exp x) K r tau)

    landing on **BRIEF_009's** `modelFreeCall`, so parity and the no-arbitrage bounds
    at the new law are inherited by instantiation — item 5's claim, discharged by
    this line.
22. `cmPriceIntegrand_reflect : Complex.exp (-(Complex.I * ↑((-u) * k))) * cmPriceKernel (contourCharFun μ) α (-u) = (Complex.exp (-(Complex.I * ↑(u * k))) * cmPriceKernel (contourCharFun μ) α u).conj` — the integrand is Hermitian-symmetric **at every law with real support**, not just the Gaussian one: the `e^{(α+1)x}` weight the contour carries is real, and `cmDenom α (-u) = conj (cmDenom α u)`. Consequence, and the reason it is in scope: the half-line representation the oracle uses (`2·∫_0^{u_max}` for the two-sided integral) is *exact at any law*, and the real-valuedness of the inversion integral has a second, independent proof.
23. `carrMadan_im_eq_zero`, 24. `carrMadan_eq_re`, 25. `carrMadan_re_eq_modelFreeCall` — the real-valuedness trio of BRIEF_008 §4, restated at the general law (both routes available: the identity with a real number, and item 22).
26. `gbm_carrMadan_eq_bsCall (S K tau r q sigma) (hS) (hK) (htau) (hsigma) (v : NNReal) (hv : (v : ℝ) = sigma ^ 2 * tau) (α) (hα : 0 < α) : cmPriceIntegral (contourCharFun (gaussianReal ((r - q - sigma^2/2) * tau) v)) α r tau S (Real.log (K / S)) = ↑(bsCall S K tau r q sigma)` — **T6's triangle, closed**: the closed form (BRIEF_008's `carrMadan_inversion_eq_bsCall`), the discounted expectation (BRIEF_007) and the inverted Carr–Madan integral (this brief) now meet in one statement, with the kernel route proved rather than assumed. Instantiating (H-decay) here uses `gbmCharFactor_contour_norm` at the shifted parameter and `gbm_contourCharFun_eq`.

### §6 Grading wiring (the repo motion)

* **Doc-comment corrections** (`Fourier.lean`, `Inversion.lean`): the two module
  headers and `carrMadanKernel`'s doc comment stop calling `φ(u + iα)` the pricing
  contour and name `cmPriceKernel` for it; `carrMadanInversion`'s doc comment
  records that its shape (not its correctness) is the shifted one. Comments are
  stripped by `scripts/pin_statements.py`, so this is free under the pins and the
  108 pre-existing entries stay byte-identical — the audit trail for the change is
  the ledger row and C12, not a pin diff.
* **`[CONTOUR]` route check** in `scripts/lean_lint.py`: the new module's kernel
  must be defined with `- ↑(α + 1) * Complex.I` (and not `+ ↑α * Complex.I`), and
  `cmPriceIntegral` must be the thing `carrMadan_eq_modelFreeCall` consumes; with
  a cheat seeded in `tests/test_lint.py` (28th mutant) so the check is itself
  falsified. This is the BRIEF_009 `[SKELETON]` pattern, one layer down: the route
  that would silently produce a different theorem gets a named check.
* **Oracle** (`experiments/black_scholes.py`): `carr_madan_by_law(probs, spots, S, r, tau, alpha, k, u_max, n)` — the inversion at an *arbitrary discrete* law, reusing `model_free_prices`' conventions; and mutant **M15** (contour swap in `bs_call_by_fourier_inversion`: `v = complex(u, +alpha)`), killed by the *existing* `test_fourier_inversion` alone, and mutant **M16** (the `−(α+1)` shift off by one in `carr_madan_by_law`), killed by the new `test_carr_madan_free_law` alone.
* **`tests/test_bs.py`**: `test_carr_madan_free_law` (16th test) — inversion vs
  `model_free_prices` at three laws (skewed, left-heavy, symmetric) and the
  degenerate one-atom law, the imaginary part via the two-sided integral, and
  rejection of `α ≤ 0`. The measured accuracy is a *discrete* law's, not GBM's
  (§"The numeric route-check"), so the tolerance is `1e-4`, not `2e-11`, and the
  test says why in its docstring.
* **`tests/test_mutants.py`**: 13 → 15 mutants.
* Pins: 108 → 108 + N in both layers, with the new entries appended and the 108
  pre-existing entries byte-identical. `deferred: {}` untouched (no `sorry`).
* Docs: `docs/04`'s queue row and its "BRIEF_010+ are not yet issued" paragraph;
  `docs/03` §D1 item 4's status line; `benchmarks/LEDGER.md` C12 and the row for
  this PR; `README.md`'s status table gains the T6-at-a-general-law line.

## The numeric route-check (measured before any Lean — ledger C4)

Run in-sandbox on 2026-09-21 against `experiments/black_scholes.py`, pure stdlib
(no numpy/scipy in this environment; the oracle needs none). Scratch script, not
committed: the brief records the numbers, the oracle test is the permanent
artifact.

| check | result |
|---|---|
| closed form vs oracle's contour `u − i(α+1)` | `7.112102348131366` vs `7.112102348131359`, rel **9.99e-16** |
| closed form vs the tree's contour `u + iα` | `1.819563153701569`, rel **7.44e-01** |
| `∫ e^{iuk}f(k)dk` vs `e^{−rτ}Sφ(u−i(α+1))/cmDenom` | rel **1.16e-16 / 5.38e-16 / 8.16e-16** at `u = 0, 0.7, −2` |
| the same vs `φ(u+iα)` | rel **1.28e-01 / 2.25e-01 / 5.41e-01** |
| strike transform `∫ e^{iuk}e^{αk}(e^x−e^k)⁺dk` vs `e^{x(α+1+iu)}/cmDenom` | rel **2.96e-09 / 2.31e-07 / 2.23e-08** (quadrature-limited; the identity is exact) |
| CGMY decay on the pricing line, `C=1, G=5, M=10, Y=0.7, τ=1, α=1` | `−Re ψ(u−i(α+1))/|u|^Y → 3.731206` at `u = 2000` vs `τC\|Γ(−Y)·2cos(πY/2)\| = 3.880411`, converging from below; `Y = 1.5`: `3.324485` vs `3.342171`; `Y = 1.9`: `10.977684` vs `10.989919` (`Γ(−0.7) = −4.273670`; `Γ(−Y)` and `cos(πY/2)` flip sign together at `Y = 1`, so `c > 0` on all of `(0,2)`) |
| the same on the tree's line | `3.731207` — identical to leading order, which is why the defect was invisible |
| free-law inversion vs `model_free_prices`, skewed 3-atom law (`0.5/80, 0.3/105, 0.2/160`, `K=110, α=1.2, u_max=800, n=20000`) | `9.704687774395` vs `9.704455335485`, rel **2.40e-05**, imaginary part **3.0e-14**; the error is truncation, and a discrete law's characteristic function does not decay — hence the `1e-4` tolerance above |
| the half-line shortcut at the same law | real parts agree to **1.0e-14** relative, confirming `cmPriceIntegrand_reflect` — and its *imaginary* part is `−1.4e+01`, i.e. the oracle's `.re` is load-bearing, not cosmetic (this doubling was expected to *fail* before the check; the measurement is why the mutant is M16 and not a doubling mutant) |
| mutant magnitudes | M15 (contour swapped to `u + iα`): rel **7.44e-01**; M16 (`−(α+1)` shifted to `−α` in the free-law route): rel **3.75e-01** — both far outside their tests' tolerances (`2e-11`, `1e-4`) |

## Done looks like (acceptance — machine-graded)

- `lake build` green; `#print axioms` of all new theorems reports exactly
  `[propext, Classical.choice, Quot.sound]` (added to `.github/workflows/lean.yml`).
- Statement pins: source layer 108 → 108 + N with the 108 existing entries
  **byte-identical**; `elab` layer committed on the second run via `--elab-merge`.
- `scripts/lean_lint.py` green, including the new `[CONTOUR]` check;
  `tests/test_lint.py` 7/7 with the new cheat killed by name.
- `tests/test_bs.py` 16/16; `tests/test_mutants.py` 4/4 with 15 mutants, M15 killed
  by `test_fourier_inversion` alone and M16 by `test_carr_madan_free_law` alone.
- `tests/test_pins.py` and `tests/test_crosscheck.py` unchanged and green.
- No existing theorem changed or weakened; no `sorry`; `deferred: {}` untouched.
- **The correction is recorded, not edited away**: C12 in `benchmarks/LEDGER.md`
  states what was wrong, why no pinned statement moves, and what now guards it;
  `README.md`, `docs/03`, `docs/04` updated as in §6.

## Explicitly out of scope (and where each goes instead)

- **The CGMY exponent itself** (kit items 1–2: the concrete `exp(τ·C·Γ(−Y)·[(M−iv)^Y − M^Y + (G+iv)^Y − G^Y] + iv·drift)` as a `def`, its continuity on the pricing contour for `0 < α`, `α + 1 < min(G, M)`, and the decay `(H-decay)` with its own `Y`) — **BRIEF_011**. This brief pins the target's shape and the numbers it must reproduce; it asserts nothing about CGMY. Tag-verified tools for it are recorded here so the next brief does not re-derive them: `Complex.continuousAt_cpow {p : ℂ × ℂ} (p.fst ∈ slitPlane)` and `continuousAt_cpow_const_of_re_pos` ✓ (`Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean` — note the tag's `slitPlane`), `Real.Gamma : ℝ → ℝ` / `Complex.Gamma` / `Real.Gamma_pos_of_pos` ✓ (`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`), and `integral_cpow_mul_exp_neg_mul_Ioi` ✓ (same file, real exponent only — recorded because it is the tempting near-miss for §2 item 7).
- **The drift condition at the new law** and the CGMY twin of
  `integral_spot_mul_phi_eq_forward` (kit item 3): not needed here — the pricing
  identity is drift-free, and BRIEF_009's `model_free_put_call_parity` is where a
  drift enters — and the concrete law's version belongs with BRIEF_011.
- **GBM as the corner `Y → 2`** (kit item 6): convergence of prices remains a
  recorded deferral.
- Any change to `bsCall`/`bsPut`/T1–T5, any new third-party Python dependency, any
  `sorry`, and any edit to `carrMadanKernel`, `carrMadanInversion` or a landed
  statement.

## Why this is worth a brief (and shaped this way)

Item 4 was queued as "the full pricing claim where no closed form exists", and the
temptation is to write it as a restatement of BRIEF_008 with `bsCall` deleted from
the right-hand side. This brief is not that, for a reason the numeric check found
before any Lean: **the object the tree calls the pricing kernel is not the pricing
kernel**, and a brief that had reused it would have proved a false identity with a
green build — the C1-item-1 failure mode (true by construction, certifying nothing)
in its identification-level form. The correction is two lines of prose, one shift
identity, and one route check; the *theorem* that was actually missing is the
strike transform plus the Fubini exchange, because that is what turns "the inverse
Fourier transform of the damped price" into "the Carr–Madan integral of `φ`" — and
it is exactly the step that only becomes visible when the closed form is removed.

The re-scope is what makes the brief landable *and* honest: the pricing identity is
law-agnostic, so it is stated once at an abstract `φ` with the CGMY step recorded as
the one hypothesis it is, and the GBM instance closes T6's triangle through the new
route so the abstraction is non-empty. Item 4's real risk — the exponent↔law
connection — is named as BRIEF_011 and given its shape, its strip condition and its
measured decay, which is the most useful thing this brief can do about a step it
does not take.
