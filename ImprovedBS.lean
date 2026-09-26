import ImprovedBS.Core
import ImprovedBS.Levy
import ImprovedBS.Fourier
import ImprovedBS.RiskNeutral
import ImprovedBS.Inversion
import ImprovedBS.Skeleton
import ImprovedBS.Pricing
import ImprovedBS.CGMY
import ImprovedBS.NonUniqueness
import ImprovedBS.Esscher
import ImprovedBS.Corner
import ImprovedBS.ParetoWitness
import ImprovedBS.VGLaw
import ImprovedBS.CompoundPoisson
import ImprovedBS.CGMYLaw

/-!
# ImprovedBS

Root module of the `ImprovedBS` library. Modules imported here are built by
`lake build`.

* `ImprovedBS.Core` — the BSM closed form and the theorem stack T1..T6.
* `ImprovedBS.Levy` — BRIEF_004: the moment obstruction (T6 sub-goal 1). §1 is
  analysis (a polynomial tail lower bound forces an infinite exponential
  moment), §2 is the modelling claim that consumes it (`E[S_T] = ∞`, hence no
  equivalent martingale measure in the exponential-Lévy ansatz).
* `ImprovedBS.Fourier` — BRIEF_005: absolute convergence of the tempered
  Carr–Madan contour (T6 sub-goal 2). §1 is the two-sided tempered-tail
  integrability, §2 the exact quartic lower bound of the strike-transform
  denominator, §3 the joining domination argument, §4 the fully
  machine-checked GBM instance of classical Fourier pricing.
* `ImprovedBS.RiskNeutral` — BRIEF_007: the closed form is the discounted
  risk-neutral expectation (T6 sub-goal 3a). §1 is the Gaussian bridge that
  identifies `phi`/`Phi` with mathlib's `gaussianPDFReal 0 1`/`gaussianReal 0 1`
  without touching the pinned definitions, §2 the tilted Gaussian integrals,
  §3 the payoff as the indicator of the exercise region, §4 the call and put
  identities, the drift condition and the same identity against mathlib's
  standard-normal and lognormal laws.
* `ImprovedBS.Inversion` — BRIEF_008: Fourier inversion of the Carr–Madan pricing
  kernel (T6 sub-goal 3b). §1 is the Fourier pricing integral and its integrability,
  §2 the damped call price and lognormal expectation, §3 the Fourier inversion formula
  via mathlib's `Continuous.fourierInv_fourier_eq` / `Integrable.fourierInv_fourier_eq`,
  §4 the main theorems landing on `bsCall_eq_lognormal_expectation` and real-valuedness.
* `ImprovedBS.Skeleton` — BRIEF_009: the model-free skeleton. §1–2 the
  price-by-expectation operators `modelFreeCall`/`modelFreePut` and payoff
  integrability, §3 parity at any terminal-spot law with the drift condition,
  §4 the no-arbitrage bounds and their put twin through parity, §5 the GBM
  instance (`lognormal_parity_gap`, `lognormal_call_bounds`), §6 the T2′/T4
  re-derivations (`*_via_skeleton`) that grade the abstraction for vacuity.
* `ImprovedBS.Pricing` — BRIEF_010: T6 at any strip law. §1 the pricing kernel
  `cmPriceKernel` on the corrected contour `v = u − i(α+1)` (C12) and its
  integrability by reuse of `carrMadanKernel_integrable`, §2 the strike
  transform (model-free) and its factorization `cmDenom_factor`, §3 the damped
  price and its Fourier transform by Fubini, §4 inversion in the tree's own
  normalization `fourierCM`, §5 the triangle at a general law landing on
  `modelFreeCall` and the GBM instance `gbm_carrMadan_eq_bsCall` closing the
  triangle through the kernel route.

* `ImprovedBS.CGMY` — BRIEF_011: BSM-2 kit items 1–2, the concrete CGMY
  characteristic exponent and its moment strip. §1 the exponent
  `Γ(−Y)[(M − iv)^Y − M^Y + (G + iv)^Y − G^Y]`, the pricing/old contours and the
  four decay constants, §2 affine-in-τ and the two bases on the corrected
  contour, §3 the sign `Γ(−Y) cos(πY/2) < 0` on `(0,2) \ {1}`, §4 the pointwise
  cpow estimates on both regimes (sharp cos for `Y < 1`, mean value for
  `Y ≥ 1`), §5 the contour bound `Re ψ ≤ −r|u|^Y + c'|u|^{Y−1} + K₀` and the
  threshold that turns it into BRIEF_010's (H-decay), §6 continuity and the
  instantiation `cgmy_cmPriceKernel_integrable`, §7 the moment strip
  (`cgmyExponent_strip`, the numéraire condition `1 < M`) and the Lévy measure
  (`∫ (1 ∧ x²) ν < ∞`). Correction C14 lives here: the pricing line's condition
  is `α + 1 < M` alone — `G` constrains only the old line `u + iα`.
* `ImprovedBS.NonUniqueness` — BRIEF_012: BSM-2 kit item 7, the machine-checked
  non-uniqueness witness. §1 the three-point law `trinomialMeasure` (mass,
  integral as a finite sum, a.e. at the atoms, `≪` between two such laws),
  §2 the witness laws A `(1/2, 1/4, 1/4)` and B `(1/4, 5/8, 1/8)` on the spots
  `(1/2, 1, 2)`: probability, integrability, drift `E[S_T] = 1`, calls `1/4`
  and `1/8`, §3 BRIEF_009's parity and bounds instantiated at both (cited, not
  re-derived — the `[NONUNIQ]` check), §4 the headline conjunction
  `static_skeleton_does_not_select_measure` (A ≠ B, A ~ B, both drifts, both
  parities, both bound pairs, `modelFreeCall A ≠ modelFreeCall B`), §5 the
  martingale segment (★) `p₃ = p₁/2, p₂ = 1 − 3p₁/2` with the call `p₁/2`
  sweeping `[0, 1/3]`, and A, B as its points `p₁ = 1/2`, `p₁ = 1/4`.
* `ImprovedBS.Esscher` — BRIEF_013: BSM-2 kit item 3, the named pricing
  measure at CGMY, landed at the characteristic-factor level (re-scope note in
  the module header: the tree has no CGMY law as a `Measure ℝ`). §1 the
  Esscher shift `ψ^θ(v) = ψ(v − iθ) − ψ(−iθ)` for a general `ψ` and the family
  closure `(G, M) ↦ (G+θ, M−θ)` (derived, not defined — the `[ESSCHER]`
  check), §2 the cumulant `κ(u) = ψ(−iu)` on the real section and its strict
  convexity (`Γ(−Y)·Y(Y−1) = Γ(2−Y) > 0` — no case split on `Y ≷ 1`), §3 the
  drift map `g(θ) = κ(θ+1) − κ(θ)`: antisymmetry about `θ₀ = (M−G−1)/2`,
  strict monotonicity on `[−G, M−1]`, edge values `±H`, and the headline pair
  `esscher_exists_unique_of_mem_range` / `esscher_no_solution_of_outside_range`
  (the strip decides solvability: exactly one `θ` for `|r−q| < H`, none
  otherwise; the admissible interval is nonempty exactly when `1 < G + M`),
  §4 the drift condition at factor level `esscher_drift_factor`, §5 pricing at
  the Esscher measure by CONSUMING `cgmy_cmPriceKernel_integrable` at the
  shifted rates with the tilted condition `α + 1 < M − θ` (C14 at
  `(G+θ, M−θ)`).
* `ImprovedBS.Corner` — BRIEF_014: BSM-2 kit item 6, the normalized CGMY → GBM
  corner, as a ONE-SIDED limit at the characteristic-exponent level. Correction
  C17 lives here: the bare "CGMY = GBM at `Y = 2`" statement of the old
  `docs/03` is false — `Γ(−Y)` has a pole there, so at fixed `C` the bracket's
  limit is multiplied by something that diverges. §1 the variance
  normalization `C_Y = (σ²/2)(2−Y)` and the forward exponent
  `Ψ_Y = ψ_Y + i(r−q−κ_Y(1))v` (defined from the CGMY data, not from the GBM
  answer), §2 the pole cancellation `ε Γ(−Y) = Γ(3−Y)/(Y(Y−1))` — one
  `Real.Gamma_add_one` past BRIEF_013's `cgmyGamma_two_sub_eq` — giving the
  finite `C_Y Γ(−Y) → σ²/4`, §3 the pointwise bracket and exponent limits (3)
  on the strip `−M < Im v < G`, §4 route A: the cumulant limit, the exact
  numéraire `Ψ_Y(−i) = r−q` and the convergence (6)–(7) of the exponent and of
  the factor to BRIEF_005's own `gbmCharFactor`, §5 route B: at the named
  `θ₀ = (M−G−1)/2` the BRIEF_013 shift alone delivers the zero-carry GBM limit
  (8) with no drift correction, plus the collapse (9) of the attainable
  half-width `H` to `(σ²/2)(G+M−1)`.
* `ImprovedBS.ParetoWitness` — BRIEF_015 (ledger C13 finding 3): the witness
  for `ImprovedBS.Levy`'s tail hypothesis. §1 the Pareto tail
  `μ[x, ∞) = t^r · x^(−r)` for mathlib's own `paretoMeasure`, §2 the discharge
  of `htail` with equality at `c = t^r, α = r, x₀ = t`, §3 the obstruction
  instantiated BY CITATION, ledger C7 as a theorem (`α ≤ 0` is unsatisfiable)
  and the headline `levy_tail_hypothesis_satisfiable_iff : (∃ law, htail) ↔
  0 < α`, §4 the discriminator: the Dirac mass fails `htail` and has a finite
  exponential moment.
* `ImprovedBS.VGLaw` — BRIEF_018: the variance-gamma law, the family's `Y = 0`
  member and the tree's first CGMY-family probability measure. §1 the law as
  the difference of two `gammaMeasure`s, §2 the Gamma mgf rung consuming
  `integral_rpow_mul_exp_neg_mul_Ioi`, §3 the law's mgf `exp(τ · κ₀)` on the
  strip `(−G, M)`, §4 the `Y ↓ 0` corner as a `𝓝[>] 0` limit (never an
  evaluation — `Real.Gamma 0 = 0`), §5 the Esscher tilt by `withDensity` with
  the numéraire derived from `esscher_tilted_numeraire`, §6 items 3 and 5 at
  the tilted law. Stage 2 (general `Y`) and G1 (complex-rate Γ integral) stay
  open.
* `ImprovedBS.CompoundPoisson` — BRIEF_019 (Stage 2a): the compound-Poisson law
  and the truncated CGMY jump law. §1 the Poisson mixture of additive
  convolution powers `cpLaw λ ρ = ∑ₙ pₙ · ρ^{*n}` — finite by `finite_of_finite_mconv`'s
  additive twin, a probability measure with mass `∑ₙ pₙ = 1`, and characteristic
  function `exp (λ (φ_ρ − 1))` via the shipped sum/integral exchange
  (`integrable_sum_measure`, `integral_sum_measure`) and `charFun_conv`. §2 the
  truncated CGMY jump measure `ν_ε = (volume.restrict {ε ≤ |x|})·cgmyLevyDensity`
  with its finite mass (`cgmyJumpMass_lt_top`, consuming the landed
  `cgmy_levy_far_moment` for both tails), positive mass, normalised jump law
  `ν_ε/λ_ε`, and the truncated exponent
  `A_ε(v) = ∫_{|x| ≥ ε} (e^{ivx} − 1) ν(dx)` as an honest Bochner integral
  (`cgmyTruncatedExponent_integrable`, dominated by `2ν`), with the marginal
  identity `charFun (cpLaw (τ λ_ε) (ν_ε/λ_ε)) t = exp (τ A_ε(t))`.
* `ImprovedBS.CGMYLaw` — BRIEF_020 (Stage 2b): the CGMY law. §1 the exact
  decomposition `A_ε = B_ε + iv·d_ε` of the truncated exponent into the
  compensated integral over `{ε ≤ |x|}` and the *paired* drift
  `C∫_ε^1 x^{−Y}(e^{−Mx} − e^{−Gx})` (ledger C25), its `ε ↓ 0` limit — two
  `tendsto_setIntegral_of_monotone`s, no dominated convergence — to the
  Lévy–Khintchine exponent `cgmyLKExponent`, and the exponent's continuity.
  §2 the law: `cgmyLaw` is `Filter.limUnder atTop` of the compound-Poisson
  marginals along `εₙ = 2⁻ⁿ`, made honest by `cgmyLaw_exists` (tightness from
  `isTightMeasureSet_of_tendsto_charFun`, Prokhorov, a convergent subsequence,
  Lévy continuity), with `charFun cgmyLaw t = exp (τ L(t))` on all of
  `0 < Y < 2` and uniqueness by `Measure.ext_of_charFun`. §3 G1, the
  complex-rate Γ integral `∫₀^∞ x^{s−1}e^{−zx} = Γ(s) z^{−s}` on `Re z > 0` by
  the identity theorem anchored on the shipped real-rate lemma, the one-sided
  closed forms by one integration by parts each, the drift identity
  `C∫₀^∞ x^{−Y}(e^{−Mx} − e^{−Gx}) = CΓ(1−Y)(M^{Y−1} − G^{Y−1})`, and the
  identification `L = cgmyExponent` for `Y ≠ 1`, so that `cgmyCharFactor` is
  the characteristic function of a law in the tree
  (`charFun_cgmyLaw_eq_cgmyCharFactor`).

## Why the module is not called `Lean.*`

The formalization previously lived at `Lean/core/bsm_theorems.lean`. With the
library root at the repository root, that makes the module name
`Lean.core.bsm_theorems` — which squats the `Lean` namespace that the
elaborator, the `Lean.Elab` machinery and every tactic implementation live in.
Importing such a module into a file that also uses tactics is a source of
elaboration-order surprises that have nothing to do with the mathematics.
`scripts/lean_lint.py` fails CI if a `.lean` file reappears under a top-level
`Lean/` directory.

## Note on this file's shape

The `import` must come first. A module doc-comment — the bang form of Lean's
block comment — is a *command*, not a comment, so placing it above the `import`
produces

    error: invalid 'import' command, it must be used in the beginning of the file

which is exactly what the first CI run of this repository reported. Ordinary
block comments and line comments are fine before imports; doc-comments are not,
and neither is this file's previous shape.

(No literal comment delimiters are written in this docstring on purpose: Lean
block comments nest, and an unbalanced pair inside prose would close the
comment early and turn the rest of the file into syntax errors.)
-/
