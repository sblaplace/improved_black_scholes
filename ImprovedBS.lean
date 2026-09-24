import ImprovedBS.Core
import ImprovedBS.Levy
import ImprovedBS.Fourier
import ImprovedBS.RiskNeutral
import ImprovedBS.Inversion
import ImprovedBS.Skeleton
import ImprovedBS.Pricing
import ImprovedBS.CGMY
import ImprovedBS.NonUniqueness

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
