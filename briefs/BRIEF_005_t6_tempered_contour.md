# BRIEF_005 — T6 sub-goal 2: absolute convergence of the tempered Carr–Madan contour

- **Status:** ready to work (queue order per docs/04 §"The brief queue";
  BRIEF_004 landed GREEN, so the dependency is satisfied)
- **Prerequisite PRs:** BRIEF_004 (PR #5) merged — sub-goal 2 stands on the
  same Lévy footing, not on its theorems. No edits to `Core.lean`/`Levy.lean`.
- **Skills:** real/complex analysis in Lean 4 (measure theory: `Integrable`,
  `IntegrableOn`, improper one-sided integrals; a little complex algebra).
  No new mathematics beyond standard Carr–Madan boilerplate.
- **Budget:** CI-only verification, same posture as BRIEF_004 — expect the
  two-run pin arc (land green except a by-design red pins step that prints
  the `elab` block, then commit it verbatim) plus elaboration fixes. Every
  mathlib name below was checked against the **pinned tag v4.34.0** before this
  brief was committed (ledger C3's rule), with the file it lives in.

## Goal

docs/03 §D1 states T6 ("the Fourier pricing kernel survives a wider increment
law") as three provable sub-goals: (1) the α-stable moment obstruction, landed
as BRIEF_004; **(2) absolute convergence of the Carr–Madan integrand on a
contour strictly inside the moment strip, for a tempered-stable exponent**;
(3) agreement with the risk-neutral expectation. This brief is sub-goal 2.

The Carr–Madan call price is (up to provenance of the contour shift)

    V = e^{-rτ} / (2π) · ∫_ℝ e^{-iuτ} · φ(u + iα) / (α² + α − u² + i(2α+1)u) du

where `φ(·) = E[e^{i·(·)·X_τ}]` is the analytic continuation of the
log-price's characteristic function at maturity `τ`, defined on the moment
strip, and `α > 0` is the damping that keeps the strike transform finite.
Absolute convergence reduces to two independent facts:

* **payoff side (elementary, and exact):** the Carr–Madan denominator satisfies

      (α² + α − u²)² + ((2α+1)·u)² = u⁴ + (2α² + 2α + 1)·u² + (α² + α)²  ≥  u⁴

  — a polynomial identity, no asymptotics anywhere — so its inverse satisfies
  `‖denom(u)⁻¹‖ ≤ 1/u²` for `|u| ≥ 1`, with no zero on ℝ when `0 < α`;
* **model side (this is what tempering buys):** a tempered-stable
  characteristic function decays along horizontal lines like
  `|φ(u + iα)| ≤ D · exp(−c·|u|^Y)` with `c > 0`, `Y > 0` — sub-Gaussian, but
  integrable (the Gaussian is `Y = 2`, the relevant tempered range is
  `Y ∈ (0, 2)`, and every `Y > 0` works: the two-sided integral of
  `exp(−c|u|^Y)` is finite, value `2·b^{−1/Y}·Γ(1/Y + 1)`).

The theorem to land is the product: polynomial decay of the strike transform
times tempered decay of the model factor ⇒ an integrable pricing kernel.

## The hypothesis discipline (same posture as BRIEF_004, and say it out loud)

mathlib v4.34.0 has **no tempered-stable (CGMY) law**, exactly as it has no
symmetric α-stable law. BRIEF_004's answer was to take the power tail as a
*hypothesis* and say so; the same discipline applies here, one analytic layer
up:

* **MACHINE-CHECKED (the deliverable):** *if* a characteristic function `φ`
  is continuous along the contour `u ↦ u + iα` **and** satisfies the tempered
  decay bound there, *then* the Carr–Madan kernel
  `u ↦ φ(↑u + ↑α·I) · (denom α u)⁻¹` is integrable,
  the two-sided tempered tail `u ↦ exp(−c·|u|^Y)` is integrable (`0 < c`,
  `0 < Y`), and — as the witnessing instance — the **GBM model factor provably
  satisfies the hypothesis** (its contour modulus is exactly
  `C₀ · exp(−(σ²τ/2)·u²)`, `Y = 2`), so the classical Fourier-pricing kernel
  is integrable in this repository as a corollary, not as literature.
* **NOT MACHINE-CHECKED (hypothesis, cited):** that the CGMY characteristic
  function `exp(τ·C·Γ(−Y)·[(M−iv)^Y − M^Y + (G+iv)^Y − G^Y] + iv·drift)`
  satisfies the decay bound with its own `Y` on contours inside the strip.
  That is the genuinely hard analytic layer (`(M−iv)^Y` via complex `cpow`,
  branch control, Gamma asymptotics) and it is the *next* sub-goal; this
  brief must not smuggle it in. The PR description and module doc-comment
  state this plainly, mirroring BRIEF_004's "what is not machine-checked".

## Scope (numbered)

1. **`ImprovedBS/Fourier.lean`** — new module, `import Mathlib`, `namespace BSM`:
   1. `integrable_exp_neg_abs_rpow : Integrable fun u : ℝ => Real.exp (-c * |u| ^ Y)`
      for `0 < c`, `0 < Y`. Route (all names verified at v4.34.0, file in
      parentheses): `Iio ∪ Ici` split (`@Iio_union_Ici ℝ _ _⟩`,
      `integrableOn_union`, `integrableOn_Ici_iff_integrableOn_Ioi`);
      the right half is the `s = 0` case of
      `integrableOn_rpow_mul_exp_neg_mul_rpow`
      (`Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`);
      the left half is the negation transport idiom used by mathlib's own
      `integrable_rpow_mul_exp_neg_mul_sq`:
      `(Measure.measurePreserving_neg volume).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding` (same file).
   2. `cmDenom (α u : ℝ) : ℂ := ((α ^ 2 + α - u ^ 2 : ℝ) : ℂ) + (((2 * α + 1) * u : ℝ) : ℂ) * Complex.I`,
      with `cmDenom_normSq`, the expansion `= u^4 + (2*α^2 + 2*α + 1) * u^2 + (α^2 + α)^2`
      (`ring`), `cmDenom_ne_zero` for `0 < α` (the constant term
      `(α·(α+1))^2 > 0` kills the only possible zero, at `u = 0`), and
      `inv_cmDenom_norm_le : ‖(cmDenom α u)⁻¹‖ ≤ 1 / u ^ 2` for `1 ≤ |u|`
      (via `normSq` monotonicity of `Real.sqrt` and `‖z⁻¹‖ = ‖z‖⁻¹`).
   3. The kernel and the main theorem:
      `carrMadanKernel (φ : ℂ → ℂ) (α u : ℝ) : ℂ := φ (↑u + ↑α * Complex.I) * (cmDenom α u)⁻¹`;
      `carrMadan_integrable : Integrable (carrMadanKernel φ α) volume` under
      `0 < α`, contour continuity (`Continuous fun u : ℝ => φ (↑u + ↑α * Complex.I)`),
      and `hdecay : ∀ u, u₀ ≤ |u| → Complex.abs (φ (↑u + ↑α * Complex.I)) ≤ D * Real.exp (-c * |u| ^ Y)`.
      Route: `Integrable.mono'` against a piecewise dominating function —
      constant on `Icc (-w) w` (`w = max u₀ 1`, compact ⇒ bounded by
      continuity; `IsCompact.exists_forall_ge`) and `D · exp(−c|u|^Y)` off it
      (item 1.1) — assembled with `Set.indicator` and `Integrable.add`.
   4. **The witnessing instance (GBM):** for `φ_gbm(v) = Complex.exp (I*v*μτ − σ²τ/2 * v^2)`
      show `Complex.abs (φ_gbm (↑u + ↑α * I)) = exp ((σ²τ·α²/2) − α·μτ) * exp (−(σ²τ/2) * u^2)`
      — exact arithmetic on `z.re` under `Complex.abs_exp` — hence the
      hypothesis with `Y = 2` (via `sq_abs : |u| ^ 2 = u ^ 2`) and
      `carrMadanKernel φ_gbm` integrable. Discount/`2π`/phase factors ride
      `Integrable.smul` / bounded-multiplier lemmas
      (`Complex.abs_exp_ofReal_mul_I`-style: the phase `e^{iuτ}` has norm 1).
2. **Numerical route-check, recorded here before any Lean** (ledger C4's
   rule: break the route on numbers first). Measured on 2026-09-20:
   * `(α²+α−u²)² + ((2α+1)u)² − (u⁴ + (2α²+2α+1)u² + (α²+α)²) = 0`
     — max relative deviation 8.5e-16 over 2·10⁵ random `(α, u)` (float slack
     on an exact identity), and the lower coefficients satisfy
     `2α²+2α+1 = α² + (α+1)² ≥ 0`, `(α²+α)² ≥ 0`, so
     `‖denom‖² ≥ u⁴` always, with equality nowhere since the constant term
     vanishes only at `α ∈ {0, −1}` — which `0 < α` excludes.
   * ∫₀¹² `exp(−2·x^Y) dx` against `2^{−1/Y}·Γ(1/Y+1)`: `Y = 1, 1.5, 2`
     agree to ≤ 1.3e-11; `Y = 0.5` shows 3.9e-3 from the **trapezoid rule at
     a derivative-singular endpoint**, converging upward toward the closed
     form — recorded because it is the local warning that the `Y < 1` regime
     likes naive numerics less than it likes the Gamma value, and that `Y = 0`
     diverges for the elementary reason (integrand `≡ e^{−2} > 0`), matching
     "the strip is nonempty iff the tempered index is positive".
   * GBM contour modulus `|exp(i(u+iα)μτ − σ²τ(u+iα)²/2)|` vs
     `exp(σ²τα²/2 − αμτ) · exp(−(σ²τ/2)u²)`: max relative disagreement 7.3e-15
     over 2·10⁵ samples (`σ²τ/2 = 0.02`, `D ≈ 0.9888` at the test point).
3. **Grading wiring (the repo motion):** new declarations enter
   `scripts/lean_lint.py` `REQUIRED` + `PROTECTED` (they land proof-complete,
   so the sorry baseline stays `deferred: {}`); `scripts/pin_statements.py
   --write` regenerates layer 1; the build job prints the `elab` block on the
   first run (red by design) and it is committed verbatim on the second.
   `docs/04`'s queue and `ImprovedBS/Core.lean`'s T6 comment are updated to
   point at the landed sub-goal status.
4. **Ledger row** in `benchmarks/LEDGER.md`.

## Done looks like (acceptance — machine-graded)

- `lake build` green, `#print axioms` audit of every new constant reports
  exactly `[propext, Classical.choice, Quot.sound]`, pins + elab green, lint
  green, oracle lane untouched and green.
- The GBM instance is machine-checked — otherwise the module proves an
  implication with no verified premise, and the honest-status section would be
  overclaiming.
- The CGMY-decay hypothesis is **not** asserted anywhere: it appears only as
  a hypothesis of the main theorem and in doc-comments that say so. (A `def`
  of the CGMY exponent is explicitly out of scope.)
- `docs/03` and the `Core.lean` T6 block updated to record which sub-goal is
  landed, without claiming more.

## Explicitly out of scope

- Proving the tempered decay for CGMY (the `cpow`/branch work; next sub-goal).
- Sub-goal 3 (Fourier inversion / agreement with the risk-neutral expectation).
- Any `sorry`, any new third-party Python dependency, any change to T1–T5.

## Why this is worth a brief (and shaped this way)

The sub-goal's folklore version is "tempering restores the Fourier integral".
Its two machine-checkable halves are *different in kind*: one is a polynomial
identity worth a `ring`, the other is the integrability of `exp(−c|u|^Y)`,
and the join is a domination argument. The expensive mathematics — *why* the
CGMY factor decays like that — is real complex analysis on a branch of `cpow`,
and pretending it is part of this brief is how proofs get asserted instead of
checked. BRIEF_004's template (hypothesis enters honestly, instance verified,
specialization cited) applies one analytic layer higher: this brief lands the
*pricing-side* theorem and the Gaussian instance, and leaves the CGMY estimate
as the next precisely-shaped unit.
