# BRIEF_008 — T6 sub-goal 3(b): Fourier inversion of the Carr–Madan pricing kernel

- **Status:** **PENDING CI** — PR #10, branch `arena/01a0c2fb-improved-black-scholes`.
  This is the item `docs/04` recorded as *"(queued) T6 sub-goal 3(b) — Fourier inversion"*,
  completing the research tier T6 program.
- **Prerequisite PRs:** BRIEF_005 (T6 sub-goal 2, `ImprovedBS/Fourier.lean`),
  BRIEF_006 (T5), and BRIEF_007 (T6 sub-goal 3a, `ImprovedBS/RiskNeutral.lean`) merged.
  No edits to existing declarations in `ImprovedBS/Core.lean`, `ImprovedBS/Levy.lean`,
  `ImprovedBS/Fourier.lean` or `ImprovedBS/RiskNeutral.lean`.
- **Skills:** Lean 4 + mathlib Fourier analysis and measure theory:
  `Mathlib.Analysis.Fourier.Inversion`, `Continuous.fourierInv_fourier_eq` /
  `MeasureTheory.Integrable.fourierInv_fourier_eq`, Bochner integral evaluation,
  and complex algebra.
- **Budget:** CI-only verification — the sandbox authoring this has no local Lean
  toolchain and no network access to the toolchain CDN, so `lake build` in CI is
  the grader. Two-run pin bootstrap (first run builds, verifies `#print axioms`,
  and prints the `elab_delta` block last; second run merges the delta verbatim).
  Every mathlib name was verified against the **pinned tag v4.34.0** before pushing
  (ledger C3), and the route was numerically checked in the oracle first (ledger C4).

## The decision: close T6 sub-goal 3(b)

`docs/03` §D1 and BRIEF_007 set out the T6 target: the Carr–Madan integral is
absolutely convergent (BRIEF_005, landed), real-valued, and agrees with
`e^{−rτ} E[(S_T − K)⁺]`.

BRIEF_007 landed sub-goal (3a): the machine-checked connection between the closed
form and the discounted expectation under the lognormal law of `log(S_T/S)`,
`bsCall_eq_lognormal_expectation`.

This brief lands sub-goal (3b): Fourier inversion of the damped Carr–Madan pricing
kernel, landing on `bsCall_eq_lognormal_expectation`, and proving the real-valuedness
of the inverted pricing integral.

## Goal

New module `ImprovedBS/Inversion.lean` (namespace `BSM`), proving for
`0 < S`, `0 < K`, `0 < τ`, `0 < σ`:

1. The inverse Fourier transform of the damped call pricing kernel inverts back
   to the damped call price at `k = log(K/S)`.
2. Undamping the inverted transform recovers the discounted lognormal expectation:

       e^{-αk} · 𝓕⁻ (𝓕 f) k = e^{-rτ} · ∫ (S e^x - K)⁺ d N((r-q-σ²/2)τ, σ²τ)(x)

   landing on BRIEF_007's `bsCall_eq_lognormal_expectation`, and therefore equals
   `bsCall S K tau r q sigma`.
3. The inverted integral is **real-valued**: its imaginary part vanishes identically,
   and it equals its real part `bsCall S K tau r q sigma`.

## Scope (numbered)

### §1 The pricing integral and integrability (3 declarations)
1. `carrMadanInversion`: the inverse Fourier integral of the dressed pricing kernel:
   `carrMadanInversion φ α r tau k = ∫ u : ℝ, (e^{-rτ}/(2π)) • (carrMadanPhase (-k) u * carrMadanKernel φ α u)`.
2. `carrMadanInversion_integrand_integrable`: integrability of the dressed pricing
   integrand for any model factor satisfying the tempered decay bound of BRIEF_005.
3. `gbm_carrMadanInversion_integrable`: the fully machine-checked GBM instance.

### §2 The damped call price and lognormal expectation (3 declarations)
4. `dampedCallPrice`: the damped call price function `k ↦ e^{α k} · e^{-rτ} E[(S e^X - S e^k)⁺]`.
5. `dampedCallPrice_log_eq`: at `k = log(K/S)`, the payoff specializes to `S e^x - K`,
   landing on `bsCall_eq_lognormal_expectation` to yield `e^{α k} · bsCall`.
6. `undamped_dampedCallPrice`: multiplying by `e^{-α k}` recovers `bsCall S K tau r q sigma`.

### §3 Fourier inversion (2 declarations)
7. `fourierInversion_dampedCallPrice`: mathlib's `Continuous.fourierInv_fourier_eq`
   applied to the damped call price.
8. `fourierInversion_dampedCallPrice_at`: pointwise evaluation at `k = log(K/S)`.

### §4 The main theorems: landing on 3(a) and real-valuedness (5 declarations)
9. `carrMadan_inversion_eq_lognormal_expectation`: the undamped inverted transform
   equals the lognormal expectation of BRIEF_007.
10. `carrMadan_inversion_eq_bsCall`: the inverted transform equals `bsCall S K tau r q sigma`.
11. `carrMadan_inversion_im_eq_zero`: the imaginary part of the inverted transform is 0.
12. `carrMadan_inversion_eq_re`: the complex inverted transform equals the cast of its real part.
13. `carrMadan_inversion_re_eq_bsCall`: the real part equals `bsCall S K tau r q sigma`.

### Oracle side
14. `experiments/black_scholes.py`:
    - `carr_madan_denom`: the strike-transform denominator.
    - `bs_call_by_fourier_inversion`: Carr–Madan Fourier inversion along `v = u - i(α+1)`,
      Simpson quadrature with adaptive `u_max = max(100, 10/(σ√τ))`.
    - `bs_call_by_fourier_inversion_complex`: two-sided complex integral verifying
      vanishment of the imaginary part.
15. `tests/test_bs.py`: `test_fourier_inversion` (15th test).
    - Checks closed form vs Fourier inversion on the 39-point golden grid (rel error ≤ 2e-11).
    - Checks expectation vs Fourier inversion.
    - Checks complex imaginary part ≤ 1e-13.
    - Checks rejection of `α ≤ 0`.
16. `tests/test_mutants.py`: mutant **M12** (Carr–Madan denominator coefficient flip),
    killed by `test_fourier_inversion` and no other test.

## Done looks like (acceptance — machine-graded)

- `lake build` green; `#print axioms` of all 11 new theorems reports exactly
  `[propext, Classical.choice, Quot.sound]` (added to `.github/workflows/lean.yml`).
- Statement pins: source layer updated (81 → 94) with the 81 existing entries
  **byte-identical**; `elab` layer committed on the second run via `--elab-merge`.
- `scripts/lean_lint.py` green (7 files, 115 declarations); `tests/test_lint.py` 7/7;
  `tests/test_pins.py` 12/12; `tests/test_crosscheck.py` 6/6.
- `tests/test_bs.py` 15/15; `tests/test_mutants.py` 4/4 with 13 mutants.
- No existing theorem changed or weakened; no `sorry`.
- `README.md`, `benchmarks/LEDGER.md`, `docs/03_research.md`, `docs/04_formal_plan.md`,
  and `ImprovedBS/Core.lean` status comment updated.
