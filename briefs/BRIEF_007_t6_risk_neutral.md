# BRIEF_007 — T6 sub-goal 3(a): the closed form IS the risk-neutral expectation

- **Status:** **LANDED GREEN** — PR #9, lean run 35574194681 (oracle lane run
  35574194638), `benchmarks/LEDGER.md` row 7. This was the item `docs/04`
  §"The brief queue" recorded as *"(queued) T6 sub-goal 3 — depends on 005,
  CI-only"*, and the half of that item this brief took.
- **Prerequisite PRs:** BRIEF_005 (T6 sub-goal 2, `ImprovedBS/Fourier.lean`)
  and BRIEF_006 (T5) merged. No edit to `ImprovedBS/Levy.lean`,
  `ImprovedBS/Fourier.lean` or `ImprovedBS/Crosscheck.lean`; the only edit to
  `ImprovedBS/Core.lean` is the T6 status comment block at the end of the
  file (no declaration touched).
- **Skills:** Lean 4 + mathlib measure theory at the Bochner-integral level:
  `integral_indicator`, `integral_sub`/`integral_add`, `integral_const_mul`,
  `integral_map`, `Integrable.congr`, half-line reflection
  (`integral_comp_neg_Ioi`), and the `ProbabilityTheory.gaussianReal` API. No
  new mathematics: the content is one Gaussian computation (the lognormal
  partial expectation) and the bookkeeping that makes it the theorem.
- **Budget:** CI-only verification — the sandbox authoring this has no Lean
  toolchain and no network path to the toolchain CDN, so `lake build` is the
  grader and the two-run `elab` pin arc is expected (land green except a
  by-design red pins step that prints the block, then commit it verbatim).
  Every mathlib name in the scope below was read in the **pinned tag
  v4.34.0** source before this brief was committed (ledger C3), and the route
  was checked numerically before any Lean was written (ledger C4 — see
  `tests/test_bs.py::test_risk_neutral_expectation` and the oracle's new
  `bs_call_by_expectation`).

## The decision: split T6(3) into (3a) the expectation and (3b) the inversion

`docs/03` §D1 states the T6 target as: the Carr–Madan integral is absolutely
convergent (**BRIEF_005, landed**), real-valued, and *agrees with*
`e^{−rτ} E[(S_T − K)⁺]`. Sub-goal 3 is the agreement, and it has two halves
that are different in kind:

- **(3a)** *What is `e^{−rτ} E[(S_T − K)⁺]`, as a machine-checked object, and
  is it the closed form?* Under the risk-neutral measure of the GBM instance
  `log(S_T/S) ~ N((r−q−σ²/2)τ, σ²τ)`, so the expectation is a concrete
  integral against a Gaussian density, and "it equals `bsCall`" is a theorem
  about one Gaussian integral (the lognormal partial expectation). Nothing in
  the repository states this yet: T1–T5 are theorems *about the closed form*,
  and the closed form has never been connected to the expectation it is
  supposed to be. BRIEF_006 deferred exactly this ("the `x = log S` /
  convolution half … to T6 sub-goal (3), where the expectation lives").
- **(3b)** *Does the damped Fourier integral of BRIEF_005 invert to that
  expectation?* That is `Integrable.fourier_inversion` applied to the
  Carr–Madan kernel, plus the identification of `carrMadanPhase` with the
  Fourier transform of the damped call price. It consumes (3a) as its
  right-hand side and BRIEF_005's integrability as its hypothesis.

This brief lands (3a) and leaves (3b) explicitly queued. Landing them
together would have made the acceptance bar "Fourier inversion against a
right-hand side that does not exist in the tree", which is the shape of
claim `docs/04` says a brief must not have.

## The second decision: bridge `phi`/`Phi` to mathlib's Gaussian, do not migrate

BRIEF_006 left "should `Phi`/`phi` be replaced by mathlib's Gaussian?" as a T6
question, noting it was safe to revisit only because the two bodies are
pinned. The answer here is **neither replace nor ignore**: three lemmas
identify the repository's definitions with mathlib's once and for all —

    phi x = gaussianPDFReal 0 1 x                     (phi_eq_gaussianPDFReal)
    Phi x = (gaussianReal 0 1 (Iic x)).toReal         (Phi_eq_gaussianReal_Iic)
    ∫ f ∂(gaussianReal 0 1) = ∫ f · phi               (integral_gaussianReal_eq_integral_mul_phi)

— so every T1–T5 statement keeps the definition it was pinned against, the 60
existing pins do not move, and every probabilistic statement from here on can
be written against mathlib's measures (`bsCall_eq_gaussianReal_expectation`,
`bsCall_eq_lognormal_expectation`). A migration would have changed what 60
pinned statements *say* for no gain in what they *prove*.

## Goal

New module `ImprovedBS/RiskNeutral.lean` (namespace `BSM`, `import
ImprovedBS.Core`), with, for `0 < S`, `0 < K`, `0 < τ`, `0 < σ`:

    bsCall S K τ r q σ = e^{−rτ} · ∫ max (S·e^{(r−q−σ²/2)τ + σ√τ·z} − K) 0 · phi z dz
    bsPut  S K τ r q σ = e^{−rτ} · ∫ max (K − S·e^{(r−q−σ²/2)τ + σ√τ·z}) 0 · phi z dz

and the same call identity against `gaussianReal 0 1` (the law of the driving
noise) and against `gaussianReal ((r−q−σ²/2)τ) v` with `(v : ℝ) = σ²τ` (the
law of `log(S_T/S)`), plus the drift condition
`∫ S·e^{(r−q−σ²/2)τ + σ√τ·z} · phi z dz = S·e^{(r−q)τ}`.

**The hypotheses are the honest ones, and `0 < σ` is load-bearing.** With
`σ < 0` the closed form evaluates to `−bsPut(|σ|)` while the expectation is
unchanged (the integrand depends on `σ√τ·z` under a symmetric law); the
numeric route-check records the pair (−5.5735 vs 10.4506 on the textbook
case) and `test_risk_neutral_expectation` asserts `bs_call(−σ) = −bs_put(σ)`.
So the theorem is not true for `σ ≠ 0`, and the brief does not ask for it.

## Scope (numbered)

### §1 The Gaussian bridge (4 lemmas)

1. `phi_eq_gaussianPDFReal`, `Phi_eq_gaussianReal_Iic`,
   `integral_gaussianReal_eq_integral_mul_phi`, `integral_phi : ∫ phi = 1`.
   mathlib inputs (all read at v4.34.0, `Mathlib/Probability/Distributions/Gaussian/Real.lean`):
   `gaussianPDFReal μ v x = (√(2πv))⁻¹ · exp(−(x−μ)²/(2v))`,
   `gaussianReal_apply_eq_integral (μ) (hv : v ≠ 0) (s)`,
   `integral_gaussianReal_eq_integral_smul (hv)`,
   `integral_gaussianPDFReal_eq_one (μ) (hv)`, `gaussianPDFReal_nonneg`.

### §2 Tilted Gaussian integrals (6 lemmas)

2. `exp_mul_phi_eq (s z) : exp(sz)·phi z = exp(s²/2)·phi(z − s)` — the T3
   tilting identity `phi_add` read at `u = z − s`, `a = s`. Everything
   Gaussian in this brief is this one line integrated.
3. `integrable_exp_mul_phi`, `integral_exp_mul_phi (s) : ∫ exp(sz)·phi = exp(s²/2)`
   (translation invariance: `Integrable.comp_sub_right`,
   `integral_sub_right_eq_self`, both `MeasureTheory.Group.Integral`).
4. `integral_phi_Ioi (a) : ∫_{(a,∞)} phi = Phi(−a)` and
   `integral_phi_sub_Ioi (a s) : ∫_{(a,∞)} phi(z − s) = Phi(s − a)` —
   reflection (`integral_comp_neg_Ioi`, root namespace,
   `Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean`) plus the
   repository's own `integral_comp_add_right_Iic`.
5. `integral_exp_mul_phi_Ioi (a s) : ∫_{(a,∞)} exp(sz)·phi = exp(s²/2)·Phi(s − a)`
   — **the lognormal partial expectation**, the single Gaussian computation
   in Black–Scholes.

### §3 The payoff (4 lemmas)

6. `sigma_sqrt_tau_mul_d2 : σ√τ·d2 = log(S/K) + (r−q−σ²/2)τ` (exposed from
   inside `d2_exponent`, `div_eq_iff` + `rfl`).
7. `spot_sub_strike_eq (S K m s d z) (hS hK) (hd : s·d = log(S/K) + m) :
   S·exp(m + sz) − K = K·(exp(s(z + d)) − 1)` — the T5 idiom: abstract the
   drift, scale and threshold, take the one relation the algebra needs as a
   hypothesis, close with `linear_combination`.
8. `max_spot_sub_strike_mul_phi … (hs : 0 < s) … : max(…) 0 · phi z =
   indicator (Ioi (−d)) (fun z => (S·exp(m + sz) − K)·phi z) z` — the
   exercise region is `{z > −d}` because `exp(s(z+d)) ≥ 1 ⇔ z ≥ −d` when
   `s > 0` (`Real.one_le_exp`, `Real.exp_le_one_iff`). This is where `0 < σ`
   enters, and the only place.
9. `max_sub_swap_eq (a b) : max(b − a) 0 = max(a − b) 0 − a + b` (the put
   payoff in terms of the call payoff).

### §4 The theorems (7 declarations)

10. `integrable_spot_mul_phi`, `integrable_max_spot_sub_strike_mul_phi` —
    integrability of the spot and of the call payoff against `phi`
    (`Integrable.indicator`, `Integrable.congr`).
11. `integral_spot_mul_phi_eq_forward (htau : 0 ≤ τ) : E[S_T] = S·e^{(r−q)τ}`
    — the drift condition, stated with the weaker `0 ≤ τ` because that is all
    `Real.sq_sqrt` needs.
12. **`bsCall_eq_riskNeutral_expectation`** — `integral_indicator` to the
    half-line, `integral_sub` to split, items 4–5 to evaluate, T1 to turn
    `σ√τ + d2` into `d1`, and `e^{−rτ}·e^{(r−q−σ²/2)τ}·e^{σ²τ/2} = e^{−qτ}`.
13. **`bsPut_eq_riskNeutral_expectation`** — T2 parity + item 9 + item 11.
14. `bsCall_eq_gaussianReal_expectation` (via item 1) and
    `bsCall_eq_lognormal_expectation (v : ℝ≥0) (hv : (v:ℝ) = σ²τ)` — the law
    of `(r−q−σ²/2)τ + σ√τ·Z` is `gaussianReal ((r−q−σ²/2)τ) (σ²τ)` by
    `gaussianReal_map_const_mul` then `gaussianReal_map_const_add` (both
    v4.34.0, `Mathlib/Probability/Distributions/Gaussian/Real.lean`), and
    `integral_map` pulls the integral back twice. The variance is a
    hypothesis on an `ℝ≥0` variable because `gaussianReal` takes it in `ℝ≥0`
    and a subtype literal in a statement is not something a reader should
    have to parse.

### Oracle side

15. `experiments/black_scholes.py` gains `bs_call_by_expectation`,
    `bs_put_by_expectation`, `forward_by_expectation` (Simpson quadrature of
    the payoff against `norm_pdf`; **no `norm_cdf`, no `_d1d2`** in the
    route, so the comparison with the closed forms is between independently
    derived numbers, the same discipline as `bs_put_by_parity`). No existing
    line of the oracle changes; every mutation anchor survives.
16. `tests/test_bs.py::test_risk_neutral_expectation` (14th test) and mutant
    **M11** in `tests/test_mutants.py` (drift sign flip in the expectation
    route), killed by that test and by no other — the closed forms do not use
    the drift helper, so parity, bounds, PDE and textbook values all stay
    green under M11 while `E[S_T]` drifts to `S·e^{(r−q+σ²)τ}`.

## Done looks like (acceptance — machine-graded)

- `lake build` green; `#print axioms` of all 21 new constants reports exactly
  `[propext, Classical.choice, Quot.sound]` (audit heredoc in
  `.github/workflows/lean.yml` extended).
- Statement pins: source layer regenerated (60 → 81) with the 60 existing
  entries **byte-identical**, and the `elab` layer committed from the build
  job's printed block on the second run; `cross_layer_check` clean.
- `scripts/lean_lint.py` green with the enlarged `REQUIRED`/`PROTECTED`
  sets; `tests/test_lint.py` 7/7; `tests/test_pins.py` 12/12 (two new tests for
  the `elab_delta` block and `--elab-merge`, the tooling this brief's first pins
  run showed was missing — see the ledger's CI history for row 7).
- `tests/test_bs.py` 14/14, `tests/test_mutants.py` 4/4 with 12 mutants
  (M11 killed by `test_risk_neutral_expectation` only);
  `tests/test_crosscheck.py` green; oracle lane green.
- No statement weakened: no hypothesis added to T1–T5 or to BRIEF_004/005's
  declarations, none removed; no existing declaration renamed or re-stated;
  `Phi`/`phi` definitions untouched (pins prove it).
- `docs/03` §D1, `docs/04` (stack table, spine, dependency table, queue),
  `README.md`, `benchmarks/LEDGER.md` row 7 and the `Core.lean` T6 block
  updated to say (3a) landed and (3b) is the remaining sub-goal — and no
  more than that.

## Explicitly out of scope

- **(3b) Fourier inversion.** `Integrable.fourier_inversion` against
  `carrMadanKernel`, the identification of `carrMadanPhase` with the Fourier
  transform of the damped price, and the real-valuedness of the inverted
  integral. Next brief; it consumes this one's `bsCall_eq_lognormal_expectation`
  as its right-hand side and BRIEF_005's `gbm_carrMadan_price_integrable` as
  its hypothesis.
- **A general-Lévy version of (3a).** The expectation identity *is* the GBM
  instance; for a tempered-stable law there is no closed form to compare
  against, and mathlib v4.34.0 has no such law. Nothing here pretends
  otherwise.
- **Migrating `Phi`/`phi` to mathlib's Gaussian.** Decided against above; the
  bridge lemmas make it unnecessary.
- **Any `sorry`, any new third-party Python dependency, any change to T1–T5.**
