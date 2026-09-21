# BRIEF_006 — T5: the closed form solves the BSM PDE

- **Status:** IN FLIGHT (this PR) — the design decision below is the item
  `docs/04` §"The brief queue" recorded as *"T5 is not yet a brief, because it
  needs a decision that belongs in the brief rather than in this document"*.
- **Prerequisite PRs:** BRIEF_003 (T3/T4) merged — T3 is the hinge this
  brief is built on, and the T4 infrastructure is untouched. No edit to
  `ImprovedBS/Levy.lean`, `ImprovedBS/Fourier.lean` or `ImprovedBS/Crosscheck.lean`.
- **Skills:** Lean 4 + mathlib real analysis: `HasDerivAt` composition, the
  interval-integral FTC, and division algebra under `Real.sqrt`. No new
  mathematics beyond freshman calculus; the content is *structural* (which
  identity cancels which term).
- **Budget:** CI-only verification — the sandbox authoring this has no Lean
  toolchain and no network path to the toolchain CDN, so `lake build` is the
  grader and the two-run `elab` pin arc is expected (land green except a
  by-design red pins step that prints the block, then commit it verbatim).
  Every mathlib name in the scope below was checked against the **pinned tag
  v4.34.0** before this brief was committed, with the signature, in
  `docs/04`'s dependency table — ledger C3's rule.

## The decision: prove the PDE in `(S, τ)`, not in `x = Real.log S`

`docs/04` §"The dependency spine" originally argued the other way:

> **Change variables before differentiating.** … Doing it in `S` coordinates
> buys nothing and costs every `1/S` factor by hand.

**That paragraph is wrong for this theorem, and the reason is a computation,
not a preference.** Write the closed form as `V = F·Φ(d1) − D·Φ(d2)` with
`F = S e^{−qτ}`, `D = K e^{−rτ}`. The two "actions" the chain rule needs are

    ∂d1/∂S = ∂d2/∂S = 1/(S σ√τ)            (identical — so S-actions cancel)
    ∂d1/∂τ − ∂d2/∂τ = σ/(2√τ)              (the τ-actions differ by a constant)

The first line is T1 read in `S` (`d1 − d2 = σ√τ` is constant in `S`), and
the second is T1 read in `τ` (differentiate both sides). T3 then cancels the
`φ`-terms *in `S`*, exactly as `docs/04` says it does:

    V_S = (F/S)Φ(d1) + Fφ(d1)·(∂_S d1) − Dφ(d2)·(∂_S d2)
        = e^{−qτ}Φ(d1) + [S e^{−qτ}φ(d1) − K e^{−rτ}φ(d2)]/(Sσ√τ)
        = e^{−qτ}Φ(d1)                                        (T3 kills the bracket)

**Consequence, and the correction:** the `S²V_SS` term in `S` coordinates is
*one* division-clearing lemma (`(σ²/2)S²·(e^{−qτ}φ(d1)/(Sσ√τ)) =
(σ/(2√τ))·S e^{−qτ}φ(d1)`), not "every `1/S` by hand" — because T1/T3 supply
the `S`-actions and the `τ`-actions rather than the author supplying them.
The `x = log S` reduction does not remove that lemma; it *replaces* it with a
change-of-variable transfer lemma plus a second statement of the PDE in the
`x` gauge, and it leaves the `τ`-derivative's `1/√τ` structure exactly as it
was (`d1`, `d2` are affine-over-`√τ` in both gauges). It is strictly more
work for strictly less machine-checked contract.

What `x = log S` genuinely buys — the operator becomes constant-coefficient
and the closed form is a convolution with the Gaussian kernel, so uniqueness
and the Feynman–Kac bridge become available — is **not what T5 claims**.
T5's claim is the residual identity. The convolution/uniqueness machinery is
load-bearing one node later, in **T6 sub-goal (3)** ("agreement with the
risk-neutral expectation"), which is where the measure-theoretic integral
actually is. The route decision therefore *places* the log-coordinate work
rather than discarding it.

So this brief states the PDE in the coordinates the oracle tests
(`experiments/black_scholes.py::bs_pde_residual` differentiates in calendar
time `t`), proves it there, and leaves `x = log S` to T6(3). `docs/04`'s spine
paragraph and the T5 note in `Core.lean` are corrected in the same PR; the
spine's *content* claim — `T5 = T3 + chain rule + Φ′ = φ` — is unchanged and
is what the scope below implements.

## Goal

Land `t5_bsCall_pde` — the closed form solves

    V_t + (r − q)·S·V_S + (σ²/2)·S²·V_SS = r·V

with `V_t` an honest derivative in calendar time (`τ = T − t`), so the
statement is the contract rather than a re-gauging of it. As landed, that is

* `t5_delta`, `t5_gamma` (the `S`-derivatives) and `t5_tau` (the `τ`-derivative)
  — the chain rule, with T3 doing the cancelling;
* `t5_bsCall_pde_tau` — the operator identity with `V_t := −∂_τ`;
* `t5_bsCall_pde` — the same identity in calendar time, by the chain rule on
  `t ↦ T − t`, which is the statement `docs/04` and the oracle both mean.

The statement is *not* weakened: hypotheses are `0 < S`, `0 < K`, `0 < τ`,
`σ ≠ 0` — the same four T3 carries, and the same ones the proof consumes
(`σ ≠ 0` is needed for `∂d1/∂S = 1/(Sσ√τ)` to be an identity; positivity of
`σ` is a modelling guard, not an algebraic one, exactly as in T3).

## Scope (numbered)

### The one new analytic input

1. **`hasDerivAt_erf`**: `HasDerivAt erf ((2/√π)·e^{−x²}) x`, from
   `intervalIntegral.integral_hasDerivAt_right` (the interval-integral FTC) and
   the constant `2/√π` in `erf`'s definition. mathlib v4.34.0 has no
   `Real.erf` and no `Real.hasDerivAt_erf` (docs/04's correction); this is
   derived, not imported.
2. **`hasDerivAt_Phi`**: `HasDerivAt Phi (phi x) x`. The only algebra is
   `(x/√2)² = x²/2` and `(2/√π)(1/√2)/2 = 1/√(2π)`. The second of those is the
   one place the two Gaussian normalizations meet; its four denominators
   (`√π`, `√2`, the numeral `2`, `√2·√π`) are cleared with `field_simp` on the
   nonzero facts `Real.sqrt_pos`/`Real.sq_sqrt`-free — the sqrt factors cancel
   as *quotients*, never as squares, so `Real.sq_sqrt`/`mul_self_sqrt` are not
   used anywhere in T5. This is the tree's first `field_simp`; the
   alternative house idioms (`div_eq_iff`, `mul_right_cancel₀`) need the same
   nonzero facts and strictly more steps, and fact-free `ring` cannot do it
   because `a / b * b = a` is false at `b = 0`.

### The shared argument shape (T1's content, differentiated)

3. **`hasDerivAt_d_spot`**: `x ↦ (log (x/K) + c)/(σ√τ)` has derivative
   `1/(Sσ√τ)` at `S` — instantiating `c` gives `∂d1/∂S = ∂d2/∂S`, the first
   half of the cancellation.
4. **`hasDerivAt_d_tau`**: `u ↦ (A + c·u)/(σ√u)` has derivative
   `(c − A/τ)/(2σ√τ)` at `τ`. Proved by the quotient rule
   (`HasDerivAt.div`) plus one committed arithmetic lemma,
   `d_tau_quotient_eq`, stated with `√τ` abstracted to `s` and the *only*
   relation the ring step needs (`s² = τ`) as a hypothesis. That lemma is
   where the division-clearing argument concentrates: the quotient rule hands
   back `X/(σs)² = (c − A/τ)/(2σs)` and the four denominators (`(σs)²`, `2σs`,
   `2s`, `τ`) are cleared against the hypotheses, after which `τ ↦ s²` makes
   the residual identity polynomial.
5. **`d1_tau_sub_d2_tau`**: the τ-actions differ by exactly `σ/(2√τ)` — the
   fact that makes the `φ`-terms combine into `e^{−qτ}φ(d1)·σ/(2√τ)`.

### T5 proper

6. **`t5_delta`**: `deriv (fun x => bsCall x K τ r q σ) S = e^{−qτ}Φ(d1)`.
   The proof must *cite* `t3_delta_identity`; the `φ`-term difference is
   `[S e^{−qτ}φ(d1) − K e^{−rτ}φ(d2)]·(Sσ√τ)⁻¹`, which is zero by T3.
7. **`t5_gamma`**: `deriv (fun x => deriv (fun y => bsCall y K τ r q σ) x) S
   = e^{−qτ}φ(d1)/(Sσ√τ)`, via `HasDerivAt.congr_of_eventuallyEq` on a
   neighbourhood of `S` where `t5_delta` identifies the inner derivative.
8. **`t5_tau`**: `HasDerivAt (fun u => bsCall S K u r q σ) (...)` with
   `−q·F·Φ(d1) + r·D·Φ(d2) + (σ/(2√τ))·F·φ(d1)`. Stated as `HasDerivAt`
   because the calendar-time form differentiates the *composite*
   `t ↦ V(S, T − t)`, which needs the chain rule, not a pointwise value.
9. **`t5_bsCall_pde_tau`** and **`t5_bsCall_pde`**: the two forms of the
   identity, the second as a one-step corollary of the first.
10. **A structural check in `scripts/lean_lint.py`** (`[SPINE]`), because
    `docs/04` claims *how* T5 is proved and nothing in the tree could see a
    route change: the T5 node must cite both `t3_delta_identity` and
    `hasDerivAt_Phi`. A brute-force differentiation of `erf ∘ (log-rational)`
    proves the same theorem while duplicating T3's cancellation — the exact
    drift `docs/04`'s "spine, not six unrelated chores" is about. A mutant is
    seeded for it in `tests/test_lint.py`, since an untested check is a
    decoration.
11. **Housekeeping:** `REQUIRED`/`PROTECTED` entries for every new
    declaration; regenerated pins (`--write`); the `#print axioms` audit list
    in `.github/workflows/lean.yml` extended; docs/04 (T5 row, spine
    correction, dependency table, brief queue), `README.md` and
    `benchmarks/LEDGER.md` updated. The sorry baseline stays `deferred: {}`.

## Done looks like (acceptance — machine-graded)

- `lake build` green; `#print axioms` shows no `sorryAx` for any new
  declaration (all on `[propext, Classical.choice, Quot.sound]`).
- Statement pins: source layer regenerated *and* the `elab` layer committed
  from the build job's printed block, `cross_layer_check` clean.
- `scripts/lean_lint.py` green with the enlarged `REQUIRED` set and the new
  `[SPINE]` check; `tests/test_lint.py` green with its mutant.
- `tests/test_bs.py` 13/13 (including `test_pde_residual_vanishes` **for both
  the call and the put** and `test_pde_residual_is_second_order`) and
  `tests/test_mutants.py` 4/4 unchanged — the residual test is T5's numeric
  shadow and it already covers the put, so the *put* PDE remains a numerically
  checked claim even though this brief lands the call side only.
- No statement weakened: no hypothesis added to T1–T4, none removed; no
  existing declaration renamed or re-stated.

## Explicitly out of scope

- **`x = Real.log S` / the heat-equation form, convolution and uniqueness.**
  Deferred to T6 sub-goal (3), where the expectation lives. If T5 is ever
  wanted in the `x` gauge, it is a *corollary* of `t5_bsCall_pde_tau` by the
  chain rule, and that is the cheap direction to add it.
- **The put side.** `t2_put_call_parity` makes it a corollary, and
  `test_pde_residual_vanishes` already checks it numerically; landing it is a
  follow-up, not part of this acceptance bar.
- **Greeks as a deliverable.** `t5_delta`/`t5_gamma`/`t5_tau` are recorded
  because T5's proof needs them, not because the tree is taking on a greeks
  library; no `bsDelta`/`bsGamma`/`bsVega` definitions, no oracle change.
- **`tests/test_bs.py::test_pde_residual_is_second_order`'s step-size
  window.** The measured window `h ∈ [1e-3, 1e-1]` stands; below `1e-3`
  round-off dominates and the residual *diverges*. Do not "strengthen" it by
  shrinking `h` (the oracle's comment says so, and the numbers back it).
- **Any narrowing of `import Mathlib`** (still toolchain-only knowledge).
