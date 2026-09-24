# 04 — Formal plan: the Lean targets

This document states the claims the repository commits to proving, and the
order in which they are provable. It is the contract that `briefs/` cite and
that CI grades.

**Where the statements live:** `ImprovedBS/Core.lean` (module
`ImprovedBS.Core`, imported by the root module `ImprovedBS.lean`). The tree was
previously at `Lean/core/bsm_theorems.lean`; that path makes the module name
`Lean.core.bsm_theorems`, which squats the `Lean` namespace the elaborator and
every tactic implementation live in. `scripts/lean_lint.py` fails CI if a
`.lean` file reappears under a top-level `Lean/`.

**What "verified" means here:** `lake build` is green on a mathlib-backed tree
*and* `#print axioms` on the node shows no dependency on `sorryAx`. Prose is
not evidence and neither is a green build alone — a `sorry` still builds. The
`.github/workflows/lean.yml` `build` job runs both.

## The theorem stack

Status is machine-derived, not typed by hand: `python3 scripts/lean_lint.py`
prints the live `[RATCHET]` line, and the baseline it ratchets against is
`.github/lean_lint_baseline.json`.

All names below are in `namespace BSM` (module `ImprovedBS.Core`), so the fully
qualified name of T1 is `BSM.t1_d1_minus_d2`. **The module name is not a
namespace** — CI run 7 failed on `#print axioms ImprovedBS.t1_d1_minus_d2`
precisely because of that.

As of run 35514867674 (PR #2; T1/T2 first at run 35509578689, PR #1) the
marked rows are machine-checked: `lake build` green *and* the `#print axioms`
audit green, i.e. no dependency on `sorryAx`. That distinction is the whole
point of the audit step, since a `sorry` builds fine. The ratchet baseline is
`deferred: {}` — nothing in the tree is `sorry`.

| #  | Lean name | statement | difficulty | status |
|----|-----------|-----------|-----------|--------|
| —  | `Phi_add_Phi_neg` | `Φ(x) + Φ(−x) = 1` | trivial given `erf_neg` — which mathlib does not have, so it is proved locally | **machine-checked** |
| T1 | `t1_d1_minus_d2` | `d1 − d2 = σ√τ` | easy (field algebra) | **machine-checked** |
| T2 | `t2_put_call_parity` | `bsPut = bsCall − S e^{−qτ} + K e^{−rτ}` | easy (linear, given Φ symmetry) | **machine-checked** |
| T2′| `t2_put_call_parity_spread` | `bsCall − bsPut = S e^{−qτ} − K e^{−rτ}` | corollary of T2 | **machine-checked** |
| T3 | `t3_delta_identity` | `S e^{−qτ} φ(d1) = K e^{−rτ} φ(d2)` | easy, given the tilting identity `phi_add` | **machine-checked** |
| T4 | `t4_call_bounds` | `max(S e^{−qτ} − K e^{−rτ}, 0) ≤ bsCall ≤ S e^{−qτ}` | medium — positivity via `Φ = ∫ φ`, *not* monotonicity (ledger C4) | **machine-checked** |
| T4′| `t4_put_bounds` | mirrored put bounds | corollary of T4 + T2 (`linarith` only) | **machine-checked** |
| T5 | `t5_bsCall_pde` (+ `t5_delta`, `t5_gamma`, `t5_tau`, `t5_bsCall_pde_tau` and six supporting lemmas) | `V_t + (r−q)S V_S + (σ²/2)S² V_SS = r V` in calendar time for `bsCall` | heavy — the one new analytic input is `Φ′ = φ`, derived from the interval-integral FTC because mathlib has no `Real.erf` | **LANDED GREEN** (BRIEF_006), lean run 35566569107 — `benchmarks/LEDGER.md` row 6 |
| T6 | sub-goals 1, 2, 3(a), 3(b) declared: `ImprovedBS/Levy.lean` (7), `ImprovedBS/Fourier.lean` (7), `ImprovedBS/RiskNeutral.lean` (21), `ImprovedBS/Inversion.lean` (13: `carrMadan_inversion_eq_lognormal_expectation`, `carrMadan_inversion_eq_bsCall`, `carrMadan_inversion_im_eq_zero`) | Fourier pricing kernel survives a wider increment law; closed form = discounted expectation = inverted Fourier transform | **LANDED GREEN** (3a BRIEF_007, 3b BRIEF_008) | restated in docs/03 D1; (3a) **LANDED GREEN** (run 35574194681), (3b) **LANDED GREEN** (run 35578278238) |

Three honest corrections to earlier versions of this table:

1. It previously read "T1 done, T2+T3 done in-code" while the adjacent rows and
   the `.lean` file both said `sorry`. Nothing was done; T1 was a one-line
   tautology and T2/T3 were `sorry`. Status now comes from the lint, so the two
   cannot disagree.
2. T1 and T2 were both **vacuous** as originally defined (`d2 := d1 − σ√τ`,
   `bsPut := bsCall − …`), so "proved" would have meant nothing. See
   docs/01 §2a. They are now proved against independent definitions.
3. T3 was **false** as originally stated — it lacked `σ ≠ 0` and `0 < τ`, and at
   σ = 0 Lean's `a / 0 = 0` collapses it to `S e^{−qτ} φ(0) = K e^{−rτ} φ(0)`.
   T4 had no Lean statement at all despite being listed as "stated" in two
   tables. Both are fixed.

## The dependency spine

The stack is a spine, not six independent chores. Arrows mean "is used by":

    erf_neg ──► Phi_add_Phi_neg ──► T2 ──► T2′
                                └──► T4′
    Real.sq_sqrt ──► T1 ──► T3 ──► T5
                      └──► T4
    integral_gaussian_Ioi ──► integral_phi_Iic_zero ──► Phi_eq_integral_Iic ──► Phi_nonneg, Phi_le_one
    phi_add (tilting identity) ──► T3                                       └──► Phi_le_exp_mul_Phi_add ──► bsCall_nonneg, bsPut_nonneg ──► T4
                └──► exp_mul_phi_eq ──► integral_exp_mul_phi_Ioi ──► bsCall_eq_riskNeutral_expectation ──► bsPut_eq_riskNeutral_expectation (via T2)
    gaussianPDFReal / gaussianReal (mathlib) ──► phi_eq_gaussianPDFReal, Phi_eq_gaussianReal_Iic ──► bsCall_eq_gaussianReal_expectation, bsCall_eq_lognormal_expectation

As landed, T3 and the T4 lower bound are the *same* identity —
`e^{a u + a²/2} φ(u + a) = φ(u)` with `u = d2`, `a = σ√τ` — used pointwise
(T3) and integrated over a half-line (T4). `d1_exponent` / `d2_exponent` /
`forward_eq` are the shared exp/log/sqrt glue. BRIEF_007 (T6 sub-goal 3a) is
the same identity a third time: read as `e^{sz} φ(z) = e^{s²/2} φ(z − s)` and
integrated over `(−d2, ∞)`, it is the lognormal partial expectation
`∫_{(a,∞)} e^{sz} φ = e^{s²/2} Φ(s − a)`, and "the closed form is the
discounted expectation" is that line plus the indicator of the exercise region.

**Prove T5 through T3.** Substituting the closed form into the BSM operator,
the `S²V_SS` term produces `φ(d1)` and `φ(d2)` contributions whose *difference*
is exactly what T3 cancels. So

    T5  =  T3  +  chain rule  +  `HasDerivAt Phi phi x`

and the only genuinely new analytic input is the derivative of Φ. Mathlib has no
`Real.erf` and therefore no `HasDerivAt erf`, so that input is *derived*: T5's
`hasDerivAt_erf` differentiates the local `erf` with the interval-integral FTC
(`intervalIntegral.integral_hasDerivAt_right`) and `hasDerivAt_Phi` is the chain
rule from `x ↦ x / √2`. Brute-force differentiation of `erf ∘ (log-rational)` in
`S`-coordinates is the slow route and buys nothing.

**T5 is proved in `(S, τ)` coordinates, with partial derivatives — corrected.**
An earlier version of this section asserted the opposite ("change variables
before differentiating": go to `x = Real.log S`, where the BSM operator has
constant coefficients and the closed form is the payoff convolved with the
Gaussian kernel, uniqueness coming from the heat-kernel side). That is a true
statement about the *mathematics* and it is the right framing for the
convolution/pricing side of T6, but it is the wrong route for T5 as a formal
target here, and BRIEF_006 commits to the direct one. Three reasons, in order of
weight:

1. **The claim being graded is the `(S, t)` PDE.** A change of variables turns
   T5 into a *different theorem* — the heat equation for `v(x, τ) = V(e^x, τ)`
   — and recovering the stated `(S, t)` identity from it needs the chain rule
   back, twice, for `V_S` and `V_SS`. The `1/S` factors the paragraph above
   wanted to avoid arrive anyway; they are just moved to the end and hidden
   inside a substitution lemma.
2. **The log-S route needs the Gaussian-kernel side to be a *theorem* here.**
   "The closed form is the convolution" is not free: it requires the measure
   `Phi_eq_integral_Iic` and its heat-kernel evolution, i.e. the very
   measure-theoretic machinery docs/04 §mathlib-table already marks as *not yet
   available* at this tier. In `(S, τ)` coordinates the derivative of `Φ`
   (one interval integral, already in the tree) is the whole analytic bill.
3. **Empirically, the feared cost is not real.** The `T5` node's `S`-side
   algebra is two `field_simp`/`ring` steps (`hasDerivAt_d_spot` and the
   `S²V_SS = (σ/(2√τ))·S V_S` collapse), and `√2`, `√π` cancel as *quotients*
   rather than as squares, so no `Real.sq_sqrt` appears anywhere in the node.
   Ledger C9 records the reversal.

The uniqueness half of the log-S picture is not dropped, it is *deferred*: it is
T6 sub-goal 3's business (Fourier inversion for the tempered-stable exponent),
where the kernel and the measure-theoretic integral are the actual objects.
Recorded there rather than silently dropped here. BRIEF_007 has since landed the
*expectation* half of that picture — the closed form equals
`e^{−rτ}∫(S e^{x} − K)⁺ dN((r−q−σ²/2)τ, σ²τ)(x)` (`bsCall_eq_lognormal_expectation`),
which is the log-S object itself — and leaves the inversion as sub-goal 3(b).

**The route is now checked, not just documented.** `scripts/lean_lint.py`'s
`[SPINE]` check (check 10, added with BRIEF_006) fails if the T5 node stops
citing `t3_delta_identity` or `hasDerivAt_Phi`, or if `t5_delta` — the step whose
proof *is* T3's cancellation — stops citing T3 and re-derives the bracket
locally. It is the repository's only mechanical statement about *how* a node is
proved rather than what it claims, and `tests/test_lint.py` seeds the
corresponding mutant, because a route check with nothing trying to break it is
prose with a regex.

## Dependencies needed from mathlib

Pinned: mathlib **v4.34.0**, toolchain **leanprover/lean4:v4.34.0** (see
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json` — all three must move
together, and `.github/workflows/lean.yml` fails the run if they disagree).

| need | available in mathlib v4.34.0? | used by |
|---|---|---|
| `Real.log`, `Real.exp` algebra | **yes** — `Mathlib.Analysis.SpecialFunctions.Log.Basic`, `.../Exp.lean` | d1, d2, T3 |
| `Real.sqrt`, `Real.sq_sqrt`, `Real.sqrt_pos`, `Real.sqrt_mul` | **yes** — `Mathlib.Analysis.Real.Sqrt` (`Data.Real.Sqrt` is a deprecated shim as of 2026-05) | T1, T3, T4 |
| `Real.pi` | **yes** (57 references in the tree) | φ, erf |
| interval integrals, `integral_comp_neg`, `integral_symm` | **yes** — `Mathlib.MeasureTheory.Integral.IntervalIntegral` | `erf_neg`, hence T2 |
| **`Real.erf`** | **NO — it does not exist.** See below. | Φ, T2 |
| `integral_gaussian_Ioi : ∫ x in Ioi 0, exp (-b x²) = √(π/b) / 2`, `integrable_exp_neg_mul_sq` | **yes** — `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` | `integral_phi_Iic_zero`, hence T3/T4; T5 |
| set integrals: `setIntegral_mono_on`, `setIntegral_nonneg`, `integral_Iic_sub_Iic`, `integral_comp_neg_Ioi`, `MeasurableEmbedding.setIntegral_map`, `map_add_right_eq_self` (in `MeasureTheory`, *not* `MeasureTheory.Measure`) | **yes** — verified by name against the v4.34.0 tag before pushing | `Phi_eq_integral_Iic`, `Phi_le_exp_mul_Phi_add` |
| normal CDF/PDF as a distribution | partial — `Mathlib.Probability.Distributions.Gaussian` has the *measure*, not a CDF function | optional; T5, T6 |
| `ProbabilityTheory.gaussianPDFReal`, `gaussianReal`, `gaussianReal_apply_eq_integral (μ) (hv : v ≠ 0) (s)`, `integral_gaussianReal_eq_integral_smul (hv)`, `integral_gaussianPDFReal_eq_one (μ) (hv)`, `gaussianPDFReal_nonneg`, `gaussianReal_map_const_mul (c)`, `gaussianReal_map_const_add (y)` | **yes** — `Mathlib/Probability/Distributions/Gaussian/Real.lean`, read at the tag (`gaussianPDFReal μ v x = (√(2πv))⁻¹ · exp(−(x−μ)²/(2v))`; the map lemmas give `gaussianReal (c·μ) (⟨c², _⟩·v)` and `gaussianReal (μ + y) v`) | BRIEF_007: the Gaussian bridge and the lognormal form of T6(3a) |
| Bochner integral bookkeeping: `integral_indicator (hs)`, `setIntegral_congr_fun (hs) (h : EqOn f g s)`, `integral_congr_ae`, `integral_add`/`integral_sub (hf hg)`, `integral_const_mul`, `integral_map (hφ : AEMeasurable φ μ) (hfm : AEStronglyMeasurable f (map φ μ))`, `Integrable.congr`/`.indicator`/`.const_mul`/`.sub`, `Integrable.comp_sub_right`, `integral_sub_right_eq_self (f) (g)` (both `MeasureTheory.Group.Integral`, to_additive of the `div` forms), `integral_comp_neg_Ioi (c) (f)` (root namespace) | **yes** — verified by name and signature against the v4.34.0 tag before pushing | BRIEF_007 |

### `Real.erf` is not in mathlib — corrected

An earlier version of this table listed "`Real.erf` (already in Mathlib:
`Mathlib.Analysis.SpecialFunctions.Erf`)" and "`Real.hasDerivAt_erf`" as
available dependencies. **Neither exists in v4.34.0.** Verified against the
release tag: there is no file named `Erf.lean` anywhere in the tree's 9112
`.lean` files, and a GitHub code search of `leanprover-community/mathlib4`
returns 0 hits for `Real.erf`, `def erf` and `erf_neg` — while returning 107
for `Real.sqrt` and 57 for `Real.pi`, so the search itself is working.

Guessing those two paths cost three consecutive red `lake build` runs
(`bad import 'Mathlib.Analysis.SpecialFunctions.Erf'`,
`bad import 'Mathlib.Data.Real.Pi'`). The lesson is recorded here rather than
buried: **a mathlib dependency is a claim about a specific version, and it has
to be checked against that version.** A path that looks canonical is not
evidence.

Consequence: `ImprovedBS/Core.lean` defines `erf` itself, as
`(2 / sqrt pi) * ∫ t in 0..x, exp (-(t^2))`, and proves `erf_neg` by
substitution in the interval integral. That is sufficient for T2, which needs
only *oddness*. T3/T4 needed one more thing — `Φ(x) = ∫_{(−∞,x]} φ`
(`Phi_eq_integral_Iic`), which imports the *value* of the Gaussian integral via
`integral_gaussian_Ioi` in exactly one lemma (`integral_phi_Iic_zero`) and then
gives `0 ≤ Φ ≤ 1` and the positivity inequality for free. Note the bounds did
**not** go through `|erf x| ≤ 1` as previously predicted; `Φ ≥ 0` is
`setIntegral_nonneg` and `Φ ≤ 1` is `Φ ≥ 0` at `−x` plus `Phi_neg`. T5 needed
`HasDerivAt erf`, which is derived rather than imported: `hasDerivAt_erf`
differentiates the local `erf` with the interval-integral FTC and
`hasDerivAt_Phi` composes it with `x ↦ x / √2` (BRIEF_006).

If mathlib grows `Real.erf`, delete the local definition and re-point
`Phi_add_Phi_neg` at `Real.erf_neg`. `scripts/lean_lint.py` has `erf`,
`erf_neg` and `exp_neg_sq_even` in both `REQUIRED` and `PROTECTED`, so that
migration cannot silently drop them.

`Φ` and `φ` are currently defined directly from `Real.erf` and `Real.exp`
rather than imported from mathlib's Gaussian machinery. That is deliberate for
T1–T4 (fewer moving parts, definitions match the oracle symbol-for-symbol) and
was to be revisited at T5/T6, where the measure-theoretic integral is the
actual object. **Decision, recorded in BRIEF_006 §2: T5 does not migrate.**
`Real.erf` does not exist in mathlib v4.34.0, so there is nothing to migrate
*to*; and `Mathlib/Probability/Distributions/Gaussian` supplies a measure, not
a CDF function, so replacing `Phi` would mean replacing a definition with a
construction plus a bridge lemma, in a node whose whole analytic content is one
derivative. The migration stays a T6 question — and the reason it is safe to
defer is that the definitions are *pinned* (`Phi`/`phi` bodies are layer-1
statement pins), so a later migration cannot be silent.

**Answered in BRIEF_007: bridge, do not migrate.** `ImprovedBS/RiskNeutral.lean`
proves `phi x = gaussianPDFReal 0 1 x`, `Phi x = (gaussianReal 0 1 (Iic x)).toReal`
and `∫ f ∂(gaussianReal 0 1) = ∫ f · phi`, so every probabilistic statement
can be written against mathlib's measures (`bsCall_eq_gaussianReal_expectation`,
`bsCall_eq_lognormal_expectation`) while the 60 pinned T1–T5 statements keep
the definitions they were pinned against. The `Phi`/`phi` bodies are unchanged;
the pins say so.

Imports in `ImprovedBS/Core.lean` are currently the whole library
(`import Mathlib`). Narrow imports are better practice — they document what a
theorem rests on and cost less elaboration — but they can only be validated by a
toolchain, and two hand-guessed narrow paths cost three red CI runs. Narrowing
the import list is a legitimate follow-up **for someone who can run
`lake build`**; it should not be attempted blind. The table above records what
is actually needed, which is the information a narrowing PR requires.

## Oracle ↔ formal correspondence

The Python oracle and the Lean tree share notation *and* arithmetic meaning,
but they are still two hand-written sources, so they can drift. Four guards,
in increasing strength:

1. **Structural** — `scripts/lean_lint.py` `[ORACLE SYNC]` checks that both
   trees define `d2` and the put independently. Runs with no toolchain.
2. **Behavioural** — `tests/test_mutants.py` seeds bugs into the oracle and
   requires the targeted test to fail, including two vacuity canaries. This is
   the check that a test can fail.
3. **Pointwise (implemented, BRIEF_002; both T3 sides since C8)** — a cross-verifier
   that evaluates
   `d1`, `d2`, `bsCall`, `bsPut`, parity and *both sides* of the delta identity at a
   fixed grid of points in *both* trees and compares: each quantity against the
   oracle's independently computed counterpart, plus the two T3 sides against each
   other. Implemented via `tests/golden_grid.json`,
   `ImprovedBS/Crosscheck.lean` (`#eval`), `tests/test_crosscheck.py`, and wired into
   CI. Not a proof — a contradiction detector against code drift. (`runCrosscheck`
   must *reference* `deltaIdentityRhs`, not merely define it — the twin
   once shipped the RHS unused, so the comparator cross-checked LHS against the
   oracle's LHS and T3's equation itself was never tested: ledger C6 item 4,
   fixed in C8. The requirement is structural in `[CROSSCHECK SYNC]` because the
   1e-12 numeric tolerance cannot see the two sides' ~7e-15 internal gap.)

4. **Pinned claims** — guards (1)–(3) can all be satisfied by a tree that proves
   the *right equations about the wrong claim*, because none of them reads a
   statement. `tests/golden_statements.json` pins every declaration in
   `REQUIRED | PROTECTED` — a theorem by its statement (the text through the first
   `:=`), a definition by its whole body, since a definition *is* the
   specification. `scripts/pin_statements.py` extracts and compares;
   `lean_lint.py` enforces the source-level half with no toolchain, and the build
   job enforces the elaborated half (`#check` type + `#print axioms` per constant)
   where a toolchain exists. `--write` refreshes layer 1 only, so an author
   without a toolchain cannot silently drop layer 2.

   Why two layers, and what each one is *not*: the source-level layer catches a
   re-stated claim (`: True`, a dropped hypothesis, `theorem`→`def`, a duplicate
   shadow declaration, a shrunk artifact) on any runner, and `cross_layer_check()`
   also catches the *stale* combination — regenerate layer 1 after editing a
   claim and leave the `elab` block behind, and the two layers disagree about which
   spec constants the theorem mentions. That one is a common accident rather than
   an attack: `--write` deliberately preserves `elab`, so an author without a
   toolchain can produce it without meaning to.

   What no local lane can catch is the deliberate, self-consistent version — hollow
   the statement, re-run `--write`, and hand-edit `elab` to match. On disk that is
   indistinguishable from an honest claim change, and this artifact exists to make
   claim changes *loud and reviewable*, not impossible. What ends it is that CI
   never reads the block, it re-elaborates it: `#check @BSM.t4_call_bounds` prints
   the bound, so a committed `: True` is a diff against reality rather than against a
   file. The residual gap is asserted mechanically, in
   `tests/test_lint.py::test_known_local_gaps_stay_open`, rather than left as
   folklore — and the mechanism has already paid for itself: the skew check above
   started life as that test's single entry, and closing it moved the mutant into
   `MUTANTS`, which is what the test tells you to do. A gap that closes without the
   entry moving turns the suite red and says so out loud.
   Note what this replaces. The audit that prompted these pins found the repo's own
   rule — *a green check is only evidence if it could have been red* — applied to
   the proofs (no `sorry`), to the tests (`test_mutants.py`), and to the
   oracle↔Lean correspondence (guards 1–3), but not to `lean_lint.py` itself,
   which is the artefact with actual authority over how the Lean tree is
   labelled: 20 KB of regexes over a proof assistant's source, gating `lake build`
   via `needs:`. That is the "unverified second pillar" this repository is
   exposed to — not the numeric oracle, which no theorem imports and whose removal
   would leave T1–T4 standing (it would leave the *gate* unable to run, which is a
   different and fixable problem). `tests/test_lint.py` seeds 25 cheats into
   throwaway copies of the tree and requires each to be killed by a named check —
   the 11-mutant discipline, turned on the grader — while 5 controls (a marker word
   inside a comment, a re-wrapped statement, parity reproved from `erf_neg`
   directly) must stay green, since a guard that rejects legitimate work is a guard
   that gets disabled. Three of its results are worth quoting: with `[PINS]` removed
   from the lint, 8 of the mutants survive (P1–P8 — measured when the suite held 22);
   with ONLY `cross_layer_check()` switched off, exactly one survives, which is how a
   check's contribution is attributed rather than assumed; and with the odd-symmetry
   guard narrowed back to a single preferred lemma name, a correct proof of T2 goes
   red. The twenty-fifth mutant arrived with `[SPINE]`: T5's delta rewritten to
   re-derive the `phi`-bracket instead of citing `t3_delta_identity`. It is the
   sharpest of the set, because *every other check is blind to it by
   construction* — same statement, same definitions, no `sorry`, no marker, all
   pins byte-identical — which is the definition of a check that had to exist
   before the route could be claimed.

Until (3) existed, the correspondence rested on (1) and (2) plus human reading of
docs/01 §4. All four guards are now active; guard (4)'s elaborated layer is
CI-only, like `lake build` itself, and its `elab` block is produced by the first
build run and committed from that run's published log.

That sentence earned itself. The first build run (35519747870) went red — `lake
build` green, `#print axioms` green, the pin step failing with
`could not recover both a type and an axiom line for BSM.Phi (type='BSM.Phi : ℝ →
ℝ', axioms='')`. `#print axioms` quotes the constant name where `#check` does not,
and the parser had assumed symmetry between two Lean commands whose output formats
are not shared. The refusal was correct — a partial pin would have looked like
coverage — but the bug was only visible in CI, which is the one place this
repository cannot iterate cheaply. `tests/test_pins.py` fixes that properly:
`parse_audit` is now a pure function over recorded output, both message shapes and
a wrapped type are replayed in-sandbox, and `test_generator_and_parser_agree_on_the_protocol`
asserts that the emitter and the reader still agree on the sentinel protocol. Two
lessons generalize: *a format assumption about a tool you cannot run is a bug
with a delay*, and *a CI-only check must fail loudly where it cannot run* — the
local `--elab-check` is a red with a message, never a skip.

## The brief queue

Order is chosen so that each brief's acceptance bar is checkable by the time it
is worked on, and so that no brief depends on a machine-checked result that does
not yet exist. BRIEF_001–010 have landed, in this order.

| brief | what it lands | depends on | locally checkable? |
|---|---|---|---|
| ~~BRIEF_001~~ | **LANDED GREEN** — `lake build` + `#print axioms`; T1/T2/`Phi_add_Phi_neg` machine-checked | — | was CI-only |
| ~~BRIEF_002~~ | **LANDED GREEN** — oracle ↔ Lean pointwise cross-verifier (39-point golden grid, docs/04 guard 3) | 001 | Python half yes; Lean `#eval` via CI |
| ~~BRIEF_003~~ | **LANDED GREEN** — T3, T4, T4′ machine-checked; sorry baseline → 0 (run 35514867674) | 001 | was CI-only |
| ~~BRIEF_004~~ | **LANDED GREEN** — α-stable exponential-moment obstruction (T6 sub-goal 1; PR #5, run 35523250105) | none | no — CI only |
| ~~BRIEF_005~~ | **LANDED GREEN** — T6 sub-goal 2: Carr–Madan absolute convergence on the tempered contour, GBM instance machine-checked (`ImprovedBS/Fourier.lean`; PR #6, run 35536031936) | 004 | no — CI only |
| ~~BRIEF_006~~ | **LANDED GREEN** — T5, the closed form solves the BSM PDE, directly in `(S, τ)` via T3 + chain rule + `Φ′ = φ`; 11 declarations in `ImprovedBS/Core.lean`, `[SPINE]` check + mutant, statement pins 49 → 60 with the existing 49 unchanged (PR #8, run 35566569107) | 003 | no — CI only |
| ~~BRIEF_007~~ | **LANDED GREEN** (PR #9, run 35574194681) — T6 sub-goal 3(a): the closed form *is* the discounted risk-neutral expectation, `bsCall_eq_riskNeutral_expectation` / `bsPut_eq_riskNeutral_expectation`, the Gaussian bridge `phi`/`Phi` ↔ `gaussianPDFReal 0 1`/`gaussianReal 0 1`, the drift condition and the lognormal form; 21 declarations in `ImprovedBS/RiskNeutral.lean`, statement pins 60 → 81 with the existing 60 unchanged, oracle expectation route + mutant M11 | 005, 006 | no — CI only |
| ~~BRIEF_008~~ | **LANDED GREEN** — T6 sub-goal 3(b): Fourier inversion of the Carr–Madan pricing kernel (`carrMadan_inversion_eq_lognormal_expectation`, `carrMadan_inversion_eq_bsCall`, `carrMadan_inversion_im_eq_zero`); 13 declarations in `ImprovedBS/Inversion.lean`, statement pins 81 → 94, oracle Fourier inversion route + mutant M12, CI run 35578278238 | 005, 007 | no — CI only |
| ~~BRIEF_009~~ | **LANDED GREEN** — the model-free skeleton: parity and the no-arbitrage bounds lifted off the closed form onto `e^{−rτ}·E[(S_T−K)⁺]` for any terminal-spot law with the drift condition (`ImprovedBS/Skeleton.lean`, 14 declarations: `modelFreeCall`/`modelFreePut`, `model_free_parity_gap`/`model_free_put_call_parity`, `model_free_call_bounds`/`model_free_put_bounds`, the GBM instance, and the T2′/T4 re-derivations `*_via_skeleton` that guard the abstraction against vacuity), statement pins 94 → 108, `[SKELETON]` route checks, oracle model-free route + mutants M13/M14, PR #11, CI run 35589005865. Item 5 of the BSM-2 kit (`docs/03` §D1): landed *before* the law is widened, so "the widening preserves the skeleton" is instantiation, not re-proof | 007 | no — CI only |

| ~~BRIEF_010~~ | **LANDED GREEN** — T6's triangle at *any* strip law: the Carr–Madan kernel on the pricing contour (`cmPriceKernel`, implementing the C12 correction), the strike transform, the Fubini exchange that identifies `𝓕(damped price)` with the kernel, inversion in the tree's own normalization, and the pricing identity landing on BRIEF_009's `modelFreeCall`; the GBM instance closes the triangle (`gbm_carrMadan_eq_bsCall`), and the CGMY exponent's decay enters as the one recorded hypothesis (item 4, re-scoped). Landed: 31 declarations in `ImprovedBS/Pricing.lean` (6 defs + 25 audited theorems, all in `REQUIRED` + `PROTECTED`), statement pins 108 → 139 in both layers with the 108 pre-existing entries byte-identical, `[CONTOUR]` route check with its cheat killed by name, oracle `carr_madan_by_law` + `test_carr_madan_free_law` + mutants M15 (kernel on the wrong contour) / M16 (strike transform) killed by that test alone, PR #16, CI run 35646623031 — green on the 9th lean run after eight red (all elaboration/API shape at the tag, incl. the by-design elab-pin bootstrap and one batch-edit race; `benchmarks/LEDGER.md` row 10 and its CI history) | 005, 007, 008, 009 | no — CI only |
| ~~BRIEF_011~~ | **LANDED GREEN** — BSM-2 kit items 1–2: the concrete CGMY characteristic exponent (the `cpow`/branch work BRIEF_005 deferred), its Lévy measure (`∫ (1 ∧ x²) ν < ∞`), and its tempered moment strip, together with the discharge of BRIEF_010 §5's (H-decay) at that exponent so item 4 lands without re-proof. Landed: 52 declarations in `ImprovedBS/CGMY.lean` (11 defs + 41 audited theorems, all in `REQUIRED` + `PROTECTED`), statement pins 139 → 165 in both layers with the 139 pre-existing entries byte-identical, audit list 107 → 148, `[CGMY]` route check with its mutant (29 lint mutants, 5 controls), oracle compensated one-sided Lévy integral + `test_cgmy_contour`, PR #17, CI run 35779316727 — green on the 5th lean run after two elaboration rounds and the by-design elab-pin bootstrap (`benchmarks/LEDGER.md` row 11 and its CI history). Corrections C14 (the pricing line needs `α + 1 < M` alone; no `min (G, M)`) and C15 (its continuity needs `G > 0`, `α > 0`) are this row's. Labelled as prose in the module header, and route-checked numerically: the Lévy–Khintchine representation itself | 005, 010 | no — CI only |
| ~~BRIEF_012~~ | **LANDED GREEN** — BSM-2 kit item 7 (ledger C13): the machine-checked non-uniqueness witness. Landed: 45 declarations in `ImprovedBS/NonUniqueness.lean` (7 defs + 38 audited theorems, all in `REQUIRED` + `PROTECTED`), statement pins 165 → 210 in both layers with the 165 pre-existing entries byte-identical (`added 45, changed 0`), audit list 148 → 186, the `[NONUNIQ]` route check with three cheats killed by name (32 lint mutants, 5 controls), oracle `test_nonuniqueness_witness` in exact `Fraction` arithmetic with mutants M17 (drift canary) / M18 (linear payoff) / M19 (B := A) killed by that test, PR #19, lean run 36052072620 (oracle lane 36052072567) — green on the 3rd lean run: one red on two `linarith` calls (an atom split by `cancelDenoms`, not mathematics), one red by design on the empty `elab` block, one green with the block merged (`benchmarks/LEDGER.md` row 12 and its CI history). Correction C16 is this row's: the brief's own canary row had the wrong mean (`3/2`, not `1.25`) and its literal M18 is blind at the witness. As issued: a one-period trinomial — spots `(1/2, 1, 2)`, `S = τ = K = 1`, `r = q = 0` — with two interior martingale measures `A = (1/2, 1/4, 1/4)` and `B = (1/4, 5/8, 1/8)`, both with `E[S_T] = 1`, both satisfying BRIEF_009's parity and no-arbitrage bounds, mutually absolutely continuous, and pricing the call at `1/4` versus `1/8`. Lands `static_skeleton_does_not_select_measure` as a conjunction, plus the martingale-set parametrization `p₃ = p₁/2`, `p₂ = 1 − 3p₁/2` that makes the witness canonical rather than cherry-picked. New module `ImprovedBS/NonUniqueness.lean`; consumes `model_free_put_call_parity`/`model_free_call_bounds` by citation (a `[NONUNIQ]` route check), and the oracle side needs **no new function** — `model_free_prices`/`model_free_forward` already cover it. Witness route-checked against the oracle before issue, incl. a drift canary whose parity gap moves to `0.25`. The brief's unmitigated risk (no toolchain *and* no network at issue, so ledger C3's name check could not run) was retired at implementation: every mathlib name was read at the v4.34.0 source before pushing, and the module built on its second compile with no name or shape error | 009 | no — CI only |
| ~~BRIEF_013~~ | **LANDED GREEN** — BSM-2 kit item 3: the Esscher drift at CGMY. Landed: 30 declarations in `ImprovedBS/Esscher.lean` (5 defs + 25 audited theorems, all in `REQUIRED` + `PROTECTED`), statement pins 210 → 240 in both layers with the 210 pre-existing entries byte-identical (`added 30, changed 0, elab now 240`), audit list 186 → 211, the `[ESSCHER]` route check with three cheats killed by name (35 lint mutants, 5 controls), oracle Esscher primitives + `test_esscher_drift` with mutants M20 (shift sign) / M21 (dropped inner abs) killed by it, PR #20, lean run 36072416203 (oracle lane 36072416317) — green on the 8th lean run after seven red, all elaboration/API shape at the tag (`Real.hasDerivAt_rpow_const`'s implicit telescope, `Function.comp` opaque to `convert`, `congr_of_eventuallyEq`'s argument orientation, `intermediate_value_Ioo` wanting `a ≤ b`) and the by-design elab-pin bootstrap with the CI-emitted block merged verbatim (`benchmarks/LEDGER.md` row 13 and its CI history). As issued: the shift `ψ^θ(v) = ψ(v − iθ) − ψ(−iθ)` keeps CGMY inside the family (`(G, M) ↦ (G+θ, M−θ)`), the cumulant is strictly convex on the strip via `κ″ = CΓ(2−Y)[(M−u)^{Y−2} + (G+u)^{Y−2}]` (the Γ rewrite `Γ(−Y)·Y·(Y−1) = Γ(2−Y)`), so `κ(θ+1) − κ(θ) = r − q` solves uniquely in `(−G, M−1)` exactly when `|r − q| < |CΓ(−Y)|·|(G+M)^Y − (G+M−1)^Y − 1|`, with zero drift at the exact `θ₀ = (M−G−1)/2`; the tilted factor equals `e^{τ(r−q)}` at the solution and the pricing kernel stays integrable on the shifted contour by consuming `cgmy_cmPriceKernel_integrable`. Lands at the factor level: the expectation-level twin of `integral_spot_mul_phi_eq_forward` stays gated on a CGMY law construction (the brief's re-scope note) | 010, 011 | no — CI only |

**BRIEF_012 landed** (row above): item 7 of the kit, the machine-checked
non-uniqueness witness, which C13 named as the successor and which was the only
remaining kit item that tests the repository's own framing rather than
extending it — the README's dynamic/static split is now a theorem
(`static_skeleton_does_not_select_measure`) rather than prose. **BRIEF_013
landed** (PR #20, lean run 36072416203; issuance row and grading row in
`benchmarks/LEDGER.md`): item 3
of the kit, the drift fixed at a *named* pricing measure — **via the Esscher
transform**, now as 30 machine-checked declarations in `ImprovedBS/Esscher.lean`: the exponent shift `ψ^θ(v) = ψ(v − iθ) − ψ(−iθ)` keeps CGMY inside
the family (`(G, M) ↦ (G+θ, M−θ)`), the drift equation
`κ(θ+1) − κ(θ) = r − q` is strictly monotone (the cumulant's strict convexity
is a second derivative, `κ'' = CΓ(2−Y)[(M−u)^{Y−2} + (G+u)^{Y−2}] > 0`), and
the strip decides solvability: a unique `θ ∈ (−G, M−1)` exists exactly when
`|r − q| < |CΓ(−Y)|·|(G+M)^Y − (G+M−1)^Y − 1|`, with the zero-drift parameter
the exact `θ₀ = (M−G−1)/2`. Item 3 lands at the factor level — the tree has no
CGMY law as a measure, so the expectation-level twin of
`integral_spot_mul_phi_eq_forward` stays gated on a law construction (the
brief's re-scope note, BRIEF_010's move one level down). The requirement it is
written against is proved: item 7 went first deliberately — C13's words are
that the witness "is what obliges item 3's 'named'" — and C13's monotonicity
remark ("non-uniqueness lives across selection principles, not within the
Esscher family") becomes the brief's in-family uniqueness theorem. **BRIEF_014+
not yet issued**: item 6, the corner recovery of GBM at `Y → 2`, has a pole to
deal with (`Γ(−Y)` at `Y = 2`) that items 3 and 7 did not; C13's two repair
briefs (the Pareto witness for `Levy.lean`'s tail hypothesis, and the Haug /
term-structure external anchor) stay queued after the kit items and are
numbered at issue (C13's provisional "013/014" assignment for them is
superseded — recorded in BRIEF_013's numbering note). Items 1–2 landed as
BRIEF_011 and item 7 as BRIEF_012 (rows above). The order constraint for
whoever issues them holds: items 3 and 6 are the new analysis and can be split
further (items 1–2 were exactly that — the exponent's `cpow`/branch work was
BRIEF_011); item 4's
exponent↔law connection was the known risky step and it took BRIEF_004's
re-scope option — BRIEF_010 landed it with the law abstracted behind a
hypothesis the way the decay bound is already abstracted, and the hypothesis
recorded rather than assumed (`docs/03` §D1 item 4 now reads that way).
BRIEF_011's acceptance bar was shaped as: supply the CGMY factor's continuity and
decay on the contour `u ↦ u − i(α+1)` for `0 < α`, `α + 1 < min(G, M)`,
instantiating BRIEF_010 §5's hypothesis so that item 4 lands at the concrete
exponent without re-proving it. It landed, with two corrections the brief found
rather than inherited: the contour condition is `α + 1 < M` alone (C14 — `G`
binds only the old line `u + iα`), and the *continuity* half additionally needs
`G > 0` and `α > 0` (C15 — the right base's imaginary part is `u`, which vanishes
at `u = 0`, so its real part carries the branch condition there).

BRIEF_004 is deliberately listed as depending on nothing: it is pure analysis
(a divergent improper integral), needs none of the BS machinery, and it is the
item that makes the tempered-stable hypothesis in `docs/03` §D1 an earned
assumption rather than a convenient one. If only one research-tier brief ever
gets worked, it should be that one.

T5 *was* the item that needed a decision belonging in the brief rather than in
this document — formalize the PDE in `(S, t)` with partial derivatives, or reduce
to the constant-coefficient heat equation in `x = Real.log S` first — and
BRIEF_006 §1 commits to the first, with the reasons above, superseding this
section's earlier argument for the second (ledger C9). The "not yet a brief"
paragraph that stood here also asked the wrong brief to make the decision: it
said "whoever writes BRIEF_005", and BRIEF_005 was the tempered contour. Two
sentences of this document have now been wrong about BRIEF_005's subject and
about T5's route; both are recorded rather than quietly edited, because the
queue is the part of the plan a contributor reads first, and a stale queue
spends someone else's budget.
