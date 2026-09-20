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

| #  | Lean name | statement | difficulty | status |
|----|-----------|-----------|-----------|--------|
| —  | `Phi_add_Phi_neg` | `Φ(x) + Φ(−x) = 1` | trivial (given `Real.erf_neg`) | **proved, no `sorry`** |
| T1 | `t1_d1_minus_d2` | `d1 − d2 = σ√τ` | easy (field algebra) | **proved, no `sorry`** |
| T2 | `t2_put_call_parity` | `bsPut = bsCall − S e^{−qτ} + K e^{−rτ}` | easy (linear, given Φ symmetry) | **proved, no `sorry`** |
| T2′| `t2_put_call_parity_spread` | `bsCall − bsPut = S e^{−qτ} − K e^{−rτ}` | corollary of T2 | **proved, no `sorry`** |
| T3 | `t3_delta_identity` | `S e^{−qτ} φ(d1) = K e^{−rτ} φ(d2)` | medium (exp/log algebra) | stated, `sorry` — route recorded below |
| T4 | `t4_call_bounds` | `max(S e^{−qτ} − K e^{−rτ}, 0) ≤ bsCall ≤ S e^{−qτ}` | medium (Φ ∈ [0,1], monotone) | stated, `sorry` |
| T4′| `t4_put_bounds` | mirrored put bounds | corollary of T4 + T2 | stated, `sorry` |
| T5 | *(not yet declared)* | `V_t + (r−q)S V_S + (σ²/2)S² V_SS = r V` | heavy | deferred — see the spine below |
| T6 | *(not yet declared)* | Fourier pricing kernel survives a wider increment law | open — research | restated in docs/03 D1 |

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

    Real.erf_neg ──► Phi_add_Phi_neg ──► T2 ──► T2′
                                     └──► T4′
    Real.mul_self_sqrt ──► T1 ──► T3 ──► T5
                            └──► T4

**Prove T5 through T3.** Substituting the closed form into the BSM operator,
the `S²V_SS` term produces `φ(d1)` and `φ(d2)` contributions whose *difference*
is exactly what T3 cancels. So

    T5  =  T3  +  chain rule  +  `HasDerivAt Phi phi x`

and the only genuinely new analytic input is the derivative of Φ, which follows
from `Real.hasDerivAt_erf`. Brute-force differentiation of `erf ∘ (log-rational)`
in `S`-coordinates is the slow route and buys nothing.

**Change variables before differentiating.** In `x = Real.log S` the BSM
operator has constant coefficients and the closed form is the convolution of the
payoff with the Gaussian kernel; uniqueness then comes from the heat-kernel
side. Working in `S` costs every `1/S` factor by hand.

## Dependencies needed from mathlib

Pinned: mathlib **v4.34.0**, toolchain **leanprover/lean4:v4.34.0** (see
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json` — all three must move
together, and `.github/workflows/lean.yml` fails the run if they disagree).

| need | available in mathlib v4.34.0? | used by |
|---|---|---|
| `Real.log`, `Real.exp` algebra | **yes** — `Mathlib.Analysis.SpecialFunctions.Log.Basic`, `.../Exp.lean` | d1, d2, T3 |
| `Real.sqrt`, `Real.mul_self_sqrt`, `Real.sqrt_pos` | **yes** — `Mathlib.Data.Real.Sqrt` | T1, T3 |
| `Real.pi` | **yes** (57 references in the tree) | φ, erf |
| interval integrals, `integral_comp_neg`, `integral_symm` | **yes** — `Mathlib.MeasureTheory.Integral.IntervalIntegral` | `erf_neg`, hence T2 |
| **`Real.erf`** | **NO — it does not exist.** See below. | Φ, T2 |
| `∫ x:ℝ, exp (-(x^2)) = sqrt pi` | **yes** — `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` | T4 bounds, T5 |
| normal CDF/PDF as a distribution | partial — `Mathlib.Probability.Distributions.Gaussian` has the *measure*, not a CDF function | optional; T5, T6 |

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
only *oddness*. It is **not** sufficient for T4, which needs `|erf x| ≤ 1` and
therefore the *value* of the Gaussian integral — measure theory rather than
interval integrals, and the genuinely expensive part of that node. T5 likewise
needs `HasDerivAt erf`, which now has to be derived rather than imported.

If mathlib grows `Real.erf`, delete the local definition and re-point
`Phi_add_Phi_neg` at `Real.erf_neg`. `scripts/lean_lint.py` has `erf`,
`erf_neg` and `exp_neg_sq_even` in both `REQUIRED` and `PROTECTED`, so that
migration cannot silently drop them.

`Φ` and `φ` are currently defined directly from `Real.erf` and `Real.exp`
rather than imported from mathlib's Gaussian machinery. That is deliberate for
T1–T4 (fewer moving parts, definitions match the oracle symbol-for-symbol) and
should be revisited at T5/T6, where the measure-theoretic integral is the
actual object. **Do not switch before then** — it would change what T1–T4 are
about without changing what they say.

Imports in `ImprovedBS/Core.lean` are currently the whole library
(`import Mathlib`). Narrow imports are better practice — they document what a
theorem rests on and cost less elaboration — but they can only be validated by a
toolchain, and two hand-guessed narrow paths cost three red CI runs. Narrowing
the import list is a legitimate follow-up **for someone who can run
`lake build`**; it should not be attempted blind. The table above records what
is actually needed, which is the information a narrowing PR requires.

## Oracle ↔ formal correspondence

The Python oracle and the Lean tree share notation *and* arithmetic meaning,
but they are still two hand-written sources, so they can drift. Three guards,
in increasing strength:

1. **Structural** — `scripts/lean_lint.py` `[ORACLE SYNC]` checks that both
   trees define `d2` and the put independently. Runs with no toolchain.
2. **Behavioural** — `tests/test_mutants.py` seeds bugs into the oracle and
   requires the targeted test to fail, including two vacuity canaries. This is
   the check that a test can fail.
3. **Pointwise (still a milestone)** — a cross-verifier that evaluates
   `d1`, `d2`, parity and the delta identity at rational grid points in *both*
   trees and compares. The natural form is a Lean `#eval` over `Float` printed
   in CI and diffed against the oracle's output, or a generated
   `tests/golden_*.json` that both sides read. Not a proof — a contradiction
   detector. Not yet built; it is the right BRIEF_002.

Until (3) exists, the correspondence rests on (1) and (2) plus human reading of
docs/01 §4. That is weaker than this repository would like and it is recorded
here rather than glossed.

## The brief queue

Order is chosen so that each brief's acceptance bar is checkable by the time it
is worked on, and so that no brief depends on a machine-checked result that does
not yet exist.

| brief | what it lands | depends on | locally checkable? |
|---|---|---|---|
| BRIEF_001 | `lake build` green; T1/T2/`Phi_add_Phi_neg` machine-checked | — | no — CI only |
| BRIEF_002 | oracle ↔ Lean pointwise cross-verifier | 001 | Python half yes; Lean `#eval` no |
| BRIEF_003 | T3 and T4 proved; sorry baseline → 0 | 001 | no — CI only |
| BRIEF_004 | α-stable exponential-moment obstruction (T6 sub-goal 1) | none | no — CI only |
| *(queued)* | **T5** — closed form solves the BSM PDE, via T3 in `x = Real.log S` coordinates | 003 | no — CI only |
| *(queued)* | **T6** sub-goals 2–3 — Carr–Madan absolute convergence and agreement with the risk-neutral expectation, for a tempered-stable exponent | 004 | no — CI only |

BRIEF_004 is deliberately listed as depending on nothing: it is pure analysis
(a divergent improper integral), needs none of the BS machinery, and it is the
item that makes the tempered-stable hypothesis in `docs/03` §D1 an earned
assumption rather than a convenient one. If only one research-tier brief ever
gets worked, it should be that one.

T5 is *not* yet a brief, because it needs a decision that belongs in the brief
rather than in this document: whether to formalize the PDE in `(S, t)`
coordinates with partial derivatives, or to reduce to the constant-coefficient
heat equation in `x = Real.log S` first. `docs/04` §"The dependency spine"
argues for the second. Whoever writes BRIEF_005 should commit to one and say
why, rather than leaving both open.
