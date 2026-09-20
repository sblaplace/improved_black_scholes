# Improved Black-Scholes

> "How to improve on Black-Scholes" is listed as an open question in
> quantitative finance. The claim this repo commits to: Black-Scholes-Merton
> is a theorem about one specific stochastic process, and its famous
> failures are failures of that process's **increment law**, not of the
> arbitrage-free skeleton that makes a closed form exist. So "improving" BS
> means widening the class of increment laws that still admit a closed
> pricing kernel — and *proving* the widening preserves the skeleton. Every
> claim lands as a Lean 4 theorem that CI machine-checks, with a
> dependency-free numeric oracle as the sanity handrail.

## Thesis

Black-Scholes-Merton is not a "wrong formula." It is the *correct price for
one specific stochastic process* — geometric Brownian motion (GBM) under a
single constant-volatility factor — and its famous failures (1987 crash, 1998
LTCM/Russian default, 2008, the vol smile) are failures of that **process
assumption**, not of the PDE/martingale skeleton that makes a closed form
exist in the first place.

That split is the lever:

- The **skeleton** (arbitrage-free pricing by risk-neutral expectation ⇒ heat
  equation ⇒ closed form when the increment is lognormal with constant vol)
  is robust and worth formalizing. It is *why BS is a theorem about GBM*. This
  is the provable part.
- The **increment law** (lognormal, constant σ, single factor) is the fragile
  bit markets reject. Improving BS = widening the class of increment laws
  that still admit a *closed pricing kernel*, and proving the widening
  preserves the skeleton.

So the program in one line: **widen the increment law, and prove you did.**
The proof checker is the judge — a theorem is done when `lake build` is
green *and* `#print axioms` shows no `sorryAx`, not when prose says so.

## A rule the whole repo is built around: no vacuous claims

A green check is only evidence if it could have been red. This applies to the
tests as much as to the proofs, and the repo has been bitten by it once
already: defining `d2 := d1 − σ√τ` and `bsPut := bsCall − S e^{−qτ} + K e^{−rτ}`
makes the first two theorems true *by construction*. Both proofs collapse to
`ring`, the parity theorem never touches `Φ(x) + Φ(−x) = 1` — the only
identity it is actually about — and a green build certifies nothing.

So every identity is checked between **independently derived** expressions, in
both trees, and the property is enforced mechanically:

- `d2` and `bsPut` have their own explicit closed forms, in
  `experiments/black_scholes.py` and in `ImprovedBS/Core.lean`.
- `scripts/lean_lint.py` fails CI if `d2` is defined from `d1`, if `bsPut` is
  defined from `bsCall`, or if `t2_put_call_parity` stops citing
  `Phi_add_Phi_neg`. It needs no Lean toolchain to do this.
- `tests/test_mutants.py` seeds 11 bugs into the oracle and requires each to be
  killed by the test meant to kill it. Two of them exist purely to prove the
  parity and `d1 − d2` tests can fail.

A third lane closes a gap neither of those could see. `lake build` proves a proof is
*correct*; nothing proves a theorem is still *the theorem*. Restate a landed node as

    theorem t4_call_bounds (S K tau r q sigma : ℝ)
        (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) : True := trivial

and it builds, shows no `sorryAx` — because `True` really is provable, which is what
makes it a *sound* way to say nothing — keeps its name for the lint's `REQUIRED`
check, and leaves the oracle suite at 13/13, since the oracle has no idea what a
Lean statement is. So every declaration in the protected stack is pinned in
`tests/golden_statements.json`: a theorem by its **statement**, a definition by its
**body** (a definition *is* the specification). `scripts/pin_statements.py`
extracts and compares; `lean_lint.py` enforces it with no toolchain, and the build
job re-elaborates the pinned `#check` types and `#print axioms` output, which is
where a statement that *reads* the same but elaborates differently gets caught.
Weakening a claim is still allowed. It is now a diff a reviewer sees.

And because `lean_lint.py` has authority over how the Lean tree is labelled while
nothing had authority over *it*, `tests/test_lint.py` seeds 22 cheats into copies
of the tree and requires each to be killed by a *named* check, keeps 5 legitimate
edits green (a re-wrapped proof, marker words inside a comment, parity reproved
from `erf_neg` directly), and asserts — rather than folklore-claims — the boundary
it cannot cross: hollow a statement, regenerate the source pins, *and* hand-forge
the elaborated block to match, and every lane that can run without a toolchain is
satisfied by the self-consistency. That forgery is exactly what CI cannot survive,
because CI re-elaborates rather than re-reading: `#check @BSM.t4_call_bounds`
prints the bound, so a committed `: True` is a diff. The half of it that *was*
local — regenerating layer 1 and leaving layer 2 stale — is now caught by the
cross-layer skew check, and its mutant moved into the must-die list.
That is also why swapping the numeric oracle for another language would have bought
nothing here: the oracle is a probe, the linter was the pillar, and a pillar is
unverified in any language until something pushes on it.

## How the work is packaged

Every unit of work is a self-contained brief in `briefs/`: background
reading in order, a numbered scope, an explicit out-of-scope, and an
acceptance bar CI can check mechanically. Each brief lands as a PR; CI
grades it (`lake build` on the Lean tree + the oracle tests + the lint), and
the outcome is recorded in `benchmarks/LEDGER.md` — GREEN/RED/PENDING from the
harness, never a human "looks good", and a RED verdict on an approach is a
result, not an incident.

Part of the motivation for this packaging: some briefs get handed to coding
agents (Arena among other venues), which is a live way to see what new
models can do on a hard, sharply-specified open problem — a real PR against
a real proof checker, not a chat answer. But the point of the repo is the
mathematics, and the bar lives in the repository, identical for whoever —
or whatever — lands the PR.

**A constraint worth stating plainly, because briefs are graded against it:**
a Lean deliverable can only be *built* where there is network access to the
Lean toolchain CDN and the Mathlib olean cache. A sandbox without that access
can still run the oracle, the mutation harness and the lint — all three are
pure Python — but it cannot substitute for the `lake build` lane. Briefs say
which of their acceptance criteria are locally checkable and which are
CI-only, so nobody spends a budget discovering this.

## Repository layout

```
ImprovedBS/         # Lean 4 library: Core.lean, `namespace BSM`, stack T1..T6
ImprovedBS.lean     # library root module
lakefile.toml       # mathlib pinned by tag; leanOptions (autoImplicit off)
lean-toolchain      # pinned toolchain — must match lake-manifest.json
lake-manifest.json  # exact dependency revisions (reproducibility)
briefs/             # task briefs: self-contained work orders, one PR each
benchmarks/         # ledger: brief -> PR -> CI verdict
experiments/        # numeric oracle (stdlib-only) — the sanity handrail
tests/              # oracle tests + 2 mutation harnesses + the pinned claims (json)
scripts/            # lean_lint.py, pin_statements.py, gen_grid.py: toolchain-free grading
docs/               # 01 baseline math, 02 failure modes, 03 research dirs, 04 formal plan
.github/workflows/  # CI: oracle lane + lean lane (lint job, then build job)
```

## The theorem stack, by threshold

Status is machine-derived: `python3 scripts/lean_lint.py` prints the live
count, and `.github/lean_lint_baseline.json` is the ceiling it ratchets
against.

| #  | Lean name | statement | difficulty | status |
|----|-----------|-----------|-----------|--------|
| —  | `Phi_add_Phi_neg` | `Φ(x) + Φ(−x) = 1` | trivial | **machine-checked** |
| T1 | `t1_d1_minus_d2` | `d1 − d2 = σ√τ` | easy | **machine-checked** |
| T2 | `t2_put_call_parity` | put-call parity | easy | **machine-checked** |
| T3 | `t3_delta_identity` | `S e^{−qτ} φ(d1) = K e^{−rτ} φ(d2)` | medium | **machine-checked** |
| T4 | `t4_call_bounds`, `t4_put_bounds` | no-arbitrage price bounds | medium | **machine-checked** |
| T5 | *(not declared)* | closed form solves the BSM PDE | heavy | deferred — provable *via* T3 |
| T6 | *(not declared)* | Fourier kernel survives a tempered-stable increment | open | restated, see docs/03 D1 |

T1–T4 are the warm-up tier, and all four are now machine-checked. T4 turned
out to be less routine than "algebra and monotonicity": its lower bound is the
positivity of the call and the put, which needs `Φ` as an *integral* of `φ`
(`Phi_eq_integral_Iic`), not just `0 ≤ Φ ≤ 1` — see ledger correction C4. T5 is
the first heavy node, and the plan is to reach it
*through* T3 — the delta identity is exactly the cancellation that makes the
PDE residual vanish, so T5 is T3 plus the chain rule plus `Φ′ = φ`, not an
independent slog through `erf` derivatives. T6 is the research claim, and it is
the place where a genuinely new approach, not a reimplementation, is the
deliverable.

**T6 carries a warning that saves a brief.** A *pure* α-stable log-increment
has infinite first moment (`P(X > x) ~ x^{−α}` ⇒ `E[e^X] = ∞`), so
`S_T = S_0 e^{X_τ}` cannot be a martingale at all and the Fourier pricing
contour has no moment strip to sit in. The obstruction is at the moment step,
not the kernel step. The direction is viable only in **tempered** form
(CGMY / Boyarchenko–Levendorskii), where an `e^{−λ|x|}` damping of the Lévy
measure restores the exponential moment, keeps algebraic tails at option
tenors, and recovers both α-stable (λ→0) and GBM (α→2) as limits. Proving the
obstruction itself — a concrete divergent integral, no finance in it — is the
cheapest high-value theorem in the research tier. Details in docs/03 §D1.

## Status

| Layer | what | status |
|---|---|---|
| Numeric oracle | independent `d1`/`d2`, independent call and put closed forms, PDE residual, delta identity | verified — 13/13 tests |
| Oracle is a falsifier | mutation harness: 11 seeded bugs, each killed by its targeted test, incl. 2 vacuity canaries | verified — 4/4 harness tests |
| Failure modes + research dirs w/ falsifiers | docs/02, docs/03 | written |
| Lean definitions | `erf`, Φ, φ, d1, d2, bsCall, bsPut — independent, matching the oracle | machine-checked |
| Lean theorems | `Phi_add_Phi_neg`, T1, T2, T2′ | **GREEN** — `lake build` + `#print axioms` audit, run 35509578689 |
| Lean theorems | T3, T4, T4′ + the `Φ = ∫ φ` infrastructure (18 lemmas) | **GREEN** — `lake build` + `#print axioms` audit, run 35514867674 |
| Deferred | *(nothing)* | ratcheted at 0 `sorry`s — `deferred: {}` |
| Lint is a falsifier | `tests/test_lint.py`: 22 seeded cheats each killed by a named check, 5 legitimate edits green, 1 residual gap asserted open | verified — 7/7 tests |
| Pinned claims | `tests/golden_statements.json`: 31 declarations — theorem statements, definition bodies | machine-checked (source level, no toolchain); `#check`/axioms layer runs in the build job |
| Grading lane | briefs/ + benchmarks/ + 2 CI workflows + toolchain-free lint + pins | standing |
| First brief | BRIEF_001, re-scoped to what is actually checkable | see briefs/ |

**T1 through T4 are machine-checked.** `lake build` is green against mathlib
v4.34.0 / Lean v4.34.0 and the `#print axioms` audit confirms that all 25
declarations in the T1–T4 node — `Phi_add_Phi_neg`, `Phi_neg`, `erf_neg`,
`exp_neg_sq_even`, `t1_d1_minus_d2`, `t2_put_call_parity`,
`t2_put_call_parity_spread`, `t3_delta_identity`, `t4_call_bounds`,
`t4_put_bounds` and the sixteen lemmas they rest on — depend only on
`[propext, Classical.choice, Quot.sound]`, never on `sorryAx`. That is the
distinction that matters, since a `sorry` still builds. T1/T2 took eight CI
runs (PR #1); T3/T4 landed green on the first run (PR #2) because every mathlib
name was checked against the pinned tag before pushing. `benchmarks/LEDGER.md`
records both histories, including one runner incident (ENOSPC) that produced no
verdict at all.

Three things that green build cost, and that a reader should know:

- **mathlib v4.34.0 has no `Real.erf`.** `docs/04` used to claim it did. `erf`
  is now defined locally from the interval integral and its oddness proved by
  substitution — enough for parity. T3/T4 additionally needed
  `Φ(x) = ∫_{(−∞,x]} φ`, which imports the *value* of the Gaussian integral
  (`integral_gaussian_Ioi`) in exactly one lemma, `integral_phi_Iic_zero`.
- All declarations live in `namespace BSM`. A module name is not a namespace,
  and a library that puts `Phi`, `d1` and `erf` in the root namespace is
  claiming names far too generic to claim.
- `import Mathlib` rather than narrow imports. Narrow imports are better
  practice but can only be validated with a toolchain; two hand-guessed paths
  cost three red runs. Narrowing the list is a legitimate follow-up for someone
  who can build.

## License

MIT. The mathematics (and its history) belongs to the half-century of
volatility-surface literature that this program builds on; our contribution
is the formal, machine-checked restatement and the widening question.

## Running the checks locally

All three are dependency-free Python; none needs a Lean toolchain.

```sh
python3 tests/test_bs.py          # 13/13 — the oracle satisfies the claimed identities
python3 tests/test_mutants.py     #  4/4  — and those tests can actually fail (11 mutants)
python3 tests/test_lint.py        #  7/7  — the linter can fail too (22 cheats, 5 controls)
python3 tests/test_pins.py        #  8/8  — and the pins that back it parse real CI output
python3 scripts/lean_lint.py      #  OK   — no sorry in the protected node, ratchet, independence, pins
python3 scripts/pin_statements.py --check   # 31 statements match tests/golden_statements.json
python3 tests/test_crosscheck.py    #  4/4  — grid + oracle self-consistency (the cross-check itself needs lake)
# or, with pytest installed:
pytest tests/
```

None of the four harnesses needs a Lean toolchain, by design: `tests/test_lint.py`
mutates copies of the tree and runs the lint against them exactly as CI does, and
`tests/test_pins.py` replays recorded `lake env lean` output through the pin
parser instead of assuming its format. The pins' elaborated layer
(`#check` types, `#print axioms`) is the one part that genuinely needs a
toolchain, so it is graded by the build job and its local behaviour is asserted to
be *red*, not skipped.

The Lean build itself needs elan + the mathlib cache:

```sh
lake exe cache get && lake build  # see docs/04 for the pinning rules
```
