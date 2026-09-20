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
tests/              # oracle tests + mutation harness (pure python, no deps)
scripts/            # lean_lint.py: toolchain-free enforcement of the grading rule
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
| T3 | `t3_delta_identity` | `S e^{−qτ} φ(d1) = K e^{−rτ} φ(d2)` | medium | stated — proof route recorded |
| T4 | `t4_call_bounds`, `t4_put_bounds` | no-arbitrage price bounds | medium | stated |
| T5 | *(not declared)* | closed form solves the BSM PDE | heavy | deferred — provable *via* T3 |
| T6 | *(not declared)* | Fourier kernel survives a tempered-stable increment | open | restated, see docs/03 D1 |

T1–T4 are the warm-up tier: routine algebra and monotonicity once the
toolchain is standing. T5 is the first heavy node, and the plan is to reach it
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
| Deferred | T3, T4, T4′ stated with proof routes | ratcheted at 3 `sorry`s |
| Grading lane | briefs/ + benchmarks/ + 2 CI workflows + toolchain-free lint | standing |
| First brief | BRIEF_001, re-scoped to what is actually checkable | see briefs/ |

**T1 and T2 are machine-checked.** `lake build` is green against mathlib
v4.34.0 / Lean v4.34.0 and the `#print axioms` audit confirms that
`Phi_add_Phi_neg`, `Phi_neg`, `erf_neg`, `exp_neg_sq_even`, `t1_d1_minus_d2`,
`t2_put_call_parity` and `t2_put_call_parity_spread` do not depend on `sorryAx`
— which is the distinction that matters, since a `sorry` still builds. It took
eight CI runs to get there; `benchmarks/LEDGER.md` records each failure and what
it taught, including one runner incident (ENOSPC) that produced no verdict at
all.

Three things that green build cost, and that a reader should know:

- **mathlib v4.34.0 has no `Real.erf`.** `docs/04` used to claim it did. `erf`
  is now defined locally from the interval integral and its oddness proved by
  substitution — enough for parity, *not* enough for T4's bounds, which need the
  value of the Gaussian integral.
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
python3 scripts/lean_lint.py      #  OK   — no sorry in the protected node, ratchet, independence
# or, with pytest installed:
pytest tests/
```

The Lean build itself needs elan + the mathlib cache:

```sh
lake exe cache get && lake build  # see docs/04 for the pinning rules
```
