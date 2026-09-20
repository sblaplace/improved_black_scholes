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
green and no `sorry` survives, not when prose says so.

## How the work is packaged

Every unit of work is a self-contained brief in `briefs/`: background
reading in order, a numbered scope, an explicit out-of-scope, and an
acceptance bar CI can check mechanically. Each brief lands as a PR; CI
grades it (`lake build` on the Lean tree + the oracle tests), and the
outcome is recorded in `benchmarks/LEDGER.md` — GREEN/RED/PENDING from the
harness, never a human "looks good", and a RED verdict on an approach is a
result, not an incident.

Part of the motivation for this packaging: some briefs get handed to coding
agents (Arena among other venues), which is a live way to see what new
models can do on a hard, sharply-specified open problem — a real PR against
a real proof checker, not a chat answer. But the point of the repo is the
mathematics, and the bar lives in the repository, identical for whoever —
or whatever — lands the PR.

## Repository layout

```
Lean/core/          # Lean 4 statements: theorem stack T1..T6 (mathlib-backed build)
briefs/             # task briefs: self-contained work orders, one PR each
benchmarks/         # ledger: brief -> PR -> CI verdict
experiments/        # numeric oracle (stdlib-only) — the sanity handrail
tests/              # oracle tests (pure python, no deps)
docs/               # 01 baseline math, 02 failure modes, 03 research dirs, 04 formal plan
.github/workflows/  # CI: oracle lane (always) + Lean build lane (mathlib)
```

## The theorem stack, by threshold

| #  | statement                              | difficulty | current |
|----|----------------------------------------|-----------|---------|
| T1 | `d1 - d2 = sigma*sqrt(tau)`             | trivial    | stated  |
| T2 | put-call parity                          | easy       | stated  |
| T3 | delta-identity `S e^{-q tau} phi(d1) = K e^{-r tau} phi(d2)` | medium | stated |
| T4 | no-arbitrage price bounds                | medium     | stated  |
| T5 | closed form solves the BSM PDE (heat identity) | heavy    | stated  |
| T6 | transport (Fourier) kernel survives a-stable increments | open  | open    |

T1–T4 are the warm-up tier — routine algebra and monotonicity once the
toolchain is standing. T5 is the first heavy node: the closed form as the
unique heat-kernel solution, which needs the `erf`/`log` derivative
machinery from mathlib. T6 is the research claim — the place where a
genuinely new approach, not a reimplementation, is the deliverable.

## Status (this box)

| Layer | what | status |
|---|---|---|
| Numeric oracle | bs_price, parity, PDE residual, delta-identity | verified (10/10 tests) |
| Failure modes + research dirs w/ falsifiers | docs/02, docs/03 | written |
| Lean statement files | T1..T6 | spec — machine-check pending a mathlib build |
| Grading lane | briefs/ + benchmarks/ + CI | bootstrapping (this commit) |
| First brief | authored, ready to hand out | see briefs/ |

## License

MIT. The mathematics (and its history) belongs to the half-century of
volatility-surface literature that this program builds on; our contribution
is the formal, machine-checked restatement and the widening question.

## Running the oracle

```sh
python3 tests/test_bs.py          # 10/10, no deps
# or, with pytest installed:
pytest tests/
```
