# Improved Black-Scholes · Arena benchmark

> "How to improve on Black-Scholes" is listed as an open question in
> quantitative finance. This is an **Arena benchmark repo**: a hard, sharply
> specified open problem that new frontier models get pointed at, with
> machine-graded acceptance, so we can *see what different models can do* —
> and accumulate the results into a public corpus.

The point of the program is measurement, not just code. Every contributed
PR is graded by a machine (no human judgment in the pass/fail), recorded in
the benchmark ledger, and the archive over many models is the actual
deliverable: which approaches succeeded, which failed instructively, and *how*
different model generations attack an open problem.

## Thesis (the framing this repo commits to)

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

So the benchmark is really "**widen the increment law, and prove you did.**"
That is a theorem program graded by a proof checker — ideal for an Arena
harness.

## Repository layout

```
Lean/core/          # Lean 4 statements: theorem stack T1..T6 (mathlib-backed build)
briefs/             # Arena briefs catalog (the tasks handed to models)
benchmarks/         # ledger: model -> brief -> PR -> machine verdict (the corpus)
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

Cold-outline: T1–T4 are within reach of most frontier models. T5 is the
centerpiece most stakes rise on. T6 is *the* research claim — the place where
a genuinely new approach (not a reimplementation) is the deliverable.

## Status (this box)

| Layer | what | status |
|---|---|---|
| Numeric oracle | bs_price, parity, PDE residual, delta-identity | verified (10/10 tests) |
| Failure modes + research dirs w/ falsifiers | docs/02, docs/03 | written |
| Lean statement files | T1..T6 | spec — machine-check pending a mathlib build |
| Arena harness | briefs/ + benchmarks/ + CI | bootstrapping (this commit) |
| First brief | authored, ready to hand out | see briefs/ |

## License

MIT. The mathematics (and its history) belongs to the half-century of
volatility-surface literature that this benchmark builds on; our contribution
is the formal, machine-checked restatement and the widening question.

## Running the oracle

```sh
python3 tests/test_bs.py          # 10/10, no deps
# or, with pytest installed:
pytest tests/
```