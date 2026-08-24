# Improved Black-Scholes

> "How to improve on Black-Scholes" is listed as an open question in
> quantitative finance. This repo formalizes *why* BS is what it is, pins
> exactly where its assumptions stop being true, and frames improvement as a
> *formal* problem — not a tweak.

The artifact is the **mathematics**, in Lean 4. Python exists only as a
numerical oracle that sanity-checks the closed form so we don't prove a bad
formula. The two are force-multipliers, not either-or.

## Thesis (the framing this repo commits to)

Black-Scholes-Merton is not a "wrong formula." It is the *correct price for
one specific stochastic process* — geometric Brownian motion (GBM) with a
single constant-volatility factor — and its famous failures (1987 crash,
1998 LTCM/Russian default, 2008, vol-smile) are all failures of that
**process assumption**, not of the PDE/martingale skeleton that makes the
closed form exist in the first place.

That split is the lever:

- The *skeleton* (arbitrage-free pricing by expectation ⇒ heat equation ⇒ a
  closed form when the increment is lognormal with constant vol) is robust
  and worth formalizing. It's why BS is *a theorem about GBM*, and it's the
  part we can prove in Lean.
- The *increment law* (lognormal, constant σ, single factor) is the fragile
  bit — and it is exactly the bit the market data (heavy tails, vol-smile,
  regimes) rejects.

So "improving BS" more precisely means: **widen the class of increment laws
that still admit an analytic pricing kernel**, and *prove* the widening
preserves the skeleton. That's a theorem program, not a code workshop.

## Repository layout

```
Lean/
  core/            # LEAN 4 (mathlib-targeted) formalization. 
                   # STATUS: statements specified, proofs soldered/in progress.
  ...
experiments/       # numeric oracle + small boot runs (stdlib-only)
docs/
  01_baseline.md        # BS from first principles: heat kernel, FTAP, the formula
  02_failure_modes.md   # exactly which assumptions fail, each pinned to a process violation
  03_research.md        # candidate "improvement" directions, EACH with a falsifier
  04_formal_plan.md     # the Lean theorem targets, by formal difficulty
```

## Status

| Layer | What | Status here |
|---|---|---|
| Numeric oracle | closed form, parity, PDE residual | ✅ verified (matches textbook 10.45/5.57) |
| Analysis | failure modes + falsifiable direction specs | ✅ written (docs/) |
| Lean formalization | theorem statements (parity, d1−d2, delta-identity, PDE) | 🚧 specified — machine-checking requires a mathlib-backed lean environment (no mathlib cache on this box) |
| New increment-law result | the actual "improvement" | 🔬 open research |

## License

MIT, but the interesting history belongs to Black, Scholes, and Merton (1973,
1997 Nobel) and to the half-century of vol-surface literature this repo
builds on.

## Running the oracle

```sh
python3 -m pytest tests/   # or: python3 tests/test_bs.py
```