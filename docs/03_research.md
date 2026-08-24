# 03 — Research directions: improving the increment law

The improvement is a **wider increment law that keeps the skeleton.**  Each
direction below names the exact claim, the parameter it would add relative to
GBM's single (σ), and a **falsifier** that would separate it from the 
alternatives. Directions are ordered by (formal tractability ∘ evidence).

## D1. Lévy / α-stable increment (heavy tails, the "hard" direction)

**Claim:** replace the Gaussian log-increment with a stable, 0-median,
scale-statistically constraint-driven dispersion that is *martingale*,
self-similar (1/α self-scaling), with tail exponent α < 2.  BS is the α = 2
limit; the smile is the counter of lower α on put options.

**What extends:** σ (single) → α and σ_α (two parameters).  Bootstrap:

    X_{t+dt} − X_t ~ Stα(µ·dt, σ_α·dt^{1/α}, β=0),   α ∈ (1,2].

The European-payoff risk-neutral value becomes an α-indexed Tikhonov
(Fourier/MP-6) integral — real analysis, still a *transport* kernel.

**Falsifier (must show):** the fitted (α,σ_α) surface for the S&P 500 / FX
panel:
  (a) explains at-least as much out-of-sample *hedging* variance per
      parameter as a GBM + smile conditional fit (ratio test on held-out tenors);
  (b) the α posterior concentrates between 1.3 and 1.9 *and* the fitted α is
      materially **less** a function of moneyness than the GBM σ is — i.e.
      moving the vol *functional dependence* into the increment itself.

**Why worth it:** puts the tail in the *increment*, not in an elastic vol,
so hedging is a single-martingale principle, and maturity- vs moneyness
mispecification are the same instability, not two hiddens.

## D2. Volatility-of-volatility extension (skeleton-preserving)

**Claim:** keep brownian log increments but let σ *itself* diffuse (a second,
independent factor).  BS is σ̇=0.  This preserves the ℚ-martingale and a
Fourier/kernel solution (this is the "stochastic-volatility family" — Heston
is the affine case).  Closed-form-kernel price, more honest tails than GBM.

**Falsifier:** a 2-factor model must beat a single-σ GBM by:
  (a) matching the smile *and* the term *structure* together (the smile's SLOPE
      changing sign along tenor is the fact GBM cannot),
  (b) out-of-sample hedge errors a forecast low-vs-high-vol regime that the
      single-martingale loses (the vol-of-vol is *calibrated*, not haunted).

## D4. Regime / me-memory increment (the "no-memory" falsifier)

A - memory / -persistence (rate + vol-clustering) increment.  The minimal
danger? claim: realized vol is **temporally persistent** (GARCH-like), so the
statement "increment is Sharpe martingale" is over wording.

**Falsifier:** the ACF/Hurst of |log-return| over 1d..4w decades LF ≠ 0
(statistically, not a point estimate) — and *any* price which prices a string
of one spot (Markov) cannot produce the observed *cluster* of extremes,
period. The model then MUST matter not measured by the price of a given spot
but the *distribution* over paths — no single-spot contract can be the whole
claim.

## Anti-directions (things that "improve BS" usually want to do and we should
   prove are traps — see 02):**

- **Recalibrate σ per manual / "the day vol":** parameter-per-print is not
  improvement; it is overfitting the surface. GBM *can* fit (a shifted smile)
  with a strike-dependent σ; that destroys the single-martingale and buys
  nothing predictive.
- **"Just add a jump term":** any number of translates of the Gaussian still
  leave the central mass-to-tail ratio near-Gaussian absent evidence the jumps
  are *independent informed* events (they aren't; jumps are informed, pricing
  the jump must price its cause, not a translate).

## The falsification loop (how a direction graduates)

For a direction → candidate → result:

1. **State** the increment-law replacement in one line (family, parameters).
2. **Fit** on (expiry × moneyness) surface, in history.
3. **Predict** out-of-sample (one tenor forward) hedged-error vs the GBM hedge.
4. **Compete** on explained-variance-per-parameter, not on fit.
5. Any model whose "improvement" shows up only by adding a constant per
   option is *disqualified on arrival* (02 §5).