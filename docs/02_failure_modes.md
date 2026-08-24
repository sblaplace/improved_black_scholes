# 02 — Failure modes: exactly which assumptions break

BS is a theorem about GBM. Real prices are not drawn from that process. Every
famous "BS failure" is a violation of a *named* process assumption, not a
bug in the algebra. This doc pins each assumption to (a) the observing
phenomenon it produces, and (b) a **falsifier** that would (bogus) separate
the assumption's contribution if it were the sole driver.

The three standard assumptions, and the three ways they leak:

## A1. Constant volatility  (σ constant in time and moneyness)

- **What BS assumes:** the realized dispersion of ln S over any remaining
  window is the same number, regardless of how far OTM/ITM or how far from
  expiry.
- **What markets show:** *implied* vol is a curved surface in (moneyness,
  tenor).  Deep OTM and deep ITM trade at higher implied vol than ATM — the
  **vol smile** (post-1987).  Tenor flattens it — the **term structure**.
- **Falsifier (would-be):** if you sell a 1-month OTM call, delta-hedge with a
  constant-vol GBM hedge, and size the static hedge error… the realized P&L
  distribution has fatter tails than the model's Gaussian hedge-error, and
  the smile fails to decay with hedging frequency the way σ-constant predicts.
  A satisfying replacement must reproduce the surface with *fewer, more
  honest* parameters than the surface itself has (that is the true material
  test of "improvement" — see 03).

**Precise feature to formalize:** the hedge error under σ-constant hedging is
the accumulation of the model's misspecification error in the first horizon it
ignores the vol smile's *state dependence* (σ depends on S via moneyness).

## A2. Lognormal increments → the tail shape

- **What it assumes:** one-period log-returns are jointly Gaussian; multi-period
  compounding keeps them Gaussian (Brownian); tails decay as e^{−x²/2}.
- **Observed:** realized daily-to-weekly log-returns concentrate mass at the
  center and, per unit bandwidth, near-extremes appear 5–50× more often than
  a Gaussian calibrated to the same variance (stable / Lévy regimes). Crises
  are not "10σ events one per century"; they are that tail class appearing
  ~every few years.
- **Falsifier:** a pure-GBM estimator of 99.9% CI on a log-return window is
  violated by observed exceedances at a frequency inconsistent with the CI
  itself — the "implied tail" is fatter regardless of σ.

**Mechanism to route around in a model:** the *increment law* — replace the
single Gaussian increment by one whose large-deviation rate is algebraic
(the α-stable, t-exponent-1/α family) instead of exponential, while preserving
scale-invariance of a martingale. The reason *this* is the high-value gap: it
does not abandon the heat skeleton.

## A3. Single factor / span sequential homogeneity

**What it assumes:** one Markov coordinate (the spot) carries all the risk;
jumps that matter aren't extra-frequent-driven by an independent
observation-arrives- cooling timeline (no stochastic vol, no jumps, no local
vol, no implied-vol-dynamics).

**Observed:** the date-stamped flow of info (earnings, macro, fed, runs)
produces *independent* vol shocks ("jumps") and a *volatility of volatility*
(clusters of low/high vol in GARCH sense) that a single-price Markov chain
cannot express — it **mixes scale classes within one increment law**.

**Falsifier (bookend):** a regime-cluster statistic (e.g. the Hurst/Persistent
of realized vol), measured on data, is inconsistent with the Markov-inverse
of a geometric random walk; the walk has no "memory," realized vol has.

## 4. The common thread

All three are *the increment law is not what BS says*.  The skeleton's failure
(FTA price by ℚ-martingale; heat equation; closed form) is **never** the
culprit.  That is the whole thesis, and the reason a "fix" should weakly be a
*wider increment law*, not a repair to the algebra.

## 5. The real test definition of "improvement"

One sentence, so we can falsify progress:

> A replacement is an improvement if it prices the same option surface with
> *materially more expressed equality* into the incomplete: (a) fits the
> observed surface at comparable or lower parameter count than the surface
> variance, and (b) *predicts* the surface (hedges) rather than only
> recalibrating it.

The ground test of (a): parameter count to explained surface- **variance** —
fewer degrees of freedom than one per quoted option.**  The ground test of
(b): **out-of-sample** — a fitted surface's hedging/scenario behavior over the
next horizon beats same-expiry of the calibrated GBM.

Every direction in 03 must name its (a) and (b) evidence, i.e. a falsifier.

## 4. Assumptions BS does NOT make

Quarantine the common misc edits so improvement proposals don't chase straw:

- it does **not** assume a normal *level*; only normal *increments*;
- it does **not** assume nonzero costless hedging; it assumes a frictionless
  continuous-rebalancing market and charges no bid-ask;
- it does not require the drift µ to equal r in the real measure; the drift is
  r − q only *under ℚ*, by martingale.* It is the *risk-adjusted* drift only.