# 02 — Failure modes: exactly which assumptions break

BS is a theorem about GBM. Real prices are not drawn from that process. Every
famous "BS failure" is a violation of a *named* process assumption, not a bug
in the algebra. This doc pins each assumption to (a) the phenomenon it produces
when violated, and (b) a **falsifier** — an observation that would separate this
assumption's contribution from the others.

The three standard assumptions, and the three ways they leak:

## A1. Constant volatility  (σ constant in time and moneyness)

- **What BS assumes:** the dispersion of ln S over any remaining window is the
  same number, regardless of how far OTM/ITM the option is or how far from
  expiry.
- **What markets show:** *implied* vol is a curved surface in
  (moneyness, tenor). Deep OTM and deep ITM trade at higher implied vol than
  ATM — the **vol smile** (post-1987). Tenor flattens it — the **term
  structure**.
- **Falsifier:** sell a 1-month OTM call, delta-hedge with a constant-vol GBM
  hedge, and measure the realized hedging error. Its distribution has fatter
  tails than the model's own Gaussian hedge-error predicts, and the residual
  does *not* decay with hedging frequency the way σ-constant implies it should.
  A satisfying replacement must reproduce the surface with *fewer, more honest*
  parameters than the surface itself has — that is the material test of
  "improvement", made precise in §5.

**Precise feature to formalize:** the hedging error under σ-constant hedging is
the accumulated misspecification of the model's *state dependence* — σ in the
real surface depends on S through moneyness, and the constant-vol model has no
variable in which to express that.

## A2. Lognormal increments → the tail shape

- **What it assumes:** one-period log-returns are Gaussian, and compounding
  keeps them Gaussian (Brownian). Tails decay as e^{−x²/2}.
- **Observed:** realized daily-to-weekly log-returns concentrate mass at the
  centre and, per unit bandwidth, put 5–50× more mass near extremes than a
  Gaussian calibrated to the same variance (stable / Lévy regimes). Crises are
  not "10σ events, one per century"; they are a tail class that appears roughly
  every few years.
- **Falsifier:** a pure-GBM 99.9% confidence interval on a log-return window is
  violated by observed exceedances at a frequency inconsistent with the interval
  itself. The implied tail is fatter *regardless of how σ is chosen* — which is
  the point: no value of σ fixes a wrong tail class.

**Mechanism to route around:** the *increment law*. Replace the single Gaussian
increment by one whose large-deviation rate is algebraic rather than
exponential — the α-stable family, with tail exponent α < 2 — while preserving
the martingale property and self-similarity. This is the high-value gap
precisely because it does not abandon the heat skeleton.

**And the trap, stated up front:** an α-stable log-increment has no finite
exponential moment, so `S_T = S_0 e^{X_τ}` cannot satisfy
`E[S_T] = S_0 e^{(r−q)τ}`. The martingale bridge of docs/01 §3 Fact B is a
statement about a first moment, and it fails before any kernel question is
reached. The direction survives only in *tempered* form. This is worked out in
docs/03 §D1; it is noted here because A2 is where a reader first meets the
tempting version.

## A3. Single factor / no memory across scales

- **What it assumes:** one Markov coordinate (the spot) carries all the risk.
  There is no second state variable, no jump component, no local-vol or
  implied-vol dynamics: nothing that can make the *dispersion itself* move
  independently of the price.
- **Observed:** the date-stamped flow of information (earnings, macro prints,
  central bank decisions, funding runs) produces vol shocks that are not
  functions of the spot, and a **volatility of volatility** — clusters of
  low- and high-vol regimes in the GARCH sense. A single-price Markov chain
  cannot express this: it would have to mix scale classes inside one increment
  law.
- **Falsifier:** a persistence statistic on realized vol (the autocorrelation
  of |log-return|, or a Hurst exponent) is significantly non-zero over
  1d..4w horizons, while the geometric random walk's own increment process has
  no memory by construction. The walk cannot reproduce the clustering; the
  statistic separates the two.

The consequence is about *what kind of object a model must be*: if vol
persists, the claim cannot be a statement about the distribution of a single
spot at a single horizon. It has to be a statement about the distribution over
**paths**, and no single-spot contract can be the whole of it.

## 4. The common thread

All three are the same statement: **the increment law is not what BS says.**
The skeleton — arbitrage-free pricing by ℚ-expectation, the heat equation, the
closed form — is never the culprit. That is the whole thesis of this
repository, and it is why a "fix" should be a *wider increment law* rather than
a repair to the algebra.

It is also why the algebra gets formalized at all. If the skeleton is the part
that survives, then the skeleton is the part worth machine-checking: T1–T4
pin down exactly which identities are structural and which are contingent on
the Gaussian increment.

## 5. The test definition of "improvement"

One sentence, so that progress can be falsified:

> A replacement is an improvement if it prices the same option surface with
> **materially more explanatory power per parameter**, and if it *predicts*
> rather than merely recalibrates.

Split into the two things that can actually be measured:

- **(a) Parsimony.** Parameters consumed versus surface variance explained. The
  bar is fewer degrees of freedom than one per quoted option — a model that
  needs a parameter per data point has not explained the surface, it has
  transcribed it.
- **(b) Out-of-sample prediction.** A surface fitted on history must produce
  hedging / scenario behaviour over the *next* horizon that beats the
  same-expiry calibrated GBM. In-sample fit is not evidence.

Every direction in docs/03 must name its (a) and (b) evidence. A direction
without a falsifier is not a direction.

## 6. Assumptions BS does **not** make

Quarantining the common misreadings, so improvement proposals don't chase straw:

- It does **not** assume normally distributed price *levels*; only normally
  distributed log-*increments*.
- It does **not** assume hedging is free or costless in a colloquial sense; it
  assumes a frictionless market with continuous rebalancing, and it charges no
  bid-ask spread, no impact and no funding spread. Those are separate
  assumptions and separate improvement directions.
- It does **not** require the real-world drift µ to equal r. The drift is
  r − q only *under ℚ*, by the martingale condition; µ under the physical
  measure is unconstrained and irrelevant to the price. This is the single most
  common misreading of the model.
- It does **not** assume the volatility is *known*. It assumes it is a constant
  parameter; estimating it is a separate problem, and the fact that different
  strikes imply different values of it is precisely A1.
