# 01 — Baseline: what Black-Scholes actually is

## 1. The model is a process, not a formula

BSM prices a European option **under a stated stochastic process**:

**Process (GBM, under risk-neutral measure ℚ):**

    dS_t = (r − q) S_t dt + σ S_t dW_t          (Ito, W_t standard Brownian)

Equivalently, the log-price is an arithmetic Brownian motion with drift:

    X_t := ln S_t
    dX_t = (r − q − σ²/2) dt + σ dW_t

so, conditional on S_t,

    X_T ~ N( X_t + (r − q − σ²/2)·τ ,  σ²·τ ),   τ = T − t.

**No-arbitrage price** (Fundamental Theorem of Asset Pricing): the price of a
claim paying f(S_T) is its discounted risk-neutral expectation,

    V_t = e^{−rτ} E_ℚ[ f(S_T) | S_t ].

For a European call, f(S) = max(S − K, 0).

## 2. The expectation reduces to two normal integrals

    V_C = e^{−rτ} ∫_{K} max(S_T − K,0) dm  ... with S_T = S_t e^{X}, X~N(µ,σ²τ),

    V_C = S_t e^{−qτ} N(d1) − K e^{−rτ} N(d2)

where the two arguments come from completing the square in the density,

    d1 = ( ln(S/K) + (r − q + σ²/2) τ ) / (σ√τ)
    d2 = d1 − σ√τ,

and N(·) is the standard-normal CDF.  This is the *Black-Scholes-Merton
formula*.  It is exact — an identity, not an approximation — **for this
process**.  The Python oracle reproduces the textbook case:

    S=K=100, r=5%, q=0, σ=20%, T=1 yr  →  call 10.4506, put 5.5735.

## 3. Why this deserves a theorem

Two structural facts are *pure mathematics* and are provable:

**Fact A (heat kernel).** The formula V(S,t) is the unique C¹ solution of the
BSM diffusion equation interior to expiry, satisfying the terminal pay off
and the spot-boundary conditions. This is the analytic contract: BS is the
price because it is the right-conditioned solution of the heat equation on
the log-price.

**Fact B (martingale bridge).** Under risk-neutrality, the process must be a
ℚ-martingale:  E_ℚ[ S_T | S_t ] = S_t e^{r τ} (Girsanov).  This is *the*
constraint that pins the drift to r − q and forces the closed form.  BS fails
in the real world not here but *below*: the ℚ-martingale condition does not
select a unique increment; it really chooses GBM out of infinitely many
risk-neutral diffusions, and real option surfaces depart from all of them.

## 4. Notation (kept identical to Lean/ and experiments/)

| symbol | meaning                                  |
|--------|-------------------------------------------|
| S_t    | spot at current time t                |
| K      | strike, K>0                            |
| τ = T−t| years to expiry, τ>0                    |
| r,q    | risk-free rate, dividend yield (annualized, decimals) |
| σ      | volatility (annualized)                     |
| Φ,φ    | standard normal CDF, PDF                                 |
| N(d1)  | shorthand for Φ(d1) in the pricing literature |

## Checklist

Intentional gaps this baseline does *not* cover (deferred to 02):

- [ ] what happens to the *whole* surface when σ is not constant
- [ ] what the central-limit/convergence claim for the increment actually is
- [ ] the vol-smile: why market prices are not GBM-lottery tickets