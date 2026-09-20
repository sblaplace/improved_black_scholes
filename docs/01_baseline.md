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

    V_C = e^{−rτ} ∫_{K} (S_T − K) dm  ... with S_T = S_t e^{X}, X~N(µ,σ²τ),

    V_C = S_t e^{−qτ} Φ(d1) − K e^{−rτ} Φ(d2)

where the two arguments come from completing the square in the density,

    d1 = ( ln(S/K) + (r − q + σ²/2) τ ) / (σ√τ)
    d2 = ( ln(S/K) + (r − q − σ²/2) τ ) / (σ√τ)

and Φ(·) is the standard-normal CDF.  This is the *Black-Scholes-Merton
formula*.  It is exact — an identity, not an approximation — **for this
process**.  The Python oracle reproduces the textbook case:

    S=K=100, r=5%, q=0, σ=20%, T=1 yr  →  call 10.4506, put 5.5735.

The put has its own closed form, obtained by the same completion of the square
against the payoff max(K − S, 0):

    V_P = K e^{−rτ} Φ(−d2) − S e^{−qτ} Φ(−d1)

## 2a. Write d2 and the put out in full — this is a methodology requirement

`d2` and `d1` are related by

    d1 − d2 = σ√τ                                                    (T1)

and the two closed forms are related by put-call parity

    V_P = V_C − S e^{−qτ} + K e^{−rτ}                                (T2)

**Both relations must be verified between independently written expressions.**
It is tempting — and it is what this repository originally did — to *define*
`d2 := d1 − σ√τ` and `V_P := V_C − S e^{−qτ} + K e^{−rτ}`. Then T1 and T2 are
true by construction, their proofs are a single `ring`, and a green build
certifies nothing at all. The definitions in §2 above are therefore the
contract: `d2` and `V_P` each get their own explicit formula, in
`experiments/black_scholes.py` and in `ImprovedBS/Core.lean`, and T1/T2 become
real claims.

The same trap exists in the test suite, and it is guarded mechanically.
`tests/test_mutants.py` seeds a perturbation of Φ that destroys its odd
symmetry and asserts that the parity test goes red; it cannot, if the put is
derived from the call. See §5.

**What T2 actually depends on.** Parity is not a consequence of the algebra of
Φ; it is a consequence of the *odd symmetry of `erf`*,

    Φ(x) + Φ(−x) = 1,      i.e.  erf(−x) = −erf(x).

Writing A = S e^{−qτ}, B = K e^{−rτ}, x = d1, y = d2:

    V_C − A + B = A·Φ(x) − B·Φ(y) − A + B
                = A·(Φ(x) − 1) + B·(1 − Φ(y))
                = −A·Φ(−x) + B·Φ(−y)
                = V_P                                        ∎

In Lean this is `BSM.Phi_add_Phi_neg`, which rests on `BSM.erf_neg` — a local
lemma, because **mathlib v4.34.0 has no `Real.erf`** (docs/04 §"`Real.erf` is
not in mathlib"). And a
proof of T2 that does not cite it is incomplete regardless of whether it
elaborates. `scripts/lean_lint.py` fails CI if `t2_put_call_parity` stops
mentioning `Phi_add_Phi_neg`.

## 3. Why this deserves a theorem

Two structural facts are *pure mathematics* and are provable:

**Fact A (heat kernel).** The formula V(S,t) is the unique C¹ solution of the
BSM diffusion equation interior to expiry, satisfying the terminal payoff
and the spot-boundary conditions. This is the analytic contract: BS is the
price because it is the right-conditioned solution of the heat equation on
the log-price.

**Fact B (martingale bridge).** Under risk-neutrality, the discounted price
process must be a ℚ-martingale:  E_ℚ[ S_T | S_t ] = S_t e^{(r−q) τ}
(Girsanov).  This is *the* constraint that pins the drift to r − q and forces
the closed form.  BS fails in the real world not here but *below*: the
ℚ-martingale condition does not select a unique increment law — it is satisfied
by infinitely many risk-neutral processes, of which GBM is one — and real
option surfaces depart from all of them.

**Fact B is also where the research direction has to be careful.** The
martingale condition is a statement about a *first moment*. Any candidate
increment law must have E[e^{X_τ}] < ∞ before it can be risk-neutral at all.
That single requirement rules out the pure α-stable law, and it is why
docs/03 D1 is stated in terms of a *tempered* stable. See docs/03 §D1.

## 4. Notation (kept identical to ImprovedBS/ and experiments/)

| symbol | meaning                                  |
|--------|-------------------------------------------|
| S_t    | spot at current time t                |
| K      | strike, K>0                            |
| τ = T−t| years to expiry, τ>0                     |
| r,q    | risk-free rate, dividend yield (annualized, decimals) |
| σ      | volatility (annualized), σ>0             |
| Φ,φ    | standard normal CDF, PDF                 |
| d1,d2  | the two BSM arguments, §2 — written out in full, never one in terms of the other |
| N(d1)  | shorthand for Φ(d1) in the pricing literature |

**Domain.** Every formula above assumes S>0, K>0, τ>0, σ>0. The oracle raises
`ValueError` outside it; the Lean statements carry the matching hypotheses.

This is not pedantry. In Lean, `a / 0 = 0` and `Real.sqrt 0 = 0` by convention,
so at σ = 0 both `d1` and `d2` collapse to `0` and identities that are true on
the domain become **false** off it. The original `t3_delta_identity` was
committed exactly that way: with only `0 < S` and `0 < K` as hypotheses, the
instance S=2, K=1, r=q=0, σ=0 reads `2·φ(0) = 1·φ(0)`, i.e. 0.797885 = 0.398942.
Statements must carry the hypotheses their proofs consume.

**Argument order.** The Lean declarations and the oracle's internal helpers both
use `(S K tau r q sigma)`. The oracle's *public* `bs_price(S, K, T, t, r, s, q)`
puts `s` before `q` — a frozen contract that predates this document. The
translation across that boundary is pinned by
`tests/test_bs.py::test_public_api_argument_order`.

## 5. How the baseline is kept honest

| claim | numeric falsifier | formal target |
|---|---|---|
| d1 − d2 = σ√τ | `test_d1_minus_d2` (independent d2) | `t1_d1_minus_d2` |
| put-call parity | `test_put_call_parity` (independent put) | `t2_put_call_parity` |
| Φ(x)+Φ(−x)=1 | `test_mutants.py` canary M7 | `Phi_add_Phi_neg` |
| S e^{−qτ}φ(d1) = K e^{−rτ}φ(d2) | `test_delta_identity_numerically` | `t3_delta_identity` |
| no-arb bounds | `test_value_bounds` | `t4_call_bounds`, `t4_put_bounds` |
| V solves the BSM PDE | `test_pde_residual_vanishes`, `test_pde_residual_is_second_order` | T5 (deferred) |
| Φ′ = φ | `test_phi_and_Phi_are_consistent` | needed by T5 |

A residual that vanishes is only evidence if it *can* stop vanishing. The PDE
residual is measured to be O(h²) on h ∈ [10⁻³, 10⁻¹] — it shrinks ~100× per
decade down to h = 10⁻³ and then **diverges** as round-off in the second
difference takes over (h = 10⁻⁴ gives a residual ten times *larger* than
h = 10⁻³). The step-size window is documented in `experiments/black_scholes.py`
and asserted by the tests; shrinking h is not an improvement.

## Checklist

Intentional gaps this baseline does *not* cover (deferred to 02 and 03):

- [ ] what happens to the *whole* surface when σ is not constant → docs/02 A1
- [ ] what the increment law's tail shape actually costs → docs/02 A2, docs/03 D1
- [ ] the vol smile: why market prices are not GBM lottery tickets → docs/02 A1
- [ ] which increment laws admit an equivalent martingale measure at all →
      docs/03 D1 (the moment-strip obstruction)
