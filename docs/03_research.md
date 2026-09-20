# 03 — Research directions: improving the increment law

The improvement is a **wider increment law that keeps the skeleton.** Each
direction below names the exact claim, the parameters it adds relative to GBM's
single σ, and a **falsifier** that would separate it from the alternatives.
Directions are ordered by (formal tractability × strength of evidence).

Every direction is graded against docs/02 §5: **(a)** explanatory power per
parameter, and **(b)** out-of-sample prediction, not in-sample fit.

---

## D1. Tempered-stable increment (heavy tails, the hard direction)

### The claim, and the obstruction that shapes it

**Claim:** replace the Gaussian log-increment by a Lévy increment with
*algebraic* rather than exponential tails, self-similar at index 1/α with
α < 2, that is nonetheless a martingale. BS is the α = 2 corner; the smile is
the shadow of lower α on the put side.

**Obstruction — read this before proposing anything.** The naive version of
this claim is *false*, and it is worth being explicit, because it is the
attractive version. Let `X_τ` be a pure symmetric α-stable law, α < 2. Its
tails satisfy `P(X_τ > x) ~ c·x^{−α}`, so

    E[e^{X_τ}] = ∫ e^x · c·x^{−α} dx = ∞.

Therefore `S_T = S_0·e^{X_τ}` has **infinite first moment** and cannot satisfy
the risk-neutral condition `E[S_T] = S_0·e^{(r−q)τ}` (docs/01 §3, Fact B). There
is no equivalent martingale measure inside the exponential-Lévy ansatz. The
consequence is not a technicality downstream — it is immediate: the
Carr–Madan / Lewis Fourier pricing integral requires a *moment strip*
`{u : E[e^{u·X_τ}] < ∞}` containing the pricing contour, and for a pure
α-stable that strip is empty on the side that matters. There is no contour to
place.

So the failure is at the **moment** step, not the **kernel** step. Any brief
that asks for "the transport kernel survives α-stable increments" is asking for
a theorem about an object that does not exist.

**Proved versus asserted (BRIEF_004).** The moment step of this obstruction is
no longer prose. `ImprovedBS/Levy.lean` proves — no `sorry`, clean `#print
axioms` audit — that a probability measure on `ℝ` whose upper tail is bounded
below by `c·x^(−α)` has no finite exponential moment
(`BSM.exp_moment_infinite_of_tail_lower_bound`, and the shifted form
`BSM.exp_moment_infinite_add_of_tail_lower_bound`), that the spot
`S_T = S₀·e^{X_τ}` therefore has infinite first moment
(`BSM.spot_not_integrable_of_tail_lower_bound`), and that no shift of the
log-drift repairs it (`BSM.no_drift_makes_spot_integrable`): drift cannot move
a tail index. Two corrections to how this section states the obstruction,
recorded in `benchmarks/LEDGER.md` C7 and in the brief's own correction record:

* **The index range is not `α < 2`.** The theorem holds for every real `α`.
  The divergent object is `exp` against `rpow`, and a genuine power tail —
  `x^(−3)` as much as `x^(−1)` — has infinite exponential moment. The `α < 2`
  above is a property of the α-stable *family*, not of the obstruction; the
  obstruction itself is wider, and `α ∈ (0, 2)` — the whole range T6 cares
  about — sits inside it. Nothing that stays within that interval can escape,
  which is why the tempered (CGMY) repair has to change the tail, not the
  index.
* **`α > 0` is a satisfiability condition on the hypothesis**, not a step in
  the proof: for `α ≤ 0` no probability measure satisfies the tail lower bound.

Still asserted rather than machine-checked, and therefore still prose here: the
**specialization** to the symmetric α-stable law — mathlib v4.34.0 has no such
law, so the tail bound enters as a hypothesis and the `c = F(−α)` constant of
the Zolotarev `S1` parametrization is cited from the literature — and everything
downstream of the moment step: emptiness of the moment strip, and the tempered
repair built on it.

**The repair.** Temper the Lévy measure. In the CGMY family
(Carr–Geman–Madan–Yor) and the Boyarchenko–Levendorskii family, the Lévy density
carries an `e^{−λ|x|}` damping:

    ν(dx) = C · e^{−G|x|} / |x|^{1+Y} dx      (x < 0)
    ν(dx) = C · e^{−M|x|} / |x|^{1+Y} dx      (x > 0)

with `Y = α ∈ (0,2)` the tail index and `G, M > 0` the two tempering rates.
Tempering restores every exponential moment on the interior of the strip, so an
equivalent martingale measure exists once the drift is fixed by the usual
exponent condition; algebraic tails survive at the scale that matters for
option tenors; and the α-stable law is recovered as `G, M → 0`, GBM as `Y → 2`.
The price paid is parameters: GBM has one (σ), CGMY has four (C, G, M, Y).
That is exactly what falsifier (a) below is for.

### What extends

    σ (one parameter)  →  C, G, M, Y (four)
    X_{t+dt} − X_t     ~  tempered stable, drift fixed by the martingale condition

The European risk-neutral value becomes a Fourier integral over a contour
inside the moment strip — real analysis, still a transport kernel, and still a
convolution of the payoff with a transition density. The skeleton of docs/01 §3
is untouched. That is the whole point: **the tail moves into the increment
rather than into an elastic volatility**, so hedging stays a single-martingale
principle, and maturity-mispecification and moneyness-mispecification become
one instability instead of two hidden ones.

### Falsifier (must show both)

Fit `(C, G, M, Y)` — or the reparametrized `(α, σ_α, λ)` — on an S&P 500 / FX
implied-vol panel, then:

- **(a)** it explains at least as much *out-of-sample hedging* variance per
  parameter as a GBM fitted conditionally to the smile, on held-out tenors
  (a ratio test, not a fit comparison); **and**
- **(b)** the posterior on α concentrates inside `(1.3, 1.9)`, **and** the
  fitted α is materially *less* dependent on moneyness than the GBM σ it
  replaces.

(b) is the real claim. If α has to vary with moneyness to fit, the model has
reintroduced an elastic volatility by another name and bought nothing — that is
anti-direction 1 below wearing a Lévy costume.

### Formal target (this is T6)

Stated in `ImprovedBS/Core.lean` as a comment block; the theorem to aim at is:

> **T6.** Let `X` be a Lévy process with characteristic exponent `ψ` affine in
> `τ`, and suppose the damping strip `{u : E[e^{u·X_τ}] < ∞}` contains both the
> pricing contour and `−1` (the numéraire point, i.e. the drift is fixed so that
> `E[e^{X_τ}] = e^{rτ}`). Then the Carr–Madan integral
>
>     V = e^{−rτ}/(2π) · ∫ e^{−i·u·τ} · f̂(u + iα) · e^{τ·ψ(u + iα)} du
>
> converges absolutely, is real-valued for real payoffs, and equals
> `e^{−rτ}·E[(S_T − K)⁺]`. GBM is the case `ψ(u) = i·u·(r−q) − σ²u²/2`.

Provable sub-goals, in increasing order of commitment:

1. **The obstruction as a theorem.** For a pure α-stable exponent with α < 2,
   `E[e^{X_τ}] = ∞`, hence the moment strip excludes the pricing contour. This
   is a concrete improper-integral divergence — no finance in it — and proving
   it *earns* the tempering hypothesis instead of assuming it. It is the highest
   value-per-effort item in the whole research tier and it should be a brief on
   its own.
2. **Absolute convergence** of the Carr–Madan integrand on a contour strictly
   inside the strip, for a tempered-stable exponent.
3. **Agreement** with the risk-neutral expectation, i.e. Fourier inversion
   against the payoff transform.

---

## D2. Volatility-of-volatility (skeleton-preserving, second factor)

**Claim:** keep Brownian log-increments but let σ itself diffuse, driven by a
second (correlated or independent) factor. BS is the zero-vol-of-vol corner.
This preserves the ℚ-martingale property and admits a Fourier/kernel solution —
the stochastic-volatility family, of which Heston is the affine case, i.e. the
case where the characteristic function is exponential-affine in the state and
therefore available in closed form.

**What it fixes and what it doesn't:** it produces a genuine smile and a genuine
term structure from two parameters of dynamics rather than one parameter per
strike. It does *not* produce algebraic tails — the increment stays Gaussian
conditional on the vol path, so extreme moves are still exponentially rare
conditional on the (now random) variance. If the evidence in docs/02 A2 is
taken seriously, D2 alone is incomplete; D1 and D2 are complements, not rivals,
and a combined tempered-stable-with-stochastic-volatility model is where the
literature actually lands.

**Falsifier:** a two-factor model must beat single-σ GBM by

- **(a)** matching the smile *and* the term structure *simultaneously* — in
  particular the fact that the smile's slope can change sign along tenor, which
  a single constant σ cannot express at any value of σ; and
- **(b)** producing out-of-sample hedging errors that forecast low- versus
  high-vol regimes, where the vol-of-vol is *calibrated once* rather than
  re-fitted per horizon.

---

## D3. Persistence / regime increment (the no-memory falsifier)

**Claim:** realized volatility is *temporally persistent* — GARCH-like
clustering — so the description "the increment is a Sharpe-optimal martingale
diffusion" is incomplete as a statement about a *process*: it constrains the
one-step law and says nothing about the dependence across steps.

This is the weakest of the three as a pricing direction and the strongest as a
*falsification* direction, because its test is cheap and its conclusion is
unambiguous: a Markov model of the spot cannot generate observed vol clustering,
period. Whatever replaces it must be a model of paths, not of a marginal.

**Falsifier:** the autocorrelation function of |log-return| over 1d..4w is
non-zero with statistical significance (not a point estimate — a confidence
statement), while the geometric random walk's ACF is zero by construction. Any
model that prices from the single-spot marginal alone is then ruled out as a
complete account, independent of how well it fits the surface.

**Interaction with D1/D2:** persistence is what makes the *fitted* parameters of
either model time-varying. A direction that reports a point estimate of α or of
vol-of-vol without reporting its persistence is reporting a sample statistic as
if it were a structural constant.

---

## Anti-directions

Things that "improve BS" proposals usually reach for, and why they are traps
(see docs/02):

- **Recalibrate σ per quote** ("use today's vol for today's option"). One
  parameter per print is not improvement; it is transcription of the surface.
  GBM *can* fit any smile with a strike-dependent σ — that is Dupire's local
  volatility, which is a perfectly good *calibration* and a perfectly useless
  *prediction*, because it destroys the single-martingale structure and buys no
  out-of-sample content. Fails (a) and (b) both, by construction.
- **"Just add a jump term."** A finite number of Gaussian translates still
  leaves the central-mass-to-tail ratio near Gaussian. Jumps help only if the
  jump arrivals and sizes are modelled as *informed events* with their own
  dynamics — and then you are pricing the cause of the jump, which is D2/D3
  territory, not a compound-Poisson afterthought.
- **Fit the surface and call the fit a model.** Any direction whose evidence is
  in-sample R² on the same panel it was calibrated to is disqualified on
  arrival (docs/02 §5). This is the single most common way a plausible-looking
  improvement turns out to be an expensive interpolation.

---

## The falsification loop (how a direction graduates)

For a direction → candidate → result:

1. **State** the increment-law replacement in one line: family, parameters, and
   the martingale condition that fixes its drift. A direction that cannot state
   its moment condition has not met Fact B and stops here.
2. **Fit** on an (expiry × moneyness) surface over history.
3. **Predict** out-of-sample — one tenor forward — and compare hedging error
   against the GBM hedge.
4. **Compete** on explained variance *per parameter*, not on fit.
5. **Formalize** whichever structural claim survived: the surviving identity
   becomes a node in the theorem stack, and `briefs/` gets a work order with a
   machine-graded acceptance bar.

A model whose "improvement" appears only by adding a constant per option is
disqualified at step 1.
