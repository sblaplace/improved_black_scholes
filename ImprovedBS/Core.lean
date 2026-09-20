/-
  ImprovedBS.Core — the BSM theorem stack (T1..T6) in Lean 4 + mathlib.

  STATUS CONVENTION (enforced mechanically by scripts/lean_lint.py, which
  needs no toolchain, and by the `lake build` job in .github/workflows/lean.yml):

    [BUILT] = proof script present, no `sorry`
    [TODO]  = statement is the agreed contract, proof deferred (`sorry`)

  The lint job hard-fails on ANY `sorry` in the T1/T2 node (the BRIEF_001
  deliverable) and ratchets the repo-wide `sorry` count against
  .github/lean_lint_baseline.json, so deferred nodes cannot silently grow.

  IMPORTANT — what was fixed here, and why
  ----------------------------------------
  The previous version of this file (Lean/core/bsm_theorems.lean) defined

      d2    := d1 - sigma * Real.sqrt tau
      bsPut := bsCall - S*e^{-q*tau} + K*e^{-r*tau}

  With those definitions T1 and T2 are true *by construction*: both proofs
  reduce to `unfold <def>; ring`, and T2 never touches the identity it is
  supposed to be about, namely Phi(x) + Phi(-x) = 1. A green build on that
  file would have certified nothing. The definitions below are therefore
  INDEPENDENT — `d2` and `bsPut` each get their own explicit closed form —
  matching docs/01_baseline.md §2 and experiments/black_scholes.py, which was
  changed the same way. The numeric oracle and this file agree to ~1e-15.

  `t3_delta_identity` also carried a FALSE statement: with mathlib's
  `a / 0 = 0` and `Real.sqrt 0 = 0`, taking sigma = 0 collapses
  d1 = d2 = 0 and the claim degenerates to S*e^{-q*tau}*phi(0) =
  K*e^{-r*tau}*phi(0), which fails for S ≠ K (e.g. S=2, K=1, r=q=0 gives
  0.797885 vs 0.398942). It now carries the hypotheses it needs.

  HYPOTHESIS DISCIPLINE
  ---------------------
  Wherever the oracle guards its inputs (`bs_price` raises ValueError for
  tau <= 0 and sigma <= 0), the Lean statement carries the matching
  hypothesis. Degenerate cases are not "extra generality"; under `div_zero`
  they are a different mathematics, and silently relying on that convention
  is how a false statement gets committed.
-/

-- `import Mathlib`, deliberately. Narrow imports are better practice -- they
-- document what a theorem rests on and cost less elaboration time -- but they
-- can only be verified by a toolchain, and this tree is authored in
-- environments that have none. Two narrow paths guessed by hand
-- (`Mathlib.Analysis.SpecialFunctions.Erf`, `Mathlib.Data.Real.Pi`) cost three
-- consecutive red CI runs. Narrowing this list is a legitimate follow-up for
-- someone who can run `lake build`; do not do it blind.
import Mathlib

-- `Real.exp`, `Real.log`, `Real.sqrt` and division on `Real` are all
-- noncomputable, and `lake build` emits C, so every definition in this file
-- that touches them has to be marked. Rather than annotate six defs (and miss
-- the seventh), the whole file is a noncomputable section.
noncomputable section

-- --------------------------------------------------------------------------
-- Notation (identical to docs/01_baseline.md and experiments/black_scholes.py)
--
--   S     : spot,            K    : strike,      K > 0
--   tau   : T - t,           tau > 0
--   r, q  : risk-free rate and dividend yield (annualized decimals)
--   sigma : volatility,      sigma > 0
--   Phi   : standard normal CDF, via the `erf` defined below
--   phi   : standard normal PDF
--
-- Argument order is (S K tau r q sigma) throughout, and
-- experiments/black_scholes.py's internal helpers use the same order.
-- NOTE the public Python `bs_price(S, K, T, t, r, s, q)` puts `s` before `q`;
-- that boundary is pinned by tests/test_bs.py::test_public_api_argument_order.
-- --------------------------------------------------------------------------

/-!
### The error function

**Mathlib v4.34.0 has no `Real.erf`.** There is no
`Mathlib/Analysis/SpecialFunctions/Erf.lean` in the v4.34.0 tree (checked
against all 9112 `.lean` files), and `erf_neg` does not exist. `docs/04`
previously asserted both as available dependencies; that was wrong, and it is
corrected there.

So `erf` is defined here, from the interval integral of the Gaussian. That is
enough for everything T1 and T2 need: the *oddness* of `erf`, which is what
put-call parity actually rests on. What it is **not** enough for is T4, whose
bounds `0 ≤ Phi ≤ 1` need the *value* of the Gaussian integral
(`∫ x:ℝ, exp(-x^2) = sqrt pi`), i.e. real measure theory rather than interval
integrals. That is recorded in the T4 doc-comment.

If mathlib ever grows `Real.erf`, this section should be deleted in favour of
it and `Phi_add_Phi_neg` re-pointed at `Real.erf_neg`.
-/

/-- The error function, `erf x = (2/sqrt pi) * ∫ t in 0..x, exp (-(t^2))`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t ^ 2))

/-- The Gaussian `t ↦ exp (-(t^2))` is even. Everything about the symmetry of
the normal distribution in this file reduces to this one line. -/
theorem exp_neg_sq_even (t : ℝ) : Real.exp (-((-t) ^ 2)) = Real.exp (-(t ^ 2)) := by
  congr 1
  ring

/-- **Oddness of `erf`**: `erf (-x) = -erf (x)`.

Proved by the substitution `t ↦ -t` on the interval integral
(`intervalIntegral.integral_comp_neg`), the evenness of the integrand, and the
orientation flip `intervalIntegral.integral_symm`. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  -- `integral_comp_neg` takes `a` and `b` IMPLICITLY; passing them positionally
  -- gives "Function expected at ... but this term has type ... = ...".
  have hcomp : ∫ t in (0:ℝ)..x, Real.exp (-(t ^ 2))
      = ∫ t in (-x)..(0:ℝ), Real.exp (-(t ^ 2)) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => Real.exp (-(u ^ 2))) (a := (0:ℝ)) (b := x)
    -- h : ∫ t in 0..x, exp(-((-t)^2)) = ∫ t in -x..-0, exp(-(t^2))
    -- simp discharges the evenness of the integrand and `-0 = 0` at once.
    simpa [exp_neg_sq_even] using h
  have hkey : ∫ t in (0:ℝ)..(-x), Real.exp (-(t ^ 2))
      = -∫ t in (0:ℝ)..x, Real.exp (-(t ^ 2)) := by
    rw [intervalIntegral.integral_symm, hcomp]
  simp only [erf, hkey]
  ring

/-- Standard normal CDF. `Phi x = (1 + erf (x / sqrt 2)) / 2`. -/
def Phi (x : ℝ) : ℝ := (1 + erf (x / Real.sqrt 2)) / 2

/-- Standard normal PDF. `phi x = exp (-(x^2)/2) / sqrt (2 pi)`. -/
def phi (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- The upper BSM argument, from its own explicit formula. -/
def d1 (S K tau r q sigma : ℝ) : ℝ :=
  (Real.log (S / K) + (r - q + sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)

/-- The lower BSM argument, from its OWN explicit formula.

Deliberately *not* `d1 - sigma * Real.sqrt tau`: that would make `t1` a
definitional tautology. The two expressions are equal, and `t1_d1_minus_d2`
is the theorem saying so. -/
def d2 (S K tau r q sigma : ℝ) : ℝ :=
  (Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)

/-- BSM European call price. -/
def bsCall (S K tau r q sigma : ℝ) : ℝ :=
  S * Real.exp (-q * tau) * Phi (d1 S K tau r q sigma)
    - K * Real.exp (-r * tau) * Phi (d2 S K tau r q sigma)

/-- BSM European put price, from its OWN closed form.

Deliberately *not* `bsCall - S*e^{-q*tau} + K*e^{-r*tau}`: that would make
`t2_put_call_parity` a definitional tautology and would never exercise
`Phi_add_Phi_neg`, which is the actual content of parity. -/
def bsPut (S K tau r q sigma : ℝ) : ℝ :=
  K * Real.exp (-r * tau) * Phi (-(d2 S K tau r q sigma))
    - S * Real.exp (-q * tau) * Phi (-(d1 S K tau r q sigma))

-- --------------------------------------------------------------------------
-- The hinge lemma. Everything about parity goes through here.
-- --------------------------------------------------------------------------

/-- **Odd symmetry of the normal CDF**: `Phi x + Phi (-x) = 1`.

This is the analytic content of put-call parity (T2). It is the lemma the
BRIEF_001 acceptance bar demands be cited: "the parity identity is not
guaranteed by the algebra of `Phi` alone — it follows from `Φ(x) + Φ(−x) = 1`".
Unconditional: it is a statement about `erf` alone. -/
theorem Phi_add_Phi_neg (x : ℝ) : Phi x + Phi (-x) = 1 := by
  have hneg : (-x) / Real.sqrt 2 = -(x / Real.sqrt 2) := by ring
  simp only [Phi, hneg, erf_neg]
  ring

/-- `Phi` is complementary under negation, in the form `ring`/`linarith` want. -/
theorem Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x := by
  linarith [Phi_add_Phi_neg x]

-- --------------------------------------------------------------------------
-- T1  [BUILT]  d1 - d2 = sigma * sqrt tau
-- --------------------------------------------------------------------------

/-- **T1.** `d1 - d2 = sigma * sqrt tau`, between two independently written
expressions. Hypotheses mirror the oracle's guards (`tau > 0`, `sigma > 0`).

Remark on degeneracy: with `d2` defined independently, this identity also
holds *unconditionally* under mathlib's `a / 0 = 0` convention (at
`sigma = 0`, `tau = 0`, or `tau < 0` both sides collapse to `0`). We do not
state it that way, because a theorem whose truth rests on a division-by-zero
convention is not the theorem the finance means. -/
theorem t1_d1_minus_d2 (S K tau r q sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    d1 S K tau r q sigma - d2 S K tau r q sigma = sigma * Real.sqrt tau := by
  have hsqrt : Real.sqrt tau ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htau)
  have hD : sigma * Real.sqrt tau ≠ 0 := mul_ne_zero hsigma hsqrt
  have hsq : Real.sqrt tau * Real.sqrt tau = tau := Real.mul_self_sqrt (le_of_lt htau)
  have hsq' : sigma * Real.sqrt tau * (sigma * Real.sqrt tau) = sigma ^ 2 * tau :=
    calc sigma * Real.sqrt tau * (sigma * Real.sqrt tau)
        = (sigma * sigma) * (Real.sqrt tau * Real.sqrt tau) := by ring
      _ = sigma ^ 2 * tau := by rw [hsq, ← pow_two]
  have key : (Real.log (S / K) + (r - q + sigma ^ 2 / 2) * tau)
      - (Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau) = sigma ^ 2 * tau := by ring
  -- `show` rather than `simp only [d1, d2, ...]`: simp left the two fractions
  -- uncombined (CI reported `sub_div` and `key` as unused simp arguments), and
  -- `rw` is deterministic where `simp` normalizes behind our back.
  show (Real.log (S / K) + (r - q + sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)
      - (Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)
      = sigma * Real.sqrt tau
  -- `div_eq_iff`, not `eq_div_iff_mul_eq`: the division is on the LEFT here.
  rw [sub_div, key, div_eq_iff hD]
  exact hsq'.symm

-- --------------------------------------------------------------------------
-- T2  [BUILT]  put-call parity
-- --------------------------------------------------------------------------

/-- **T2.** Put-call parity for the BSM closed forms:

    bsPut = bsCall - S * e^{-q*tau} + K * e^{-r*tau}

Unconditional — it is a consequence of `Phi_add_Phi_neg` and nothing else, so
it holds even in the degenerate parameter regimes. The proof cites the
symmetry lemma at both `d1` and `d2`, as the brief requires. -/
theorem t2_put_call_parity (S K tau r q sigma : ℝ) :
    bsPut S K tau r q sigma
      = bsCall S K tau r q sigma - S * Real.exp (-q * tau) + K * Real.exp (-r * tau) := by
  -- `linarith` FAILS here, and it is worth recording why: the goal contains
  -- `K * exp(-r*tau) * Phi(-(d2 ...))`, a *product* of two atoms, so the goal is
  -- not linear in them. Rewriting `Phi (-x)` to `1 - Phi x` first makes it a
  -- ring identity in the atoms S, K, exp(-q*tau), exp(-r*tau), Phi(d1), Phi(d2).
  -- The odd-symmetry content still comes from `Phi_add_Phi_neg`, via `Phi_neg`.
  simp only [bsPut, bsCall, Phi_neg]
  ring

/-- Parity in the traded form: the call minus the put is the discounted
forward-spread. Restated from `t2_put_call_parity` so the ledger can point at
the identity practitioners actually quote. -/
theorem t2_put_call_parity_spread (S K tau r q sigma : ℝ) :
    bsCall S K tau r q sigma - bsPut S K tau r q sigma
      = S * Real.exp (-q * tau) - K * Real.exp (-r * tau) := by
  linarith [t2_put_call_parity S K tau r q sigma]

-- --------------------------------------------------------------------------
-- T3  [TODO]  the delta identity
-- --------------------------------------------------------------------------

/-- **T3.** `S * e^{-q*tau} * phi(d1) = K * e^{-r*tau} * phi(d2)`.

This is the analytic hinge for the greeks and for the martingale bridge, and
(via the chain rule) the cancellation that makes the BSM PDE residual vanish
— so T5 is proved *through* T3, not independently of it. See docs/04.

CORRECTED HYPOTHESES. The previous statement carried only `0 < S` and `0 < K`
and was **false**: at `sigma = 0`, mathlib's `a / 0 = 0` and `Real.sqrt 0 = 0`
force `d1 = d2 = 0`, and the claim becomes `S*e^{-q*tau}*phi(0) =
K*e^{-r*tau}*phi(0)`, which fails whenever `S*e^{-q*tau} ≠ K*e^{-r*tau}`
(concretely: S=2, K=1, r=q=0, sigma=0 gives 0.797885 ≠ 0.398942). The
hypotheses below are the ones the proof actually consumes:

* `0 < S`, `0 < K` — so `Real.log (S/K)` is the genuine logarithm and
  `exp (-(log (S/K))) = K/S`;
* `sigma ≠ 0`, `0 < tau` — so `sigma * Real.sqrt tau ≠ 0` and
  `Real.sqrt tau * Real.sqrt tau = tau`, both needed for
  `d1^2 - d2^2 = 2*log(S/K) + 2*(r-q)*tau`.

Proof route (recorded so the next contributor does not rediscover it):
1. `d1^2 - d2^2 = (d1 - d2) * (d1 + d2) = 2*Real.log (S/K) + 2*(r-q)*tau`
   — by T1 and `field_simp`, using `Real.mul_self_sqrt`.
2. Hence `-(d1^2)/2 = -(d2^2)/2 - (Real.log (S/K) + (r-q)*tau)`, so by
   `Real.exp_add` / `Real.exp_sub` and `Real.exp_log (by positivity)`:
   `phi d1 = (K/S) * Real.exp (-(r-q)*tau) * phi d2`.
3. Multiply through by `S * Real.exp (-q*tau)` and `ring`. -/
theorem t3_delta_identity (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)
      = K * Real.exp (-r * tau) * phi (d2 S K tau r q sigma) := by
  sorry

-- --------------------------------------------------------------------------
-- T4  [TODO]  no-arbitrage bounds
-- --------------------------------------------------------------------------

/-- **T4.** No-arbitrage bounds on the call:

    max (S e^{-q*tau} - K e^{-r*tau}) 0 ≤ bsCall ≤ S e^{-q*tau}

Previously this node existed only as a row in README/docs tables; it had no
Lean statement at all, so nothing in the tree could contradict the claim that
it was "stated". It is stated here now.

Proof route: both bounds follow from `0 ≤ Phi` and `Phi ≤ 1` (the upper bound
by dropping the non-negative `K e^{-r*tau} Phi(d2)` term; the lower by
`bsCall ≥ S e^{-q*tau} Phi(d1) - K e^{-r*tau} Phi(d1)` once `Phi` is shown
monotone, then `Phi(d1) ≥ Phi(d2)` from `d1 ≥ d2`, i.e. T1 plus
`0 ≤ sigma * Real.sqrt tau`).

**This is the node that the missing `Real.erf` actually bites.** Oddness (all
T2 needs) comes from a substitution in an interval integral. *Bounds* are
different: `0 ≤ Phi x` and `Phi x ≤ 1` need `|erf x| ≤ 1`, which needs the
**value** of the Gaussian integral, `∫ x:ℝ, Real.exp (-(x^2)) = Real.sqrt
Real.pi` — real measure theory, not interval integrals. Mathlib has this in
`Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`; start there
rather than trying to squeeze it out of the `erf` definition above. Budget
accordingly: this is the expensive part of T4, not the monotonicity.

The numeric shadow of this theorem is
`tests/test_bs.py::test_value_bounds`, which checks it on a 6-point grid. -/
theorem t4_call_bounds (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0
      ≤ bsCall S K tau r q sigma ∧
    bsCall S K tau r q sigma ≤ S * Real.exp (-q * tau) := by
  sorry

/-- **T4 (put side).** The mirrored bounds, obtained from the call bounds by
parity (T2) — so this is a corollary, not an independent analytic claim. -/
theorem t4_put_bounds (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    max (K * Real.exp (-r * tau) - S * Real.exp (-q * tau)) 0
      ≤ bsPut S K tau r q sigma ∧
    bsPut S K tau r q sigma ≤ K * Real.exp (-r * tau) := by
  sorry

/-!
--------------------------------------------------------------------------
T5  [DEFERRED — not yet declared]  the closed form solves the BSM PDE
--------------------------------------------------------------------------

    V_t + (r - q) * S * V_S + (sigma^2 / 2) * S^2 * V_SS = r * V

This is the first heavy node and the reason the stack has a spine rather than
six unrelated chores. Two decisions recorded here so the brief that picks it
up does not relitigate them:

1. **Prove T5 through T3, not around it.** Substituting the closed form, the
   `S^2 V_SS` term produces `phi(d1)` and `phi(d2)` contributions whose
   *difference* is exactly what T3 cancels. So the PDE identity is
   `T3 + chain rule + Phi' = phi`, and the only genuinely new analytic input
   is `HasDerivAt Phi phi x` (from `Real.hasDerivAt_erf`). Attempting it by
   brute-force differentiation of `erf ∘ (log-rational)` is the slow route.

2. **Change variables before differentiating.** In `x = Real.log S` the BSM
   operator becomes a constant-coefficient operator and the closed form is a
   convolution of the payoff with the Gaussian kernel; uniqueness then follows
   from the heat-kernel/Feynman–Kac side. Doing it in `S` coordinates buys
   nothing and costs every `1/S` factor by hand.

Numeric shadow, with a measured step-size window:
`tests/test_bs.py::test_pde_residual_vanishes` and
`::test_pde_residual_is_second_order`. Note that the residual is O(h^2) only
for `h ∈ [1e-3, 1e-1]`; below `1e-3` round-off dominates and it *diverges*.
Do not "strengthen" that test by shrinking `h`.

Not declared yet: it needs a PDE/derivative notation decision (partial
derivatives over `(S, t)` vs. the `x = log S` reduction) and that decision
belongs in the brief, not in a comment.
-/

/-!
--------------------------------------------------------------------------
T6  [OPEN — research]  the Fourier pricing kernel survives a wider
                       increment law
--------------------------------------------------------------------------

RESTATED. The previous formulation ("transport (Fourier) kernel survives
a-stable increments") is **not reachable as written**, and it is worth being
explicit about why before anyone spends a brief on it.

If `X_tau` is a pure symmetric alpha-stable law with `alpha < 2`, then
`P(X_tau > x) ~ c * x^(-alpha)`, so

    E[exp X_tau] = ∫ e^x · c x^(-alpha) dx = ∞.

Hence `S_T = S_0 * exp(X_tau)` has **infinite first moment** and cannot
satisfy the risk-neutral martingale condition `E[S_T] = S_0 * e^{r*tau}`.
There is no equivalent martingale measure inside the exponential-Lévy ansatz,
so the Carr–Madan / Lewis Fourier integral never becomes well defined: the
pricing contour cannot be placed in a moment strip that does not exist. The
obstruction is at the *moment* step, not the *kernel* step.

The repair keeps everything the direction actually wants (algebraic tails, BS
as a limit) and is standard: **temper** the Lévy measure. In the CGMY /
Boyarchenko–Levendorskii family the Lévy density carries an `e^{-lambda*|x|}`
damping, which restores the exponential moment at the cost of one extra
parameter `lambda`, with the alpha-stable law recovered as `lambda → 0` and BS
as the `alpha = 2` corner.

So the theorem to aim at is not "stable increments still transport" but:

    **T6 (target).** Let `X` be a Lévy process with characteristic exponent
    `psi` affine in `tau`, and let the damping strip
    `{u : ℝ | E[exp (u * X_tau)] < ∞}` contain the pricing contour and `-1`
    (the martingale/numéraire point, i.e. `psi(-i) = -i*r*tau` after the
    drift is fixed). Then the Carr–Madan integral

        V = e^{-r*tau} / (2*pi) * ∫ e^{-i*u*tau} · fhat(u + i*alpha) ·
            exp(tau * psi(u + i*alpha)) du

    is absolutely convergent, real-valued on real payoffs, and agrees with
    `e^{-r*tau} * E[(S_T - K)⁺]`. GBM is the case `psi(u) = i*u*(r-q) -
    sigma^2*u^2/2` (alpha = 2, lambda = 0).

Provable sub-goals, in increasing order of commitment:
  (a) the moment-strip condition `⇔` finiteness of `E[exp(u * X_tau)]` for a
      tempered-stable exponent — this is where the alpha-stable obstruction
      above gets *proved* rather than asserted, and it is a theorem about a
      concrete integral, not about finance;
  (b) absolute convergence of the Carr–Madan integrand on a contour strictly
      inside the strip;
  (c) agreement with the risk-neutral expectation, i.e. Fourier inversion
      against the payoff transform.

See docs/03_research.md D1, which carries the falsifier (fitted `alpha`
concentrating in `(1.3, 1.9)` and being materially *less* moneyness-dependent
than the GBM `sigma` it replaces).
-/
