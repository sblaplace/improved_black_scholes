# BRIEF_009 — the model-free skeleton: parity and bounds at the expectation level

- **Status:** **ISSUED** — no PR yet. This is item 5's machinery of the BSM-2
  kit in `docs/03` §D1 ("What extends"): before the increment law is widened,
  parity and the no-arbitrage bounds are lifted off the closed form onto
  `e^{−rτ}·E[(S_T − K)⁺]`, so that "the widening preserves the skeleton"
  becomes instantiation rather than re-proof.
- **Prerequisite PRs:** BRIEF_007 (T6 sub-goal 3a, `ImprovedBS/RiskNeutral.lean`)
  merged — and through it BRIEF_005/006. BRIEF_008 is merged but **not
  consumed** here. No edit to any existing declaration in
  `ImprovedBS/Core.lean`, `ImprovedBS/Levy.lean`, `ImprovedBS/Fourier.lean`,
  `ImprovedBS/RiskNeutral.lean` or `ImprovedBS/Inversion.lean`; the only
  changes outside the new module are the root `import` line + blurb in
  `ImprovedBS.lean`.
- **Skills:** Lean 4 + mathlib measure theory at the Bochner-integral level:
  `integral_congr_ae`, `integral_add`/`integral_sub`, `integral_const`,
  `integral_nonneg`, `integral_mono`/`integral_mono_ae`, the `Integrable`
  closure lemmas, `MeasureTheory.IsProbabilityMeasure`, and BRIEF_007's
  `gaussianReal` bridge. **No new mathematics**: the whole analytic content is
  `max_sub_swap_eq` (already in the tree) and `le_max_left`/`le_max_right`
  moved under an integral. This is bookkeeping in exchange for a theorem
  schema.
- **Budget:** CI-only verification — no local Lean toolchain, two-run `elab`
  pin bootstrap as in BRIEF_007/008. Names verified at the pinned tag
  v4.34.0 before this brief was committed (ledger C3) are marked ✓ below;
  names marked ? are the expected route and must be re-read at the tag before
  pushing. The numeric route is checked in the oracle **before** any Lean is
  written (ledger C4): `tests/test_bs.py::test_model_free_skeleton` is the
  shadow of every statement in §3–§5 below.

## Background, in order

1. README, "Thesis" and "A rule the whole repo is built around" — skeleton vs
   increment law; independent derivations only.
2. `docs/01` §3, Fact B — the drift condition `E[S_T] = S e^{(r−q)τ}` is the
   martingale bridge; it is the only market hypothesis this brief needs.
3. `docs/03` §D1, "What extends → BSM 2" — the commit criterion this brief
   serves; item 5 is the skeleton-preservation clause.
4. `docs/04` "The dependency spine" and guard (4) — T4′ is T4 + T2 + `linarith`;
   this brief mirrors that route one layer down, and every new declaration is
   pinned.
5. `ImprovedBS/RiskNeutral.lean` §4 — the expectation layer this generalizes
   (`bsCall_eq_riskNeutral_expectation`, `integral_spot_mul_phi_eq_forward`,
   `max_sub_swap_eq`, the `gaussianReal` bridge).
6. `benchmarks/LEDGER.md` C4 (route numerically first) and C7 (hypotheses are
   load-bearing or they are wrong).

## The decision: lift T2/T4 off the closed form before widening the law

As landed, T2/T4 and their primes are theorems **about `bsCall`/`bsPut`** — the
closed forms. The tempered-stable (CGMY) law of `docs/03` §D1 has **no closed
form**: its price *is* the expectation/Fourier integral. A skeleton expressed
only through `bsCall` cannot be "preserved" by a law that never meets one. The
content of the two claims is model-free:

- **parity** is the pointwise payoff identity `(x−K)⁺ − (K−x)⁺ = x − K`
  (`max_sub_swap_eq`) integrated against *any* terminal-spot law, plus the
  drift condition to turn `E[S_T] − K` into the forward spread;
- **the bounds** are pointwise monotonicity — `0 ≤ (x−K)⁺`, `x − K ≤ (x−K)⁺`,
  and `(x−K)⁺ ≤ x` for nonnegative spots — integrated against the same law.

Nothing about either uses a Gaussian. So state them once, for a probability
measure `μ` on `ℝ` and a terminal-spot map `X : ℝ → ℝ`, and every future law
inherits them by supplying three facts: `Integrable X μ`, the drift condition,
and `0 ≤ X`. The GBM instance then **re-derives T2′ and T4 through the new
layer** (new names, `must-not-cite` the closed-form proofs) — which is the
vacuity guard: a mistyped operator, a wrong discount, or a drift condition
stated at the wrong measure cannot survive that re-derivation, and a green
build certifies the abstraction is actually wired to the model we have.

The oracle canary is the other half of the same discipline: the drift
hypothesis is proved *load-bearing* by asserting forward parity **fails** at a
wrong-drift law (BRIEF_007's `σ < 0` check, one layer up).

## The second decision: the operators take `(μ, X)`, not a process

Mathlib v4.34.0 has no Lévy processes and no Lévy–Khintchine. What the tree
already has — from BRIEF_007 — is the right interface: a law of the log-price
(`gaussianReal`) and the spot map composed into it. So `modelFreeCall`/
`modelFreePut` take a probability measure `μ` (the law of the terminal state)
and `X : ℝ → ℝ` (the terminal spot read off that state). The CGMY
instantiation later supplies its own `(μ, X)`; nothing here anticipates its
shape.

Corollary of the interface: `model_free_parity_gap` is stated **without** the
drift condition first — the unfixed form
`call − put = e^{−rτ}(E[S_T] − K)` *is* the pointwise identity's honest
shadow, true for every law including wrong-drift ones — and the drift
hypothesis enters only in `model_free_put_call_parity`, where it converts the
gap into the forward spread `S e^{−qτ} − K e^{−rτ}`. Two theorems, not one,
because the oracle tests exactly that seam.

## Goal

New module `ImprovedBS/Skeleton.lean` (namespace `BSM`, `import
ImprovedBS.RiskNeutral`, `noncomputable section`), **14 declarations** (2
`def`s and 12 lemmas/theorems), stated below in exact shape. For `μ : Measure ℝ` with `[IsProbabilityMeasure μ]`, `X : ℝ → ℝ` the
terminal-spot map:

    modelFreeCall μ X K r tau − modelFreePut μ X K r tau = e^{−rτ}(∫ X ∂μ − K)
    ∫ X ∂μ = S e^{(r−q)τ}  ⟹  the gap is the forward spread S e^{−qτ} − K e^{−rτ}
    0 ≤ X, 0 ≤ K           ⟹  max(S e^{−qτ} − K e^{−rτ}, 0) ≤ modelFreeCall ≤ S e^{−qτ}
                                (and the mirrored put bounds, via parity)

plus the GBM instance at `gaussianReal 0 1` and the closed-form re-derivations
of T2′ and T4 through the layer.

## Scope (numbered)

### §1 The operators (2 defs)

1. `modelFreeCall (μ : Measure ℝ) (X : ℝ → ℝ) (K r tau : ℝ) : ℝ :=
    Real.exp (-r * tau) * ∫ s, max (X s - K) 0 ∂μ` and
   `modelFreePut ... := Real.exp (-r * tau) * ∫ s, max (K - X s) 0 ∂μ`.
   Independent definitions, oracle-style: the put is **not** the call minus
   anything (the `[INDEPENDENCE]` rule, one layer down). Both `noncomputable`
   (Bochner). These are the definitions the pins guard — a definition *is* the
   specification.

### §2 Payoff integrability (2 lemmas)

2. `integrable_call_payoff (hX : Integrable X μ) :
    Integrable (fun s => max (X s - K) 0) μ` — route: the pointwise bound
    `|max (X s - K) 0| ≤ |X s| + |K|` (`le_trans (le_abs_self _) ...`,
    `Real.abs_sub`, `Real.abs_add`) and `Integrable.mono` ?
   over `hX.abs.add (integrable_const |K|)` ?. Measurability of the payoff
   from `hX.aestronglyMeasurable` via `fun_prop` ? (BRIEF_007: `fun_prop`
   closed the Gaussian-side measurability at this tag).
3. `integrable_put_payoff (hX : Integrable X μ) :
    Integrable (fun s => max (K - X s) 0) μ` — route: congruence along
    `max_sub_swap_eq (X s) K`, i.e. the put payoff is
    `max (X s - K) 0 - X s + K`, and `Integrable.sub`/`.add` of items 2, `hX`,
    and the constant. This item must cite `max_sub_swap_eq`; the put's
    integrability coming from the call's *is* the parity identity in embryo.

### §3 Parity — the model-free skeleton, parity half (2 theorems)

4. **`model_free_parity_gap`** — the unfixed-drift form:

       modelFreeCall μ X K r tau - modelFreePut μ X K r tau
         = Real.exp (-r * tau) * ((∫ s, X s ∂μ) - K)

   hypotheses `[IsProbabilityMeasure μ] (hX : Integrable X μ)` only. Route:
   `max_sub_swap_eq`, `integral_sub`/`integral_add` (items 2–3, `hX`, the
   constant `K`), `integral_const` ? with `IsProbabilityMeasure.measure_univ`
   so `∫ s, K ∂μ = K`, then `mul_sub`/`Real.exp` algebra.
5. **`model_free_put_call_parity`** — the forward form (T2′'s shape):

       (hE : ∫ s, X s ∂μ = S * Real.exp ((r - q) * tau)) :
       modelFreeCall μ X K r tau - modelFreePut μ X K r tau
         = S * Real.exp (-q * tau) - K * Real.exp (-r * tau)

   Route: item 4 + `hE` + `Real.exp` algebra (`−rτ + (r−q)τ = −qτ`). The
   statement mirrors `t2_put_call_parity_spread` (the traded form); the put-form
   `t2_put_call_parity` is `linarith` away and is deliberately not restated.

### §4 Bounds — the model-free skeleton, bounds half (3 theorems)

6. `model_free_call_nonneg : 0 ≤ modelFreeCall μ X K r tau` — **no
   hypotheses** beyond the implicit measure: `Real.exp_pos` and
   `MeasureTheory.integral_nonneg` ✓ of `le_max_right`. Nonnegativity of a
   nonneg integrand needs no integrability; the statement should not pretend
   otherwise.
7. **`model_free_call_bounds`** — T4's shape:

       (hE : ∫ s, X s ∂μ = S * Real.exp ((r - q) * tau))
       (hK : 0 ≤ K) (hX0 : ∀ᵐ s ∂μ, 0 ≤ X s) (hX : Integrable X μ) :
       max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0
         ≤ modelFreeCall μ X K r tau ∧
       modelFreeCall μ X K r tau ≤ S * Real.exp (-q * tau)

   Route, each half one pointwise inequality integrated:
   lower `x − K ≤ (x−K)⁺` (`le_max_left`) + `hE` + discount, with the `0`
   side from item 6 (`max_le`, mirroring `t4_call_bounds`'s `refine ⟨max_le ...⟩`);
   upper `(x−K)⁺ ≤ x` from `hX0`, `hK` (two cases at `x ≥ K` and `x < K`) +
   `integral_mono_ae` ✓ + `hE` + discount. Note `hK : 0 ≤ K` rather than
   `0 < K` — the inequality is what it needs. `hX0` is what makes the upper
   bound true at all (at `X s < 0` it is false), so it is a hypothesis, not a
   comment.
8. **`model_free_put_bounds`** — mirrored put bounds, statement shaped after
   `t4_put_bounds`:

       max (K * Real.exp (-r * tau) - S * Real.exp (-q * tau)) 0
         ≤ modelFreePut μ X K r tau ∧
       modelFreePut μ X K r tau ≤ K * Real.exp (-r * tau)

   **Route (checked, see `[SKELETON]` below): item 7 + item 5 + `linarith`
   only** — the exact shape of `t4_put_bounds` over `t4_call_bounds` +
   `t2_put_call_parity`. The upper bound's content is `bsPut ≤ K e^{−rτ}`-via-
   parity; the lower's is `put ≥ 0` and `put ≥ K e^{−rτ} − S e^{−qτ}` from
   `call ≥ 0` and parity. No new integration.

### §5 The GBM instance (3 declarations)

9. `integrable_gaussianReal_iff (f : ℝ → ℝ) :
    Integrable f (ProbabilityTheory.gaussianReal 0 1)
      ↔ Integrable (fun z => f z * phi z)` — the integrability twin of
   BRIEF_007's `integral_gaussianReal_eq_integral_mul_phi`, same proof shape
   (`gaussianReal_of_var_ne_zero` ? + withDensity integrability transfer,
   `MeasureTheory.Integrable.withDensity_iff` ? — verify at tag; the one-ne-zero
   variance hypothesis discharge is the same `(one_ne_zero : (1 : ℝ≥0) ≠ 0)`
   pattern BRIEF_007 used).
10. **`lognormal_parity_gap`** — item 5 instantiated at
    `μ := ProbabilityTheory.gaussianReal 0 1` and
    `X := fun z => S * Real.exp ((r - q - sigma ^ 2 / 2) * tau + sigma * Real.sqrt tau * z)`
    (the map written **inline**, syntactically identical to
    `bsCall_eq_gaussianReal_expectation`'s integrand — no wrapper `def`, per
    BRIEF_006's unapplied-`def` elaboration cost):

        (S K tau r q sigma : ℝ) (htau : 0 ≤ tau) :
        modelFreeCall (gaussianReal 0 1) (fun z => S * Real.exp (...)) K r tau
          - modelFreePut (gaussianReal 0 1) (fun z => S * Real.exp (...)) K r tau
          = S * Real.exp (-q * tau) - K * Real.exp (-r * tau)

    Hypotheses: `htau : 0 ≤ tau` **and nothing else** — no `0 < S`, no `0 < K`,
    no `0 < sigma`. Model-free parity is strictly stronger than the closed-form
    identities at the lognormal law, and the statement is where that shows.
    Route: item 5 with `hX` from item 9 + `integrable_spot_mul_phi` and `hE`
    from item 9 + `integral_spot_mul_phi_eq_forward`; the instance
    `ProbabilityTheory.instIsProbabilityMeasureGaussianReal` ✓ is what
    supplies `[IsProbabilityMeasure]` (confirmed at tag v4.34.0).
11. **`lognormal_call_bounds`** — item 7 at the same `(μ, X)`:

        (S K tau r q sigma : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (htau : 0 ≤ tau) :
        max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0
          ≤ modelFreeCall (gaussianReal 0 1) (fun z => S * Real.exp (...)) K r tau ∧
        modelFreeCall (gaussianReal 0 1) (fun z => S * Real.exp (...)) K r tau
          ≤ S * Real.exp (-q * tau)

    `hS : 0 ≤ S` discharges `hX0` (`Real.exp_pos`); `sigma` again arbitrary.
    The put instance is `model_free_put_bounds` at the same data and is
    **not** restated — the put side is already proved generically through
    parity (item 8's route), and its GBM instance adds a pin, not a claim.

### §6 The closed-form re-derivations (2 theorems — the vacuity guard)

12. **`t2_spread_via_skeleton`** — T2′'s exact statement
    (`bsCall S K tau r q sigma - bsPut S K tau r q sigma
     = S * Real.exp (-q * tau) - K * Real.exp (-r * tau)`) re-derived through
    items 5/10 and the BRIEF_007 bridge
    (`bsCall_eq_riskNeutral_expectation`, `bsPut_eq_riskNeutral_expectation`,
    item 9). **Must not cite** `t2_put_call_parity` or
    `t2_put_call_parity_spread`. Honesty note in the doc-comment: T2′ is
    hypothesis-free and this twin inherits `0 < S`, `0 < K`, `0 < tau`,
    `0 < sigma` from the expectation bridge — same identity, stronger
    hypotheses, different route, and the route is the point.
13. **`t4_call_bounds_via_skeleton`** — T4's exact statement
    (the `max ... ∧ ...` shape of `t4_call_bounds`) re-derived through items
    7/11 and `bsCall_eq_gaussianReal_expectation`. **Must not cite**
    `t4_call_bounds`, `bsCall_nonneg`, `bsPut_nonneg`,
    `Phi_le_exp_mul_Phi_add`, or anything in the T3/T4 analytic spine — the
    proof must go through the model-free layer and the BRIEF_007 identities.
    T4′'s re-derivation is `linarith` of items 12–13 and is not separately
    declared (it is `t4_put_bounds`'s own route, one level up).

Two named theorems of T2′/T4 with two proofs each is not redundancy: it is the
repository's mutant discipline applied to an abstraction. If item 12 could be
closed by `exact t2_put_call_parity_spread`, the skeleton would certify
nothing.

### The route checks (`[SKELETON]`, in `scripts/lean_lint.py`)

Two clauses, each with a seeded cheat in `tests/test_lint.py` (continuing the
`L` series), modeled on `[SPINE]`:

- **(i)** `model_free_put_bounds` must cite `model_free_put_call_parity` —
  the T4′-via-T2 mirror. Cheat: put bounds re-derived from scratch without the
  parity cite.
- **(ii)** every `*_via_skeleton` node must cite at least one of
  `model_free_put_call_parity`, `model_free_call_bounds`,
  `lognormal_parity_gap`, `lognormal_call_bounds`, and must **not** cite
  `t2_put_call_parity`, `t2_put_call_parity_spread`, `t4_call_bounds`,
  `t4_put_bounds`, `bsCall_nonneg`, `bsPut_nonneg`, `Phi_le_exp_mul_Phi_add`.
  Cheat: `t2_spread_via_skeleton` closed by `exact t2_put_call_parity_spread`.

### Oracle side (checked before any Lean is written — C4)

14. `experiments/black_scholes.py` gains two stdlib-only helpers, no existing
    line changed, every mutation anchor survives:

        def model_free_prices(probs, spots, K, r, tau):
            # (discounted call, discounted put) against an explicit discrete law
            call = sum(p * max(s - K, 0.0) for p, s in zip(probs, spots)) * math.exp(-r * tau)
            put  = sum(p * max(K - s, 0.0) for p, s in zip(probs, spots)) * math.exp(-r * tau)
            return call, put

        def model_free_forward(probs, spots):
            return sum(p * s for p, s in zip(probs, spots))

    No `norm_cdf`, no `_d1d2`, no `phi` in the route — the same independence
    rule as `bs_call_by_expectation`.
15. `tests/test_bs.py::test_model_free_skeleton` (16th test), on hand-built
    **non-lognormal** laws (a skewed 3-point law, a 51-point uniform
    discretization, a wrong-drift 3-point law, a degenerate one-point law):
    1. **gap identity** at all four laws:
       `call − put ≈ e^{−rτ}(mean − K)` (abs 1e-12) — the shadow of item 4;
    2. **forward parity** at the laws whose mean is scaled to `S e^{(r−q)τ}`
       (with `q ≠ 0`): `call − put ≈ S e^{−qτ} − K e^{−rτ}` — item 5;
    3. **drift canary** at the wrong-drift law:
       `|call − put − (S e^{−qτ} − K e^{−rτ})| > 1e-6`, with the gap matching
       `e^{−rτ}(mean − K)` instead — the drift hypothesis is load-bearing and
       the test could have been red (the `σ < 0` discipline of BRIEF_007, one
       layer up);
    4. **bounds** at the correctly-drifted laws with `q ≠ 0`:
       `max(S e^{−qτ} − K e^{−rτ}, 0) ≤ call ≤ S e^{−qτ}` and the mirrored put
       bounds — items 7–8;
    5. **degenerate law** (one point at the forward): the call/put values are
       `e^{−rτ}(F − K)⁺`, `e^{−rτ}(K − F)⁺` exactly to 1e-12 and **at least
       one bound edge binds** at both `K < F` and `K > F` — edge tightness, so
       a bound with a slack constant cannot pass as the bound.
16. `tests/test_mutants.py` grows by exactly two entries, each killed by
    `test_model_free_skeleton` **and by no other test** (the helpers are used
    nowhere else):
    - **M13** put payoff corrupted to the call payoff:
      anchor `"p * max(K - s, 0.0)"` → `"p * max(s - K, 0.0)"`;
    - **M14** the mean corrupted to the second moment (a drift bug, the twin
      of M11 one layer up): anchor
      `"sum(p * s for p, s in zip(probs, spots))"` →
      `"sum(p * s * s for p, s in zip(probs, spots))"`.

## Done looks like (acceptance — machine-graded)

- `lake build` green; `#print axioms` of all 14 new constants reports exactly
  `[propext, Classical.choice, Quot.sound]` (audit heredoc in
  `.github/workflows/lean.yml` extended).
- Statement pins: source layer regenerated (94 → 108) with the 94 existing
  entries **byte-identical** in both layers; `elab` layer committed from the
  build job's printed block on the second run (the two-run bootstrap of
  rows 7–8); `cross_layer_check` clean.
- `scripts/lean_lint.py` green with the enlarged `REQUIRED`/`PROTECTED` sets
  (all 14 at `ImprovedBS/Skeleton.lean`) and `[SKELETON]` active;
  `tests/test_lint.py` green with the two new cheats killed by `[SKELETON]`
  and every control still green; `tests/test_pins.py` green.
- `tests/test_bs.py` 16/16; `tests/test_mutants.py` green with M13/M14 killed
  by `test_model_free_skeleton` and by no other test; `tests/test_crosscheck.py`
  green **unmodified** (the cross-verifier's domain is the closed form's grid —
  see out-of-scope); oracle lane green.
- No statement weakened or strengthened: no hypothesis added to or removed
  from T1–T6 or any BRIEF_004/005/007/008 declaration; no existing
  declaration renamed, re-stated or re-proved; `Phi`/`phi` and the closed-form
  definitions untouched (pins prove it); `deferred: {}` untouched.
- Docs sweep, and no more than this: `docs/03` §D1 BSM-2 item 5 marked landed,
  `docs/04` (stack table row for the model-free layer, spine diagram gaining
  `max_sub_swap_eq → model_free_parity_gap → model_free_put_call_parity`,
  dependency table, queue row marked landed), `README.md` status (including
  the stale `14/14` run-line and the mutant counts), `benchmarks/LEDGER.md`
  row 9 with the CI arc, and the `Core.lean` T6 comment block noting the
  skeleton layer.

## Explicitly out of scope

- **The CGMY/tempered-stable exponent and everything under it** — the concrete
  `ν`/`ψ` with the `cpow`/branch work BRIEF_005 deferred, the moment strip's
  positive half, the drift fix at the new law, T6 instantiated at a
  non-Gaussian exponent, the corner limit. Items 1–4 and 6 of the BSM-2 kit
  (`docs/03` §D1); the next briefs. This one deliberately lands **before**
  any of them exists, while GBM is still the only law available to instantiate
  at.
- **Instantiating the skeleton at any non-Gaussian law.** There is nothing to
  instantiate at yet — that is the reason to build the schema now rather than
  later.
- **Vega, rho, and the rest of the Greek set** — closed-form domain
  (`Core.lean`), not skeleton domain; their own brief. (Vega/rho are cheap
  given `t5_delta`/`hasDerivAt_Phi` and belong in the queue, not here.)
- **Payoff classes beyond the call and put** (digitals, spreads, power
  payoffs) and model-free bounds for them. The payoff identity behind parity
  is call/put-specific; a general payoff class is a different theorem schema.
- **Uniqueness / Feynman–Kac verification** (the deferred log-S half of
  `docs/04`).
- **The empirical falsifier** of `docs/03` §D1 (fitted α, out-of-sample
  hedging per parameter): needs market data, separate track.
- **Any `sorry`, any new third-party Python dependency, any change to
  `ImprovedBS/Crosscheck.lean`** (its grid is a closed-form instrument), any
  change to T1–T6 or BRIEF_004/005/007/008 declarations.
