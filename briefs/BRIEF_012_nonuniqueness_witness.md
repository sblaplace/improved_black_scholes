# BRIEF_012 — the machine-checked non-uniqueness witness (BSM-2 kit item 7)

- **Status:** **LANDED GREEN** @ `a61be00` — lean run 36052072620 (oracle lane
  run 36052072567), PR [#19](https://github.com/sblaplace/improved_black_scholes/pull/19):
  `lake build` (`✔ Built ImprovedBS.NonUniqueness`, no warnings) + the
  `#print axioms` audit on all 186 entries (the 148 previous plus this brief's
  38 theorems, every one on `[propext, Classical.choice, Quot.sound]`) +
  **statement pins (elab, all 210)** + the oracle↔Lean cross-verifier + `lint`
  (incl. `[NONUNIQ]`) + `oracle` (incl. `test_nonuniqueness_witness`, mutants
  M17–M19) all green; `benchmarks/LEDGER.md` row 12 has the verdict, the
  three-run CI arc and correction C16 (two numerical slips in this brief's own
  route-check table, found by implementing it). Issued by PR
  [#18](https://github.com/sblaplace/improved_black_scholes/pull/18) @ `a3d3939`
  (documentation only; lean run 36035539204). This is **item 7** of the BSM-2
  kit in `docs/03` §D1 and the successor `docs/04`'s
  queue names explicitly: *"the machine-checked non-uniqueness witness (item 7
  — the named successor `BRIEF_012`, ledger C13: one period is enough, and the
  witness is a trinomial)"*. Items 1–2 landed as BRIEF_011; items 3 and 6 are
  still unissued and are **not** this brief (§"Explicitly out of scope").
- **Why this one, and not item 3 or 6.** Three reasons, each checkable in the
  tree rather than argued:
  1. It is the only remaining kit item that tests the repository's *own*
     framing. C13's finding 2 words it as *"a RED verdict on the thesis's
     dynamic half, which by this ledger's rules is a result, not an incident"*.
     Every preservation theorem landed so far is about the **static** layer —
     the layer, C13 says, *"that was never in danger"*. Until this lands, the
     README's dynamic/static split is prose.
  2. It is the cheapest. `docs/03` §D1 item 7: *"A one-period trinomial witness
     suffices (finite sums, no Lévy machinery)."* No `cpow`, no contour, no
     Fourier inversion — finite sums of Dirac masses. Compare item 6 (a
     `Filter.Tendsto` limit of `cgmyExponent` as `Y → 2`, where `Γ(−Y)` has a
     pole and the corner needs its own statement) and item 3 (an Esscher or
     minimal-entropy measure construction).
  3. It *consumes* landed machinery instead of building any. Item 7's
     requirement — *"both satisfy the skeleton layer's parity and bounds (item
     5's three facts)"* — is literally BRIEF_009's `model_free_put_call_parity`
     and `model_free_call_bounds`, instantiated. And the oracle already has the
     discrete-law API: `model_free_prices(probs, spots, K, r, tau)` and
     `model_free_forward(probs, spots)` (`experiments/black_scholes.py`), the
     numeric shadows of `modelFreeCall`/`modelFreePut`. **No new numeric
     route**, unlike BRIEF_007/008/010/011 which each added one.
- **Prerequisite PRs:** BRIEF_009 (`ImprovedBS/Skeleton.lean`) merged — this
  brief is one new module that instantiates its layer, plus grading wiring.
  **No edit to any existing declaration** anywhere in the tree, and no
  pre-existing pin may move: the brief is append-only in both pin layers.
- **Skills:** Lean 4 + mathlib at the pinned tag v4.34.0: `Measure.dirac`,
  `Measure.smul`, `IsProbabilityMeasure`, integrals against finite Dirac sums
  (`integral_dirac`, `integral_add`, `integral_smul`), and `linarith`/`norm_num`
  on dyadic rationals. No analysis beyond finite sums.
- **Budget:** one CI-only lane (no local Lean toolchain). The mathematics is
  already fixed and route-checked (§"The numeric route-check"), so the expected
  failure mode is *not* wrong math — it is API shape at the tag, which is what
  cost BRIEF_010 nine runs and BRIEF_011 five. Budget for elaboration rounds,
  not for rediscovery.

## Background, in order

1. `docs/03` §D1 item 7 is the requirement, verbatim: *"The tree contains a
   machine-checked non-uniqueness witness: two distinct probability measures,
   both satisfying the drift condition, giving different call prices — while
   both satisfy the skeleton layer's parity and bounds (item 5's three facts).
   That is the formal statement that static-skeleton preservation is
   necessary-but-not-sufficient, and it is what obliges item 3's 'named'."*
2. `benchmarks/LEDGER.md` C13 is the correction that queued this brief, and it
   contains a **constraint on the witness that a first attempt will get
   wrong**: *"within a single exponential-Lévy model the Esscher martingale
   equation is strictly monotone in the parameter (the cumulant is strictly
   convex), so non-uniqueness lives **across** selection principles, not within
   the Esscher family — the witness must be cross-family, or **finite**."* A
   witness built from two Esscher transforms of one CGMY law is therefore a
   *false theorem*, not a hard one. The trinomial is the finite escape, and it
   is why this brief is discrete.
3. `ImprovedBS/Skeleton.lean` (BRIEF_009) is the layer being instantiated. Its
   three facts, and the exact names:
   - `hX : Integrable X μ` — item 5's integrability;
   - `hE : ∫ s, X s ∂μ = S * Real.exp ((r - q) * tau)` — the drift condition;
   - `hX0 : ∀ᵐ s ∂μ, 0 ≤ X s` (plus `hK : 0 ≤ K`) — for
     `model_free_call_bounds`' upper half.
   Supply those three and `model_free_put_call_parity` /
   `model_free_call_bounds` / `model_free_put_bounds` are inherited. That is
   BRIEF_009's own claim — *"a later law inherits T2/T4 by supplying three
   facts, not by re-proof"* — and this brief is the first place it is exercised
   at a law that is not lognormal.
4. The `[SKELETON]` lint check (BRIEF_009) already enforces a *route*
   commitment: the `*_via_skeleton` nodes must cite the model-free layer and
   must **not** cite the closed-form proofs. This brief's `[NONUNIQ]` check
   (§"Grading wiring") is the same species: the witness must consume
   BRIEF_009's theorems, not restate parity and bounds from scratch.

## The witness — fixed numeric contract

`S = 1`, `tau = 1`, `r = 0`, `q = 0`, `K = 1`, so the discount factor is `1`
and the drift condition is exactly `E[S_T] = 1`. Terminal spots are the three
atoms `(1/2, 1, 2)`, and `X := id`, so the law *is* the terminal-spot law and
no separate state space is needed.

The martingale solutions form a segment, and it is worth having the segment
before picking points on it: `p₁ + p₂ + p₃ = 1` together with
`p₁/2 + p₂ + 2p₃ = 1` gives

    p₃ = p₁/2,      p₂ = 1 − 3p₁/2,      p₁ ∈ [0, 2/3]        (★)

Both witnesses are taken **strictly inside** that segment, so both are fully
supported and neither is a Dirac or a two-point law:

| | `p = (p₁, p₂, p₃)` | `E[S_T]` | `call = E[(S_T−1)⁺]` | `put = E[(1−S_T)⁺]` |
|---|---|---|---|---|
| **A** | `(1/2, 1/4, 1/4)` | `1/4 + 1/4 + 1/2 = 1` | `1/4` | `1/4` |
| **B** | `(1/4, 5/8, 1/8)` | `1/8 + 5/8 + 2/8 = 1` | `1/8` | `1/8` |

Everything about this table is dyadic, so the Lean side states it over `ℚ`
with `norm_num` and no floating-point tolerance anywhere.

**Why the interior matters, and state it in the module.** The endpoints of (★)
are `p₁ = 0` (degenerate at `S_T = 1`, call price `0`) and `p₁ = 2/3`
(`p₂ = 0`). A witness built from either endpoint invites the dismissal *"the
measures differ only because one is degenerate"* — and, worse, at the `p₁ = 0`
endpoint the law is a Dirac, where the call price is `0` and a reader can
suspect the difference is a support artifact rather than incompleteness. Two
interior points are **mutually equivalent** probability measures (same full
support on three atoms), so the price difference cannot be a measure-equivalence
artifact. Mutual absolute continuity of A and B is a scope item below for
exactly this reason, and it is the part of the statement that makes it an
incompleteness theorem rather than two unrelated measures.

**Why the payoff vector escapes the span.** With spots `(1/2, 1, 2)` and
`K = 1`, the payoff vector `(S_i − K)⁺` is `(0, 0, 1)`, which is *not* in the
span of `{(1,1,1), (1/2, 1, 2)}`. That is the whole mechanism: the martingale
condition pins the law's action on `1` and on `S_T`, and the call payoff is
linearly independent of both, so the price is free to move along (★). A
**linear** payoff would give the same price at every measure on (★) — which is
the forward, and is precisely why parity holds at both A and B while the call
price does not.

## The mathematics to land

New module `ImprovedBS/NonUniqueness.lean`, `namespace BSM`, structured as:

**§1 The trinomial law.** One definition and its three basic facts.

    noncomputable def trinomialMeasure (p₁ p₂ p₃ s₁ s₂ s₃ : ℝ) : Measure ℝ :=
      ENNReal.ofReal p₁ • Measure.dirac s₁
        + ENNReal.ofReal p₂ • Measure.dirac s₂
        + ENNReal.ofReal p₃ • Measure.dirac s₃

    theorem trinomialMeasure_isProbability  -- given p ≥ 0 and p₁+p₂+p₃ = 1
    theorem trinomialMeasure_integral       -- ∫ s, f s ∂μ = p₁·f s₁ + p₂·f s₂ + p₃·f s₃

`trinomialMeasure_integral` is the workhorse: it is `integral_add` +
`integral_smul` + `integral_dirac`, and every subsequent fact about A and B
routes through it rather than re-integrating. `IsProbabilityMeasure` is
`measure_univ` on the same decomposition. **A definition is a specification**
(`scripts/lean_lint.py`'s `[PINS]` rule), so `trinomialMeasure` is pinned by its
body: hollowing it to `0` or collapsing it to a single Dirac is a diff.

**§2 The two measures.** `witnessMeasureA` and `witnessMeasureB` as
`trinomialMeasure` at the table above, with `witnessSpotLo/Mid/Hi := 1/2, 1, 2`
as definitions (not literals scattered through proofs), and:

    witnessA_prob witnessB_prob        : IsProbabilityMeasure _
    witnessA_integrable witnessB_integrable : Integrable id _
    witnessA_nonneg   witnessB_nonneg  : ∀ᵐ s ∂_, 0 ≤ id s
    witnessA_drift    witnessB_drift   : ∫ s, id s ∂_ = 1 * exp ((0 - 0) * 1)
    witnessA_call     witnessB_call    : modelFreeCall _ id 1 0 1 = 1/4 / = 1/8

**§3 The skeleton survives at both.** `witnessA_parity`/`witnessB_parity` and
`witnessA_bounds`/`witnessB_bounds`, each **citing**
`model_free_put_call_parity` / `model_free_call_bounds` and supplying the three
facts. This is the `[NONUNIQ]` route commitment.

**§4 The witness.** The four statements that make it item 7:

    witnessA_ne_B            : witnessMeasureA ≠ witnessMeasureB
    witnessCall_ne           : modelFreeCall witnessMeasureA id 1 0 1
                               ≠ modelFreeCall witnessMeasureB id 1 0 1
    witness_equivalent       : witnessMeasureA ≪ witnessMeasureB
                               ∧ witnessMeasureB ≪ witnessMeasureA
    static_skeleton_does_not_select_measure
                             : -- the packaged conjunction: two distinct,
                               -- mutually equivalent probability measures,
                               -- both with the drift condition, both
                               -- satisfying parity and the no-arbitrage
                               -- bounds, and pricing the call differently

`static_skeleton_does_not_select_measure` is the headline and the pin that
matters: it must be a **conjunction** carrying the drift, parity, bounds,
distinctness and price difference together, not a bare `≠`. A bare `≠` between
two `modelFreeCall` terms would be true of many unrelated pairs and would not
say that the skeleton failed to select anything.

**§5 The martingale set (★).** Cheap, and it is what makes the witness
canonical rather than cherry-picked:

    martingale_set_param : p₁ + p₂ + p₃ = 1 → p₁/2 + p₂ + 2·p₃ = 1
                           → p₃ = p₁/2 ∧ p₂ = 1 − 3·p₁/2

`linarith`. Two consequences, both worth landing because together they turn a
two-point witness into a statement about the whole pricing set:

    martingale_set_nondegenerate : ∃ p₁ p₁', p₁ ≠ p₁' ∧ both in [0, 2/3]
                                   -- the one-period market with one risky
                                   -- asset and three states is INCOMPLETE
    martingale_set_call_eq       : on (★), modelFreeCall = p₁/2

That last one is the sharp form of the incompleteness and it is measured, not
conjectured: a sweep of (★) over `p₁ ∈ {0, 1/24, …, 2/3}` (17 points, exact
`Fraction` arithmetic, route-checked before this brief was written) gives
`0 violations` of normalization/drift/nonnegativity and call prices
`0, 1/48, 1/24, 1/16, 1/12, 5/48, 1/8, 7/48, 1/6, 3/16, 5/24, 11/48, 1/4,
13/48, 7/24, 5/16, 1/3` — i.e. **exactly `p₁/2`**, ranging over the whole
interval `[0, 1/3]`. So it is not merely that two martingale measures disagree:
*every* price in `[0, 1/3]` is attained by some martingale measure, and the
skeleton's bounds (`0 ≤ call ≤ 1`) do not come close to pinning it. The same
sweep shows the forward — a *linear* payoff — is constant at `1` on the entire
segment, which is the mechanism stated as a measurement: the martingale
condition pins the law on `1` and on `S_T`, and nothing else.
`p₂ ≥ 0` fails exactly past `p₁ = 2/3` (at `p₁ = 17/24`, `p₂ = −1/16`), which
is what bounds the segment.


## The numeric route-check (measured before the Lean — ledger C4)

The witness above is not proposed from algebra alone; it was run through the
repository's own oracle before this brief was written, exactly as BRIEF_011's
route check was. Scratch script, `model_free_prices` / `model_free_forward`
only — no new oracle code, which is itself the finding that makes this brief
cheap:

| check | measure | result |
|---|---|---|
| `sum(p) = 1` | A, B | `True`, `True` (exact, dyadic) |
| drift `E[S_T] = 1` (`witnessA_drift`/`witnessB_drift`) | A, B | `True`, `True`; float `E[S_T] = 1.0` both |
| `call` (`witnessA_call`/`witnessB_call`) | A, B | `0.25`, `0.125`; exact `Fraction` agrees with the float bit-for-bit |
| `put` | A, B | `0.25`, `0.125` |
| parity gap `call − put − (S e^{−qτ} − K e^{−rτ})` (`*_parity`) | A, B | `0.0`, `0.0` |
| bounds `max(S e^{−qτ} − K e^{−rτ}, 0) ≤ call ≤ S e^{−qτ}` (`*_bounds`) | A, B | `0 ≤ 0.25 ≤ 1`, `0 ≤ 0.125 ≤ 1` |
| **prices differ** (`witnessCall_ne`) | A vs B | `True`, gap `0.125` |
| **drift canary** `p = (1/4, 5/8, 3/8)` | — | `sum(p) ≠ 1`, `E[S_T] = 1.25 ≠ 1`, **parity gap jumps to `0.25`** |
| (★) sweep, `p₁ ∈ {0, 1/24, …, 2/3}`, 17 points, exact `Fraction` (`martingale_set_param`, `martingale_set_call_eq`) | segment | `0` violations of norm/drift/nonnegativity; call `= p₁/2` at every point; forward constant `1.0`; `p₂ < 0` first at `p₁ = 17/24` |

The last row is the point of the exercise and it is why the drift hypothesis is
load-bearing rather than decorative: break the drift by moving `p₃` from `1/8`
to `3/8` and parity in *traded* form fails immediately, gap `0.25`, while the
*unfixed* gap identity still holds and the bounds still hold. That is
`model_free_put_call_parity` versus `model_free_parity_gap` behaving exactly as
BRIEF_009 stated — one needs the drift, the other provably does not. The
committed mutant (§below) seeds this canary so the new test can fail.

## Grading wiring (the repo motion)

* `scripts/lean_lint.py`: the new declarations go in `REQUIRED` **and**
  `PROTECTED` (`trinomialMeasure` included — a definition is a specification),
  and a new **`[NONUNIQ]` check** with three clauses and at least one mutant:
  1. `witnessA_parity`/`witnessB_parity`/`witnessA_bounds`/`witnessB_bounds`
     must **cite** `model_free_put_call_parity` / `model_free_call_bounds`
     (the route commitment; the cheat is restating parity from `max_sub_swap_eq`
     inside the new module);
  2. `static_skeleton_does_not_select_measure` must contain **both**
     `witnessA_drift`-class drift content and a `≠` on the two prices — the
     cheat is weakening the headline to a bare inequality;
  3. `trinomialMeasure` must be a sum of **three** `Measure.dirac` terms — the
     cheat is collapsing it to one Dirac, which would make `witnessCall_ne`
     unprovable and, if quietly restated, would hollow the whole module.
  Mutants seeded in `tests/test_lint.py`: the collapsed Dirac (clause 3), the
  re-derived parity (clause 1), the weakened headline (clause 2). House rule:
  each must be killed **by name**, and the count in the README and this brief
  must move with it.
* `experiments/black_scholes.py` + `tests/test_bs.py`: a committed
  `test_nonuniqueness_witness` asserting the whole route-check table — both
  drifts, both prices at their exact dyadic values, both parity gaps at zero,
  both bound pairs, `call(A) ≠ call(B)`, the (★) parametrization on a sweep of
  `p₁`, and the drift canary's rejection. **Uses only the existing
  `model_free_prices`/`model_free_forward`**; if it needs a new oracle
  function, that is a sign the witness has drifted from the model-free layer.
* `tests/test_mutants.py`: at least two mutants, each killed by
  `test_nonuniqueness_witness` alone — **M17** the drift canary (`p₃ : 1/8 →
  3/8`, breaking the drift so the parity assertion fails) and **M18** a
  payoff-vector corruption (call payoff evaluated with the put's `max(K−s,0)`),
  which destroys `call(A) ≠ call(B)` without touching any probability.
* `tests/golden_statements.json`: append-only, both layers, with the 165
  pre-existing entries **byte-identical**. The `elab` layer for the new names
  bootstraps red on the first CI run by design and the printed `elab_delta` is
  merged verbatim; the commit is a pure insertion and `changed` must be `0`.
* `ImprovedBS.lean`: one import line + blurb. Nothing else outside the module.
* `benchmarks/LEDGER.md`: a row when CI grades it. `docs/03` §D1 item 7 and
  `docs/04`'s queue get the landed status; both currently say "queued".

## Done looks like (acceptance — machine-graded)

1. `lake build` green at the pinned tag, with `#print axioms` on the new
   `-- BRIEF_012:` section showing `[propext, Classical.choice, Quot.sound]`
   and never `sorryAx`.
2. `static_skeleton_does_not_select_measure` is a theorem, not a `sorry` and
   not a `True`: the elaborated pin must show the conjunction with the drift
   condition, parity, both bound pairs, measure distinctness and the price
   `≠` all present. **This is the criterion the `[PINS]` lane exists for** —
   a hollowed headline builds fine and certifies nothing.
3. `witness_equivalent` is proved: the two measures are mutually absolutely
   continuous, so the price difference is incompleteness and not a support
   artifact.
4. `martingale_set_param` and `martingale_set_call_eq` are proved, so the
   witness is a point on a characterized segment rather than a lucky pair, and
   the price range `[0, 1/3]` is a theorem rather than a route-check
   observation.
5. `lint` green including `[NONUNIQ]`, with each of its mutants red under
   mutation and killed by name.
6. `oracle` lane green including `test_nonuniqueness_witness`; mutation harness
   green with M17/M18 killed by that test alone.
7. No pinned statement outside `ImprovedBS/NonUniqueness.lean` moved;
   `deferred: {}` untouched; T1–T6 and BRIEF_004–011 statements unchanged.

## Explicitly out of scope

* **Item 3** (the drift fixed at a *named* pricing measure — Esscher,
  minimal-entropy, mean-correcting) is the next brief's content. This one proves
  the *need* for a name; it does not supply one. Note the ordering logic in
  C13: item 7 is what "obliges item 3's 'named'", so landing 7 first means
  item 3 is written against a proved requirement rather than an assertion.
* **Item 6** (the GBM corner `ψ_CGMY → ψ_GBM` as `Y → 2`) is deferred, as
  `docs/04`'s queue says. `Γ(−Y)` has a pole at `Y = 2`, so the corner needs its
  own normalization before it needs a brief.
* **The compound-Poisson version.** `docs/03` item 7 notes it *"ties it to the
  Lévy line"*; it is genuinely more interesting and genuinely more work (an
  infinite-activity-free but infinite-state law, so integrability is no longer
  finite sums). Not here.
* **No Lévy process, no stochastic integral, no hedging.** The witness is a
  one-period market. `docs/03` already flags the hedging horizon as mathlib
  frontier work at the pinned tag (no Itô formula, no stochastic integral);
  nothing in this brief touches it.
* **No claim about which measure is right.** The theorem is that the skeleton
  does not choose; it is not evidence for any particular selection principle.
* **Mathlib API names in §1–§2 are NOT verified against the pinned tag.** This
  brief was written in a sandbox with no route to the toolchain *or* to the
  mathlib source (`curl` to both `leanprover-community.github.io` and
  `raw.githubusercontent.com` fails at the TLS layer), so ledger C3's
  "verify every name at the tag before pushing" step could not be run. The
  names relied on — `Measure.dirac`, `Measure.smul`, `IsProbabilityMeasure`,
  `MeasureTheory.integral_dirac`, `integral_add`, `integral_smul`,
  `MeasureTheory.Measure.AbsolutelyContinuous` — are long-standing and
  low-risk, but the first CI run should be treated as the name check. Fallback
  if `IsProbabilityMeasure` on a three-term Dirac sum resists: prove
  `measure_univ` directly from `Measure.smul_apply` and `measure_dirac_apply`
  with `ENNReal` normalization by `norm_num`, rather than hunting for a
  convex-combination instance that may not exist at v4.34.0.

## Why this is worth a brief (and shaped this way)

Because it is the only node in the program whose expected verdict is a
**negative** result about the program's own thesis, and the ledger has to be
able to record that. C13 is explicit that a RED verdict on an approach is a
result, not an incident; this brief is where that rule gets used, since the
dynamic skeleton's uniqueness genuinely does fail and the tree should say so in
a checked statement rather than in a paragraph.

The two things a reviewer should check are the two the guards watch. First, the
witness must be **finite or cross-family** — C13's monotonicity remark makes an
intra-Esscher witness a false theorem, and `[NONUNIQ]` clause 3 plus the
three-Dirac pin is what stops the module from quietly degenerating to a
one-point law where the price difference cannot exist. Second, the headline must
stay a **conjunction** — `witnessCall_ne` alone is true of countless unrelated
pairs and would prove nothing about selection, which is exactly the
"green build certifying nothing" failure the README's founding rule is about,
and exactly why acceptance item 2 asks for the elaborated pin rather than the
name.
