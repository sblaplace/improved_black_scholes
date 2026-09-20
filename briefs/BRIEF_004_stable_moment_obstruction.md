# BRIEF_004 — The α-stable moment obstruction (T6, sub-goal 1)

- **Status:** IN PROGRESS — PR
  [#5](https://github.com/sblaplace/improved_black_scholes/pull/5), commit
  `54a0ff6`. `ImprovedBS/Levy.lean` is in the tree (seven declarations, no
  `sorry`), imported by the root module, listed in `REQUIRED`/`PROTECTED` and in
  the `#print axioms` audit, pins refreshed 31 → 38. The verdict is CI's and is
  recorded in `benchmarks/LEDGER.md` row 4; the correction record below is
  written now because both corrections were found by *proving* the theorem, not
  by running the grader.
- **Prerequisite PRs:** none in the Lean tree. This brief is deliberately
  independent of BRIEF_001–003: it needs no BS machinery at all.

---

## Correction record

Recorded here and in `benchmarks/LEDGER.md` (row **C7**) rather than silently
rewritten, per the ledger's archival rule. The brief as issued asked for a
theorem stated for `α ∈ (0, 2)` and made "the hypotheses are *used*: `0 < α`,
`α < 2`, …" an acceptance item, with a sanity check meant to force it. Two
things are wrong, and both make the *stated target* wrong rather than making the
proof harder. **Everything from `## Goal` down is the brief as issued**; where
it conflicts with this record, the record wins.

1. **`α < 2` is not needed, and the sanity check that demanded it is false.**
   The acceptance item reads: "with `α ≥ 2`-like Gaussian tails the exponential
   moment is finite, so a proof that never uses `α < 2` has proved something
   false". The fear is legitimate — a proof that ignores a hypothesis might be a
   proof of a false statement — but the premise is not: a Gaussian tail
   `e^{−x²/2}` is not an `α ≥ 2` power law. It is eventually *below*
   `c·x^(−α)` for **every** `α`, so it never satisfies the hypothesis
   `μ([x, ∞)) ≥ c·x^(−α)` at any index, and it cannot be the counterexample the
   item claims it is. For a genuine power tail the conclusion holds at every
   index — a `x^(−3)` tail still has infinite exponential moment, because
   `∫ e^x x^(−3) dx` diverges. The dichotomy the obstruction turns on is
   **polynomial versus exponential decay**, not `α < 2` versus `α ≥ 2`.
   The correction therefore *strengthens* the result: the theorem is stated for
   every real `α`, and the machine-checked statement of "the proof does not
   secretly need `α < 2`" is that `α < 2` does not appear in it. This also makes
   the obstruction more useful to T6 than the brief's version: `α ∈ (0, 2)` is
   not where it lives, so no amount of parameter-range argument inside that
   interval can escape it.
2. **`0 < α` is a regime hypothesis, not a proof step.** It is likewise never
   used: the divergence is `exp` against `rpow`, and the index does not enter
   the estimate. What `α > 0` actually does is make the hypothesis
   *satisfiable*: for `α ≤ 0` the bound `μ([x, ∞)) ≥ c·x^(−α)` forces
   `c ≤ μ([x, ∞))` for all large `x`, impossible for a probability measure as
   `x → ∞`. So `α > 0` is exactly the range in which the hypothesis is about
   something, and it is recorded as a statement note in the module doc-comment,
   in `docs/03` §D1 and in ledger row C7 — not kept as a binder the proof never
   touches, which is the vacuity shape this repository rejects everywhere else.

**Scope item 3 is honoured as the exception it allows:** mathlib v4.34.0 has no
symmetric α-stable law, so the specialization is *not* machine-checked. The tail
bound is the hypothesis of the theorem, and the `c = F(−α)` citation for the
Zolotarev `S1` parametrization stays in `docs/03` §D1. The PR says so in those
words.

---
- **Skills:** Lean 4 + mathlib measure theory and improper integrals
  (`MeasureTheory.Integral`, tail estimates, `Real.rpow`). The finance content
  is one sentence; the analysis is the whole brief.
- **Budget:** this is the one brief here without a confident estimate. The
  statement is short and the mathematics is standard, but divergence proofs in
  mathlib are less travelled than convergence proofs. Budget 2 days, and treat
  "here is the obstruction, here is how far I got, here is the exact missing
  lemma" as an acceptable GREEN-adjacent outcome — recorded honestly in the
  ledger, per the repo's rule that a RED verdict is a result.

## Goal

**Prove the negative result that shapes the entire research direction.**

`docs/03` §D1 and the T6 comment block in `ImprovedBS/Core.lean` both record
that a *pure* α-stable log-increment cannot be a risk-neutral log-price,
because it has no finite exponential moment. That claim is currently
**prose**. This brief makes it a theorem.

Why it is the highest value-per-effort item in the research tier: every
alternative approach to T6 has to assume its way past this obstruction. Proving
it means the tempered-stable hypothesis in D1 is *earned* rather than
convenient — and it converts the most likely RED verdict in the research tier
into a theorem that is true, checked, and useful.

## The statement

Work with the tail, not the characteristic function — it is far easier to make
divergence precise from a tail bound, and it is the form the finance actually
needs.

Let `α ∈ (0, 2)` and let `μ` be a probability measure on `ℝ` whose upper tail
is regularly varying at index `α`: there are `c > 0` and `x₀` with

    μ ([x, ∞)) ≥ c · x^(−α)        for all x ≥ x₀.

Then

    ∫ x, Real.exp x ∂μ = ∞.

and consequently, for `S_T = S₀ · e^{X_τ}` with `X_τ ~ μ`,

    E[S_T] = ∞,

so there is no drift adjustment making `S_T` integrable, and hence no
equivalent martingale measure within the exponential-Lévy ansatz.

Suggested Lean shape (adjust to what mathlib offers; do not fight it):

```lean
/-- A probability measure with a regularly varying upper tail of index α < 2
has no finite exponential moment. -/
theorem exp_moment_infinite_of_tail_lower_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (α c x₀ : ℝ)
    (hα : 0 < α) (hα2 : α < 2) (hc : 0 < c)
    (htail : ∀ x ≥ x₀, c * x ^ (-α) ≤ μ (Set.Ici x)) :
    ¬ MeasureTheory.Integrable (fun x => Real.exp x) μ := by
  sorry
```

Proving non-integrability is usually easier through the layer-cake / tail
representation

    ∫ e^x dμ ≥ Σₙ eⁿ · μ([n, ∞)) ≥ Σₙ eⁿ · c · n^(−α) = ∞

than by manipulating the integral directly, since the summands grow. A
comparison-test route against a divergent series is likely the cleanest; look
for what mathlib has on `Real.exp` growth versus `rpow` decay before choosing.

## Scope (numbered)

1. State and prove the tail ⇒ divergent exponential moment theorem above, in a
   new module `ImprovedBS/Levy.lean` (imported by `ImprovedBS.lean`). Keep it
   free of any option-pricing vocabulary: this is analysis, and mixing the two
   makes it unreviewable.
2. State the corollary in financial terms — `E[S₀·e^{X_τ}] = ∞` ⇒ no EMM in the
   exponential-Lévy ansatz — as a *separate* theorem that consumes (1). The
   separation matters: (1) is checkable analysis, (2) is the modelling claim,
   and a reader should be able to accept one while doubting the other.
3. Specialize to the symmetric α-stable law if and only if mathlib has enough
   about it to make that cheap. If it does not, state the specialization as a
   `def`-free remark in the doc-comment with the exact tail asymptotic cited
   from the literature, and **say in the PR that the specialization is not
   machine-checked**. Do not fake it.
4. Record in `docs/03` §D1 which parts of the obstruction argument are now
   theorems and which remain prose. That section currently asserts the whole
   chain; after this brief it should distinguish them.
5. Add the new theorem names to `REQUIRED` in `scripts/lean_lint.py` and to the
   `#print axioms` audit list in `.github/workflows/lean.yml`.
6. Ledger row.

## Done looks like (acceptance — machine-graded)

- `lake build` green with `ImprovedBS/Levy.lean` in the tree.
- `#print axioms` on `exp_moment_infinite_of_tail_lower_bound` and the EMM
  corollary shows no `sorryAx`.
- `scripts/lean_lint.py` green, baseline unchanged (this brief adds proved
  nodes; it must not add `sorry`s).
- The hypotheses are *used*: `0 < α`, `α < 2`, `0 < c` and the tail bound each
  appear in the proof or the statement is over-general. (Sanity check: with
  `α ≥ 2`-like Gaussian tails the exponential moment is finite, so a proof that
  never uses `α < 2` has proved something false.)
- `docs/03` §D1 updated to separate proved from asserted.

## Explicitly out of scope

- **The positive half of T6.** Absolute convergence of the Carr–Madan integral
  for a *tempered* exponent, and its agreement with the risk-neutral
  expectation, are sub-goals 2 and 3 in `docs/03` §D1 and are separate briefs.
  Do not start them here; this brief's value is that it is small and complete.
- Any CGMY / Boyarchenko–Levendorskii construction. The tempered family is what
  this obstruction *motivates*, not what it proves.
- Empirical work: fitting α to a panel, the falsifiers (a) and (b) in
  `docs/03` §D1. Those need data and a different harness entirely.
- T5, and anything in `ImprovedBS/Core.lean` beyond importing the new module.

## Why a negative result gets its own brief

Because the repository's thesis is that BS's failures are failures of the
increment law, and the first thing anyone reaching for a heavier-tailed
increment law discovers is that most heavy tails are not admissible at all.
Knowing *precisely which* ones are, and why, is the difference between a
research program and a series of plausible-sounding dead ends. `docs/02` §5
demands a falsifier for every direction; this brief supplies the falsifier for
the most attractive version of D1, and it is a theorem rather than an opinion.
