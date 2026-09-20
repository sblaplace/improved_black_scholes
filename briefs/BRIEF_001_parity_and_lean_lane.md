# BRIEF_001 — Put–call parity (T1 + T2) and the Lean grading lane

- **Status:** OPEN / first in the brief series
- **Prerequisite PRs:** none (this is the bootstrap brief; base on current `main`)
- **Skills:** Lean 4 + mathlib basics; this brief is the on-ramp
- **Budget:** ≤ 60 wall-clock minutes of E2B compute, comfortably within tool limits

## Goal

Stand up the machine-grading pipeline *and* land the first two formally
checked results, so later briefs (T5, T6 — the ones with actual research
stakes) have a proven mechanical grader. Concretely: make
`Lean/core/bsm_theorems.lean` a file that formally *and mechanically*
verifies the put-call parity identity (T2) and the
`d1 - d2 = sigma*sqrt(tau)` identity (T1), with a `lake build` CI lane that
either compiles the theorems or fails loudly — **no prose-assumed proof is
acceptable**. The deliverable is measured by the machine, not by a human.

1. **T1**: `d1(S,K,τ,r,q,σ) − d2(S,K,τ,r,q,σ) = σ·√τ`  (pure real algebra)
2. **T2**: put-call parity — for the SAME BSM European-option closed form,
   `bsPut == bsCall - S e^{−qτ} + K e^{−rτ}`

And make CI mechanically check it. Do NOT change any parameter meanings,
definitions, or the numeric contract in `experiments/` (those stay exactly as
committed — grep `bs_price`, `_d1d2`, `bs_pde_residual` to confirm your Lean
definitions use the same real-arithmetic meanings as the oracle).

## Background (read in order)

- `docs/01_baseline.md` — the math, notation, and the exact definitions of
  `d1`, `d2`, `bsCall`, `bsPut`. Flat notation is the source of truth;
  your Lean reals must match it.
- `docs/04_formal_plan.md` — the T1..T6 stack, difficulty tiers, and what a
  "verified" theorem means in THIS repo (a mathlib-backed machinery check).
- `experiments/black_scholes.py` — the *numeric oracle*: pure-stdlib Python
  implementing exactly the formulas in docs/01, plus the PDE residual,
  put-call parity, and delta-identity checks. Lean definitions must agree
  with this symbol-for-symbol.
- `Lean/core/bsm_theorems.lean` — current stub (SPEC only, currently NOT
  checked by CI; you are completing it).

State-vector / symbol map you need:
- `Phi(x) := (1 + Real.erf(x/sqrt 2))/2`
- `d1 := ( ln(S/K) + (r−q+σ²/2)τ ) / (σ·sqrt τ)`
- `d2 := d1 − σ·sqrt τ`
- `bsCall := S e^{−qτ} Φ(d1) − K e^{−rτ} Φ(d2)`
- `bsPut := bsCall − S e^{−qτ} + K e^{−rτ}`

## Scope (numbered)
1. **Implement** a real-typed `def` for `d1`, `d2`, `Phi`, `phi`, `bsCall`,
   `bsPut` in `Lean/core/bsm_theorems.lean` (built on `Real`, `Real.sqrt`,
   `Real.log`, `Real.exp`, `Real.erf`).
2. **Prove T1** (`d1 − d2 = σ√τ`) with an automation (ring/simp/`linarith`)
   the checker accepts.
3. **Prove T2** (put-call parity) in the SAME file, from the same `def`s.
   NOTE the parity identity is **not** guaranteed by the algebra of `Phi`
   alone — it follows from `Φ(x) + Φ(−x) = 1` (the odd-symmetry identity),
   and a correct proof must cite that. A proof that merely *asserts* parity
   without the symmetry lemma is not mechanically complete.
4. **Add a `.github/workflows/lean.yml`** that installs Lean/mathlib, runs
   `lake build` on the `Lean/` tree, and uploads a fail artifact on a non-`
   clean exit. The grader reads the CI conclusion; a green `lake build`
   meeting a `lean`-backed `exp` is the PASS condition.
5. **Benchmarks ledger:** append a row to `benchmarks/LEDGER.md` for this
   PR (contributor, brief, PR link, verdict after CI), blank verdict until
   the harness grades it.

## Expected / anticipated
- A working lean build lane in CI and a merger-commit that compiles, with the
  parity proof genuinely associated to the parity theorem (not just stated).
- If mathlib-as-a-remote proves too slow to compile on the action budget,
  the brief must FAIL loudly with the exact failure (never an "assumed good").

## Done looks like (acceptance — machine-graded)
- `lean.yml` exists and necessarily exits non-zero on a broken proof; the
  graded run must pass the full Lean tree when rebased on `main`.
- `Lean/core/bsm_theorems.lean` compiles; T1 and T2 are the *verified* nodes
  (a `lean`-backed, `sorry`-free tree). A `sorry` anywhere in the parity /
  d1−d2 node is an automatic reject.
- No `.lean` change breaks the numeric oracle; `tests/test_bs.py` remains
  green (10/10).
- `benchmarks/LEDGER.md` row added, honest verdict.

## Explicitly out of scope
- **T3–T6.** This brief is the on-ramp. Do *not* attempt the PDE
  identity (T5) or the α-stable transport kernel (T6): those are later
  briefs with separate graders.
- No changes to `experiments/black_scholes.py` or its tests.
- No new third-party python deps.
- No re-scoping of `d1`/`d2` semantics.

## Sequencing
Independent brief; base `origin/main`. Later briefs that touch
`Lean/core/` must land after this is merged.
