# BRIEF_001 — Put–call parity (T1 + T2) and the Lean grading lane

- **Status:** CORRECTED AND PARTIALLY LANDED — see the correction record below.
  The remaining ask is verification, not authorship.
- **Prerequisite PRs:** none (this is the bootstrap brief; base on current `main`)
- **Skills:** Lean 4 + mathlib basics; this brief is the on-ramp
- **Budget:** see "Budget and what is locally checkable" — the original figure
  was wrong and is the reason this brief was corrected.

---

## Correction record

Recorded here and in `benchmarks/LEDGER.md` rather than silently rewritten, per
the ledger's archival rule. The brief as first issued asked a contributor to
write definitions, prove T1 and T2, and add a Lean CI lane. Three defects in
the repository made that ask unachievable as written, and one made it
*worthless if achieved*:

1. **The two theorems were tautologies.** `Lean/core/bsm_theorems.lean` defined
   `d2 := d1 − σ√τ` and `bsPut := bsCall − S e^{−qτ} + K e^{−rτ}`. Both T1 and
   T2 then reduce to `unfold <def>; ring`. In particular T2 never touches
   `Φ(x) + Φ(−x) = 1`, which scope item 3 of this same brief required be cited.
   A contributor could have produced a green `lake build` that certified
   nothing, and been graded GREEN. **Fixed:** `d2` and `bsPut` now have their
   own explicit closed forms, in `ImprovedBS/Core.lean` and in the oracle.
2. **The acceptance bar was unenforceable in the venue named.** The brief
   budgeted "≤ 60 wall-clock minutes of E2B compute" against a bar of
   "`lake build` green". In a sandbox with no route to `elan.lean-lang.org` or
   to the Mathlib olean cache, no Lean toolchain can be installed at all, so
   the bar cannot be met locally at any budget. **Fixed:** the brief now splits
   its acceptance criteria into locally-checkable and CI-only, and the CI-only
   half runs on a GitHub-hosted runner where the cache works.
3. **The Lean lane did not exist and could not have started.** `lakefile.toml`
   was not valid Lake configuration (mathlib requirement commented out;
   `[lake] binary` and `precompiled` are not real keys), there was no
   `lean-toolchain`, no `lake-manifest.json`, no root module, and no
   `lean.yml`. `Lean/core/bsm_theorems.lean` also made the module
   `Lean.core.bsm_theorems`, squatting the elaborator's own namespace.
   **Fixed:** valid `lakefile.toml`, toolchain and manifest pinned to mathlib
   v4.34.0, module moved to `ImprovedBS/Core.lean`, `lean.yml` added.
4. **`t3_delta_identity` was false as stated** (not in this brief's scope, but
   found while auditing it): it lacked `σ ≠ 0` and `0 < τ`, and at σ = 0 Lean's
   `a / 0 = 0` collapses it to `S e^{−qτ} φ(0) = K e^{−rτ} φ(0)`, false for
   S = 2, K = 1. **Fixed:** hypotheses added, proof route recorded in the file.

What has *not* been done: **nothing in the Lean tree has ever been compiled.**
The definitions and the T1/T2 proofs were written and reviewed by hand in an
environment with no toolchain. They are best-effort, not verified.

---

## Goal

Make the machine-grading pipeline actually run, and turn T1/T2 from
hand-reviewed tactic scripts into machine-checked theorems. Concretely: get
`.github/workflows/lean.yml` green on a GitHub-hosted runner, with
`ImprovedBS/Core.lean` compiling and the parity proof genuinely resting on the
odd-symmetry identity. **No prose-assumed proof is acceptable** — the
deliverable is measured by the machine.

The two identities, against the independent definitions now in the tree:

1. **T1**: `d1(S,K,τ,r,q,σ) − d2(S,K,τ,r,q,σ) = σ·√τ`, where `d2` is written
   out as `(ln(S/K) + (r−q−σ²/2)τ)/(σ√τ)` and *not* as `d1 − σ√τ`.
2. **T2**: put-call parity — for the SAME BSM closed forms, with the put
   written as `K e^{−rτ} Φ(−d2) − S e^{−qτ} Φ(−d1)` and *not* in terms of the
   call:  `bsPut = bsCall − S e^{−qτ} + K e^{−rτ}`.

Do NOT change any parameter meanings, definitions, or the numeric contract in
`experiments/`. Grep `bs_price`, `_d1d2`, `bs_pde_residual` to confirm the Lean
definitions use the same real-arithmetic meanings as the oracle. Note that the
public `bs_price(S, K, T, t, r, s, q)` puts `s` before `q` while the Lean
declarations and the oracle's internal helpers use `(S K tau r q sigma)`; that
boundary is pinned by `tests/test_bs.py::test_public_api_argument_order`.

## Background (read in order)

- `docs/01_baseline.md` — the math and notation. **§2a is the reason this brief
  was corrected**: it states why `d2` and the put must be written out in full.
  §4 records the domain hypotheses and why σ = 0 is a counterexample, not a
  degenerate case.
- `docs/04_formal_plan.md` — the stack, the dependency spine, the mathlib
  dependencies actually needed, and what "verified" means in this repo.
- `experiments/black_scholes.py` — the numeric oracle. Its module docstring
  states the derivation-independence rule.
- `ImprovedBS/Core.lean` — the file you are finishing. Its header comment
  records the correction history.
- `scripts/lean_lint.py` — read the checks. It will reject the obvious ways to
  make CI green without doing the work.

Symbol map:

- `Phi(x) := (1 + Real.erf(x/sqrt 2))/2`
- `phi(x) := Real.exp (-(x^2)/2) / Real.sqrt (2 * Real.pi)`
- `d1 := ( ln(S/K) + (r−q+σ²/2)τ ) / (σ·sqrt τ)`
- `d2 := ( ln(S/K) + (r−q−σ²/2)τ ) / (σ·sqrt τ)`   ← independent
- `bsCall := S e^{−qτ} Φ(d1) − K e^{−rτ} Φ(d2)`
- `bsPut := K e^{−rτ} Φ(−d2) − S e^{−qτ} Φ(−d1)`   ← independent

## Scope (numbered)

1. **Make the `build` job of `.github/workflows/lean.yml` run.** First run will
   fetch the Mathlib cache for v4.34.0. If it fails, the failure is the
   deliverable: capture it, do not work around it by weakening the pin.
2. **Repair the tactic scripts until `lake build` is green.** `Phi_add_Phi_neg`,
   `t1_d1_minus_d2`, `t2_put_call_parity` and `t2_put_call_parity_spread` are
   hand-written and uncompiled. Expected failure modes, in order of likelihood:
   - `simp only [d1, d2, sub_div, key]` in T1 not rewriting as intended —
     the denominators must be *syntactically* equal after unfolding;
   - `nlinarith [hsq]` not finding the certificate for
     `σ²·τ = σ·√τ·(σ·√τ)` — `ring_nf` first, or supply
     `sq_nonneg sigma` as an extra hint;
   - `Phi_add_Phi_neg`'s `simp only [Phi, hneg, Real.erf_neg]` — if `simp`
     normalizes `-(x / Real.sqrt 2)` differently, use `Real.neg_div` explicitly
     or `rw [← neg_div]` before `Real.erf_neg`;
   - `linarith` in T2 needing the atoms spelled out — the goal is linear in
     `Phi (d1 …)`, `Phi (-(d1 …))`, `S * Real.exp (-q * tau)`,
     `K * Real.exp (-r * tau)`, so it should close; if it doesn't, `ring_nf`
     first.
   Changing a *proof* is in scope. Changing a *statement* or a *definition* is
   not — if a statement looks wrong, stop and file it, don't fix it silently.
3. **Confirm the `#print axioms` audit passes**: no `sorryAx` in any of
   `Phi_add_Phi_neg`, `Phi_neg`, `t1_d1_minus_d2`, `t2_put_call_parity`,
   `t2_put_call_parity_spread`. This is the step that distinguishes a proved
   theorem from a built one.
4. **Keep `scripts/lean_lint.py` green** without editing `PROTECTED`,
   `REQUIRED` or `.github/lean_lint_baseline.json`. The baseline must not move;
   T3/T4 stay deferred under BRIEF_003.
5. **Benchmarks ledger:** record the verdict for this PR in
   `benchmarks/LEDGER.md` from the CI conclusion. If the build is red, the row
   is RED with the exact error — a RED verdict is a result.

## Budget and what is locally checkable

| check | command | needs |
|---|---|---|
| oracle identities | `python3 tests/test_bs.py` (13/13) | python3 only |
| oracle is a falsifier | `python3 tests/test_mutants.py` (4/4, 11 mutants) | python3 only |
| Lean tree honest | `python3 scripts/lean_lint.py` | python3 only |
| toolchain pins agree | `lean.yml` → lint job | python3 only |
| **the proofs are correct** | `lake exe cache get && lake build` | **elan + network to the Lean CDN and Mathlib cache — CI only** |

Expect the first CI build to take 10–25 minutes (cache download dominates;
`ImprovedBS` itself is one small file). Subsequent runs are a few minutes.
There is no budget at which the last row is checkable in a sandbox without
outbound access to `elan.lean-lang.org` and Mathlib's cache host — if your
environment lacks it, do the first four rows, push, and read the CI log. That
is the intended workflow, not a failure of it.

## Expected / anticipated

- A green `lean.yml` on a GitHub-hosted runner, with the parity proof genuinely
  resting on `Phi_add_Phi_neg`, and an `#print axioms` audit showing no
  `sorryAx`.
- If the Mathlib cache proves too slow on the action budget, or the pin
  conflicts with the runner's toolchain, the brief must FAIL loudly with the
  exact failure — never an "assumed good". A toolchain/manifest mismatch
  presents as a timeout because Lake silently falls back to building mathlib
  from source; the lint job checks the three pins agree before the build job
  spends a runner on it.

## Done looks like (acceptance — machine-graded)

- `lean.yml` exists and necessarily exits non-zero on a broken proof; the graded
  run passes the full Lean tree when rebased on `main`.
- `ImprovedBS/Core.lean` compiles; `Phi_add_Phi_neg`, T1, T2 and T2′ are the
  *verified* nodes — `sorry`-free and `sorryAx`-free per `#print axioms`. A
  `sorry` anywhere in that node is an automatic reject, and
  `scripts/lean_lint.py` enforces it without needing a toolchain.
- No `.lean` change breaks the numeric oracle: `tests/test_bs.py` stays 13/13
  and `tests/test_mutants.py` stays 4/4.
- `benchmarks/LEDGER.md` row added, honest verdict.

## Explicitly out of scope

- **T3–T6.** This brief is the on-ramp. Do *not* attempt the delta identity
  (T3), the no-arb bounds (T4), the PDE identity (T5) or the tempered-stable
  kernel (T6): those are BRIEF_003 and later, with separate graders.
- No changes to `experiments/black_scholes.py` or its tests.
- No new third-party python deps.
- No re-scoping of `d1`/`d2` semantics, and no re-deriving `d2` from `d1` or
  `bsPut` from `bsCall` — `scripts/lean_lint.py` rejects both.
- No edits to `.github/lean_lint_baseline.json`, `PROTECTED`, or `REQUIRED`.

## Sequencing

Independent brief; base on `origin/main`. BRIEF_002 (oracle↔Lean cross-verifier)
and BRIEF_003 (T3 + T4) both touch `ImprovedBS/Core.lean` and must land after
this is merged and green.
