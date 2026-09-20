# Ledger

Every PR landed against a brief gets a row here. The deliverable is the
verified theorem stack; this table is the record of how it was reached —
including the approaches that failed the grader.

Verdict discipline:
- Only CI-graded verdicts count. A row is `PENDING` until the harness says
  GREEN/RED. No human "looks good".
- A brief whose proof is asserted but not checker-backed (a stray `sorry`)
  is RED, by definition of the grader (see BRIEF_001).
- Separate *incident* (harness broke, runner lost) from *verdict* (the
  approach failed the grader). A RED verdict is a result, not a bug report.

| # | brief | contributor | PR | verdict |
|---|-------|-------------|----|---------|
| 1 | BRIEF_001 (T1+T2, Lean lane) | arena-ai-coding-agent | [#1](https://github.com/sblaplace/improved_black_scholes/pull/1) | **GREEN** @ `638c66e`, run 35509578689 — `lake build` + `#print axioms` audit + `lint` + `oracle` all pass. Reached on the 8th run; see the CI history. |
| 2 | BRIEF_002 (oracle ↔ Lean cross-verifier) | arena-ai-coding-agent | [#3](https://github.com/sblaplace/improved_black_scholes/pull/3) | **GREEN** @ `2a7bacb`, run 35517328856 — 39-point golden grid, docs/04 guard (3) active: `ImprovedBS/Crosscheck.lean` (#eval) cross-verified against `experiments/black_scholes.py` with max price diff 1.6e-14 (tol 1e-12) and 4/4 mutants caught. |
| 3 | BRIEF_003 (T3 delta identity + T4 bounds) | arena-ai-coding-agent | [#2](https://github.com/sblaplace/improved_black_scholes/pull/2) | **GREEN** @ `726325d`, run 35514867674 (first green: run 35514609619 @ `2273461`) — `lake build` + `#print axioms` audit + `lint` + `oracle` all pass; ratchet 3 → 0. Reached on the 1st run; see the CI history and correction C4. |
| — | *(tooling, no brief)* statement pins + the lint's own falsifiers | arena-ai-coding-agent | [#4](https://github.com/sblaplace/improved_black_scholes/pull/4) | **GREEN** @ `341b9f4`, run 35520713909 — `lake build` + `#print axioms` audit + **Statement pins (elab)** + `lint` + `oracle` all pass. Three-run arc, which is the informative part: run 35519747870 red on an empty `elab` block (by design — a pin that was never produced is not a passing pin) → run 35520154876 red on a parser format bug (`#print axioms` quotes the constant, `#check` does not; the parser refused to half-pin and printed the block instead) → block committed verbatim → run 35520713909 green, the 31 elaborated pairs reproducing identically across two independent checkouts, which is what makes them a pin rather than a transcription. Locally: `test_lint.py` 7/7 (22 cheats killed by named checks, 5 controls green, 1 residual gap asserted open), `test_pins.py` 8/8, `lean_lint` OK (43 decls, 31 pins + 31 elab, cross-layer skew clean), oracle 13/13, mutants 4/4, crosscheck 4/4. No `.lean` file changed; sorry baseline untouched. |
| 4 | BRIEF_004 (α-stable moment obstruction) | — | — | OPEN — not started, independent of #1–#3 |

## Corrections and co-recorded changes to the ask

Briefs are committed in-repo up front, so a correction is recorded here rather
than edited silently into the original text.

### C1 — BRIEF_001, corrected before any PR existed

**Date:** 2026-09-20. **Trigger:** an audit of the tree, not a contributor's
PR. Full detail is in the correction record at the top of
`briefs/BRIEF_001_parity_and_lean_lane.md`.

Four defects made the brief as issued either unachievable or — worse —
*achievable without meaning anything*:

1. **T1 and T2 were tautologies.** `d2 := d1 − σ√τ` and
   `bsPut := bsCall − S e^{−qτ} + K e^{−rτ}` made both theorems true by
   construction (`unfold; ring`). T2 in particular never touched
   `Φ(x) + Φ(−x) = 1`, which the brief's own scope item 3 required be cited. A
   contributor could have shipped a green build certifying nothing and been
   graded GREEN. The same circularity was mirrored in the oracle: the put was
   *computed* via parity, so `test_put_call_parity` could not fail. Demonstrated
   by mutation: a Φ perturbed to lose odd symmetry passed that test.
2. **`t3_delta_identity` was false as stated** — missing `σ ≠ 0` and `0 < τ`.
   At σ = 0, Lean's `a / 0 = 0` collapses it to `S e^{−qτ} φ(0) = K e^{−rτ} φ(0)`;
   S=2, K=1, r=q=0 gives 0.797885 ≠ 0.398942. A contributor would have hit a
   red build caused by the statement and spent their budget on the wrong problem.
3. **The Lean lane could not start.** Invalid `lakefile.toml` (mathlib
   requirement commented out; `[lake] binary` / `precompiled` are not Lake
   keys), no `lean-toolchain`, no `lake-manifest.json`, no root module, no
   `lean.yml`. `Lean/core/bsm_theorems.lean` also made the module
   `Lean.core.*`, squatting the elaborator's namespace.
4. **The acceptance bar was unenforceable in the named venue.** The brief
   budgeted ≤60 minutes of sandbox compute against a bar of "`lake build`
   green". Sandboxes without a route to `elan.lean-lang.org` and the Mathlib
   olean cache cannot install a toolchain at any budget.

**Changes landed with this correction:**

- `d2`, `bsPut` given independent explicit closed forms in both trees; values
  unchanged to 3.6e-15 across a 6-point grid, so the frozen numeric contract
  holds. Oracle tests 10 → 13.
- `tests/test_mutants.py` added: 11 seeded bugs, each required to be killed by
  its targeted test, including two *vacuity canaries* (M7 breaks Φ's odd
  symmetry, M8a/M8b corrupt the independent `d2`). Baseline before the fix: M7
  and M8 survived their targeted tests.
- `test_pde_residual_refines_with_h` (`r2 <= r1 + 1e-4`, satisfiable even when
  the residual got worse) replaced by `test_pde_residual_is_second_order`,
  asserting the measured O(h²) shrink inside a documented h-window. Measured:
  100× per decade from h=1e-2 to 1e-3, then divergence below 1e-3 as round-off
  dominates — the window is a fact about finite differences, recorded in
  `experiments/black_scholes.py` so nobody "improves" the test by shrinking h.
- Lean tree moved to `ImprovedBS/`; pinned to mathlib v4.34.0 /
  Lean v4.34.0 across `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`.
- `.github/workflows/lean.yml` added: a toolchain-free `lint` job and a
  `build` job (`leanprover/lean-action@v1`) that tees `lake build` to an
  artifact and audits `#print axioms` for `sorryAx`.
- `scripts/lean_lint.py` added. No toolchain required. Enforces: no `sorry` in
  the protected T1/T2 node; a ratchet on total deferred markers; no new axioms;
  every stack theorem still declared; and the independence guard (`d2` not from
  `d1`, `bsPut` not from `bsCall`, T2 citing `Phi_add_Phi_neg`). Verified to
  catch all 8 seeded regressions of those properties.
- T3 hypotheses corrected; T4 stated for the first time (it had no Lean
  declaration despite being listed "stated" in two tables); T5's proof route
  recorded (via T3, in `x = log S` coordinates); T6 restated around the
  tempered-stable repair.
- `docs/01` §2a, §4, §5 and `docs/04` rewritten to state the independence rule
  and the domain hypotheses; `docs/02` and `docs/03` repaired (duplicate `## 4.`
  heading, a D4 with no D3, and several unparseable sentences); `docs/03` §D1
  rewritten around the exponential-moment obstruction, which is now BRIEF_004.
- BRIEF_002, BRIEF_003, BRIEF_004 authored.

**Honest status of what landed:** the Lean definitions, the `Phi_add_Phi_neg`,
T1, T2 and T2′ proof scripts, and all Lean-side scaffolding were written and
reviewed by hand in an environment with **no Lean toolchain and no route to
install one**. They have never been compiled. They are best-effort, not
verified, and row 1 is PENDING precisely because of that. The Python half —
oracle, tests, mutation harness, lint — has been executed and is green.

### C2 — `docs/04` status table, corrected

The table previously read "T1 done, T2+T3 done in-code" in one cell while the
adjacent rows and the `.lean` file both said `stated` / `sorry`. Nothing was
done. Status in that table is now derived from `scripts/lean_lint.py` output
rather than typed, so the two cannot disagree.

## CI history for row 1 (PR #1)

Recorded because a verdict without its history is not reproducible, and because
the failures produced findings that changed the plan and two brief budgets.
Eight runs, one of which was an *incident* rather than a verdict.

| # | head | `lake build` | cause |
|---|---|---|---|
| 1 | `fbbc6d8` | fail 3m49s | `ImprovedBS.lean:21:0: invalid 'import' command` — a module doc-comment is a *command*, so placing it above the `import` makes the import illegal |
| 2 | `e806581` | fail 3m38s | same |
| 3 | `07f5aa8` | fail | `bad import 'Mathlib.Analysis.SpecialFunctions.Erf'`, `bad import 'Mathlib.Data.Real.Pi'` — neither path exists in v4.34.0, and `Real.erf` does not exist at all (correction C3) |
| 4 | `b1084d3` | fail | six × `failed to compile definition, consider marking it as 'noncomputable'`; `integral_comp_neg` applied to explicit args it takes implicitly; T1's `simp` left the fractions uncombined and used `eq_div_iff_mul_eq` where the division is on the left; T2's `linarith` on a goal containing a *product* of atoms |
| 5 | `a47b029` | **INCIDENT** | runner died: `System.IO.IOException: No space left on device`. No verdict — nothing after the cache step ran, including the log publisher |
| 6 | `9d6dd16` | fail | one error: `sub_div` in v4.34.0 is `(a - b) / c = a / c - b / c`, i.e. it *splits* a fraction; combining two fractions needs `← sub_div` |
| 7 | `b96d61a` | **build GREEN**, audit fail | `#print axioms ImprovedBS.t1_d1_minus_d2` — module name is not namespace; with no `namespace` command the theorems were in the root namespace |
| 8 | `638c66e` | **GREEN** 5m32s | all steps pass |

What the runs established, beyond the verdict:

- **The scaffolding was correct from run 1.** `Set up Lean + Mathlib cache`
  succeeded every time: elan installed, the v4.34.0 olean cache fetched, and
  `lakefile.toml` / `lean-toolchain` / `lake-manifest.json` resolved and agreed.
  A build is ~5m30s end to end, not the hours a from-source mathlib build would
  take. So correction C1 item 3 is genuinely fixed.
- **`Real.erf` is not in mathlib v4.34.0** (correction C3). Run 3 forced this
  out and it re-budgets T4 and T5.
- **Two reporting gaps hid real results, and both are now closed.** Run 5 died of
  ENOSPC before any step could report, so the failure was invisible except in a
  check-run annotation. Run 7 had a *green build and a red audit*, and the
  publisher shipped only `lake-build.log`, so the PR comment showed three
  expected `sorry` warnings and nothing else — which reads like success. The job
  now measures disk before spending it, and publishes every log it produces.

  Generalizable: a CI lane that cannot report its own failure is worse than no
  lane, because it produces a red X with no diagnosis and invites a contributor
  to guess. Reporting is part of the grader, not a convenience.

### Machine-checked as of run 8

`lake build` green **and** the `#print axioms` audit green, which is the
distinction this repository cares about — a `sorry` still builds, it just
elaborates to `sorryAx`. Verified free of `sorryAx`:

    BSM.exp_neg_sq_even   BSM.erf_neg   BSM.Phi_add_Phi_neg   BSM.Phi_neg
    BSM.t1_d1_minus_d2    BSM.t2_put_call_parity   BSM.t2_put_call_parity_spread

So T1 and T2 — and the odd-symmetry identity T2 actually rests on — are
machine-checked results, not prose. At that point `BSM.t3_delta_identity`,
`BSM.t4_call_bounds`, `BSM.t4_put_bounds` were still deferred and ratcheted at
3 markers; they landed in PR #2 (row 3, below).

### C3 — `docs/04` claimed a mathlib dependency that does not exist

`docs/04_formal_plan.md` listed "`Real.erf` (already in Mathlib:
`Mathlib.Analysis.SpecialFunctions.Erf`)" and "`Real.hasDerivAt_erf`" as
available dependencies. **Neither exists in v4.34.0.** Verified against the
release tag: no file named `Erf.lean` among the tree's 9112 `.lean` files, and
GitHub code search over `leanprover-community/mathlib4` returns 0 hits for
`Real.erf`, `def erf` and `erf_neg` — against 107 for `Real.sqrt` and 57 for
`Real.pi`, so the search itself was working.

`ImprovedBS/Core.lean` now defines `erf` itself as
`(2 / Real.sqrt Real.pi) * ∫ t in 0..x, Real.exp (-(t^2))` and proves `erf_neg`
by substitution in the interval integral. That supplies exactly the *oddness*
T2 needs.

It does **not** supply what T4 and T5 need, and this changes their budgets:
bounds `0 ≤ Phi ≤ 1` require `|erf x| ≤ 1`, hence the *value* of the Gaussian
integral `∫ x:ℝ, exp (-(x^2)) = sqrt pi` — measure theory
(`Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`), not
interval integrals. T5 likewise needs `HasDerivAt erf`, now derived rather than
imported. Both briefs should be re-budgeted before being handed out; BRIEF_003
already carries the warning in T4's doc-comment.

*(Outcome, PR #2: half right. The Gaussian integral's value was needed and it
was measure theory — but it entered through `Φ(x) = ∫_{(−∞,x]} φ`, not through
`|erf x| ≤ 1`, and the bounds `0 ≤ Φ ≤ 1` were the cheap part. The expensive
part was the T4 *lower* bound, whose recorded route was wrong. See C4.)*

**Generalizable lesson, and the reason this is in the ledger rather than a
commit message:** a mathlib dependency is a claim about a *specific version* and
must be checked against that version. Two plausible-looking import paths,
guessed without a toolchain, cost three red runs. Any brief that adds a mathlib
dependency should require the author to verify the path against the pinned tag —
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.34.0` is
reachable even where the Lean toolchain is not.

## CI history for row 3 (PR #2)

Two runs, both green. Recorded anyway, because the *reason* it was one run
rather than eight is the transferable part.

| # | head | `lake build` | notes |
|---|---|---|---|
| 1 | `2273461` | **GREEN** 3m54s | T3 + T4 + 18 helper lemmas, first push |
| 2 | `726325d` | **GREEN** 3m10s | workflow-only change: post the `#print axioms` output as a PR comment on success, so the audit is quotable without artifact access |

What made the difference from PR #1's eight runs: **every mathlib name was
checked against the pinned tag before pushing**, via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.34.0`, and
that check caught one real error at the desk — `map_add_right_eq_self` is in
namespace `MeasureTheory`, not `MeasureTheory.Measure` (its source file `open`s
`MeasureTheory.Measure`, which is why the sibling `map_neg_eq_self` *looks*
namespaced in mathlib's own proofs). Three stylistic rules also paid for
themselves: fully qualified names and no `open`, so nothing resolves by
accident; `mul_comm`/`mul_assoc` always with explicit arguments, because bare
`mul_comm` will happily rewrite the `2 * π` inside `√(2π)`; and no `field_simp`,
whose closes-or-doesn't behaviour cannot be predicted without a toolchain.

### Machine-checked as of run 35514867674

Quoted from the audit comment the workflow now posts on PR #2 — all 25
declarations in the T1–T4 node depend on exactly
`[propext, Classical.choice, Quot.sound]` and nothing else:

    BSM.exp_neg_sq_even   BSM.erf_neg   BSM.Phi_add_Phi_neg   BSM.Phi_neg
    BSM.t1_d1_minus_d2    BSM.t2_put_call_parity   BSM.t2_put_call_parity_spread
    BSM.phi_neg   BSM.phi_nonneg   BSM.phi_integrable   BSM.phi_add
    BSM.integral_phi_Iic_zero   BSM.Phi_eq_integral_Iic   BSM.Phi_nonneg   BSM.Phi_le_one
    BSM.integral_comp_add_right_Iic   BSM.Phi_le_exp_mul_Phi_add
    BSM.d1_exponent   BSM.d2_exponent   BSM.forward_eq
    BSM.bsCall_nonneg   BSM.bsPut_nonneg
    BSM.t3_delta_identity   BSM.t4_call_bounds   BSM.t4_put_bounds

`.github/lean_lint_baseline.json` now reads `"deferred": {}`. The lint's
`PROTECTED` set covers all of the above, so none of them can go back to `sorry`
without an automatic reject; `REQUIRED` covers them so none can be deleted.

### C4 — BRIEF_003's T4 route was wrong, and its budget was inverted

**Date:** 2026-09-20. **Trigger:** analysis before writing any Lean, confirmed
by the proof that landed. Full detail in the correction record at the top of
`briefs/BRIEF_003_t3_t4_bounds.md` and in the T4 doc-comment in
`ImprovedBS/Core.lean`.

The brief (and the T4 doc-comment it pointed to) said the lower bound
`max(F − D, 0) ≤ bsCall` follows from `0 ≤ Φ ≤ 1` plus monotonicity of `Φ` and
`d2 ≤ d1`. It does not. Monotonicity gives `bsCall ≥ (F − D)·Φ(d1)`, and since
`0 ≤ Φ(d1) ≤ 1` that is *weaker* than both `bsCall ≥ 0` and `bsCall ≥ F − D`
in the regime where each is the binding one. Concretely, S=100, K=120, τ=1,
r=q=0, σ=0.2: `bsCall ≈ 2.15` and `(F − D)·Φ(d1) ≈ −4.17`. A contributor
following the brief would have proved `Phi_monotone` (real work — it needs
`Φ′ = φ` or the integral representation) and then found that `linarith` cannot
close T4 from it, with no explanation in the tree of why.

What the lower bound actually is: the BSM price is the discounted expectation
of a non-negative payoff, so `bsCall ≥ 0`, `bsPut ≥ 0`, and parity turns the
second into `bsCall ≥ F − D`. That is a statement about `Φ` as an *integral*,
and it landed as one inequality, `Phi_le_exp_mul_Phi_add`:
`Φ(x) ≤ e^{a x + a²/2} Φ(x + a)` for `a ≥ 0`, which is the pointwise identity
`e^{a u + a²/2} φ(u + a) = φ(u)` (complete the square) integrated over
`(−∞, x]`. At `x = d2`, `a = σ√τ` it reads `D·Φ(d2) ≤ F·Φ(d1)`; at `x = −d1`
it reads `F·Φ(−d1) ≤ D·Φ(−d2)`. The same pointwise identity, un-integrated, *is*
T3. So the budget line was backwards: T3 is an eight-line corollary of the
tilting identity, and T4 is where the analysis lives — sixteen infrastructure
lemmas plus the two positivity lemmas, ~200 lines with their doc-comments,
including a translation-invariance lemma for half-line integrals
(`integral_comp_add_right_Iic`) that mathlib v4.34.0 has only in reflection form.

**Generalizable:** a recorded proof route is a claim and should be checked the
way a statement is — by trying to break it on a numeric example *before*
formalising. Ten seconds with the oracle (`bsCall(100,120,1,0,0,0.2)` against
`(F − D)·Φ(d1)`) falsified the route; the brief's author had checked the
*statement* numerically (`test_value_bounds`) but not the *route*. The T4
doc-comment now records the failed route and the counterexample next to the
proof, so the next reader does not have to rediscover it.

### C5 — BRIEF_002: Oracle ↔ Lean pointwise cross-verifier (guard 3)

**Date:** 2026-09-20. **Landed:** PR #3, run 35517328856.

**Summary:**
Stands up guard (3) from `docs/04` §"Oracle ↔ formal correspondence":
- **Golden grid:** `tests/golden_grid.json` commits 39 parameter points covering
  moneyness $S/K \in \{0.5, 0.8, 1.0, 1.2, 2.0\}$, tenors $\tau \in \{1/12, 0.25, 1.0, 3.0\}$,
  vols $\sigma \in \{0.05, 0.2, 0.6\}$, non-zero dividend yield $q$, and negative rates $r$.
  Inputs only are committed; single source of truth managed via `scripts/gen_grid.py`.
- **Lean side:** `ImprovedBS/Crosscheck.lean` implements independent closed forms in IEEE-754
  double precision (`Float`) and evaluates them via `#eval runCrosscheck`, emitting greppable
  `CK` records with high-precision Cody (1969) rational Chebyshev approximation for `erf`
  (accuracy $\sim 1.1\times 10^{-16}$).
- **Oracle side:** `tests/test_crosscheck.py` cross-verifies all six quantities
  ($d_1, d_2$, call, put, parity, delta identity) against `experiments/black_scholes.py`.
- **Tolerance:** Double precision matches across all 39 points with worst-case differences:
  $\Delta d_1, \Delta d_2 \le 1.1\times 10^{-16}$, $\Delta \text{call}, \Delta \text{put} \le 1.6\times 10^{-14}$.
  Committed tolerances set to $10^{-12}$ (safety factor $> 50\times$).
- **Anti-vacuity & non-tautology:** 4/4 mutation tests in `test_crosscheck.py` prove that
  deliberately perturbing $d_2$ (e.g. flipping $-\sigma^2/2$ to $+\sigma^2/2$), call, put,
  or parity immediately fails CI with the exact diverging points named. Structural guards
  in `scripts/lean_lint.py` enforce derivation independence and grid synchronization.
- **CI integration:** Wired into `.github/workflows/lean.yml` (`lake env lean ... | python3 tests/test_crosscheck.py`)
  and `.github/workflows/oracle.yml`. Failure logs and divergence reports are automatically
  published back to the PR if triggered.

### C6 — statement pins and the lint's own mutation harness

**Date:** 2026-09-20. **Trigger:** an audit of the *grading lane* — the question
asked was whether the toolchain-free Python had become an unverified pillar under
the Lean assumptions. Four findings, only one of which was about the oracle.

1. **No theorem depends on the Python, and that was worth checking rather than
   asserting.** `ImprovedBS/Core.lean` imports no numeric value, declares no
   `axiom`, and its 25 protected declarations are all `∀ S K tau r q sigma`
   proved from mathlib; deleting `experiments/` and `tests/` leaves T1–T4
   theorems of mathlib. The oracle is load-bearing in a different way: emptying
   those directories turns `scripts/lean_lint.py` red, so the *gate* needs the
   Python even though the *proofs* do not.
   Notably, the thing a numeric oracle would otherwise be trusted to supply —
   that `Φ` is normalized to integrate to 1 — stopped being a Python assumption
   when BRIEF_003 landed: `integral_phi_Iic_zero` derives it from
   `integral_gaussian_Ioi`, and halving `erf`'s `2/√π` prefactor now fails the
   build instead of failing a comparison.
2. **The linter was the unverified pillar.** `lean_lint.py` decides whether the
   tree is honestly labelled and gates `lake build` via `needs:`, and nothing
   tested it. `tests/test_lint.py` now does, with the repo's own discipline
   (21 seeded cheats, each required to be killed by a named check; 5 legitimate
   edits required to stay green; a baseline guard so "all mutants killed" cannot
   be satisfied by an always-red lint).
3. **The vacuity hole the repo's rule had not been applied to.** Replacing a
   landed theorem's statement with `: True := trivial` was, before this change,
   invisible to every lane: it builds, shows no `sorryAx`, keeps its name, and
   the oracle suite stays 13/13. Conversely the parity guard was *too* strict —
   reproving T2 with `simp only [bsPut, bsCall, Phi, erf_neg]`, i.e. odd
   symmetry one step closer to its source, was a lint failure. Both directions
   are now pinned: `[PINS]` (source text, everywhere) + the CI `elab` layer
   (elaborated types), and `ODD_SYMMETRY_WITNESSES` accepting any real witness of
   the symmetry. `tests/test_mutants.py`'s positive-anchor trick was also missing
   from `[ORACLE SYNC]`, whose checks were all prohibitions — a hollowed-out
   oracle satisfied it. `ORACLE_ANCHORS` fixes that, and the mutant
   "M-oracle-3" proves the fix does the work.
4. **Two defects found in the BRIEF_002 lane, deliberately not fixed here** (they
   belong to guard (3), not to this change; recorded so they are not lost):
   `ImprovedBS/Crosscheck.lean` defines `deltaIdentityRhs` and never prints it,
   so the cross-verifier compares *LHS to LHS* and never checks T3's equation
   across trees, while its module header claims both sides do; and
   `tests/test_crosscheck.py --run-lean` is unreachable whenever stdin is not a
   tty (`not sys.stdin.isatty()` claims the input first), so it prints
   `4/4 crosscheck unit test(s) passed` without cross-verifying anything —
   reproducible with `echo -n | python3 tests/test_crosscheck.py --run-lean`.
   The deeper point about that lane, for a future brief: `Crosscheck.lean`
   imports *nothing*, so guard (3) cross-checks the oracle against a hand-written
   `Float` twin rather than against `BSM.*`, and the twin↔formal link is carried
   by prose and by `[CROSSCHECK SYNC]`'s regexes. The chain
   "published textbook values ≡ oracle ≡ Lean" is therefore only as strong as a
   human reading that the twin matches the tree. A `BSM.*`-anchored version of
   that guard (validated bounds on the real definitions via `norm_num`/`interval`
   arithmetic, at a few grid points) is the fix, and it would retire the twin.

5. **The bootstrap and the skew.** `elab` can only be produced by `lake env lean`,
   so the artifact ships with an empty block and the build job prints the block to
   commit — a red first run, by design, because a pin that was never produced is not
   a passing pin. That red found a real bug: `#print axioms` quotes the constant name
   (`'BSM.Phi' depends on axioms: [...]`) where `#check` does not (`BSM.Phi : ℝ → ℝ`),
   and the parser had assumed symmetry between two commands that share no format. The
   parser refused to pin a half-result (type recovered, axioms empty), which is the
   behaviour that made this a fixable log line rather than a corrupt artifact. It is
   now a pure function tested against recorded CI output in `tests/test_pins.py`, so
   the assumption is exercised where it can be iterated on. Committing a real `elab`
   block then enabled a check the empty artifact could not have: `cross_layer_check()`
   compares which spec constants the pinned *statement* mentions against which the
   pinned *type* mentions, catching the stale combination (`--write` preserves `elab`,
   so a toolchain-less author can produce it by accident). The mutant that used to be
   the harness's declared local gap is now killed by it, and the gap entry was
   replaced by the deliberate self-consistent forgery — hollow the claim, re-run
   `--write`, hand-edit `elab` — which no local lane can see and CI sees instantly,
   because CI re-elaborates rather than re-reading. Attribution was checked, not
   assumed: disabling only `cross_layer_check()` leaves exactly one survivor out of
   22 mutants; deleting the whole `[PINS]` block leaves eight.

**Generalizable:** a graded tree needs its *grader* graded. Every lane here had a
falsifier except the one whose verdicts the others were written to satisfy, and
the class of cheat that slips through a name-and-marker check — keep the name,
keep the absence of `sorry`, change what is claimed — is exactly the class that
cannot be caught syntactically, which is why the answer is a pinned artifact plus
an elaboration diff, not a stricter regex.
