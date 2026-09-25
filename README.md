# Improved Black-Scholes

> The claim this repo commits to: Black-Scholes-Merton
> is a theorem about one specific stochastic process, and its famous
> failures are failures of that process's **increment law**, not of the
> arbitrage-free skeleton that makes a closed form exist. So "improving" BS
> means widening the class of increment laws that still admit a closed
> pricing kernel — and *proving* the widening preserves the skeleton. Every
> claim lands as a Lean 4 theorem that CI machine-checks, with a
> dependency-free numeric oracle as the sanity handrail.

## Thesis

Black-Scholes-Merton is not a "wrong formula." It is the *correct price for
one specific stochastic process* — geometric Brownian motion (GBM) under a
single constant-volatility factor — and its famous failures (1987 crash, 1998
LTCM/Russian default, 2008, the vol smile) are failures of that **process
assumption**, not of the PDE/martingale skeleton that makes a closed form
exist in the first place.

That split is the lever:

- The **skeleton** has two layers, and they do not survive equally. The
  *static* layer — parity, no-arbitrage bounds, price as a discounted
  expectation under a pricing measure — is model-free and survives any
  increment law with the drift condition (machine-checked in
  `ImprovedBS/Skeleton.lean`). The *dynamic* layer — a self-financing
  replicating portfolio, a *unique* martingale measure, the PDE as its
  consequence — is what makes BS a theorem about GBM specifically, and it
  does not survive jumps: outside the complete-market cases the martingale
  condition no longer selects a measure, and different admissible choices
  price the same call differently. So the widening's honest shape is
  *increment law + a named selection principle*, and the non-uniqueness
  itself is now machine-checked: `ImprovedBS/NonUniqueness.lean`'s
  `static_skeleton_does_not_select_measure` exhibits two equivalent
  martingale laws on three spots that satisfy the skeleton's parity and
  bounds verbatim and price the same call at `1/4` and `1/8`, and on the
  whole martingale segment the call is exactly `p₁/2` (docs/03 §D1 item 7;
  ledger C13, row 12). This split is the provable part.
- The **increment law** (lognormal, constant σ, single factor) is the fragile
  bit markets reject. Improving BS = widening the class of increment laws
  that still admit a *closed pricing kernel* — an explicit one-dimensional
  Fourier integral where no elementary closed form exists — and proving the
  widening preserves the static skeleton.

So the program in one line: **widen the increment law, and prove you did.**
The proof checker is the judge — a theorem is done when `lake build` is
green *and* `#print axioms` shows no `sorryAx`, not when prose says so.

## A rule the whole repo is built around: no vacuous claims

A green check is only evidence if it could have been red. This applies to the
tests as much as to the proofs, and the repo has been bitten by it once
already: defining `d2 := d1 − σ√τ` and `bsPut := bsCall − S e^{−qτ} + K e^{−rτ}`
makes the first two theorems true *by construction*. Both proofs collapse to
`ring`, the parity theorem never touches `Φ(x) + Φ(−x) = 1` — the only
identity it is actually about — and a green build certifies nothing.

So every identity is checked between **independently derived** expressions, in
both trees, and the property is enforced mechanically:

- `d2` and `bsPut` have their own explicit closed forms, in
  `experiments/black_scholes.py` and in `ImprovedBS/Core.lean`.
- `scripts/lean_lint.py` fails CI if `d2` is defined from `d1`, if `bsPut` is
  defined from `bsCall`, or if `t2_put_call_parity` stops citing
  `Phi_add_Phi_neg`. It needs no Lean toolchain to do this.
- `tests/test_mutants.py` seeds 20 bugs into the oracle and requires each to be
  killed by the test meant to kill it. Two of them exist purely to prove the
  parity and `d1 − d2` tests can fail.

A third lane closes a gap neither of those could see. `lake build` proves a proof is
*correct*; nothing proves a theorem is still *the theorem*. Restate a landed node as

    theorem t4_call_bounds (S K tau r q sigma : ℝ)
        (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) : True := trivial

and it builds, shows no `sorryAx` — because `True` really is provable, which is what
makes it a *sound* way to say nothing — keeps its name for the lint's `REQUIRED`
check, and leaves the oracle suite at 20/20, since the oracle has no idea what a
Lean statement is. So every declaration in the protected stack is pinned in
`tests/golden_statements.json`: a theorem by its **statement**, a definition by its
**body** (a definition *is* the specification). `scripts/pin_statements.py`
extracts and compares; `lean_lint.py` enforces it with no toolchain, and the build
job re-elaborates the pinned `#check` types and `#print axioms` output, which is
where a statement that *reads* the same but elaborates differently gets caught.
Weakening a claim is still allowed. It is now a diff a reviewer sees.

And because `lean_lint.py` has authority over how the Lean tree is labelled while
nothing had authority over *it*, `tests/test_lint.py` seeds 35 cheats into copies
of the tree and requires each to be killed by a *named* check, keeps 5 legitimate
edits green (a re-wrapped proof, marker words inside a comment, parity reproved
from `erf_neg` directly), and asserts — rather than folklore-claims — the boundary
it cannot cross: hollow a statement, regenerate the source pins, *and* hand-forge
the elaborated block to match, and every lane that can run without a toolchain is
satisfied by the self-consistency. That forgery is exactly what CI cannot survive,
because CI re-elaborates rather than re-reading: `#check @BSM.t4_call_bounds`
prints the bound, so a committed `: True` is a diff. The half of it that *was*
local — regenerating layer 1 and leaving layer 2 stale — is now caught by the
cross-layer skew check, and its mutant moved into the must-die list.
That is also why swapping the numeric oracle for another language would have bought
nothing here: the oracle is a probe, the linter was the pillar, and a pillar is
unverified in any language until something pushes on it.

## How the work is packaged

Every unit of work is a self-contained brief in `briefs/`: background
reading in order, a numbered scope, an explicit out-of-scope, and an
acceptance bar CI can check mechanically. Each brief lands as a PR; CI
grades it (`lake build` on the Lean tree + the oracle tests + the lint), and
the outcome is recorded in `benchmarks/LEDGER.md` — GREEN/RED/PENDING from the
harness, never a human "looks good", and a RED verdict on an approach is a
result, not an incident.

**A constraint worth stating plainly, because briefs are graded against it:**
a Lean deliverable can only be *built* where there is network access to the
Lean toolchain CDN and the Mathlib olean cache. A sandbox without that access
can still run the oracle, the mutation harness and the lint — all three are
pure Python — but it cannot substitute for the `lake build` lane. Briefs say
which of their acceptance criteria are locally checkable and which are
CI-only, so nobody spends a budget discovering this.

## Repository layout

```
ImprovedBS/         # Lean 4 library, `namespace BSM`: Core.lean (T1..T5), Levy.lean, Fourier.lean, RiskNeutral.lean, Inversion.lean (T6 sub-goals 1, 2, 3a, 3b), Skeleton.lean (model-free parity + bounds), Pricing.lean (T6 at any strip law: kernel on the pricing contour, strike transform, Fubini exchange, inversion, pricing identity), CGMY.lean (the concrete CGMY exponent, its Lévy measure, its moment strip), NonUniqueness.lean (two martingale laws, one skeleton, two prices — the static layer does not select the measure), Crosscheck.lean (#eval twin, guard 3)
ImprovedBS.lean     # library root module
lakefile.toml       # mathlib pinned by tag; leanOptions (autoImplicit off)
lean-toolchain      # pinned toolchain — must match lake-manifest.json
lake-manifest.json  # exact dependency revisions (reproducibility)
briefs/             # task briefs: self-contained work orders, one PR each
benchmarks/         # ledger: brief -> PR -> CI verdict
experiments/        # numeric oracle (stdlib-only) — the sanity handrail
tests/              # oracle tests + 2 mutation harnesses + the crosscheck lane + the pinned claims (json)
scripts/            # lean_lint.py, pin_statements.py, gen_grid.py: toolchain-free grading
docs/               # 01 baseline math, 02 failure modes, 03 research dirs, 04 formal plan
.github/workflows/  # CI: oracle lane + lean lane (lint job, then build job)
```

## The theorem stack, by threshold

Status is machine-derived: `python3 scripts/lean_lint.py` prints the live
count, and `.github/lean_lint_baseline.json` is the ceiling it ratchets
against.

| #  | Lean name | statement | difficulty | status |
|----|-----------|-----------|-----------|--------|
| —  | `Phi_add_Phi_neg` | `Φ(x) + Φ(−x) = 1` | trivial | **machine-checked** |
| T1 | `t1_d1_minus_d2` | `d1 − d2 = σ√τ` | easy | **machine-checked** |
| T2 | `t2_put_call_parity` | put-call parity | easy | **machine-checked** |
| T3 | `t3_delta_identity` | `S e^{−qτ} φ(d1) = K e^{−rτ} φ(d2)` | medium | **machine-checked** |
| T4 | `t4_call_bounds`, `t4_put_bounds` | no-arbitrage price bounds | medium | **machine-checked** |
| T5 | `t5_bsCall_pde`, `t5_delta`, `t5_gamma`, `t5_tau` | closed form solves the BSM PDE | heavy | **LANDED GREEN** (BRIEF_006) — run 35566569107; `benchmarks/LEDGER.md` row 6 |
| T6 | sub-goals 1, 2, 3(a), 3(b): `ImprovedBS/Levy.lean`, `ImprovedBS/Fourier.lean`, `ImprovedBS/RiskNeutral.lean`, `ImprovedBS/Inversion.lean` (`bsCall_eq_riskNeutral_expectation`, `bsCall_eq_lognormal_expectation`, `carrMadan_inversion_eq_bsCall`) | Fourier kernel survives a tempered-stable increment; closed form = discounted expectation = inverted Fourier integral | **LANDED** (3a BRIEF_007, 3b BRIEF_008) | restated, see docs/03 D1; (3a) **LANDED GREEN** (run 35574194681), (3b) landed (BRIEF_008) |
| — | `model_free_put_call_parity`, `model_free_call_bounds`, `model_free_put_bounds` (+ the GBM re-derivations `t2_spread_via_skeleton`, `t4_call_bounds_via_skeleton`) | parity and the no-arbitrage bounds lifted off the closed form onto `e^{−rτ}·E[(S_T−K)⁺]` — any terminal-spot law with the drift condition | model-free layer (BSM-2 kit item 5) | **LANDED GREEN** (BRIEF_009) — run 35589005865 |
| — | `cmPriceKernel`, `strikeTransform`, `fourierDampedModelFreeCall_eq`, `fourierCM_inversion`, `carrMadan_eq_modelFreeCall` (+ the GBM instance `gbm_carrMadan_eq_bsCall`) | T6's triangle at *any* strip law: the Carr–Madan kernel on the pricing contour `u − i(α+1)` (C12), the strike transform, the Fubini exchange, inversion, and the pricing identity landing on the model-free layer | model-free pricing layer (BSM-2 kit item 4, re-scoped) | **LANDED GREEN** (BRIEF_010) — run 35646623031 |
| — | `cgmyExponent`, `cgmyExponent_strip`, `cgmy_numeraire_strip`, `cgmy_contour_decay`, `cgmy_cmPriceKernel_integrable`, `cgmy_levy_sq_integrable` | the concrete CGMY exponent `Γ(−Y)[(M−iv)^Y − M^Y + (G+iv)^Y − G^Y]`, its tempered moment strip `(−G, M)`, the contour decay that discharges BRIEF_010's (H-decay), and `∫ (1 ∧ x²) ν < ∞` | BSM-2 kit items 1–2 | **LANDED GREEN** (BRIEF_011) — run 35779316727; corrections C14 (`α + 1 < M`, no `min (G, M)`) and C15 (continuity also needs `G > 0`, `α > 0`) |
| — | `static_skeleton_does_not_select_measure`, `witness_equivalent`, `martingale_set_param`, `martingale_set_call_eq` (+ `witnessMeasureA`/`witnessMeasureB`, the three-point law `trinomialMeasure`) | two equivalent probability laws on the spots `(1/2, 1, 2)` at `S = K = τ = 1`, `r = q = 0`, both with the drift, both satisfying BRIEF_009's parity and bounds *as instantiated*, pricing the call at `1/4` and `1/8`; the whole martingale set is the segment `(p₁, 1 − 3p₁/2, p₁/2)` and the call on it is exactly `p₁/2` | BSM-2 kit item 7: the static layer does not select the measure | **LANDED GREEN** (BRIEF_012) — run 36052072620; correction C16 (the brief's canary mean and its literal M18) |
| — | `esscher_cgmy_shift`, `esscher_tilt_factorization`, `cgmyCumulant_eq_strip`, `esscher_exists_unique_of_mem_range`, `esscher_no_solution_of_outside_range`, `esscher_theta_zero_unique`, `esscher_drift_factor`, `esscher_cmPriceKernel_integrable` (+ `esscherExponent`, `cgmyCumulant`, `esscherDriftMap`, `esscherThetaZero`, `esscherDriftBound`) | the Esscher shift keeps CGMY inside the family (`(G, M) ↦ (G+θ, M−θ)`), the cumulant `κ` is strictly convex on the strip (`κ″ = CΓ(2−Y)[(M−u)^{Y−2} + (G+u)^{Y−2}] > 0`), so the drift equation `κ(θ+1) − κ(θ) = r − q` has a unique `θ ∈ (−G, M−1)` exactly when `|r−q|` is below the edge-value bound `H = |CΓ(−Y)|·|(G+M)^Y − (G+M−1)^Y − 1|`, the tilted factor equals `e^{τ(r−q)}` at the solution, and the pricing kernel stays integrable on the shifted contour | BSM-2 kit item 3: the drift fixed at a named pricing measure | **LANDED GREEN** (BRIEF_013) — run 36072416203 |
| — | `cgmyCornerC`, `cornerForwardExponent`, `cgmyCornerGamma_eq`, `cgmyBracket_tendsto`, `cgmyCornerExponent_tendsto`, `cgmyCornerCumulant_one_tendsto`, `cornerForward_numeraire`, `cornerForwardExponent_tendsto`, `cornerForwardFactor_tendsto`, `cornerEsscherZero_mem`, `cornerEsscherZero_numeraire`, `cornerEsscherZero_tendsto`, `cornerEsscherBound_tendsto` | the normalized CGMY → GBM corner at the scale `C_Y = (σ²/2)(2−Y)`: the pole cancels (`ε Γ(−Y) = Γ(3−Y)/(Y(Y−1))`, from BRIEF_013's `cgmyGamma_two_sub_eq`), the exponent converges **pointwise** on `−M < Im v < G` to `−(σ²/2)v² + i(σ²/2)(G−M)v` as `Y → 2⁻` — one-sided, and never an equality at the pole, where `Real.Gamma (-2)` is *defined* as `0` — route A's algebraic forward normalization lands it on the risk-neutral GBM exponent and its factor on `gbmCharFactor` (with `Ψ_Y(−i) = r−q` exact at every `Y`, consuming `cgmyExponent_strip`), and route B's named `θ₀ = (M−G−1)/2` lands it on the zero-carry GBM exponent with no correction at all, by consuming `esscher_cgmy_shift` at the shifted rates | BSM-2 kit item 6: GBM comes back at the corner | **LANDED GREEN** (BRIEF_014) — run 36111570530; correction C17 (the pole, and the old bare `Y → 2` / `G,M → σ²/2` wording) |

T1–T4 are the warm-up tier, and all four are now machine-checked. T4 turned
out to be less routine than "algebra and monotonicity": its lower bound is the
positivity of the call and the put, which needs `Φ` as an *integral* of `φ`
(`Phi_eq_integral_Iic`), not just `0 ≤ Φ ≤ 1` — see ledger correction C4. T5 is
the first heavy node, and it was reached *through* T3 — the delta identity is
exactly the cancellation that makes the PDE residual vanish, so T5 is T3 plus
the chain rule plus `Φ′ = φ`, not an independent slog through `erf` derivatives.
The route is now checked rather than asserted: `[SPINE]` in `scripts/lean_lint.py`
fails if `t5_delta` stops consuming `t3_delta_identity`, and
`tests/test_lint.py` seeds the mutant that proves the check can fire. T6 is the
research claim; its mathematical content is the Carr–Madan / CGMY
Fourier-pricing machinery (1999–2002) restated as machine-checked theorems —
the deliverable is the formalization and its grading apparatus, not new
mathematics.

**T6 carries a warning that saves a brief.** A *pure* α-stable log-increment
has infinite first moment (`P(X > x) ~ x^{−α}` ⇒ `E[e^X] = ∞`), so
`S_T = S_0 e^{X_τ}` cannot be a martingale at all and the Fourier pricing
contour has no moment strip to sit in. The obstruction is at the moment step,
not the kernel step. The direction is viable only in **tempered** form
(CGMY / Boyarchenko–Levendorskii), where an `e^{−λ|x|}` damping of the Lévy
measure restores the exponential moment, keeps algebraic tails at option
tenors, and offers an α-stable (λ→0) corner and a **normalized** GBM
(`Y ↑ 2`, `C_Y = (σ²/2)(2−Y)`) corner. Holding `C` fixed at `Y = 2` would
hit a pole, not a Gaussian limit (BRIEF_014, ledger C17 — now a landed one-sided
theorem at the normalized scale). The **dynamic** half of the same warning is
issued as BRIEF_016: a pure exponential-Lévy smile decays like `τ^(−1)` (the
model's measured ATM-skew exponent is `1.0857` at the published Carr–Madan VG
test case, `0.9682` at a CGMY witness) while the market's published power-law
fits decay like `τ^(−0.36..−0.45)` (ledger C19, which corrects the reviewer's
`τ^(−1/2)`) — disjoint bands at the two witness sets, no universality claim over
the family. That claim's falsifier, and the oracle's one genuinely external
anchor, are now **landed as BRIEF_016** (`tests/test_bs.py::test_term_structure_anchor`:
the published Carr–Madan (1999) §5 Case-4 put prices reproduced to `≤ 3.6e−5`
by both parameterizations of the same variance-gamma law, that paper's own
failing VGPS row rejected as a free negative control, and the measured model
bands `[0.90, 1.15]` against the market's `(0.30, 0.50)`); the RED is in
`docs/02` §A1 and the correction in ledger C19.
**The law side is issued as BRIEF_017.** Every CGMY declaration the tree has is
about the characteristic *exponent*; the expectation-level twins of items 3 and
5 need an actual `Measure ℝ`, and the feasibility audit (mathlib at the pinned
tag has no Lévy–Khintchine, no infinite divisibility, no stable laws, no
Bochner — but it does ship the Gamma law, the Γ-integral identities, the
`mgf`/`complexMGF` layer and the Lévy-continuity/Prokhorov layer) decides the
route in two stages: **Stage 1** is the family's `Y = 0` member, the
variance-gamma law as the difference of two `gammaMeasure`s — the published law
of BRIEF_016's anchor — which lands the first non-Gaussian martingale law in
the tree; **Stage 2** is the general-`Y` law as the compound-Poisson truncation
limit. Two traps are named in the brief: `Real.Gamma 0 = 0` (and `Gamma (−1)`)
makes a raw evaluation at `Y = 0` or `Y = 1` *silently* the Dirac law, and the
landed Esscher range `H_Y` degenerates at the corner (`H_Y ~ C/Y → ∞`).
**Stage 1 is specified in BRIEF_018** (same PR): `ImprovedBS/VGLaw.lean` — the
law as the difference of two `gammaMeasure`s, its mgf on the strip `(−G, M)`
(consuming `integral_rpow_mul_exp_neg_mul_Ioi`), the corner as a `𝓝[>] 0`
limit, the law-level Esscher tilt, and the expectation-level twins of items 3
and 5 at the tilted law — with four `[VGLaw]` lint clauses (44 → 48 lint
mutants), the oracle's `gamma_mgf`/`vg_cumulant`/`vg_mgf`/`vg_drift_map`/
`vg_tilted_cumulant`/`vg_esscher_solve`, `test_vg_law` and mutants M30–M33;
pins 268 → 268 + 22, audit 237 → 237 + 22 (the landed count rules).
Proving the
obstruction itself — a concrete divergent integral, no finance in it — is the
cheapest high-value theorem in the research tier. Details in docs/03 §D1.

## Status

| Layer | what | status |
|---|---|---|
| Numeric oracle | independent `d1`/`d2`, independent call and put closed forms, PDE residual, delta identity, quadrature of the risk-neutral expectation, Carr–Madan Fourier inversion, model-free expectation route, Carr–Madan at any strip law, the CGMY exponent's contour and decay, the non-uniqueness witness in exact rationals, the Esscher drift map, its zero and its solvability bound, the normalized CGMY → GBM corner against an independently expanded polynomial, the **published Carr–Madan (1999) anchor** (both parameterizations of the same VG law) and the **term-structure falsifier** (measured ATM-skew exponents vs the cited market band) | verified — 23/23 tests |
| Oracle is a falsifier | mutation harness: 30 seeded bugs, each killed by its targeted test, incl. 2 vacuity canaries | verified — 4/4 harness tests |
| Failure modes + research dirs w/ falsifiers | docs/02, docs/03 | written |
| Lean definitions | `erf`, Φ, φ, d1, d2, bsCall, bsPut — independent, matching the oracle | machine-checked |
| Lean theorems | `Phi_add_Phi_neg`, T1, T2, T2′ | **GREEN** — `lake build` + `#print axioms` audit, run 35509578689 |
| Lean theorems | T3, T4, T4′ + the `Φ = ∫ φ` infrastructure (18 lemmas) | **GREEN** — `lake build` + `#print axioms` audit, run 35514867674 |
| Lean theorems | T6 sub-goal 1: the moment obstruction (`ImprovedBS/Levy.lean`, 7 declarations) | **GREEN** — `lake build` + `#print axioms` audit + statement pins, run 35523250105 |
| Lean theorems | T6 sub-goal 2: tempered-contour absolute convergence (`ImprovedBS/Fourier.lean`, 7 declarations) | **GREEN** — `lake build` + `#print axioms` audit + statement pins, run 35536031936 |
| Lean theorems | T5: the closed form solves the BSM PDE (`ImprovedBS/Core.lean`, 11 declarations) | **GREEN** — `lake build` + `#print axioms` audit + statement pins (elab, 60), run 35566569107 |
| Lean theorems | T6 sub-goal 3(a): the closed form is the discounted risk-neutral expectation, plus the `phi`/`Phi` ↔ mathlib-Gaussian bridge (`ImprovedBS/RiskNeutral.lean`, 21 declarations) | **GREEN** — `lake build` + `#print axioms` audit + statement pins (elab, 81), run 35574194681; `benchmarks/LEDGER.md` row 7 |
| Lean theorems | T6 sub-goal 3(b): Fourier inversion of the Carr–Madan pricing kernel onto the lognormal expectation, and real-valuedness (`ImprovedBS/Inversion.lean`, 13 declarations) | **GREEN** — `lake build` + `#print axioms` audit + statement pins (elab, 94), run 35578278238; `benchmarks/LEDGER.md` row 8 |
| Lean theorems | the model-free skeleton: put-call parity + no-arbitrage bounds at the expectation level, for any terminal-spot law with the drift condition (`ImprovedBS/Skeleton.lean`, 14 declarations) | **GREEN** — `lake build` + `#print axioms` audit + statement pins (elab, 108), run 35589005865; `benchmarks/LEDGER.md` row 9 |
| Lean theorems | T6's triangle at *any* strip law: the Carr–Madan kernel on the pricing contour `u − i(α+1)` (C12 corrected), the strike transform, the Fubini exchange, Fourier inversion in the tree's own normalization, and the pricing identity landing on the model-free layer — instantiated at GBM, the CGMY decay entering only as a recorded hypothesis (`ImprovedBS/Pricing.lean`, 31 declarations) | **GREEN** — `lake build` + `#print axioms` audit + statement pins (elab, 139), run 35646623031; `benchmarks/LEDGER.md` row 10 |
| Lean theorems | BSM-2 kit items 1–2: the concrete CGMY characteristic exponent `Γ(−Y)[(M−iv)^Y − M^Y + (G+iv)^Y − G^Y]`, its Lévy measure (`∫ (1 ∧ x²) ν < ∞`), its tempered moment strip `(−G, M)`, and the contour decay that discharges BRIEF_010 §5's (H-decay) at that exponent (`ImprovedBS/CGMY.lean`, 52 declarations) | **GREEN** — `lake build` + `#print axioms` audit (148 entries) + statement pins (elab, 165), run 35779316727; `benchmarks/LEDGER.md` row 11, corrections C14/C15 |
| Lean theorems | BSM-2 kit item 7: the static skeleton does not select the measure — two mutually absolutely continuous three-point martingale laws satisfying BRIEF_009's parity and bounds *by instantiation* and pricing the same call at `1/4` and `1/8`; the martingale set on those spots parametrized as a segment with the call exactly `p₁/2` on it (`ImprovedBS/NonUniqueness.lean`, 45 declarations) | **GREEN** — `lake build` (no warnings on the module) + `#print axioms` audit (186 entries) + statement pins (elab, 210), run 36052072620; `benchmarks/LEDGER.md` row 12, correction C16 |
| Lean theorems | BSM-2 kit item 3: the Esscher drift at CGMY — the exponent shift `ψ^θ(v) = ψ(v − iθ) − ψ(−iθ)` keeps the family (`(G, M) ↦ (G+θ, M−θ)`), the cumulant's strict convexity makes the drift map strictly increasing, `θ₀ = (M−G−1)/2` is its unique zero, in-range targets solve uniquely and out-of-range ones have no solution, the tilted numeraire condition `1 < M − θ` holds on the strip, and pricing at the tilted rates consumes `cgmy_cmPriceKernel_integrable` (`ImprovedBS/Esscher.lean`, 30 declarations) | **GREEN** — `lake build` + `#print axioms` audit (211 entries) + statement pins (elab, 240), run 36072416203; `benchmarks/LEDGER.md` row 13 |
| Lean theorems | BSM-2 kit item 6: the normalized CGMY → GBM corner — at the scale `C_Y = (σ²/2)(2−Y)` the Γ pole cancels and `ψ_Y(v) → −(σ²/2)v² + i(σ²/2)(G−M)v` **pointwise** on `−M < Im v < G`, as a one-sided `Y → 2⁻` limit; route A's algebraic forward normalization `Ψ_Y(v) = ψ_Y(v) + i(r−q−κ_Y(1))v` (numéraire exact at every `Y`, consuming `cgmyExponent_strip`) lands it on the risk-neutral GBM exponent and its factor on `gbmCharFactor`, route B's named `θ₀ = (M−G−1)/2` lands it on the zero-carry GBM exponent with no correction at all (consuming `esscher_cgmy_shift` at the shifted rates), and the drift half-width collapses to `(σ²/2)(G+M−1)` (`ImprovedBS/Corner.lean`, 17 declarations) | **GREEN** — `lake build` + `#print axioms` audit (226 entries) + statement pins (elab, 257), run 36111570530; `benchmarks/LEDGER.md` row 14, correction C17 |
| Lean theorems | the obstruction's tail hypothesis is non-vacuous — mathlib's Pareto law has `μ[x,∞) = t^r·x^(−r)`, so `htail` holds with equality and `Levy.lean`'s obstruction is instantiated at a real law by citation; C7's `α ≤ 0` remark is a theorem, giving `(∃ law, htail) ↔ 0 < α`, and a Dirac mass shows the hypothesis can fail (`ImprovedBS/ParetoWitness.lean`, 11 theorems) | **GREEN** — `lake build` + `#print axioms` audit (237 entries) + statement pins (elab, 268), run 36119639468; `benchmarks/LEDGER.md` row 15 |
| Deferred | *(nothing)* | ratcheted at 0 `sorry`s — `deferred: {}` |
| Lint is a falsifier | `tests/test_lint.py`: 44 seeded cheats each killed by a named check, 5 legitimate edits green, 1 residual gap asserted open | verified — 7/7 tests |
| Pinned claims | `tests/golden_statements.json`: 268 declarations — theorem statements, definition bodies | machine-checked (source 268, elab 268); `#check`/axioms layer verified in build job |
| Grading lane | briefs/ + benchmarks/ + 2 CI workflows + toolchain-free lint + pins | standing |
| First brief | BRIEF_001, re-scoped to what is actually checkable | see briefs/ |

**T5 is landed and green too** (BRIEF_006, run 35566569107): `t5_delta`,
`t5_gamma`, `t5_tau` and the two forms of the PDE identity, in `(S, τ)`
coordinates and without a `sorry` — the one genuinely new analytic input is
`Φ′ = φ`, derived from the interval-integral FTC because mathlib v4.34.0 has no
`Real.erf`. The audit puts the 11 new constants on
`[propext, Classical.choice, Quot.sound]`, and the pins grew 49 → 60 with the
49 pre-existing entries unchanged. Its verdict, and the four-run elaboration
arc that got there, are recorded in `benchmarks/LEDGER.md` row 6.

**T6 sub-goal 3(a) is landed and green** (BRIEF_007, PR #9, run 35574194681): until it, every Lean
theorem in the tree was a theorem *about the closed form* — its parity, its
bounds, its PDE — and nothing connected the closed form to the expectation it
is supposed to be. `ImprovedBS/RiskNeutral.lean` states and proves that
connection for the GBM instance: with `log(S_T/S) ~ N((r−q−σ²/2)τ, σ²τ)`,
`bsCall = e^{−rτ}·E[(S_T−K)⁺]` and `bsPut = e^{−rτ}·E[(K−S_T)⁺]`, as a
Lebesgue integral against the repository's `phi` and, through three bridge
lemmas (`phi = gaussianPDFReal 0 1`, `Phi x = gaussianReal 0 1 (Iic x)`,
`∫ f ∂gaussianReal 0 1 = ∫ f·phi`), against mathlib's `gaussianReal` in both
the standard-normal and the lognormal form; the drift condition
`E[S_T] = S e^{(r−q)τ}` comes with it. The whole analytic content is one
Gaussian integral, `∫_{(a,∞)} e^{sz} φ(z) dz = e^{s²/2} Φ(s − a)`, which is
T3's tilting identity integrated over a half-line — the same identity T4's
lower bound already used. The oracle grew a quadrature route
(`bs_call_by_expectation`, no `norm_cdf` and no `d1`/`d2` in it) that agrees
with the closed form to 1.6e-12 on the golden grid, and mutant M11 shows the
new test can fail. `0 < σ` is load-bearing: at `−σ` the closed form is
`−bsPut(σ)` while the expectation does not move, and the test asserts exactly
that, so the theorem is not being claimed for a sign it is false at. The audit
puts all 21 new constants on `[propext, Classical.choice, Quot.sound]`, the pins
grew 60 → 81 with the 60 pre-existing entries unchanged, and 20 of the 21
declarations elaborated on the first CI run. Verdict and arc:
`benchmarks/LEDGER.md` row 7 (and C10, the pin channel defect that arc found and
fixed).

**The model-free skeleton is landed and green** (BRIEF_009, PR #11, run 35589005865):
parity and the no-arbitrage bounds are lifted off the closed form onto
`e^{−rτ}·E[(S_T−K)⁺]` for *any* terminal-spot law with the drift condition
(`model_free_put_call_parity`, `model_free_call_bounds`, `model_free_put_bounds`),
and the GBM instance re-derives T2′ and T4 *through* the new layer
(`t2_spread_via_skeleton`, `t4_call_bounds_via_skeleton`, graded to consume the
model-free proofs and not the closed-form ones). This is item 5 of the BSM-2 kit
(docs/03 §D1) landed before the law is widened: "the widening preserves the
skeleton" is a theorem schema now — a later law inherits T2/T4 by supplying
three facts (`Integrable X`, the drift condition, `0 ≤ X`), not by re-proof.
All 12 new audited constants sit on `[propext, Classical.choice, Quot.sound]`,
and the pins grew 94 → 108 with the 94 pre-existing entries unchanged.

**T6's triangle holds at any strip law** (BRIEF_010, PR #16, run 35646623031):
the Carr–Madan kernel now lives on the pricing contour `u − i(α+1)` — the
contour correction C12 implemented, not edited away — and the full pricing
chain (`strikeTransform`, the Fubini exchange `fourierDampedModelFreeCall_eq`,
inversion `fourierCM_inversion`, and `carrMadan_eq_modelFreeCall` landing on
BRIEF_009's model-free layer) is proved for *any* law satisfying the strip
conditions, with GBM as the closed instance (`gbm_carrMadan_eq_bsCall`). The
CGMY decay enters only as a recorded hypothesis — the exponent itself is
BRIEF_011's deliverable. This is item 4 of the BSM-2 kit (docs/03 §D1) under
the re-scope `docs/04` pre-committed for it. All 25 new audited theorems sit on
`[propext, Classical.choice, Quot.sound]`, the pins grew 108 → 139 in both
layers with the 108 pre-existing entries byte-identical, and the `[CONTOUR]`
lint check with its own mutant guards the contour from here on.

**BSM-2 kit items 1–2 are landed too** (BRIEF_011, PR #17, run 35779316727):
the widening now has a concrete law rather than a hypothesis about one.
`ImprovedBS/CGMY.lean` defines the exponent
`ψ(v) = C Γ(−Y)[(M − iv)^Y − M^Y + (G + iv)^Y − G^Y]` on the principal branch,
proves it affine in τ, proves its moment strip `E[e^{uX_τ}] < ∞` on the whole
open strip `(−G, M)` (`cgmyExponent_strip`) — the positive twin of
`Levy.lean`'s obstruction, and the point where the tempered repair stops being
asserted — and proves the contour bound
`Re ψ ≤ −r|u|^Y + c'|u|^{Y−1} + K₀` that turns into BRIEF_010's (H-decay) past
`cgmyDecayThreshold`, so `cgmy_cmPriceKernel_integrable` *consumes*
`cmPriceKernel_integrable` rather than re-deriving it. The Lévy measure's
near-zero and far-field moments are theorems (`∫ (1 ∧ x²) ν < ∞` on the first,
`∫_{x≥1} e^{ux} ν⁺(dx) < ∞` for `u < M` on the second). All 41 new audited
theorems sit on `[propext, Classical.choice, Quot.sound]`, the pins grew
139 → 165 with the 139 pre-existing entries byte-identical, and the `[CGMY]`
lint check with its own mutant guards the exponent's shape and the contour
condition. Two corrections the brief found rather than inherited: **C14** — the
pricing line `v = u − i(α+1)` needs `α + 1 < M` *alone*, and the `min (G, M)`
spelling in `docs/03` §D1 had swapped which tempering rate binds which half of
the law (`G` constrains only the old line `u + iα`); **C15** — the contour's
*continuity* additionally needs `G > 0` and `α > 0`, because the right base's
imaginary part is `u`, which vanishes at the origin. Labelled prose in the
module header and route-checked numerically rather than machine-checked: the
Lévy–Khintchine representation itself, since mathlib v4.34.0 has no such
theorem.

**T1 through T4 are machine-checked.** `lake build` is green against mathlib
v4.34.0 / Lean v4.34.0 and the `#print axioms` audit confirms that all 25
declarations in the T1–T4 node — `Phi_add_Phi_neg`, `Phi_neg`, `erf_neg`,
`exp_neg_sq_even`, `t1_d1_minus_d2`, `t2_put_call_parity`,
`t2_put_call_parity_spread`, `t3_delta_identity`, `t4_call_bounds`,
`t4_put_bounds` and the sixteen lemmas they rest on — depend only on
`[propext, Classical.choice, Quot.sound]`, never on `sorryAx`. That is the
distinction that matters, since a `sorry` still builds. T1/T2 took eight CI
runs (PR #1); T3/T4 landed green on the first run (PR #2) because every mathlib
name was checked against the pinned tag before pushing. `benchmarks/LEDGER.md`
records both histories, including one runner incident (ENOSPC) that produced no
verdict at all.

**T6 sub-goal 1 is machine-checked too** (BRIEF_004, run 35523250105), and it is
where the repository's thesis starts to bite: a probability measure whose upper
tail is bounded below by `c·x^(−α)` has **no finite exponential moment**, for
every real `α` — `ImprovedBS/Levy.lean` proves it through the half-line levels
`x = 2^k` and `exp u / u^s → ∞` — and the two corollaries that make it a finance
result: `S_T = S₀·e^{X_τ}` has infinite first moment, and no shift of the drift
repairs it. That is the negative half of T6 as a theorem rather than a
paragraph, and it is why the tempered (CGMY) hypothesis in `docs/03` §D1 is
earned. Two corrections to the brief that demanded it are recorded in
`benchmarks/LEDGER.md` C7; one of them (`α < 2` is not needed, and the sanity
check that insisted on it was a false statement about Gaussian tails) makes the
theorem strictly stronger than the brief asked for. What is *not* checked: the
specialization to the symmetric α-stable law, since mathlib v4.34.0 has no such
law — the tail bound enters as the hypothesis and the `c = F(−α)` constant stays
a citation, as scope item 3 allows.

Three things that green build cost, and that a reader should know:

- **mathlib v4.34.0 has no `Real.erf`.** `docs/04` used to claim it did. `erf`
  is now defined locally from the interval integral and its oddness proved by
  substitution — enough for parity. T3/T4 additionally needed
  `Φ(x) = ∫_{(−∞,x]} φ`, which imports the *value* of the Gaussian integral
  (`integral_gaussian_Ioi`) in exactly one lemma, `integral_phi_Iic_zero`.
- All declarations live in `namespace BSM`. A module name is not a namespace,
  and a library that puts `Phi`, `d1` and `erf` in the root namespace is
  claiming names far too generic to claim.
- `import Mathlib` rather than narrow imports. Narrow imports are better
  practice but can only be validated with a toolchain; two hand-guessed paths
  cost three red runs. Narrowing the list is a legitimate follow-up for someone
  who can build.

## License

MIT. The mathematics (and its history) belongs to the half-century of
volatility-surface literature that this program builds on; our contribution
is the formal, machine-checked restatement and the widening question.

## Running the checks locally

All five harnesses are dependency-free Python; none needs a Lean toolchain.

```sh
python3 tests/test_bs.py          # 23/23 — the oracle satisfies the claimed identities
python3 tests/test_mutants.py     #  4/4  — and those tests can actually fail (30 mutants)
python3 tests/test_lint.py        #  7/7  — the linter can fail too (44 cheats, 5 controls)
python3 tests/test_pins.py        # 12/12 — and the pins that back it parse real CI output, and the delta/merge path works
python3 scripts/lean_lint.py      #  OK   — no sorry in the protected node, ratchet, independence, pins, spine, skeleton, contour, cgmy, nonuniq, esscher, corner, pareto (14 files, 321 declarations)
python3 scripts/pin_statements.py --check   # 268 statements match tests/golden_statements.json
python3 tests/test_crosscheck.py    #  6/6  — grid + oracle self-consistency, both T3 sides, input-source routing (the cross-check itself needs lake)
# or, with pytest installed:
pytest tests/
```

None of the five harnesses needs a Lean toolchain, by design: `tests/test_lint.py`
mutates copies of the tree and runs the lint against them exactly as CI does, and
`tests/test_pins.py` replays recorded `lake env lean` output through the pin
parser instead of assuming its format. The pins' elaborated layer
(`#check` types, `#print axioms`) is the one part that genuinely needs a
toolchain, so it is graded by the build job and its local behaviour is asserted to
be *red*, not skipped.

The Lean build itself needs elan + the mathlib cache:

```sh
lake exe cache get && lake build  # see docs/04 for the pinning rules
```
