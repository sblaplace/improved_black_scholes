# BRIEF_014 — the normalized CGMY → GBM corner (BSM-2 kit item 6)

- **Status: ISSUED, NOT LANDED** (2026-09-25). The route has been checked
  numerically with `python3 scripts/check_gbm_corner.py`; **no Lean theorem,
  statement pin, or audit entry for this brief exists yet**. The script is a
  pre-brief contradiction detector, not evidence of a proved limit.
- **Prerequisites:** BRIEF_011 (`cgmyExponent`, `cgmyExponent_strip`,
  `cgmyCharFactor`), BRIEF_013 (`cgmyCumulant`, `cgmyGamma_two_sub_eq`,
  `esscher_cgmy_shift`, `esscherThetaZero`, `esscherDriftMap_zero`,
  `esscher_drift_factor`) and BRIEF_005 (`gbmCharFactor`) are LANDED GREEN.
  Item 6 in `docs/03` §D1 asks for **pointwise exponent convergence** at the
  GBM corner, *not* convergence of option prices. This is the next kit brief
  after item 3. Ledger C13's old tentative "BRIEF_014 = Haug benchmark" was
  superseded by the ordering recorded in BRIEF_013; that repair stays queued
  after the kit.
- **Skills and budget:** a one-sided `Filter.Tendsto` at 2, two Gamma
  recurrences, and continuity of real/complex powers in their **exponent**
  at fixed, nonzero bases. New Lean work is CI-only here (no installed local
  toolchain); verify names at mathlib v4.34.0, then allow for elaboration and
  the by-design elaborated-pin bootstrap. No uniform Fourier bounds needed.

## First fix the statement: the bare corner in the old docs is false (C17)

At the actual `ImprovedBS/CGMY.lean` definition, with `M` on the positive
side and `G` on the negative side,

    B_Y(v) = (M−iv)^Y − M^Y + (G+iv)^Y − G^Y,
    ψ_Y(v) = C Γ(−Y) B_Y(v).

`Γ(−Y)` has a pole as `Y ↑ 2`. With **fixed** `C > 0` and, say, `G = M = 3`,
`v = 1`, the bracket tends `−2`, so `Re ψ_Y(1) ~ −C/(2−Y)`, **not** a finite
Gaussian exponent. At the tag Lean defines `Real.Gamma (-2) = 0` at the pole;
evaluating `cgmyExponent ... 2 v` would give the wrong answer as well. The
target must be a **one-sided limit**, never an equality at `Y = 2`.

The alternative printed in the old `docs/03` item 6, "or `G, M → σ²/2`", is
also not a GBM limit: changing the tempering rates at fixed noninteger `Y`
leaves nonquadratic complex powers. Neither limit is interchangeable with the
one this brief proves. C17 in the ledger records these corrections.

Fix `σ > 0`, `G > 0`, `M > 1` and vary **both** `Y` and `C`:

    1 < Y < 2,                ε = 2−Y,
    C_Y = (σ²/2) ε > 0.       [variance normalization]

BRIEF_013 already proved `Γ(2−Y) = Y(Y−1) Γ(−Y)` on `(1,2)`; one further
`Real.Gamma_add_one` gives

    ε Γ(−Y) = Γ(3−Y) / (Y(Y−1))  →  Γ(1)/2 = 1/2,
    C_Y Γ(−Y) → σ²/4.                              (1)

This is the whole pole cancellation; it is also the numerically stable route
around `sin(πY)` in the oracle's reflection formula. In particular, a scaling
`C_Y = σ² ε` would give **twice** the desired variance. Do not assert a
raw `Γ(−Y)` limit, and do not hide the scaling in a definition of the GBM
answer (the C1 vacuity failure, now at a limit).

For every fixed `v : ℂ` with both bases in the moment strip
`−M < Im v < G`, the powers have nonzero bases, and

    B_Y(v) → B_2(v)
           = (M−iv)² − M² + (G+iv)² − G²
           = −2v² + 2i(G−M)v.                       (2)

From (1)–(2), the **uncorrected** limit is

    ψ_Y(v) → −(σ²/2)v² + i(σ²/2)(G−M)v.             (3)

The diffusion variance is `σ²`; the remaining mean depends on `G−M`.
Equation (3) alone is *not* the risk-neutral GBM exponent at arbitrary
`r−q`. This matters: "the bracket is Gaussian" does not imply "the model
prices under the intended martingale measure."

## Drift and the connection to the landed GBM factor

There are two **different** routes below. Keep their selection principles
separate; the second consumes the named Esscher selection of BRIEF_013.

**A. General carry: algebraic forward normalization, not an Esscher law.** On
the strip let `κ_Y(1) := cgmyCumulant C_Y G M Y 1 = ψ_Y(−i)` (consume
`cgmyExponent_strip`). For fixed real `r, q`, put

    b_Y := r−q−κ_Y(1),
    Ψ_Y(v) := ψ_Y(v) + i b_Y v.                         (4)

This is a *deterministic linear correction to the exponent*, not an Esscher
tilt and not a claim that the tree contains a risk-neutral CGMY measure.
Algebraically, at every `Y ∈ (1,2)`:

    Ψ_Y(−i) = r−q,
    exp(τ Ψ_Y(−i)) = exp(τ(r−q)).                     (5)

Equation (2) at `v = −i` gives

    κ_Y(1) → (σ²/2)(G−M+1).

Thus the unwanted `G−M` cancels, with the correct log-drift:

    Ψ_Y(v) → i(r−q−σ²/2)v − (σ²/2)v²,                (6)
    exp(τ Ψ_Y(v)) → gbmCharFactor
                       ((r−q−σ²/2)τ) ((σ²/2)τ) v. (7)

Use the **existing** `BSM.gbmCharFactor m s v = exp(i·m·v − s·v²)` as the target
of (7), not a new function whose definition could conceal the comparison.
For the pricing line `v = u − i(α+1)`, (6) applies **pointwise** when
`0 < α` and `α + 1 < M` (C14). This is NOT an interchange of a `Y`-limit with
the Fourier pricing integral; (H-decay) for each `Y` is not one uniform
integrable bound as `Y ↑ 2`.

**B. Named Esscher selection: the exact zero-carry instance.** Set
`θ₀ = esscherThetaZero G M = (M−G−1)/2`. If `G+M > 1`, then
`θ₀ ∈ (−G, M−1)` and the shifted rates are

    G′ = G + θ₀ = (G+M−1)/2 > 0,
    M′ = M − θ₀ = (G+M+1)/2 > 1,    G′−M′ = −1.

By `esscher_cgmy_shift` and `esscherDriftMap_zero`, the **same** parameter
solves the Esscher equation `g_Y(θ₀) = 0` for *every* Y in scope. In
particular `esscher_drift_factor` gives the exact factor `= 1` at `v = −i`
when `r = q` — no approximated root or unproved limiting measure. Apply (3)
to the shifted rates:

    esscherExponent (cgmyExponent C_Y G M Y) θ₀ v
      = cgmyExponent C_Y G′ M′ Y v
      → −(σ²/2)v² − i(σ²/2)v,
    cgmyCharFactor C_Y G′ M′ Y τ v
      → gbmCharFactor (−σ²τ/2) (σ²τ/2) v.          (8)

That is a **named-selection** recovery of zero-carry risk-neutral GBM at the
factor level. It does not turn route A into an Esscher theorem for nonzero
carry. Also, BRIEF_013's attainable drift half-width obeys

    esscherDriftBound C_Y G M Y → (σ²/2)(G+M−1).   (9)

A proposed extension to general-carry Esscher solutions must impose
`|r−q| < (σ²/2)(G+M−1)` before asserting `θ_Y` exists near the corner, and
must separately prove `θ_Y` converges. Neither follows just from (7) or
(9); that extension is **out of scope** here.

## The Lean work to land (not yet written)

New module `ImprovedBS/Corner.lean` in `namespace BSM`, importing
`ImprovedBS.Esscher` (and `ImprovedBS.Fourier` for the GBM target), then added
to the root `ImprovedBS.lean`. Suggested statement shapes (exact binder names
are not the spec; **the equations and hypotheses above are**):

1. `cgmyCornerC (σ Y : ℝ)` is the independent scaling `(σ²/2)·(2−Y)`;
   `cornerForwardExponent` is `cgmyExponent (cgmyCornerC σ Y) G M Y v +
   i·(r−q−cgmyCumulant (cgmyCornerC σ Y) G M Y 1)·v` — **not** the GBM
   formula. Pin both definition bodies, as in BRIEF_011/013.
2. `cgmyCornerGamma_eq` states the identity in (1) on `1 < Y < 2`, **citing**
   `cgmyGamma_two_sub_eq` and `Real.Gamma_add_one`;
   `cgmyCornerGamma_tendsto` gets the finite `σ²/4` coefficient, not a
   fictitious `Γ(−2)` value. Verify `0 < C_Y` on the punctured interval.
3. `cgmyBracket_tendsto` proves (2) for fixed `v` in the strip, and
   `cgmyCornerExponent_tendsto` proves (3). On fixed nonzero complex bases,
   `Filter.Tendsto.const_cpow` reaches exponent `2` and `Complex.cpow_two`
   reduces to a polynomial; for positive real `M,G`, use real `rpow`
   continuity. This is **pointwise** in `v`.
4. `cgmyCornerCumulant_one_tendsto` obtains the `κ_Y(1)` limit from the
   **real** `cgmyCumulant` definition, and `cornerForward_numeraire` proves
   (5) by *consuming* `cgmyExponent_strip`. Then
   `cornerForwardExponent_tendsto` and `cornerForwardFactor_tendsto` prove
   (6)–(7), the latter using continuity of `Complex.exp` and the actual
   `gbmCharFactor`.
5. `cornerEsscherZero_numeraire` cites `esscher_drift_factor` and
   `esscherDriftMap_zero` with an explicit proof that `θ₀` lies in its
   admissible interval; `cornerEsscherZero_tendsto` proves (8) by
   *consuming* `esscher_cgmy_shift` and the general exponent limit at
   `(G′, M′)`. `cornerEsscherBound_tendsto` proves (9) from the landed
   `esscherDriftBound` body and (1), not from a new independent bound.

Use one-sided `Filter.Tendsto` as `Y → 2⁻` (eventually `1 < Y < 2`), not `= 2`
or a two-sided limit across the Gamma pole. The natural statement for (3) is
`v : ℂ`, `−M < v.im < G`; `G > 0`, `M > 1` cover `v = −i`, real-frequency
points and the pricing line under `α + 1 < M`. In (8) the strip must use
**shifted** rates `G′, M′`, not automatically the original ones. Even with
`v : ℝ` as a first lemma, the final theorem should include the complex
points needed for (5) and the contour statement; proving only `v = 0`
would be vacuous.

## Numeric route-check (measured at issue, not a proof)

`python3 scripts/check_gbm_corner.py` runs against the **existing** oracle
`cgmy_exponent` (Gamma from Euler reflection), `cgmy_cumulant` (separate real
route), `esscher_exponent`/`esscher_drift_map`, and an independently expanded
GBM polynomial target. It is also run by the `oracle` CI workflow, which
checks numeric consistency but does not compile or prove the corner. The
stable Gamma coefficient uses the recurrence and `math.gamma(3−Y)`, not the
oracle's `sin(πY)` expression. Cases
`(G,M,σ,r,q,α,τ)` are `(3,3,.2,.05,.02,.3,.8)`,
`(.5,1.8,.65,−.01,.02,.2,1.2)`, `(5,8,.37,.05,0,.4,2)`;
6 fixed complex points per case include `0`, positive and negative real
frequencies, `−i`, an interior complex point and the *pricing* contour
`u−i(α+1)` with `α+1 < M` **and** `α+1 < M′` at `θ₀`. Four steps
`ε ∈ {.1,.01,.001,.0001}` (72 exponent/point probes per route, and 12
case/step probes for each coefficient, `κ(1)` and bound). Errors below are
`|actual−target|/(1+|target|)`, maxima over cases and points where applicable;
the exact numéraire tests use absolute error `< 1e−10` at every step, and the
oracle explicitly rejects the pole `Y=2`.

| route | ε=.1 | ε=.0001 |
|---|---:|---:|
| recurrence coefficient vs the independent reflection form | 6.68e−18 | 3.95e−14 |
| raw CGMY vs the polynomial (3) | 6.97e−2 | 8.09e−5 |
| `κ_Y(1)` vs its limit | 2.54e−2 | 2.94e−5 |
| forward-normalized exponent vs GBM (6) | 5.05e−2 | 5.85e−5 |
| factor vs `gbmCharFactor` (7) | 5.00e−2 | 5.48e−5 |
| zero-carry Esscher vs GBM (8) | 4.96e−2 | 5.76e−5 |
| Esscher range `H_Y` vs (9) | 8.62e−2 | 1.01e−4 |
| Esscher shift vs independent shifted-rate exponent | 5.93e−17 | 4.54e−17 |

**Negative controls measured, not merely proposed:** at `C=.35, G=M=3,
v=1`, fixed-C `Re ψ(1)` runs `−2.980` at `ε=.1` to `−349.411` at
`ε=.001`; the scaled value `ε·Re ψ(1)` is approaching `−.35` and the
unscaled value diverges. At fixed `Y=1.5, C=.2, G=M=σ²/2=1.125` (with
`σ=1.5`, so `M>1` and the numéraire is inside the strip),
`Re ψ(2)/Re ψ(1) = 3.691`, not the Gaussian quadratic ratio `4`: the old
*rate-only* alternative fails too. At `σ=.75, G=M=3, r−q=.03,
v=2, ε=.0001`, the corrected GBM discrepancy is `< .001`, while doubling
`C_Y` makes it `1.257` and omitting `−κ_Y(1)` makes it `.563`. The script
**asserts** these canaries and the error shrinkage; the observed ~O(ε)
errors are diagnostics, not a theorem of convergence or a rounding guarantee
as `ε → 0` in Float.

## Grading and acceptance at implementation

- Add the new declarations to `REQUIRED` and `PROTECTED` in
  `scripts/lean_lint.py`, append statement pins for every new theorem and
  **full bodies** for new definitions to `tests/golden_statements.json`. All
  existing 240 source/elaborated pairs remain byte-identical; `deferred: {}`
  stays empty. Bootstrap the new `elab` entries from CI output; a green
  local lint does **not** imply a machine-checked Lean result.
- Add a `[CORNER]` route check plus named lint mutants: the scale contains
  `(2−Y)` and the `σ²/2` factor, not `σ²` or `Γ(−2)`; the gamma identity
  consumes `cgmyGamma_two_sub_eq`; the factor target uses
  `gbmCharFactor`, and the zero-carry Esscher instance consumes
  `esscher_cgmy_shift`/`esscher_drift_factor`, not a rederived exponent.
  Protect the `𝓝[<] 2` limit and the strip hypotheses in the pins.
- Make the pre-brief numerical checks a committed oracle test when the Lean
  implementation lands (reuse this script or move its independent routes
  into `tests/test_bs.py`) and seed mutants for at least doubled scaling
  and missing drift correction. Their large measured residuals above
  demonstrate that those tests can fail. Preserve the existing CGMY
  oracle's restriction `Y < 2`: it must **not** evaluate at the pole.
- Only call this brief **GREEN** after `lake build`, `#print axioms` (no
  `sorryAx`), elaborated statement pins, the oracle tests, and both
  mutation harnesses pass in CI; then record the verdict and actual counts
  in `benchmarks/LEDGER.md`. Until then this is an **issued** brief.

**Verified at mathlib v4.34.0 source at issue:** `Real.Gamma_add_one` and
`Real.Gamma_one` (`Gamma/Basic.lean`), `Real.differentiableAt_Gamma` on
positive inputs (`Gamma/Deriv.lean`), `Filter.Tendsto.const_cpow`
(`Pow/Continuity.lean`), and `Complex.cpow_two` (`Pow/Complex.lean`). The
previously landed `cgmyGamma_two_sub_eq` uses the first Gamma recurrence.
There is no Lean compiler available in this checkout: these are source
checks, **not** proof-elaboration results.

## Explicitly out of scope

- A CGMY probability measure, a Lévy–Khintchine identification of its
  exponent with an expectation, or an Esscher-tilted measure. The current
  tree has the *factor* and Lévy density, not a CGMY `Measure ℝ`; (5) and
  (8) are factor-level statements just like BRIEF_013. Even the factor
  limit does not itself construct a weak limit of measures.
- Convergence of call prices or Fourier integrals. Pointwise convergence
  of a characteristic factor is **not** a uniform dominating bound on the
  Carr–Madan contour and does not justify interchanging the limit and the
  pricing integral (or any uniform-in-v / uniform-in-τ assertion).
- A general-carry Esscher theorem. Proving `θ_Y → θ_GBM` for the unique
  BRIEF_013 roots, under the strict limiting range bound in (9), is a
  separate inverse-limit argument. Route A is an explicitly **different**
  drift normalization, not a substitute for that argument.
- The other (α-stable) corner `G,M → 0`, hedging/PDE recovery under jumps,
  and an empirical claim that CGMY performs better out of sample. None is
  a consequence of an exponent limit.
