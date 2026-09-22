# BRIEF_011 — the CGMY exponent, its Levy measure, and the moment strip (BSM-2 kit items 1–2)

- **Status:** **ISSUED** — implemented in `ImprovedBS/CGMY.lean`; verdict is the
  CI run on this branch (see `benchmarks/LEDGER.md` row 11). This is **items 1–2**
  of the BSM-2 kit in `docs/03` §D1: *the concrete CGMY characteristic exponent*
  (the `cpow`/branch work BRIEF_005 explicitly deferred) as the next brief's
  work, and *the moment strip* — the tempered region on which
  `E[e^{uX_τ}] < ∞`, containing both the pricing contour and the numéraire
  point. Landing it also corrects the strip condition that `docs/03` §D1 and
  `docs/04`'s queue state as `α + 1 < min(G, M)` (§"Correction C14" below;
  recorded as correction C14 in `benchmarks/LEDGER.md`).
- **Prerequisite PRs:** BRIEF_005 (`ImprovedBS/Fourier.lean`, the abstract
  (H-decay) hypothesis this brief discharges), BRIEF_010
  (`ImprovedBS/Pricing.lean`, the `cmPriceKernel_integrable` interface this
  brief instantiates) merged. **No edit to any existing declaration** anywhere in
  the tree: the whole brief is one new module plus grading wiring, so no pinned
  statement outside the new module moves.
- **Skills:** Lean 4 + mathlib at the pinned tag v4.34.0: complex `cpow` and its
  branch (`slitPlane`, `Complex.log`/`Complex.arg`), Euler reflection for
  `Γ(−Y)`, the mean value inequality on `[0, a]` for a `ℂ`-valued map, and
  `IntegrableOn` domination by `x ^ s * exp (−b x ^ p)`. No new mathematics:
  every ingredient is calculus and the Euler reflection formula.
- **Budget:** CI-only verification (no local Lean toolchain). Expect the two-run
  `elab` pin bootstrap as in BRIEF_007–010 (first run red by design and printing
  the block, second run merging it verbatim) plus elaboration fixes on the
  mean-value step. Every mathlib name this brief relies on was verified against
  the pinned tag before it was committed (ledger C3); the numeric route was
  checked in the oracle **before** the Lean was written (ledger C4) and is
  recorded in §"The numeric route-check".

## Background, in order

1. `docs/03` §D1 lists the BSM-2 kit. Item 1 is the concrete CGMY exponent,
   item 2 the moment strip that makes its damping legal. `docs/04`'s queue
   assigns both to BRIEF_011 and states the acceptance bar that shapes this
   brief: the module must supply the CGMY factor's **continuity and decay on the
   contour** `u ↦ u − i(α+1)`, so that BRIEF_010 §5's (H-decay) hypothesis is
   discharged at the concrete exponent *without re-proving the pricing node*.
2. `ImprovedBS/Fourier.lean` (BRIEF_005) already carries the shape, as a named
   hypothesis: `hdecay : ∀ u, u₀ ≤ |u| → ‖φ (↑u + ↑α * I)‖ ≤ D * exp (−c * |u| ^ Y)`.
   What it did *not* have — and said so in its header — is a `ψ` with a `Γ(−Y)`
   in it. CGMY's exponent needs `(M − iv)^Y` for non-integer real `Y`, i.e. the
   principal-branch complex power, and that is the work BRIEF_005 deferred
   (`NOT MACHINE-CHECKED: CGMY exponent existence ... BRIEF_011`).
3. `ImprovedBS/Pricing.lean` (BRIEF_010, correction C12) moved the pricing kernel
   to the line `v = u − i(α+1)` and proved `cmPriceKernel_integrable` at any `φ`
   that is continuous on the contour and decays like `D e^{−c|u|^Y}`. That is the
   interface this brief instantiates. Since it is a *general* theorem, the CGMY
   instance must **cite** it rather than re-derive integrability — a route
   commitment the `[CGMY]` lint check enforces (mutant C2).
4. The measurability half of the strip (item 2) is what the Lévy measure needs:
   `ν` must satisfy `∫ (1 ∧ x²) ν < ∞` for `ψ` to be a characteristic exponent,
   and the tempering is what makes `∫ (1 ∧ x²)ν` finite while leaving the
   exponential moment finite on a *strip* rather than nowhere (BRIEF_004 is the
   theorem that an untempered power tail has no exponential moment at all).

## Correction C14 — the pricing-line condition is `α + 1 < M`, not `min (G, M)`

On the C12 pricing contour `v = u − i(α+1)` the two cpow bases of the exponent are

    M − iv = (M − (α+1)) − iu        Re = M − (α+1)     — needs α + 1 < M
    G + iv = (G + α+1) + iu           Re = G + α + 1     — positive for free

so the branch condition on the pricing line is `α + 1 < M` **alone**. `G` does
not constrain that line at all; it binds only the *old* line `v = u + iα` that
`Fourier.lean`'s `carrMadanKernel` sits on, where `G + iv = G + i(u + iα)` has
real part `G − α`, negative once `α ≥ G`. The `min (G, M)` spelling in
`docs/03` §D1 and `docs/04`'s queue is the *intersection* of the two lines'
conditions, and the prose that justified it (`the strip is α + 1 < G`) swapped
which tempering rate controls which half of the law — `M` tempers the positive
half `C e^{−Mx} x^{−1−Y}`, `G` the negative half `C e^{−G|x|} |x|^{−1−Y}`.

The landed statements therefore use `α + 1 < M` and require only `G > 0`:

* `cgmyExponent_contour_re_le`, `cgmyExponent_contour_re_le_half`,
  `cgmy_contour_decay` and `cgmy_cmPriceKernel_integrable` all carry
  `(hMG : α + 1 < M)`;
* `cgmyOldContour_base_right_re` keeps the witness `Re(G + iv) = G − α` as a
  theorem, so the correction is checkable rather than a comment;
* the `[CGMY]` lint check fails if a landed statement grows a `min` over `G`/`M`
  or loses its `α + 1 < M`, and mutant **C2** in `tests/test_lint.py` seeds that
  regression (`α + 1 < min G M`) so the guard is falsified, not assumed;
* `tests/test_bs.py::test_cgmy_contour` checks the two lines' base reals
  numerically at the M-side witness `G = 0.5, M = 10, α = 1.5`, where
  `G < α < M − 1`.

`Fourier.lean`'s `carrMadanKernel` stays where it is (`u + iα` is the α-damped
kernel and `α < G` is its correct condition), and the numéraire condition
`1 < M` is untouched — it is the same `M`, which is why the docs' right wing
`α < M − 1` was already correct.

## The mathematics, as landed

**The exponent** (`cgmyExponent`) is

    ψ(v) = C Γ(−Y) [ (M − iv)^Y − M^Y + (G + iv)^Y − G^Y ],

with `cgmyCharFactor C G M Y τ = exp (τ ψ)`, affine in `τ`
(`cgmyCharFactor_add`, `cgmyCharFactor_zero`). Primitive-branch powers: `M^Y`
and `G^Y` are the *real* `rpow`s (`Complex.ofReal_cpow`), and the branch of the
two `cpow`s is the principal one, which is exactly what C14's condition buys.

**The strip** (`cgmyExponent_strip`): for `v = −iu` with `u ∈ (−G, M)` both
bases are the *positive* reals `M − u` and `G + u`, so `ψ(−iu)` is real,

    ψ(−iu) = C Γ(−Y) [(M − u)^Y − M^Y + (G + u)^Y − G^Y] ∈ ℝ,

and `E[e^{u X_τ}] = exp(τ ψ(−iu)) < ∞` on the whole open strip. The numéraire
point `u = 1` therefore needs `1 < M` (`cgmy_numeraire_strip`), and the contour's
imaginary shift `α + 1` lies in the strip exactly when `α + 1 < M`
(`cgmy_contour_mem_strip` — where `α + 1 > 0 > −G` is free).

**The decay** (BRIEF_010 §5's (H-decay), at the concrete exponent). With
`y = |u|`, `a₁ = M − (α+1)`, `a₂ = G + α + 1` the contour's two-base real part is

    Re ψ(u − i(α+1)) = C Γ(−Y) [ Re((a₁ + iy)^Y) + Re((a₂ + iy)^Y) − M^Y − G^Y ]

(`cgmyExponent_contour_re`, `cgmyExponent_contour`), and each base is estimated by

* `cgmy_cpow_re_ge_of_lt_one`, `Y < 1`: the sharp
  `y^Y cos(πY/2) ≤ Re((a + iy)^Y)`, from `Re(z^Y) = ‖z‖^Y cos(arg z · Y)`
  (`cgmy_cpow_re_eq`), `cos` decreasing on `[0, π]` and `‖z‖ ≥ y`;
* `cgmy_cpow_re_le_of_one_le`, `1 ≤ Y < 2`: the mean value inequality on
  `t ↦ (t + iy)^Y`, whose derivative is `Y (t + iy)^{Y−1}` with norm
  `Y ‖t + iy‖^{Y−1} ≤ Y (2y)^{Y−1}` for `t ≤ y`, giving
  `Re((a + iy)^Y) ≤ y^Y cos(πY/2) + 2^{Y−1} Y a y^{Y−1}`.

Both signs of `Γ(−Y) cos(πY/2)` (negative on `(0,2) \ {1}`:
`cgmy_tempered_prod_neg`, which is Euler reflection `cgmyGamma_neg_eq` for the
`Γ`, `cos_pos_of_mem_Ioo`/`cos_neg_of_pi_div_two_lt_of_lt` for the cosine)
produce the same statement, the brief's headline inequality:

    cgmyExponent_contour_re_le :
      Re ψ(u − i(α+1)) ≤ −r |u|^Y + c' |u|^{Y−1} + K₀        (|u| ≥ M + G)

with `r = 2 C |Γ(−Y) cos(πY/2)|` (`cgmyTemperedRate`, positive by
`cgmyTemperedRate_pos`), `c' = 2^{Y−1} Y (M+G) |C Γ(−Y)|`
(`cgmyTemperedCorrection`) and `K₀ = C |Γ(−Y)| (M^Y + G^Y)`
(`cgmyTemperedConstant`). The correction's `M + G` is `a₁ + a₂`: the bases' real
parts sum, which is why `c'` carries no `α`.

Past the explicit `cgmyDecayThreshold = max (M+G) (max (4c'/r) (max 1 ((4K₀/r)^{1/Y})))`
the correction and the constant each cost at most a quarter of the leading term
(`cgmyExponent_contour_re_le_half`), so

    cgmy_contour_decay :
      ‖exp (τ ψ(u − i(α+1)))‖ ≤ exp (−(τ r / 2) |u|^Y),

and `cgmy_cmPriceKernel_integrable` is BRIEF_010's `cmPriceKernel_integrable`
instantiated at `c := τ r/2`, `D := 1`, `Y := Y`, `u₀ := cgmyDecayThreshold` —
i.e. the (H-decay) hypothesis of BRIEF_010 §5 is *discharged*, not assumed.

**The Levy measure** (`cgmyLevyDensity`): `C e^{−Mx} x^{−1−Y}` on `x > 0` and
`C e^{Gx} (−x)^{−1−Y}` on `x < 0`. `cgmy_levy_sq_integrable` is the near-zero
half of `∫ (1 ∧ x²) ν < ∞` — the `x²`-weighted density is `C e^{−Mx} x^{1−Y}`,
integrable on `(0,1)` exactly when `Y < 2` — and `cgmy_levy_far_moment` is the
tempered far-field moment `∫_{x ≥ 1} e^{ux} ν⁺(dx) < ∞` for `u < M`, which after
`e^{ux} e^{−Mx} = e^{−(M−u)x}` is mathlib's `∫₀^∞ x^{−1−Y} e^{−bx}` at
`b = M − u > 0`. Tempering is what makes this work: without it the far moment
diverges (BRIEF_004's obstruction), and the strip is `(−G, M)` and nothing
wider.

## The numeric route-check (measured before the Lean — ledger C4)

`tests/test_bs.py::test_cgmy_contour` is the committed shadow; the pre-Lean
route check (scratch, `/tmp/b11/route4.py`) ran the same statements against the
oracle on larger grids:

| check (Lean declaration it shadows) | grid | result |
|---|---|---|
| `y^Y cos(πY/2) ≤ Re((a+iy)^Y)`, `Y < 1` (`cgmy_cpow_re_ge_of_lt_one`) | `Y ∈ {0.2, 0.5, 0.9, 0.99}`, `y ∈ {0.05 … 40}`, `a ∈ {0 … 100}` | worst excess `0.0` |
| `Re((a+iy)^Y) ≤ y^Y cos(πY/2) + 2^{Y−1} Y a y^{Y−1}`, `1 ≤ Y < 2`, `a ≤ y` (`cgmy_cpow_re_le_of_one_le`) | `Y ∈ {1, 1.05, 1.2, 1.5, 1.8, 1.95}`, `y ∈ {0.05 … 250}`, `a = y·i/100` | worst excess `0.0` |
| `Re ψ ≤ −r|u|^Y + c'|u|^{Y−1} + K₀`, `|u| ≥ M+G` (`cgmyExponent_contour_re_le`) | 48 parameter sets, 5040 points, `u` up to `5000` | **0 violations** |
| `Re ψ ≤ −(r/2)|u|^Y` past `cgmyDecayThreshold` (`cgmyExponent_contour_re_le_half`) | at `u₀`, `1.7u₀`, `12u₀` for every set | worst excess `0.0` |
| base reals on the two lines (C14) | `G=0.5, M=10`, `α = 0.5 … 2.9` | pricing `(M−(α+1), G+α+1) ≥ 0`; old line `G − α < 0` for `α > G` |

Two facts the check also pins down, because they are easy to get wrong: the
*rate is approached from below* — `−Re ψ/(r|u|^Y)` is `0.84 … 0.90` at
`u = 5000` for the slowest sets, so a test asserting the sharp rate needs large
`u` and a one-sided tolerance (the committed test asserts `0.8 < ratio < 1.02`) —
and the untempered/old-line probes are *inconclusive*, so the module asserts
nothing about them beyond C14's base-level witness.

`cgmyDecayThreshold(1, 5, 10, 0.7) = 165.0385` (M+G = 15, `4c'/r = 37.57`): the
constant term dominates the threshold, which is why the def carries
`(4K₀/r)^{1/Y}` and not just `M+G`.

## Grading wiring (the repo motion)

* `scripts/lean_lint.py`: 26 new `REQUIRED` **and** `PROTECTED` names (the
  exponent, the three decay constants, the threshold, the density and 18
  carrying theorems — a definition is a specification, so hollowing
  `cgmyExponent` to `0` is a diff), and a new **`[CGMY]` check (13)** with one
  mutant: exponent must be the two-base `Γ(−Y)` form; the integrability instance
  must cite `cmPriceKernel_integrable` and supply `cgmyDecayThreshold`; the
  landed statements must carry `α + 1 < M` and no `min` over `G`/`M`; the
  old-line witness must stay. Mutant **C2** (the `min (G,M)` regression) is
  seeded and killed by that check alone (29 mutants, 5 controls).
* `tests/test_bs.py::test_cgmy_contour`: the committed numeric shadow — closed
  form vs pieces, τ-affinity, `cgmyCharFactor 0 = 1`, the compensated
  Lévy-integral route check, the sign `Γ(−Y)cos(πY/2) < 0`, both pointwise
  regimes, the contour bound, the threshold bound, the sharpness ratio, the C14
  witness table and the strip's real-valuedness.
* `tests/golden_statements.json`: pins `139 → 165`, the 139 pre-existing entries
  **byte-identical** (append-only). The `elab` layer for the 26 new names
  bootstraps red on the first CI run by design, then the printed block is merged
  verbatim.
* `ImprovedBS.lean`: one import line + blurb; nothing else outside the module.
* `benchmarks/LEDGER.md`: correction **C14** (both above and in the corrections
  section) and row 11 for the verdict.

## Done looks like (acceptance — machine-graded)

1. `lake build` green at the pinned tag, with `#print axioms` on the new
   `-- BRIEF_011:` section showing `[propext, Classical.choice, Quot.sound]` and
   never `sorryAx`.
2. Statement pins: all 165 present, the `elab` layer matching the tree.
3. `lint` green including `[CGMY]`, with mutant C2 red under mutation.
4. `oracle` lane green including `test_cgmy_contour`.
5. No pinned statement outside `ImprovedBS/CGMY.lean` moved; `deferred: {}`
   untouched; T1–T6 and BRIEF_004–010 statements unchanged.

## Explicitly out of scope

* **Item 3 of the kit** (the drift fixed at a *named* pricing measure, i.e.
  `ψ` + numéraire condition ⇒ a martingale measure, not just a real exponent) is
  the next brief's content: this module lands the strip that makes it possible
  (`cgmyExponent_strip`, `cgmy_numeraire_strip`) and stops there.
* **Item 6** (the GBM corner recovery `Y → 2` / `G, M → σ²/2` as `Y → 2`:
  `ψ(v) → C Γ(−2)[...]` degenerates and the corner needs its own statement) is
  deferred, as `docs/04`'s queue says.
* **The Levy–Khintchine representation itself is NOT machine-checked.** That the
  compensated integral of `ν` *equals* the closed-form `ψ` is the one step this
  module labels as prose: mathlib v4.34.0 has no such theorem (the same caveat
  sits in `Fourier.lean`'s header), and the Taylor step from
  `∫ (1 ∧ x²) ν < ∞` to the compensated integrand is analytic, not algebraic.
  Both are route-checked numerically (the oracle's compensated one-sided
  integral against `cgmy_exponent_one_sided_compensated`, in
  `test_cgmy_contour`), and the module header says so. Nothing in the tree
  *assumes* the identity: the exponent is a definition, and every theorem about
  it is a theorem about that definition.
* **BRIEF_012** (kit item 7's machine-checked non-uniqueness witness, ledger
  C13) is untouched.

## Why this is worth a brief (and shaped this way)

Because it is the first place the program's abstraction meets a real model. Every
earlier node either proved something about BSM's closed form or *assumed* its
analytic inputs as hypotheses; this one has to produce a `ψ` whose branch is
correct, show that its decay is the kind BRIEF_010 consumes, and say honestly
which step remains prose. The two things a reviewer should check are the two
things the guards watch: the condition is `α + 1 < M` and not the docs' `min`
(C14 — a hypothesis stronger than the mathematics needs is invisible to the
build, which is why it is pinned and mutated), and the integrability is
*consumed* from BRIEF_010 rather than re-proved (a route commitment, like
`[SPINE]` for T5 and `[SKELETON]` for the model-free layer).
