# BRIEF_016 — the external anchor: the published Carr–Madan test case, and the term-structure falsifier (ledger C13 finding 4)

- **Status:** **ISSUED** (this PR) — documentation plus a committed numeric
  route-check. No `.lean` file, no pin, no audit entry, no lint rule and no
  `.github` workflow changes: the subject of this brief is the **oracle's
  agreement with the literature**, not a new Lean theorem, and there is no Lean
  module to guard. The issuance verdict is recorded in `benchmarks/LEDGER.md`
  when CI grades the documentation commit; the implementation's verdict gets
  its own row when the oracle work is graded.
- **What this is.** The **second and last** of the two repair briefs ledger C13
  queued after the BSM-2 kit. The first was the Pareto witness (C13 finding 3),
  landed as BRIEF_015. This one is C13 finding 4: *"the oracle and the Lean twin
  share an author. Agreement between them is weaker evidence than the crosscheck
  section claims by omission."* C13's provisional label for it was "BRIEF_014"; that assignment is
  superseded (the kit items took 013 and 014), and this brief takes the next
  free number. The repair C13 prescribed has two halves —
  **(a)** pin published benchmark values as **literal constants in `tests/`**
  ("one genuinely external anchor"), and **(b)** add the review's
  **term-structure falsifier** to the oracle, comparing the model's measured
  ATM-skew decay exponent against a *cited* market power law, with the outcome
  landing in `docs/02` as a RED against the T6 direction taken alone.
- **The anchor is re-scoped, and stronger.** C13 named Haug's book as the
  source. The book's numeric tables are not reachable from the issuing sandbox
  (the Haug search returns metadata only — no test-case values), and Haug is
  not the lane this repository implements. The anchor is instead the **published
  test case of Carr & Madan (1999)** — the paper this tree's Fourier pricing
  lane *is*, cited by `ImprovedBS/Fourier.lean`, `ImprovedBS/Pricing.lean` and
  their oracle shadows. It is public, it is checkable to four decimal places,
  and it turns out to live at **`Y = 0`, the Variance-Gamma corner of the CGMY
  family** (F3 below) — the same corner a future CGMY-law brief would build in
  Lean. This is a strict improvement on the Haug plan: one external source
  anchors both the oracle's Fourier route and (numerically) the family corner.
- **Why this one next.** It is the only queued repair, it is Python plus docs,
  it needs no toolchain beyond Python 3 (the router's oracle tests are
  stdlib-only by construction, and the *whole* route-check below was run that
  way), and it attacks the one piece of evidence the repository has never had:
  a number from outside the tree.
- **Prerequisites:** none beyond the landed oracle primitives
  (`carr_madan_denom`, `cgmy_exponent`, `bs_call`, `norm_cdf`) and BRIEF_014's
  corner pattern. The brief is **append-only** for the tree: one new brief,
  additive oracle functions, one new test, new mutants, docs edits.
- **Skills:** Python 3 (stdlib only), the repo's Carr–Madan contour
  conventions (`v = u − i(α+1)`, `carr_madan_denom`), BS implied-vol inversion
  by bisection, and the power-law fit described below.
- **Budget:** one CI lane (the `oracle` lane; the `lean` lane must stay green
  with **nothing** changed). The mathematics is fixed and route-checked below;
  the expected failure mode is transcription (the published literals), not
  derivation.

## Findings recorded at issue

**F1. The anchor exists, it is public, and it is this repository's own method.**
Carr, P. and Madan, D. B. (1999), *Option valuation using the fast Fourier
transform*, Journal of Computational Finance **2**(4), 61–73,
DOI `10.21314/JCF.1999.043`. Section 5 illustrates the method on the
Variance-Gamma (VG) model; Table 1 fixes four parameter cases, and the text
fixes the market conventions for the detailed price evaluation:

    Case 4:  sigma = 0.25,  nu = 2.0,  theta = -0.10,  t = 0.25
    with     S0 = 100,  r = 0.05,  q = 0.03     (Section 5, around Figure 2)

The paper prints three prices in Section 5 (the sentence that introduces
Figure 2), at strikes 77, 78 and 79:

    published, agreed by VGP / VGFIC / TV to four decimals:  0.6356  0.6787  0.7244
    published, the failing VGPS (Pi1/Pi2) route at the same strikes:  0.2425  0.2299  1.5386

**F2. The published row is the OTM price, not the call.** The paper says
"option prices"; the numbers are the **put** prices (equivalently the call's
time value, equivalently the OTM option value) at those strikes. The call at
`K = 77` is `≈ 23.84`, so `0.6356` cannot be a call and the VGPS row cannot be
calls either. The route-check below reproduces the *put* column to all four
published decimals, which is what identifies the row. Any implementation must
read the anchor that way, and must pin the **literals** (`0.6356, 0.6787,
0.7244`) plus a citation comment, not a recomputation.

**F3. The Case-4 parameters are CGMY at `Y = 0`.** VG is the `Y → 0` boundary
of the family this tree prices, with the standard correspondence

    C = 1/nu,   s = sqrt(theta^2 + 2 sigma^2 / nu),
    G = (s + theta)/sigma^2,   M = (s - theta)/sigma^2,

which at the Case-4 numbers is `C = 0.5`, `G = 2.708131881...`,
`M = 5.908131881...` — with `1 < M`, so the numéraire condition
(`cgmy_numeraire_strip`, BRIEF_011) holds. So the anchor is reachable from the
CGMY lane as the `Y = 0` corner, and the test may price it **by that route**,
which is the corner the family's `Y → 2` twin (BRIEF_014) does not cover. The
`Y = 0` exponent is the limit

    psi_0(v) = C [ log(M / (M - iv)) + log(G / (G + iv)) ],

not an evaluation of `cgmy_exponent` at `Y = 0` — the landed `cgmy_gamma_neg`
has a pole there (`Gamma(0)`), exactly as BRIEF_014's corner had a pole at
`Y = 2`. Any implementation must define the corner exponent explicitly and
never divide by zero on the way in.

**F4. C13's own parenthetical is wrong, and the correction strengthens the
RED.** C13 finding 4 says pure exponential-Lévy smiles *"decay like
`τ^(−1/2)` at long ones"*. The **cited** large-maturity rate for exponential
Lévy models is `O(τ^(−1))`: Figueroa-López, Forde and Jacquier, *The large-time
smile and skew for exponential Lévy models* (Proposition 4.1:
`∂_x[σ̂_t(x)² · t] → a₀(0) = 8(p₀ − 1/2)`; the literature quotes the Lévy rate
as `O(τ^(−1))`). The measured exponents below agree with the citation, not with
C13's parenthetical: the `τ^(−1/2)` rate is the rate of the *standardized
skewness* under the Edgeworth expansion, not of the ATM implied-vol skew in
log-moneyness. Recorded as **ledger C19** — the next free letter after C18 (BRIEF_014's route-check correction) — and the *facts*, not the parenthetical, are what the RED rests on. The correction matters because the
gap to the market is *wider* than C13 thought: the family decays like `1/τ`
while the market decays like `τ^(−0.36..−0.45)`, and it is the family — not
the market — that is on the wrong side of the conventional stochastic-vol rate.

**F5. The market side has a citable exponent table, with a regime change.**
El Amrani and Guyon, *Does the term structure of the at-the-money skew really
follow a power law?* (Risk, Cutting Edge; two years of SPX / SX5E / DAX data):
the ATM skew follows a power law `τ^(−α)` for maturities **above** three to
four weeks with `α = 0.43` (SPX), `0.44` (SX5E), `0.45` (DAX); **below** three
weeks the exponents are `0.19 / 0.04 / 0.08`, i.e. the short end does **not**
blow up, and the extrapolated zero-maturity skew is finite, of order `1.5` in
absolute value. Gatheral, Jaisson and Rosenbaum (Quantitative Finance 18(6),
2018, "Volatility is rough") state the same law as `α ∈ (0.3, 0.5)` over a wide
range of expirations, with an SPX power-law fit of `τ^(−0.44)`. The brief pins
the market band as `(0.30, 0.50)` with those fitted values in the comment.

## §1 The anchor to land (published constants, literal in `tests/`)

Pin, in `tests/`, with the citation adjacent:

    CARR_MADAN_1999_CASE4 = ((77.0, 0.6356), (78.0, 0.6787), (79.0, 0.7244))
    CARR_MADAN_1999_VGPS_WRONG = (0.2425, 0.2299, 1.5386)   # same paper, same strikes
    CARR_MADAN_1999_CASE4_PARAMS = dict(sigma=0.25, nu=2.0, theta=-0.10,
                                        tau=0.25, S=100.0, r=0.05, q=0.03)

and assert, in a new `test_term_structure_anchor`:

* **A1** the oracle's VG put prices at the three strikes reproduce the pinned
  literals to `|diff| <= 5e-5` (the published four-decimal precision);
* **A2** the oracle's VG **call** prices at the same strikes do **not** match
  the literals (the call is `≈ 23.84`; the check is that `|call − literal| > 1`),
  so a call/put convention slip cannot pass;
* **A3** the published-wrong row is **rejected**: `|vg_put(K) − VGPS_wrong| >= 0.3`
  at every strike (measured gaps below), so the test distinguishes a right
  anchor from a wrong one — a published wrong answer is a free mutant;
* **A4** parity holds at the anchor's own numbers (`call − put = S e^{−qτ} − K e^{−rτ}`
  to `1e-9`), the oracle's version of T2 at the published parameter set;
* **A5** the VG → GBM corner: with `theta` and `sigma` fixed and `nu → 0`
  (a sequence `nu ∈ {0.2, 0.05, 0.01, 0.002, 0.0004}`), the VG call converges
  to `bs_call(S, K, tau, r, q, sigma)` at the measured rate `err/nu → 2.31`
  (machine-checked structure, no Lean input).

## §2 The falsifier to land (the RED in `docs/02`)

Measure, for two witness parameter sets and the fixed window
`τ ∈ [0.25, 5]` (the window is part of the test's literals, see §3), the ATM
skew `ψ(τ) = ∂σ_BS(k, τ)/∂k` at `k = ln(K/F) = 0` by central difference with
`h = 0.005`, and fit `log|ψ| = A − α_model log τ` by least squares:

| witness set | measured `α_model` | `\|ψ\|·τ` over the window |
|---|---|---|
| VG at the **published** Case-4 parameters (`r = 0.05`, `q = 0.03`) | **1.0857** | `0.263 … 0.341` |
| CGMY `C = 1, G = 5, M = 10, Y = 0.7` (`r = q = 0`) | **0.9682** | `0.0447 … 0.0493` |

Pin the literals `MODEL_SKEW_EXPONENT_BAND = (0.90, 1.15)`,
`MARKET_SKEW_EXPONENT_BAND = (0.30, 0.50)`, the two measured exponents
(`1.0857`, `0.9682`, tolerance `±0.02`), the window `(0.25, 5.0)` and the
quadrature settings, then assert:

* **F1** each measured exponent is in the model band and within `±0.02` of its
  pinned literal (so a mutation of the exponent, the CF or the fit is caught by
  the same test that carries the anchor);
* **F2** the two bands are **disjoint** (`0.90 > 0.50`; the gap is `0.40`),
  which is the RED in machine-checkable form. Widening either band, alone, is a
  visible diff to a literal;
* **F3** `|ψ|·τ` is bounded on the window (measured: both sets lie in
  `[0.04, 0.35]`) — the `1/τ` law — while `|ψ|·√τ` **decreases** by more than a
  factor of `2` across the same window on the CGMY set. That is C19 (the
  correction of F4) as a checkable claim rather than prose: the `τ^(−1/2)` form
  is *not* what the family does;
* **F4** the same exponent band holds at `u_max ∈ {1000, 2000, 4000}` and
  `n ∈ {40000, 80000}` (quadrature-independence; measured below), so the RED is
  not a quadrature artifact.

Then `docs/02_failure_modes.md` gets the verdict in prose, under A1/A2: the
pure exponential-Lévy direction, taken alone, **fails the term-structure
falsifier** — its ATM skew decays like `1/τ` where the market's decays like
`τ^(−0.36..−0.45)`, with disjoint measured bands — and the citation set
(F5) plus the two measured exponents are recorded there verbatim. This is the
"dynamic half" C13 finding 4 demanded, and it is the repository's *own*
statement of what the T6 direction does not buy.

## The numeric route-check (run at issue, per ledger C4)

Scratch script, Python 3 stdlib only, importing the router's existing oracle
(`experiments/black_scholes.py`: `carr_madan_denom`, `cgmy_gamma_neg`,
`bs_call`, `norm_cdf`). Settings: `alpha = 1.5`, `u_max = 2000`,
`n = 80000`, Simpson; `h = 0.005`; implied vol by bisection to `1e-9`.

| check | lands as | result |
|---|---|---|
| VG put at `K = 77` vs published `0.6356` | A1 | `0.635631` → `3.1e-5` |
| VG put at `K = 78` vs published `0.6787` | A1 | `0.678705` → `4.9e-6` |
| VG put at `K = 79` vs published `0.7244` | A1 | `0.724436` → `3.6e-5` |
| VG call at the same strikes vs the same literals | A2 | `23.84495 / 22.90044 / 21.95860`; gap `> 21` |
| published VGPS row vs the computed puts | A3 | gaps `0.3929 / 0.4488 / 0.8140` → rejection at `0.3` |
| parity at the anchor (`K = 77, 78, 79`) | A4 | residual `<= 1e-9` (bisection floor) |
| VG → GB at `nu = 0.2, 0.05, 0.01, 0.002, 0.0004`, `K = 100` | A5 | errors `4.16e-1, 1.13e-1, 2.30e-2, 4.62e-3, 9.25e-4`; `err/nu` `2.08 → 2.31` |
| ATM skew, VG Case-4 set, `τ = 0.25 … 5` | F1/F2 | `−1.33362, −0.68164, −0.32191, −0.14639, −0.05267`; fit `1.0857` |
| ATM skew, CGMY `(1, 5, 10, 0.7)`, `τ = 0.25 … 5` | F1/F2 | `−0.17869, −0.09335, −0.04797, −0.02437, −0.00985`; fit `0.9682` |
| `\|ψ\|·√τ` on the CGMY set | F3 | `0.0893, 0.0660, 0.0480, 0.0345, 0.0220` — strictly decreasing |
| the fit at `(u_max, n) ∈ {1000, 2000, 4000} × {40000, 80000}` | F4 | exponent moves `<= 0.002` |
| **canary**: `k = 0` skew at the GBM instance | — | exponent `≈ 0.5` (the closed-form instance is *not* the falsifier's target; it is the sanity check that the measurement can see a different power law) |
| **mutant**: `C = 1/nu → nu` in the corner map | M26 | anchor prices move by `O(1)`; A1 red |
| **mutant**: exponent `−(τ/ν)log(·) → −τ log(·)` | M27 | anchor and both exponents move; A1/F1 red |
| **mutant**: `ω = (1/ν)log(1 − θν − σ²ν/2) → (1/ν)log(1 + θν + σ²ν/2)` | M28 | martingale normalization fails; A1/A4 red |
| **mutant**: `θ → −θ` in the corner exponent | M29 | anchor prices move by `O(1)`; A1 red |

Two measurements are **recorded and deliberately not pinned**: at `τ <= 1/12`
the skew is `h`-sensitive with a fixed window (`|ψ|` at `τ = 1/52` moves
`−1.096 → −1.586` between `h = 0.02` and `h = 0.005`), and the short-end local
exponent is therefore not a stable literal; the pinned window starts at `0.25`,
where the `h`-sensitivity is `<= 0.2%`. The short end is exactly where the
market's own regime change sits (F5), so a *second* brief could pin it with an
adaptive-`h` scheme — recorded here as the open edge of this one, not as a
claim.

## Grading wiring (the repo changes)

* **`experiments/black_scholes.py`** (additive only; no existing function
  edited):
  * `vg_exponent(sigma, nu, theta, tau, r, q, v)` — the `Y = 0` corner
    exponent (F3), with `1 < M` documented as the numéraire condition;
  * `cgmy_zeroth_corner_map(sigma, nu, theta)` → `(C, G, M)` (F3's algebra),
    so the anchor's parameters and the CGMY corner cannot drift apart;
  * `carr_madan_by_exponent(expf, S, K, tau, r, q, alpha, u_max, n)` — the
    contour quadrature generalized to any exponent callable, written so that
    `bs_call_by_fourier_inversion`'s GBM exponent is an instance of it (the
    derivation-independence rule: the *new* route is the general one, the
    landed route keeps its own `norm_cdf`-free derivation);
  * `implied_vol_bs(price, S, K, tau, r, q, lo=1e-6, hi=5.0)` — bisection on
    `bs_call`;
  * `atm_skew(expf, S, tau, r, q, h)` and
    `power_law_exponent(expf, S, r, q, taus)` — the falsifier's measurement;
  * the pinned literals of §1–§2 live in `tests/`, **not** here: C13's phrase
    is "literal constants in `tests/`", and a constant that the oracle defines
    is not an external check.
* **`tests/test_bs.py`.** One new `test_term_structure_anchor` carrying A1–A5,
  F1–F4 and the `k = 0` GBM canary; the test's docstring names the citation
  (Carr–Madan 1999 §5 Table 1 / Figure 2; El Amrani–Guyon; Gatheral–Jaisson–
  Rosenbaum 2018; Figueroa-López–Forde–Jacquier) and states that the literals
  are quoted from the source, not computed. Count `22 → 23`.
* **`tests/test_mutants.py`.** M26 (C-map), M27 (ν-scaling), M28 (ω sign),
  M29 (θ sign). Each must be killed **by `test_term_structure_anchor` alone**,
  and the harness count `26 → 30`.
* **`scripts/lean_lint.py`: no change.** No Lean module is touched, so no lint
  clause is added; pins stay `268`, the audit list stays `237`, lint mutants
  stay `44 / 5 controls`. The brief records those invariants so the next
  brief's author does not have to guess whether they moved.
* **`docs/02_failure_modes.md`:** the RED of §2, with the citation set and the
  measured exponents. **`docs/03_research.md` §D1:** the falsifier result and
  the C19 correction (a pointer, not a rewrite; §D1's CGMY text keeps its
  landed status). **`docs/04_formal_plan.md`:** the queue row and the
  "still queued" sentence at the end of §D1's landing paragraph.
  **`benchmarks/LEDGER.md`:** the issuance row (this PR) and correction C19.
  **`README.md`:** the harness counts (`22 → 23`, `26 → 30`) and a status-table
  row.

## Done looks like (acceptance, machine-graded)

1. The three published literals (and the VGPS-wrong row) are in `tests/` with
   the citation comment; nothing recomputes them at import time.
2. `python3 tests/test_bs.py` is green with the new test: A1 to `5e-5`, A2
   rejection, A3 rejection at `0.3`, A4 at `1e-9`, A5's rate, F1–F4's bands,
   windows and exponents.
3. `python3 tests/test_mutants.py` is green with M26–M29 each killed by the new
   test alone.
4. `python3 tests/test_lint.py`, `tests/test_pins.py`, `scripts/lean_lint.py`
   and `pin_statements.py --check` are unchanged and green (no Lean, no pins).
5. `docs/02` carries the RED with the citations and the measured numbers;
   `docs/03`/`docs/04`/README/LEDGER are updated; C19 is on record.
6. The `oracle` lane is green on the implementation commit and the `lean` lane
   is green with no diff to any `.lean` file.

## Explicitly out of scope

* **No Lean.** The anchor's subject is the oracle's agreement with a published
  table; there is no theorem to prove and no module to guard. If a later brief
  wants the `Y = 0` corner *proved*, that is the CGMY-law work, not this one.
* **No CGMY law construction.** The VG corner here is a *numerical* object
  (a callable exponent), not a `Measure`. The expectation-level items of the
  kit remain gated, and the feasibility question is its own brief.
* **No market data.** The falsifier compares the model's measured exponent to
  **published fitted exponents**, not to a fitted surface. No calibration, no
  data, no out-of-sample claim.
* **No universality claim.** The pinned band covers the two witness sets and
  the pinned window. "No parameter choice in the family can reach the market's
  `0.3 … 0.5`" is *not* claimed here; the citation (Figueroa-López et al.) gives
  the asymptotic rate `O(τ^(−1))` for the family, and the falsifier's measured
  evidence is what the test pins.
* **No change to `Levy.lean`, `CGMY.lean`, `Skeleton.lean` or any other Lean
  file**; no new lint clause; no workflow change.

## Name-check status (ledger C3)

Python-only: the two external names are the papers (Carr–Madan 1999;
Figueroa-López–Forde–Jacquier; plus El Amrani–Guyon and Gatheral–Jaisson–
Rosenbaum on the market side), and both Carr–Madan and the Figueroa-López et
al. preprint were read at the source in the issuing sandbox. **One transcription
caveat, recorded rather than hidden:** the three published literals were read
from a PDF text extraction whose leading characters are mangled (the extracted
sentence prints `":2425"` and `":6356"`), so the implementer must **verify the
three values against the paper's rendering before pinning them**. The
identification is not in doubt — the computed puts match the candidate row to
four decimals (`0.635631 / 0.678705 / 0.724436`) and fail the VGPS row by
`0.39 … 0.81` — but the brief pins what the paper says, and "what the paper
says" has to be read off the paper.
