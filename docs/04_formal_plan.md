# 04 — Formal plan: the Lean targets

This directory is the reason the repo is "formal math first."  It states the
claims we commit to proving.  **Nothing here is a finished proof yet** — the
theorem *statements* are a contract for a mathlib-backed Lean 4 environment,
where each will be machine-checked.  On this sandbox (no mathlib cache) the
.lean files are specification, not checked deliverables.

## The theorem stack (order of formal difficulty)

| #  | Statement (lean)          | difficulty | status |
|----|---------------------------|------------|--------|
| T1 | `d1 − d2 = σ√τ`            | trivial (algebra)      | T1 done, T2+T3 done in-code |
| T2 | put-call parity            | rewrite + semiring     | stated |
| T3 | delta-identity: `S e^{−qτ} φ(d1) = K e^{−rτ} φ(d2)` (pairs pdf) | needs `exp` | stated |
| T4 | no-arb bounds              | monotonicity of Φ      | stated |
| T5 | the closed form solves the BSM PDE (heat identity)  | heavy (Mathlib.Log ∘ erf derivatives) | the centerpiece |
| T6 | "generalized kernel": transport / Fourier-integral form survives for α-stable increments | open — this is the research claim | open |

`Φ` and `φ` will come from Mathlib's `StatisticalDistributions` (normal CDF/PDF)
in a mathlib-backed tree. Until then the Lean files keep the statements as
self-contained *synthetic* definitions (so the syntax and claim-shape are
reviewable) with `sorry`s where the analytic content is pending.

## Dependencies / prerequisites (needed from Mathlib)

- `Real.erf` (already in Mathlib: `Mathlib.Analysis.SpecialFunctions.Erf`),
  the normal CDF `Φ(x) := (1 + erf(x/√2))/2`, and its derivative identity
  `d/dx Φ(x) = φ(x) = e^{−x²/2}/√(2π)`.
- Real log/exp/pow and `Ito`-style differential form for the martingale bridge
  (or, minimally, the minimal GBM-increment invariance lemma for T1–T4).

## Formatting the numeric oracle ↔ formal correspondence

The Python oracle and the Lean statements share *notation but not* — in the
current tree — a single auto-generated source. A later milestone: a
`Lean/`-side reflection or a `tests/` property that evaluates `d1,d2,parity`
at integer grid points and checks them against the oracle (a cross-verifier,
not a proof), so the two faithfully contradict each other on any drift.