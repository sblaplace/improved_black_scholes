/-
  Lean 4 formalization — TARGET STATE (syntax check PENDING).

  This file is a *specification contract*, not a finished artifact:
  it requires a mathlib-backed Lean 4 environment (Mathlib.Analysis has
  Real.erf / the normal CDF) that this sandbox does not carry, so the
  declarations are intended as the claims to machine-check, NOT as
  a currently-building Lean library.

  Status convention in this file:
    [SPEC]  = statement is the agreed contract   (from docs/04)
    [TODO]  = proof is intentionally deferred (`sorry`); build goal.
    [BUILT] = would machine-check in a mathlib tree.

  The formal statement of the whole stack lives in docs/04_formal_plan.md.
-/

import Mathlib

-- ------------------------------------------------------------------
-- Notation (keep identical to docs/01 and experiments/).
--   S t : spot, K : strike, tau : T - t > 0, r,q : rates (decimal)
--   sigma : vol; Erf-based normal CDF Phi; pdf phi.
-- ------------------------------------------------------------------

def Phi (x : ℝ) : ℝ := (1 + Real.erf (x / Real.sqrt 2)) / 2

def phi (x : ℝ) : ℝ :=
  (1 / (Real.sqrt (2 * Real.pi))) * Real.exp (-x^2 / 2)

-- d1 does not hit the formula unless ln/exp/pow defined over ℝ in mathlib;
-- state it with the standard real functions.

def d1 (S K tau r q sigma : ℝ) : ℝ :=
  (Real.log (S / K) + (r - q + sigma^2 / 2) * tau) / (sigma * Real.sqrt tau)

def d2 (S K tau r q sigma : ℝ) : ℝ := d1 S K tau r q sigma - sigma * Real.sqrt tau

def bsCall (S K tau r q sigma : ℝ) : ℝ :=
  S * Real.exp (-q * tau) * Phi (d1 S K tau r q sigma)
    - K * Real.exp (-r * tau) * Phi (d2 S K tau r q sigma)

def bsPut (S K tau r q sigma : ℝ) : ℝ :=
  bsCall S K tau r q sigma - S * Real.exp (-q * tau) + K * Real.exp (-r * tau)

/-
  T1 [BUILT-algebra]:  d2 = d1 - sigma sqrt tau, by definition.
-/
theorem t1_d1_minus_d2 (S K tau r q sigma : ℝ) :
  d1 S K tau r q sigma - d2 S K tau r q sigma = sigma * Real.sqrt tau := by
  unfold d2; ring

/-
  T2 [SPEC] Put-call parity.

     bsPut = bsCall - S e^{-q tau} + K e^{-r tau}

  Treated as the *call* theorem below needs Phi replaced by its
  density transitively:
-/
theorem t2_put_call_parity (S K tau r q sigma : ℝ) :
  bsCall S K tau r q sigma + K * Real.exp (-r * tau)
    - S * Real.exp (-q * tau) = bsPut S K tau r q sigma := by
  sorry

/-
  T3 [SPEC] delta-identity between pairs of normal densities —
  the analytic hinge for the greeks + the maringale bridge:
      S e^{-q tau} phi(d1)  =  K e^{-r tau} phi(d2)
-/
theorem t3_delta_identity (S K tau r q sigma : ℝ) (hS : 0 < S) (hK : 0 < K) :
  S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)
    = K * Real.exp (-r * tau) * phi (d2 S K tau r q sigma) := by
  sorry

/-
  T5 [SPEC, centerpiece] The closed form solves the BSM heat identity:
      V_t + (r-q) S V_S + (sigma^2/2) S^2 V_SS  =  r V .
  Needs the differential form of Phi (d/dx Phi = phi) in mathlib.  Declared
  as a contract once the PDE notation (partial/time-derivatives over S,t)
  is in the tree; per docs/04 this is the heavyweight target and is deferred.
-/
--         (to be declared with Mathlib.PDE / HasDerivAt once available)

/-
  T6 [OPEN / research] transport (Fourier-)kernel survives replacing the
  Gaussian increment by an σ-stable one with α∈(1,2]: formal shape found,
  proof and correct condition NOT yet stated (docs/03 D1).
-/
-- (no declaration until t5 lands)