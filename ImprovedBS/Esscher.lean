/-
  ImprovedBS/Esscher.lean — BRIEF_013: the Esscher drift (BSM-2 kit item 3),
  the named pricing measure at CGMY, landed at the characteristic-factor level.

  What this file proves, in one line:

    the Esscher tilt ψ^θ(v) = ψ(v − iθ) − ψ(−iθ) stays INSIDE the CGMY family
    (it is the same exponent at shifted tempering rates (G+θ, M−θ)), the drift
    g(θ) = κ(θ+1) − κ(θ) it delivers is strictly monotone with exactly one zero
    θ₀ = (M−G−1)/2, and the strip decides solvability of the martingale
    equation g(θ) = r − q:                        -- esscher_exists_unique_of_mem_range
    exactly one θ ∈ (−G, M−1) when |r−q| < H, none when |r−q| ≥ H, where
    H = |CΓ(−Y)|·|(G+M)^Y − (G+M−1)^Y − 1| is a function of (C, Y, G+M) alone.

  BRIEF_012 proved the requirement this brief answers: the static skeleton
  does not select the measure, so a named measure is the most any drift
  condition can deliver. This is that name, at CGMY, as a theorem — the
  intra-family uniqueness half of ledger C13 finding 2, which BRIEF_012 needed
  true in order to rule out intra-family witnesses.

  Re-scope (honesty item, BRIEF_013 §"Re-scope note"). The tree has no CGMY
  law as a `Measure ℝ` — BRIEF_011 landed the exponent and the Lévy density,
  with the Lévy–Khintchine representation itself labelled prose. So item 3's
  drift condition is landed at the level the tree can carry: the factor
  identity `esscher_drift_factor`,
  `cgmyCharFactor C (G+θ*) (M−θ*) Y τ (−I) = exp(τ(r−q))`, which IS
  `E^{θ*}[e^{X_τ}] = e^{(r−q)τ}` once the factor is read as the tilted law's
  transform. The expectation-level twin of `integral_spot_mul_phi_eq_forward`
  is gated on a law construction and is explicitly out of scope.

  The numeric contract (fixed by the brief, asserted by
  tests/test_bs.py::test_esscher_drift at the same numbers before the Lean
  landed — ledger C4): four witness sets at τ = 1 (bisection, 200 steps):

    A (1, 5, 10, 0.7), r−q = 0.05:  θ* = 2.381041,  H = 2.932381
    B (1, 2, 8, 1.5),  r−q = 0.05:  θ* = 2.531499,  H = 8.561606
    C (0.5, 0.05, 1, 0.3), r−q = 0.05: θ* = −0.021865, H = 0.848811
    D (1, 0.5, 3, 1.9), r−q = 0.05: θ* = 0.752775,  H = 22.837027

  Exact anchors the tests carry tolerance-free: g(θ₀) = 0 at θ₀ = (M−G−1)/2
  (set A: θ₀ = 2), the antisymmetry g(θ₀+t) = −g(θ₀−t) (a corollary of
  `esscherDriftMap_reflect`), and the H closed form above. Canaries: an
  out-of-range target (no solution, asserted rejected), an empty admissible
  interval (G + M ≤ 1), and the strong tilt at which the TILTED contour
  condition `α + 1 < M − θ*` starts to bind.

  Route discipline. No new analysis beyond calculus on the real section
  `cgmyExponent_strip` opens: the shift is term algebra (`push_cast; ring`),
  convexity is a second derivative rewritten by `Real.Gamma_add_one` into the
  positive curvature constant `Γ(2−Y)`, monotonicity is
  `strictMonoOn_of_deriv_pos`, existence is `intermediate_value_Ioo` on the
  closed strip. The pricing line is CONSUMED, not rebuilt:
  `esscher_cmPriceKernel_integrable` is BRIEF_011's
  `cgmy_cmPriceKernel_integrable` at the shifted rates with the tilted
  condition `α + 1 < M − θ` (C14 at (G+θ, M−θ): `G+θ` does not constrain the
  line), and `esscher_correction_invariant` records why the decay survives the
  tilt: `r` carries only (C, Y), `c'` only (C, Y, G+M), both tilt-invariant.
-/
import Mathlib
import ImprovedBS.CGMY

noncomputable section

namespace BSM

open MeasureTheory Filter Set
open scoped Topology

/-! ## §1 the Esscher shift — algebra on BRIEF_011 -/

/-- The Esscher tilt of a characteristic exponent: `ψ^θ(v) = ψ(v − iθ) − ψ(−iθ)`,
defined for a GENERAL `ψ` by the shift — so the CGMY closure below is a theorem
relating two independent expressions, not a definitional tautology (the C1
failure mode; the `[ESSCHER]` check guards the body). -/
def esscherExponent (ψ : ℂ → ℂ) (θ : ℝ) (v : ℂ) : ℂ :=
  ψ (v - (θ : ℂ) * Complex.I) - ψ (-(θ : ℂ) * Complex.I)

/-- The CGMY exponent vanishes at the origin: both bases evaluate to their
subtracted real powers. -/
theorem cgmyExponent_zero (C G M Y : ℝ) : cgmyExponent C G M Y 0 = 0 := by
  unfold cgmyExponent
  simp only [mul_zero, sub_zero]
  ring

/-- The Esscher shift of the CGMY exponent stays inside the family: the tilt
just moves the tempering rates, `(G, M) ↦ (G+θ, M−θ)`. This is the whole
algebraic content of the Esscher transform for CGMY — term algebra on the two
bases, no branch hypothesis needed. -/
theorem esscher_cgmy_shift (C G M Y θ : ℝ) :
    esscherExponent (cgmyExponent C G M Y) θ =
      cgmyExponent C (G + θ) (M - θ) Y := by
  funext v
  unfold esscherExponent cgmyExponent
  have hL : (M : ℂ) - Complex.I * (v - (θ : ℂ) * Complex.I) =
      ((M - θ : ℝ) : ℂ) - Complex.I * v := by
    rw [mul_sub, ← mul_assoc, mul_comm Complex.I (θ : ℂ), mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  have hR : (G : ℂ) + Complex.I * (v - (θ : ℂ) * Complex.I) =
      ((G + θ : ℝ) : ℂ) + Complex.I * v := by
    rw [mul_sub, ← mul_assoc, mul_comm Complex.I (θ : ℂ), mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  have hL0 : (M : ℂ) - Complex.I * (-(θ : ℂ) * Complex.I) = ((M - θ : ℝ) : ℂ) := by
    rw [neg_mul, mul_neg, ← mul_assoc, mul_comm Complex.I (θ : ℂ), mul_assoc,
      Complex.I_mul_I]
    push_cast
    ring
  have hR0 : (G : ℂ) + Complex.I * (-(θ : ℂ) * Complex.I) = ((G + θ : ℝ) : ℂ) := by
    rw [neg_mul, mul_neg, ← mul_assoc, mul_comm Complex.I (θ : ℂ), mul_assoc,
      Complex.I_mul_I]
    push_cast
    ring
  rw [hL, hR, hL0, hR0]
  ring

/-- The tilt factorization: `e^{τψ(v−iθ)} = e^{τψ^θ(v)} · e^{τψ(−iθ)}` — the
discount-free change of numéraire at the factor level, before any measure is
named. -/
theorem esscher_tilt_factorization (C G M Y τ θ : ℝ) (v : ℂ) :
    cgmyCharFactor C G M Y τ (v - (θ : ℂ) * Complex.I) =
      cgmyCharFactor C (G + θ) (M - θ) Y τ v *
        cgmyCharFactor C G M Y τ (-(θ : ℂ) * Complex.I) := by
  simp only [cgmyCharFactor]
  have hψ : cgmyExponent C G M Y (v - (θ : ℂ) * Complex.I) =
      cgmyExponent C (G + θ) (M - θ) Y v +
        cgmyExponent C G M Y (-(θ : ℂ) * Complex.I) := by
    have := congr_fun (esscher_cgmy_shift C G M Y θ) v
    unfold esscherExponent at this
    rw [← this]
    ring
  rw [hψ, mul_add, Complex.exp_add]

/-! ## §2 the cumulant and its strict convexity — real analysis on the strip -/

/-- The cumulant `κ(u) := ψ(−iu)` on the real section of the strip: BRIEF_011's
`cgmyExponent_strip` says this is the real value the exponent takes on
`v = −iu`, `u ∈ (−G, M)` — the closed form of `log E[e^{uX_τ}]/τ`. -/
def cgmyCumulant (C G M Y u : ℝ) : ℝ :=
  C * Real.Gamma (-Y) * ((M - u) ^ Y - M ^ Y + (G + u) ^ Y - G ^ Y)

/-- The cumulant is the exponent on the strip, cited from BRIEF_011 — not
re-proved. -/
theorem cgmyCumulant_eq_strip (C G M Y u : ℝ) (hG : 0 < G) (hM : 0 < M) (h₁ : -G < u)
    (h₂ : u < M) :
    cgmyExponent C G M Y (-(Complex.I * (u : ℂ))) =
      ((cgmyCumulant C G M Y u : ℝ) : ℂ) := by
  rw [cgmyExponent_strip C G M Y u hG hM h₁ h₂, cgmyCumulant]

/-- `κ` is continuous on the CLOSED strip `[−G, M]`: both rpow bases are
nonnegative there, and `x ↦ x^Y` is continuous at `0` for `0 < Y`
(`0^Y = 0`). This is the continuity the IVT below runs on. -/
theorem cgmyCumulant_continuousOn (C G M Y : ℝ) (hY : 0 < Y) :
    ContinuousOn (cgmyCumulant C G M Y) (Icc (-G) M) := by
  unfold cgmyCumulant
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const continuousOn_const)
    (ContinuousOn.sub (ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_) ?_)
  · exact (continuousOn_const.sub continuousOn_id).rpow_const fun u _ => Or.inr hY.le
  · exact continuousOn_const.rpow_const fun u _ => Or.inr hY.le
  · exact (continuousOn_const.add continuousOn_id).rpow_const fun u _ => Or.inr hY.le
  · exact continuousOn_const.rpow_const fun u _ => Or.inr hY.le

/-- The first derivative of the cumulant on the OPEN strip: both bases are
strictly positive there, so real `rpow` is differentiable with no case split. -/
theorem cgmyCumulant_hasDerivAt (C G M Y u : ℝ) (h₁ : -G < u) (h₂ : u < M) :
    HasDerivAt (cgmyCumulant C G M Y)
      (C * Real.Gamma (-Y) * Y * ((G + u) ^ (Y - 1) - (M - u) ^ (Y - 1))) u := by
  unfold cgmyCumulant
  have hMu : M - u ≠ 0 := by linarith
  have hGu : G + u ≠ 0 := by linarith
  have hdM : HasDerivAt (fun u => (M - u) ^ Y) (-Y * (M - u) ^ (Y - 1)) u := by
    have hdu : HasDerivAt (fun x => M - x) (-1) u := by
      simpa using (hasDerivAt_const u M).sub (hasDerivAt_id u)
    convert (Real.hasDerivAt_rpow_const (h := Or.inl hMu) (p := Y)).comp u hdu using 1
    ring
  have hdG : HasDerivAt (fun u => (G + u) ^ Y) (Y * (G + u) ^ (Y - 1)) u := by
    have hgu : HasDerivAt (fun x => G + x) 1 u := by
      simpa using (hasDerivAt_const u G).add (hasDerivAt_id u)
    convert (Real.hasDerivAt_rpow_const (h := Or.inl hGu) (p := Y)).comp u hgu using 1
    ring
  have hdB : HasDerivAt (fun u => (M - u) ^ Y - M ^ Y + (G + u) ^ Y - G ^ Y)
      (-Y * (M - u) ^ (Y - 1) - 0 + Y * (G + u) ^ (Y - 1) - 0) u :=
    ((hdM.sub (hasDerivAt_const u (M ^ Y))).add hdG).sub (hasDerivAt_const u (G ^ Y))
  convert (hasDerivAt_const u (C * Real.Gamma (-Y))).mul hdB using 1
  ring

/-- The Γ rewrite the curvature needs: `Γ(−Y)·Y·(Y−1) = Γ(2−Y)`, two
`Real.Gamma_add_one` steps. `2−Y > 0` keeps the positivity argument one line,
with no case split on `Y ≷ 1` (the pole at `Y = 1` is excluded as everywhere
in BRIEF_011). -/
theorem cgmyGamma_two_sub_eq (Y : ℝ) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    Real.Gamma (-Y) * Y * (Y - 1) = Real.Gamma (2 - Y) := by
  have hne : 1 - Y ≠ 0 := by
    intro h
    apply hY₁
    linarith
  have hstep1 : Real.Gamma (1 - Y) = -Y * Real.Gamma (-Y) := by
    rw [show (1 : ℝ) - Y = -Y + 1 by ring]
    exact Real.Gamma_add_one (by linarith : -Y ≠ 0)
  have hstep2 : Real.Gamma (2 - Y) = (1 - Y) * Real.Gamma (1 - Y) := by
    rw [show (2 : ℝ) - Y = 1 - Y + 1 by ring]
    exact Real.Gamma_add_one hne
  rw [hstep2, hstep1]
  ring

/-- The second derivative of the cumulant: the `Γ(−Y)·Y(Y−1)` prefactor is
`Γ(2−Y)` by the rewrite above, so the curvature constant is positive for
`Y ∈ (0,2)` in one line. -/
theorem cgmyCumulant_hasDerivAt2 (C G M Y u : ℝ) (h₁ : -G < u) (h₂ : u < M)
    (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    HasDerivAt (deriv (cgmyCumulant C G M Y))
      (C * Real.Gamma (2 - Y) * ((M - u) ^ (Y - 2) + (G + u) ^ (Y - 2))) u := by
  have hMu : M - u ≠ 0 := by linarith
  have hGu : G + u ≠ 0 := by linarith
  have hdG : HasDerivAt (fun u => (G + u) ^ (Y - 1)) ((Y - 1) * (G + u) ^ (Y - 2)) u := by
    have hgu : HasDerivAt (fun x => G + x) 1 u := by
      simpa using (hasDerivAt_const u G).add (hasDerivAt_id u)
    convert (Real.hasDerivAt_rpow_const (h := Or.inl hGu) (p := Y - 1)).comp u hgu using 1
    ring
  have hdM : HasDerivAt (fun u => (M - u) ^ (Y - 1)) (-(Y - 1) * (M - u) ^ (Y - 2)) u := by
    have hdu : HasDerivAt (fun x => M - x) (-1) u := by
      simpa using (hasDerivAt_const u M).sub (hasDerivAt_id u)
    convert (Real.hasDerivAt_rpow_const (h := Or.inl hMu) (p := Y - 1)).comp u hdu using 1
    ring
  have hexpr : HasDerivAt
      (fun u => C * Real.Gamma (-Y) * Y * ((G + u) ^ (Y - 1) - (M - u) ^ (Y - 1)))
      (C * Real.Gamma (-Y) * Y *
        ((Y - 1) * (G + u) ^ (Y - 2) + (Y - 1) * (M - u) ^ (Y - 2))) u := by
    have hdB : HasDerivAt (fun u => (G + u) ^ (Y - 1) - (M - u) ^ (Y - 1))
        ((Y - 1) * (G + u) ^ (Y - 2) - (-(Y - 1) * (M - u) ^ (Y - 2))) u :=
      hdG.sub hdM
    convert (hasDerivAt_const u (C * Real.Gamma (-Y) * Y)).mul hdB using 1
    ring
  have hκ : (fun x => deriv (cgmyCumulant C G M Y) x) =ᶠ[𝓝 u]
      fun x => C * Real.Gamma (-Y) * Y * ((G + x) ^ (Y - 1) - (M - x) ^ (Y - 1)) := by
    filter_upwards [Ioo_mem_nhds h₁ h₂] with x hx
    exact (cgmyCumulant_hasDerivAt C G M Y x hx.1 hx.2).deriv
  have hfinal : HasDerivAt (deriv (cgmyCumulant C G M Y))
      (C * Real.Gamma (-Y) * Y * (Y - 1) *
        ((M - u) ^ (Y - 2) + (G + u) ^ (Y - 2))) u := by
    convert hexpr.congr_of_eventuallyEq hκ using 1
    ring
  convert hfinal using 1
  rw [← cgmyGamma_two_sub_eq Y hY hY₂ hY₁]
  ring

/-- The second derivative is strictly positive on the open strip:
`Γ(2−Y) > 0` for `Y ∈ (0,2)`, and both rpow bases are positive there. -/
theorem cgmyCumulant_second_deriv_pos (C G M Y u : ℝ) (hC : 0 < C) (h₁ : -G < u)
    (h₂ : u < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    0 < deriv (deriv (cgmyCumulant C G M Y)) u := by
  rw [(cgmyCumulant_hasDerivAt2 C G M Y u h₁ h₂ hY hY₂ hY₁).deriv]
  refine mul_pos (mul_pos hC (Real.Gamma_pos_of_pos (by linarith))) (add_pos ?_ ?_)
  · exact Real.rpow_pos_of_pos (by linarith) (Y - 2)
  · exact Real.rpow_pos_of_pos (by linarith) (Y - 2)

/-- `κ'` is strictly increasing on the strip: the derivative of `κ'` is
`κ'' > 0` (§2 above), and `strictMonoOn_of_deriv_pos` turns that into strict
monotonicity. This is the intra-family uniqueness engine of ledger C13
finding 2. -/
theorem cgmyCumulant_deriv_strictMono (C G M Y : ℝ) (hC : 0 < C) (hY : 0 < Y)
    (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    StrictMonoOn (deriv (cgmyCumulant C G M Y)) (Ioo (-G) M) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo (-G) M) ?cont ?pos
  · intro x hx
    have hd := cgmyCumulant_hasDerivAt2 C G M Y x hx.1 hx.2 hY hY₂ hY₁
    exact hd.differentiableAt.continuousAt.continuousWithinAt
  · intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    exact cgmyCumulant_second_deriv_pos C G M Y x hC hx.1 hx.2 hY hY₂ hY₁

/-- The cumulant is strictly convex on the strip: positive second derivative,
packaged for the record (the drift map's strict monotonicity below consumes
the derivative's strict monotonicity directly). -/
theorem cgmyCumulant_strictConvex (C G M Y : ℝ) (hC : 0 < C) (hY : 0 < Y)
    (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    StrictConvexOn ℝ (Ioo (-G) M) (cgmyCumulant C G M Y) := by
  have hcont : ContinuousOn (cgmyCumulant C G M Y) (Ioo (-G) M) :=
    (cgmyCumulant_continuousOn C G M Y hY).mono Ioo_subset_Icc_self
  have hsm : StrictMonoOn (deriv (cgmyCumulant C G M Y)) (interior (Ioo (-G) M)) := by
    rw [isOpen_Ioo.interior_eq]
    exact cgmyCumulant_deriv_strictMono C G M Y hC hY hY₂ hY₁
  exact hsm.strictConvexOn_of_deriv (convex_Ioo (-G) M) hcont

/-! ## §3 the Esscher equation, and the strip decides solvability -/

/-- The drift the tilt at `θ` delivers: `g(θ) = κ(θ+1) − κ(θ)`. The martingale
condition is `g(θ) = r − q`; admissibility is `θ ∈ (−G, M−1)` (both `θ` and
`θ+1` in the strip), nonempty exactly when `1 < G + M`. -/
def esscherDriftMap (C G M Y θ : ℝ) : ℝ :=
  cgmyCumulant C G M Y (θ + 1) - cgmyCumulant C G M Y θ

/-- The zero-drift Esscher parameter: `(M−G−1)/2`, independent of `Y` — the
fixed point of the reflection below. -/
def esscherThetaZero (G M : ℝ) : ℝ := (M - G - 1) / 2

/-- The half-width `H` of the attainable drift interval: a function of
`(C, Y, G+M)` alone. The closed form IS the specification (the `[ESSCHER]`
check guards the body). -/
def esscherDriftBound (C G M Y : ℝ) : ℝ :=
  |C * Real.Gamma (-Y)| * |(G + M) ^ Y - (G + M - 1) ^ Y - 1|

/-- Antisymmetry of the drift map about `θ₀ = (M−G−1)/2`: writing
`x = M − θ`, `s = G + M`, the map is
`CΓ(−Y)[(x−1)^Y + (s−x+1)^Y − x^Y − (s−x)^Y]`, and `x ↦ s+1−x` swaps the
bracket's halves and negates it. `ring` on rpow terms after the arguments are
put in normal form. -/
theorem esscherDriftMap_reflect (C G M Y θ : ℝ) :
    esscherDriftMap C G M Y (M - G - 1 - θ) = - esscherDriftMap C G M Y θ := by
  unfold esscherDriftMap cgmyCumulant
  have h₁ : M - (M - G - 1 - θ + 1) = G + θ := by ring
  have h₂ : M - (M - G - 1 - θ) = G + θ + 1 := by ring
  have h₃ : G + (M - G - 1 - θ + 1) = M - θ := by ring
  have h₄ : G + (M - G - 1 - θ) = M - θ - 1 := by ring
  rw [h₁, h₂, h₃, h₄]
  ring

/-- The zero-drift Esscher parameter delivers drift exactly `0`: it is the
fixed point of the reflection, and a real number equal to its own negative is
zero. Independent of `Y`. -/
theorem esscherDriftMap_zero (C G M Y : ℝ) :
    esscherDriftMap C G M Y (esscherThetaZero G M) = 0 := by
  have hfix : M - G - 1 - esscherThetaZero G M = esscherThetaZero G M := by
    unfold esscherThetaZero
    ring
  have hr := esscherDriftMap_reflect C G M Y (esscherThetaZero G M)
  rw [hfix] at hr
  linarith

/-- `g` is continuous on the closed admissible interval: `κ` is continuous on
the closed strip (§2), and both `θ ↦ θ` and `θ ↦ θ+1` carry
`[−G, M−1]` into it. -/
private theorem esscherDriftMap_continuousOn (C G M Y : ℝ) (hY : 0 < Y) :
    ContinuousOn (esscherDriftMap C G M Y) (Icc (-G) (M - 1)) := by
  unfold esscherDriftMap
  have hκ : ContinuousOn (cgmyCumulant C G M Y) (Icc (-G) M) :=
    cgmyCumulant_continuousOn C G M Y hY
  refine (hκ.comp (continuousOn_id.add continuousOn_const) ?_).sub
    (hκ.comp continuousOn_id ?_)
  · intro θ hθ
    simp only [Pi.add_apply, id_eq]
    constructor
    · linarith [hθ.1]
    · linarith [hθ.2]
  · intro θ hθ
    simp only [id_eq]
    exact ⟨hθ.1, by linarith [hθ.2]⟩

/-- The drift map is strictly increasing on the WHOLE closed admissible
interval `[−G, M−1]`: its derivative is `κ'(θ+1) − κ'(θ) > 0` because `κ'` is
strictly increasing (§2), and `strictMonoOn_of_deriv_pos` on the closed
interval gives the boundary comparisons downstream for free. -/
theorem esscherDriftMap_strictMono (C G M Y : ℝ) (hC : 0 < C) (hY : 0 < Y)
    (hY₂ : Y < 2) (hY₁ : Y ≠ 1) :
    StrictMonoOn (esscherDriftMap C G M Y) (Icc (-G) (M - 1)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc (-G) (M - 1))
    (esscherDriftMap_continuousOn C G M Y hY) ?_
  intro θ
  rw [interior_Icc]
  intro hθ
  have hκθ := cgmyCumulant_hasDerivAt C G M Y θ hθ.1 (by linarith [hθ.2])
  have hκ1 :=
    cgmyCumulant_hasDerivAt C G M Y (θ + 1) (by linarith [hθ.1]) (by linarith [hθ.2])
  have hinner : HasDerivAt (fun θ => θ + 1) 1 θ := by
    have h : HasDerivAt (fun θ => θ + 1) (1 + 0) θ :=
      ((hasDerivAt_id θ).add (hasDerivAt_const θ (1 : ℝ))).congr_of_eventuallyEq (by
        filter_upwards with x
        simp only [Pi.add_apply, id_eq])
    convert h using 1
    ring
  have h1 : HasDerivAt (fun θ => cgmyCumulant C G M Y (θ + 1))
      (deriv (cgmyCumulant C G M Y) (θ + 1)) θ := by
    rw [hκ1.deriv]
    convert hκ1.comp θ hinner using 1
    ring
  have h2 : HasDerivAt (fun θ => cgmyCumulant C G M Y θ)
      (deriv (cgmyCumulant C G M Y) θ) θ := by
    rw [hκθ.deriv]
    exact hκθ
  have hg : HasDerivAt (fun θ => cgmyCumulant C G M Y (θ + 1) - cgmyCumulant C G M Y θ)
      (deriv (cgmyCumulant C G M Y) (θ + 1) - deriv (cgmyCumulant C G M Y) θ) θ :=
    h1.sub h2
  unfold esscherDriftMap
  rw [hg.deriv]
  have hsm := cgmyCumulant_deriv_strictMono C G M Y hC hY hY₂ hY₁
  have hin : θ ∈ Ioo (-G) M := ⟨hθ.1, by linarith [hθ.2]⟩
  have hin1 : θ + 1 ∈ Ioo (-G) M := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  exact sub_pos.mpr (hsm hin hin1 (by linarith))

/-- The right edge of the admissible interval delivers POSITIVE drift: `θ₀` is
the unique zero (§3), the map is strictly increasing, and `θ₀ < M − 1` is
exactly `1 < G + M`. -/
private theorem esscherDriftMap_pos_at_right_edge (C G M Y : ℝ) (hC : 0 < C)
    (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hGM : 1 < G + M) :
    0 < esscherDriftMap C G M Y (M - 1) := by
  have hsm := esscherDriftMap_strictMono C G M Y hC hY hY₂ hY₁
  rw [← esscherDriftMap_zero C G M Y]
  apply hsm
  · unfold esscherThetaZero
    constructor <;> linarith
  · exact ⟨by linarith, le_refl _⟩
  · unfold esscherThetaZero
    linarith

/-- The attainable drift interval is the symmetric `(−H, H)`: the two edge
values of `g` are `±H`, with `H` of §"§3". The right edge is the closed form
(algebra plus `0^Y = 0`, `1^Y = 1`), positive by the previous lemma; the left
edge is its negative by the reflection. -/
theorem esscherDriftMap_bound_eq (C G M Y : ℝ) (hC : 0 < C) (hY : 0 < Y) (hY₂ : Y < 2)
    (hY₁ : Y ≠ 1) (hGM : 1 < G + M) :
    esscherDriftMap C G M Y (-G) = - esscherDriftBound C G M Y ∧
      esscherDriftMap C G M Y (M - 1) = esscherDriftBound C G M Y := by
  have hpos := esscherDriftMap_pos_at_right_edge C G M Y hC hY hY₂ hY₁ hGM
  have hgeq : esscherDriftMap C G M Y (M - 1) =
      C * Real.Gamma (-Y) * ((G + M) ^ Y - (G + M - 1) ^ Y - 1) := by
    unfold esscherDriftMap cgmyCumulant
    have hM0 : M - (M - 1 + 1) = 0 := by ring
    have hM1 : M - (M - 1) = 1 := by ring
    have hG1 : G + (M - 1) = G + M - 1 := by ring
    have hG0 : G + (M - 1 + 1) = G + M := by ring
    rw [hM0, Real.zero_rpow hY.ne', hM1, Real.one_rpow, hG1, hG0]
    ring
  have hright : esscherDriftMap C G M Y (M - 1) = esscherDriftBound C G M Y := by
    rw [hgeq, esscherDriftBound, ← abs_mul]
    exact (abs_of_pos (by rwa [← hgeq])).symm
  have hreflect := esscherDriftMap_reflect C G M Y (M - 1)
  have hfix : M - G - 1 - (M - 1) = -G := by ring
  rw [hfix] at hreflect
  exact ⟨by rw [hreflect, hright], hright⟩

/-- `H > 0` in the theorem range: the right edge value is positive
(strict monotonicity from the zero `θ₀`), and it IS `H`. -/
theorem esscherDriftBound_pos (C G M Y : ℝ) (hC : 0 < C) (hY : 0 < Y) (hY₂ : Y < 2)
    (hY₁ : Y ≠ 1) (hGM : 1 < G + M) :
    0 < esscherDriftBound C G M Y := by
  rw [← (esscherDriftMap_bound_eq C G M Y hC hY hY₂ hY₁ hGM).2]
  exact esscherDriftMap_pos_at_right_edge C G M Y hC hY hY₂ hY₁ hGM

/-- Inside the admissible interval the values of `g` stay STRICTLY inside the
edge values: strict monotonicity on the closed interval, applied at the
endpoints. -/
theorem esscherDriftMap_mem_range (C G M Y θ : ℝ) (hC : 0 < C) (hY : 0 < Y)
    (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hGM : 1 < G + M)
    (hθ : θ ∈ Ioo (-G) (M - 1)) :
    - esscherDriftBound C G M Y < esscherDriftMap C G M Y θ ∧
      esscherDriftMap C G M Y θ < esscherDriftBound C G M Y := by
  have hsm := esscherDriftMap_strictMono C G M Y hC hY hY₂ hY₁
  have hbe := esscherDriftMap_bound_eq C G M Y hC hY hY₂ hY₁ hGM
  have hlo : -G ∈ Icc (-G) (M - 1) := ⟨le_refl _, by linarith⟩
  have hhi : M - 1 ∈ Icc (-G) (M - 1) := ⟨by linarith, le_refl _⟩
  have hθ' : θ ∈ Icc (-G) (M - 1) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  constructor
  · rw [← hbe.1]
    exact hsm hlo hθ' hθ.1
  · rw [← hbe.2]
    exact hsm hθ' hhi hθ.2

/-- THE STRIP DECIDES SOLVABILITY, positive half: when the target drift lies
strictly inside the edge values `|r−q| < H`, there is EXACTLY ONE admissible
Esscher parameter. Existence is the IVT on the continuous extension of `g` to
the closed interval (`intermediate_value_Ioo` lands the witness in the open
one directly); uniqueness is strict monotonicity. `1 < G + M` is exactly the
nonemptiness of the admissible interval — `G = 0.3, M = 0.5` is the canary. -/
theorem esscher_exists_unique_of_mem_range (C G M Y r q : ℝ) (hC : 0 < C)
    (hG : 0 < G) (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1)
    (hGM : 1 < G + M) (hd : |r - q| < esscherDriftBound C G M Y) :
    ∃! θ : ℝ, θ ∈ Ioo (-G) (M - 1) ∧ esscherDriftMap C G M Y θ = r - q := by
  have hab : -G < M - 1 := by linarith
  have hbe := esscherDriftMap_bound_eq C G M Y hC hY hY₂ hY₁ hGM
  have hmem : r - q ∈
      Ioo (esscherDriftMap C G M Y (-G)) (esscherDriftMap C G M Y (M - 1)) := by
    rw [hbe.1, hbe.2]
    exact abs_lt.mp hd
  obtain ⟨θ, hθI, hθ⟩ :=
    (intermediate_value_Ioo hab.le (esscherDriftMap_continuousOn C G M Y hY)) hmem
  refine ⟨θ, ⟨hθI, hθ⟩, ?_⟩
  intro θ' ⟨hθ'I, hθ'⟩
  have hsm := esscherDriftMap_strictMono C G M Y hC hY hY₂ hY₁
  rcases lt_trichotomy θ' θ with hlt | rfl | hlt
  · exfalso
    have := hsm ⟨le_of_lt hθ'I.1, le_of_lt hθ'I.2⟩ ⟨le_of_lt hθI.1, le_of_lt hθI.2⟩ hlt
    linarith [hθ, hθ']
  · rfl
  · exfalso
    have := hsm ⟨le_of_lt hθI.1, le_of_lt hθI.2⟩ ⟨le_of_lt hθ'I.1, le_of_lt hθ'I.2⟩ hlt
    linarith [hθ, hθ']

/-- THE STRIP DECIDES SOLVABILITY, negative half: at and beyond the edge
values there is NO admissible parameter — `mem_range` contraposed. Together
with the positive half: exactly one solution strictly inside `(−H, H)`, none
otherwise. No third case. -/
theorem esscher_no_solution_of_outside_range (C G M Y r q : ℝ) (hC : 0 < C)
    (hG : 0 < G) (hM : 0 < M) (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1)
    (hGM : 1 < G + M) (hd : esscherDriftBound C G M Y ≤ |r - q|) :
    ¬ ∃ θ : ℝ, θ ∈ Ioo (-G) (M - 1) ∧ esscherDriftMap C G M Y θ = r - q := by
  rintro ⟨θ, hθ, heq⟩
  have hmr := esscherDriftMap_mem_range C G M Y θ hC hY hY₂ hY₁ hGM hθ
  rw [heq] at hmr
  have habs : |r - q| < esscherDriftBound C G M Y :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-- The exact zero-drift anchor: `θ₀ = (M−G−1)/2` is the unique admissible
parameter delivering drift `0` (membership of `θ₀` in the admissible interval
is itself equivalent to `1 < G + M`). -/
theorem esscher_theta_zero_unique (C G M Y : ℝ) (hC : 0 < C) (hY : 0 < Y)
    (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hGM : 1 < G + M) :
    esscherThetaZero G M ∈ Ioo (-G) (M - 1) ∧
      (esscherDriftMap C G M Y (esscherThetaZero G M) = 0 ∧
        ∀ θ ∈ Ioo (-G) (M - 1), esscherDriftMap C G M Y θ = 0 →
          θ = esscherThetaZero G M) := by
  have hmem : esscherThetaZero G M ∈ Ioo (-G) (M - 1) := by
    unfold esscherThetaZero
    constructor <;> linarith
  refine ⟨hmem, esscherDriftMap_zero C G M Y, ?_⟩
  intro θ hθ hz
  have hsm := esscherDriftMap_strictMono C G M Y hC hY hY₂ hY₁
  rcases lt_trichotomy θ (esscherThetaZero G M) with hlt | rfl | hlt
  · exfalso
    have := hsm ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩ hlt
    linarith [hz, esscherDriftMap_zero C G M Y]
  · rfl
  · exfalso
    have := hsm ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ hlt
    linarith [hz, esscherDriftMap_zero C G M Y]

/-! ## §4 the drift condition at the named measure -/

/-- The tilted exponent at `v = −i` is exactly the delivered drift, as a real
number: `cgmyExponent_strip` applies twice (`θ` and `θ+1` are both in the
strip), and the difference is `g(θ)`. -/
theorem esscherExponent_neg_I_eq (C G M Y θ : ℝ) (hG : 0 < G) (hM : 0 < M)
    (hθ : θ ∈ Ioo (-G) (M - 1)) :
    esscherExponent (cgmyExponent C G M Y) θ (-Complex.I) =
      ((esscherDriftMap C G M Y θ : ℝ) : ℂ) := by
  unfold esscherExponent
  have h1 : (-Complex.I : ℂ) - (θ : ℂ) * Complex.I =
      -(Complex.I * ((θ + 1 : ℝ) : ℂ)) := by
    push_cast
    ring
  have h0 : -(θ : ℂ) * Complex.I = -(Complex.I * (θ : ℂ)) := by
    rw [neg_mul, mul_comm (θ : ℂ) Complex.I]
  rw [h1, h0,
    cgmyExponent_strip C G M Y (θ + 1) hG hM (by linarith [hθ.1])
      (by linarith [hθ.2]),
    cgmyExponent_strip C G M Y θ hG hM hθ.1 (by linarith [hθ.2])]
  unfold esscherDriftMap cgmyCumulant
  norm_cast

/-- ITEM 3'S DELIVERABLE, at the factor level (re-scope note): the Esscher
parameter `θ` delivering `g(θ) = r − q` makes the TILTED characteristic factor
at `v = −i` exactly `exp(τ(r−q))` — read as `E^{θ}[e^{X_τ}] = e^{(r−q)τ}`, the
CGMY twin of `integral_spot_mul_phi_eq_forward` at the exponent level. -/
theorem esscher_drift_factor (C G M Y τ r q θ : ℝ) (hG : 0 < G) (hM : 0 < M)
    (hθ : θ ∈ Ioo (-G) (M - 1)) (hE : esscherDriftMap C G M Y θ = r - q) :
    cgmyCharFactor C (G + θ) (M - θ) Y τ (-Complex.I) =
      Complex.exp (↑τ * ↑(r - q)) := by
  have hψ : cgmyExponent C (G + θ) (M - θ) Y (-Complex.I) = (↑(r - q) : ℂ) := by
    rw [← congr_fun (esscher_cgmy_shift C G M Y θ) (-Complex.I),
      esscherExponent_neg_I_eq C G M Y θ hG hM hθ, hE]
  unfold cgmyCharFactor
  rw [hψ]

/-- The admissibility of `θ` does double duty: `θ + 1 < M` places the numéraire
point `u = 1` inside the TILTED strip `(-(G+θ), M−θ)` — the drift condition and
the moment condition never separate in this family. -/
theorem esscher_tilted_numeraire (G M θ : ℝ) (hθ : θ ∈ Ioo (-G) (M - 1)) :
    1 < M - θ := by
  linarith [hθ.2]

/-! ## §5 pricing at the Esscher measure — consuming BRIEF_010/011 -/

/-- The subleading decay correction is tilt-invariant: `c'` carries `M + G`,
and `(M−θ) + (G+θ) = M + G`. -/
theorem esscher_correction_invariant (C G M Y θ : ℝ) :
    cgmyTemperedCorrection C (G + θ) (M - θ) Y =
      cgmyTemperedCorrection C G M Y := by
  unfold cgmyTemperedCorrection
  have h : M - θ + (G + θ) = M + G := by ring
  rw [h]

/-- The tilted law plugs straight into BRIEF_011's pricing machine:
`cgmy_cmPriceKernel_integrable` at the shifted rates `(G+θ, M−θ)`, whose own
pricing-line condition is `α + 1 < M − θ` (C14 at shifted rates: `G+θ` does
not constrain the line). Continuity, the decay rate, the correction, the
threshold — all inherited. -/
theorem esscher_cmPriceKernel_integrable (C G M Y τ α θ : ℝ) (hC : 0 < C)
    (hY : 0 < Y) (hY₂ : Y < 2) (hY₁ : Y ≠ 1) (hα : 0 < α) (hτ : 0 < τ)
    (hθ : θ ∈ Ioo (-G) (M - 1)) (hcontour : α + 1 < M - θ) :
    Integrable (cmPriceKernel (cgmyCharFactor C (G + θ) (M - θ) Y τ) α) := by
  refine cgmy_cmPriceKernel_integrable C (G + θ) (M - θ) Y τ α hC ?_ ?_ hY hY₂ hY₁ hα
    hcontour hτ
  · linarith [hθ.1]
  · linarith [hθ.2]

end BSM
