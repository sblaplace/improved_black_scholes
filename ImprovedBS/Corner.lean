/-
  ImprovedBS/Corner.lean — BRIEF_014: the normalized CGMY → GBM corner
  (BSM-2 kit item 6), landed at the characteristic-exponent level.

  What this file proves, in one line:

    at the scale `C_Y = (σ²/2)·(2−Y)` the CGMY exponent converges POINTWISE,
    as `Y → 2⁻` and for every fixed `v` in the strip `−M < Im v < G`, to the
    Gaussian exponent `−(σ²/2)v² + i(σ²/2)(G−M)v`; the algebraic forward
    normalization `Ψ_Y(v) = ψ_Y(v) + i(r−q−κ_Y(1))v` lands that on the
    risk-neutral GBM exponent `i(r−q−σ²/2)v − (σ²/2)v²`, and at the NAMED
    zero-carry Esscher parameter `θ₀ = (M−G−1)/2` the BRIEF_013 family shift
    alone — no drift correction at all — lands it on the zero-carry GBM
    exponent `−(σ²/2)v² − i(σ²/2)v`.

  Why every statement here is a ONE-SIDED LIMIT and not an equality at
  `Y = 2` (ledger C17). `Γ(−Y)` has a pole at `Y = 2`, so at FIXED `C > 0`
  the bracket's finite limit is multiplied by something that diverges: with
  `G = M = 3`, `v = 1`, `Re ψ_Y(1) ~ −C/(2−Y)`. The bare "CGMY → GBM at
  `Y = 2`" statement in the old `docs/03` item 6 is therefore FALSE, and
  evaluating `cgmyExponent ... 2 v` would in any case land on the tag's
  `Real.Gamma (-2) = 0`, i.e. the wrong answer. Everything below is a
  `Filter.Tendsto` on `𝓝[<] 2` — eventually `1 < Y < 2` — and nothing in
  this module evaluates the pole. The alternative printed in the old docs,
  `G, M → σ²/2` at fixed `Y`, is not a GBM limit either: it leaves
  non-quadratic complex powers behind (`tests/test_bs.py::test_gbm_corner`
  measures the failure of the Gaussian ratio `Re ψ(2)/Re ψ(1) = 4` there, and
  asserts it on every oracle run — it is one of the canaries C17 is built on).

  The pole cancellation, which is the whole engine:
  `ε Γ(−Y) = Γ(3−Y)/(Y(Y−1))`, two `Real.Gamma_add_one` steps away from
  BRIEF_013's `cgmyGamma_two_sub_eq` (`Γ(−Y)·Y·(Y−1) = Γ(2−Y)`), so
  `C_Y Γ(−Y) → σ²/4` — finite, and the reason `C_Y` carries the half
  `(σ²/2)` and not `σ²`.

  Two routes, kept deliberately separate (they are different selection
  principles, and route A is NOT an Esscher theorem):

    A. `cornerForwardExponent` adds `i·(r−q−κ_Y(1))·v`, i.e. a deterministic
       linear correction chosen so that `Ψ_Y(−i) = r−q` EXACTLY at every `Y`
       in scope (`cornerForward_numeraire`). It is algebra on BRIEF_011's
       `cgmyExponent_strip`, not a claim that the tree contains a
       risk-neutral CGMY measure.
    B. `cornerEsscherZero_*` consumes BRIEF_013's named selection: at
       `θ₀ = (M−G−1)/2` the shifted rates are `G′ = (G+M−1)/2`,
       `M′ = (G+M+1)/2` with `G′−M′ = −1`, `esscherDriftMap_zero` solves the
       Esscher equation at every `Y` exactly, so the zero-carry GBM limit
       needs no correction.

  Re-scope, as briefed (and as in BRIEF_013). The tree has the CGMY
  exponent and its Lévy density, not a CGMY law as a `Measure ℝ`, so all of
  this is factor-level: a limit of characteristic factors is proved, and no
  weak limit of measures, no convergence of option prices and no
  interchange of the `Y`-limit with the Carr–Madan pricing integral is
  claimed or used. Pointwise convergence at each `v` is not a uniform
  dominating bound on the contour, and (H-decay) at fixed `Y` is not one
  uniform bound as `Y ↑ 2`.
-/
import Mathlib
import ImprovedBS.Fourier
import ImprovedBS.Esscher

noncomputable section

namespace BSM

open MeasureTheory Filter Set
open scoped Topology

/-! ## §1 the variance normalization, and the forward exponent -/

/-- The corner scale `C_Y = (σ²/2)·(2−Y)`: the independent parameter the pole
cancellation runs on. The `σ²/2` is a half-variance, not a choice of
convenience — `C_Y Γ(−Y) → σ²/4`, so the bracket's `−2v²` becomes
`−(σ²/2)v²` and the diffusion variance is `σ²`. The scale `σ²·(2−Y)` would
give twice the variance, and a limit statement that fixed `C` would diverge.
-/
def cgmyCornerC (σ Y : ℝ) : ℝ := (σ ^ 2 / 2) * (2 - Y)

/-- The forward-normalized exponent `Ψ_Y(v) = ψ_Y(v) + i·b_Y·v` with
`b_Y = r − q − κ_Y(1)`: a deterministic linear correction of the CGMY
exponent, defined from the CGMY data alone. It is **not** the GBM formula
(the C1 failure, one level up: a definition that already contained the
answer would make the limit a tautology) and it is **not** an Esscher tilt —
no tilted measure is constructed or claimed here. -/
def cornerForwardExponent (σ G M Y r q : ℝ) (v : ℂ) : ℂ :=
  cgmyExponent (cgmyCornerC σ Y) G M Y v +
    Complex.I * ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) * v

/-- `0 < C_Y` on the punctured interval (`Y < 2`, `σ ≠ 0`): the corner scale
is a genuine intensity for every `Y` the limit runs over, and it degenerates
exactly at the pole. -/
theorem cgmyCornerC_pos (σ Y : ℝ) (hσ : σ ≠ 0) (hY₂ : Y < 2) : 0 < cgmyCornerC σ Y := by
  unfold cgmyCornerC
  exact mul_pos (div_pos (sq_pos_of_ne_zero hσ) (by norm_num)) (by linarith)

/-! ## §2 the pole cancellation: `ε Γ(−Y) = Γ(3−Y)/(Y(Y−1)) → 1/2` -/

/-- The pole cancellation as an exact identity on `1 < Y < 2`. One
`Real.Gamma_add_one` past BRIEF_013's `cgmyGamma_two_sub_eq`
(`Γ(−Y)·Y·(Y−1) = Γ(2−Y)`) turns the diverging `Γ(−Y)` into the harmless
`Γ(3−Y)` and the single factor `2 − Y` that the scale `C_Y` supplies. This
is also the numerically stable route around `sin (πY)` in the oracle's
reflection formula. -/
theorem cgmyCornerGamma_eq (Y : ℝ) (hY₁ : 1 < Y) (hY₂ : Y < 2) :
    (2 - Y) * Real.Gamma (-Y) = Real.Gamma (3 - Y) / (Y * (Y - 1)) := by
  have hYpos : 0 < Y := by linarith
  have hYne : Y ≠ 1 := by linarith
  have hYY : Y * (Y - 1) ≠ 0 := ne_of_gt (mul_pos hYpos (by linarith))
  have htwo : Real.Gamma (2 - Y) = Real.Gamma (-Y) * Y * (Y - 1) :=
    (cgmyGamma_two_sub_eq Y hYpos hY₂ hYne).symm
  have hthree : Real.Gamma (3 - Y) = (2 - Y) * Real.Gamma (2 - Y) := by
    rw [show 3 - Y = (2 - Y) + 1 by ring]
    exact Real.Gamma_add_one (by linarith : 2 - Y ≠ 0)
  rw [hthree, htwo]
  field_simp [hYY]

/-- The finite limit of the normalized pole coefficient: `C_Y Γ(−Y) → σ²/4`.
Not a value of `Γ(−2)` — the limit is taken through `𝓝[<] 2`, i.e. eventually
`1 < Y < 2`, and `Γ` is only ever evaluated at `3 − Y ∈ (1,2)`, where it is
continuous. -/
theorem cgmyCornerGamma_tendsto (σ : ℝ) :
    Tendsto (fun Y : ℝ => cgmyCornerC σ Y * Real.Gamma (-Y)) (𝓝[<] (2 : ℝ))
      (𝓝 (σ ^ 2 / 4)) := by
  have hnear : Ioi (1 : ℝ) ∈ 𝓝[<] (2 : ℝ) :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have heq : (fun Y : ℝ => cgmyCornerC σ Y * Real.Gamma (-Y)) =ᶠ[𝓝[<] (2 : ℝ)]
      fun Y : ℝ => (σ ^ 2 / 2) * (Real.Gamma (3 - Y) / (Y * (Y - 1))) := by
    filter_upwards [hnear, self_mem_nhdsWithin] with Y hY₁ hY₂
    have heps := cgmyCornerGamma_eq Y hY₁ hY₂
    unfold cgmyCornerC
    calc
      ((σ ^ 2 / 2) * (2 - Y)) * Real.Gamma (-Y)
          = (σ ^ 2 / 2) * ((2 - Y) * Real.Gamma (-Y)) := by ring
      _ = (σ ^ 2 / 2) * (Real.Gamma (3 - Y) / (Y * (Y - 1))) := by rw [heps]
  have hΓcont : ContinuousAt Real.Gamma (1 : ℝ) :=
    (Real.differentiableAt_Gamma (s := 1) (by
      intro m hm
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      linarith)).continuousAt
  have hΓ0 : Tendsto (fun Y : ℝ => Real.Gamma (3 - Y)) (𝓝[<] (2 : ℝ))
      (𝓝 (Real.Gamma ((fun Y : ℝ => 3 - Y) (2 : ℝ)))) := by
    have hf : ContinuousAt (fun Y : ℝ => 3 - Y) (2 : ℝ) :=
      continuousAt_const.sub continuousAt_id
    have hg : ContinuousAt Real.Gamma ((fun Y : ℝ => 3 - Y) (2 : ℝ)) := by
      convert hΓcont using 1
      norm_num
    exact (hg.comp hf).continuousWithinAt.tendsto
  have hΓ : Tendsto (fun Y : ℝ => Real.Gamma (3 - Y)) (𝓝[<] (2 : ℝ)) (𝓝 (Real.Gamma 1)) := by
    convert hΓ0 using 1
    norm_num
  have hden0 : Tendsto (fun Y : ℝ => Y * (Y - 1)) (𝓝[<] (2 : ℝ))
      (𝓝 ((fun Y : ℝ => Y * (Y - 1)) (2 : ℝ))) := by
    have hc : ContinuousAt (fun Y : ℝ => Y * (Y - 1)) (2 : ℝ) :=
      continuousAt_id.mul (continuousAt_id.sub continuousAt_const)
    exact hc.continuousWithinAt.tendsto
  have hden : Tendsto (fun Y : ℝ => Y * (Y - 1)) (𝓝[<] (2 : ℝ)) (𝓝 (2 : ℝ)) := by
    convert hden0 using 1
    norm_num
  have hquot : Tendsto (fun Y : ℝ => Real.Gamma (3 - Y) / (Y * (Y - 1))) (𝓝[<] (2 : ℝ))
      (𝓝 (Real.Gamma 1 / 2)) := by
    convert hΓ.div hden (by norm_num : (2 : ℝ) ≠ 0) using 1
  have hlim : Tendsto (fun Y : ℝ => (σ ^ 2 / 2) * (Real.Gamma (3 - Y) / (Y * (Y - 1))))
      (𝓝[<] (2 : ℝ)) (𝓝 ((σ ^ 2 / 2) * (Real.Gamma 1 / 2))) :=
    tendsto_const_nhds.mul hquot
  have hlim' : Tendsto (fun Y : ℝ => (σ ^ 2 / 2) * (Real.Gamma (3 - Y) / (Y * (Y - 1))))
      (𝓝[<] (2 : ℝ)) (𝓝 (σ ^ 2 / 4)) := by
    convert hlim using 1
    rw [Real.Gamma_one]
    ring
  exact Filter.Tendsto.congr' heq.symm hlim'

/-! ## §3 the bracket, and the pointwise exponent limit on the strip -/

/-- `Re (M − iv) = M + Im v`: the positive-tail base's real part, and the
reason the strip condition `−M < Im v` is exactly "the base stays in the open
right half plane" (hence off the branch cut, hence a nonzero base). -/
private theorem corner_base_left_re (M : ℝ) (v : ℂ) :
    ((M : ℂ) - Complex.I * v).re = M + v.im := by
  simp [Complex.sub_re, Complex.mul_re]

/-- `Re (G + iv) = G − Im v`: the negative-tail base's real part, positive
exactly when `Im v < G`. -/
private theorem corner_base_right_re (G : ℝ) (v : ℂ) :
    ((G : ℂ) + Complex.I * v).re = G - v.im := by
  simp [Complex.add_re, Complex.mul_re]
  ring

/-- The bracket `B_Y(v)` tends to `B₂(v) = −2v² + 2i(G−M)v`, pointwise in `v`
on the strip. Each of the four terms is `z ^ (Y : ℂ)` at a FIXED nonzero base
`z` (`Filter.Tendsto.const_cpow`), so only the exponent moves and the limit
is `z²`; the strip hypotheses are what make all four bases nonzero, which is
why the theorem carries them. -/
theorem cgmyBracket_tendsto (G M : ℝ) (hG : 0 < G) (hM : 0 < M) (v : ℂ)
    (hv₁ : -M < v.im) (hv₂ : v.im < G) :
    Tendsto
      (fun Y : ℝ =>
        ((M : ℂ) - Complex.I * v) ^ (Y : ℂ) - (M : ℂ) ^ (Y : ℂ) +
          ((G : ℂ) + Complex.I * v) ^ (Y : ℂ) - (G : ℂ) ^ (Y : ℂ))
      (𝓝[<] (2 : ℝ))
      (𝓝 (-2 * v ^ 2 + 2 * Complex.I * ((G - M : ℝ) : ℂ) * v)) := by
  have hY : Tendsto (fun Y : ℝ => (Y : ℂ)) (𝓝[<] (2 : ℝ)) (𝓝 (2 : ℂ)) := by
    have h : ContinuousAt (fun Y : ℝ => (Y : ℂ)) (2 : ℝ) :=
      Complex.continuous_ofReal.continuousAt
    exact h.continuousWithinAt.tendsto
  have hneL : (M : ℂ) - Complex.I * v ≠ 0 := by
    intro h
    have : M + v.im = 0 := by
      rw [← corner_base_left_re M v, h]
      rfl
    linarith
  have hneR : (G : ℂ) + Complex.I * v ≠ 0 := by
    intro h
    have : G - v.im = 0 := by
      rw [← corner_base_right_re G v, h]
      rfl
    linarith
  have hneM0 : (M : ℂ) ≠ 0 := by
    intro h
    have hr : ((M : ℂ).re) = (0 : ℂ).re := by rw [h]
    simp at hr
    linarith
  have hneG0 : (G : ℂ) ≠ 0 := by
    intro h
    have hr : ((G : ℂ).re) = (0 : ℂ).re := by rw [h]
    simp at hr
    linarith
  have hL : Tendsto (fun Y : ℝ => ((M : ℂ) - Complex.I * v) ^ (Y : ℂ)) (𝓝[<] (2 : ℝ))
      (𝓝 (((M : ℂ) - Complex.I * v) ^ (2 : ℂ))) :=
    Filter.Tendsto.const_cpow hY (Or.inl hneL)
  have hM0 : Tendsto (fun Y : ℝ => (M : ℂ) ^ (Y : ℂ)) (𝓝[<] (2 : ℝ))
      (𝓝 ((M : ℂ) ^ (2 : ℂ))) :=
    Filter.Tendsto.const_cpow hY (Or.inl hneM0)
  have hR : Tendsto (fun Y : ℝ => ((G : ℂ) + Complex.I * v) ^ (Y : ℂ)) (𝓝[<] (2 : ℝ))
      (𝓝 (((G : ℂ) + Complex.I * v) ^ (2 : ℂ))) :=
    Filter.Tendsto.const_cpow hY (Or.inl hneR)
  have hG0 : Tendsto (fun Y : ℝ => (G : ℂ) ^ (Y : ℂ)) (𝓝[<] (2 : ℝ))
      (𝓝 ((G : ℂ) ^ (2 : ℂ))) :=
    Filter.Tendsto.const_cpow hY (Or.inl hneG0)
  have hcomb : Tendsto
      (fun Y : ℝ =>
        ((M : ℂ) - Complex.I * v) ^ (Y : ℂ) - (M : ℂ) ^ (Y : ℂ) +
          ((G : ℂ) + Complex.I * v) ^ (Y : ℂ) - (G : ℂ) ^ (Y : ℂ))
      (𝓝[<] (2 : ℝ))
      (𝓝 (((M : ℂ) - Complex.I * v) ^ (2 : ℂ) - (M : ℂ) ^ (2 : ℂ) +
        ((G : ℂ) + Complex.I * v) ^ (2 : ℂ) - (G : ℂ) ^ (2 : ℂ))) :=
    ((hL.sub hM0).add hR).sub hG0
  convert hcomb using 1
  · simp only [Complex.cpow_two]
    push_cast
    ring_nf
    rw [show (Complex.I : ℂ) ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring

/-- THE UNCORRECTED CORNER (3): `ψ_Y(v) → −(σ²/2)v² + i(σ²/2)(G−M)v`,
pointwise, at the scale `C_Y`. The diffusion variance is `σ²`; the remaining
mean `G − M` is the tempering asymmetry, and it is exactly what the two
routes below remove — algebraically in route A, by the shift in route B.
This is a statement about the exponent at each fixed `v` in the strip, not
about option prices and not a uniform bound on the pricing contour. -/
theorem cgmyCornerExponent_tendsto (σ G M : ℝ) (hG : 0 < G) (hM : 1 < M) (v : ℂ)
    (hv₁ : -M < v.im) (hv₂ : v.im < G) :
    Tendsto (fun Y : ℝ => cgmyExponent (cgmyCornerC σ Y) G M Y v) (𝓝[<] (2 : ℝ))
      (𝓝 (-((σ ^ 2 / 2 : ℝ) : ℂ) * v ^ 2 +
        Complex.I * ((σ ^ 2 / 2 : ℝ) : ℂ) * ((G - M : ℝ) : ℂ) * v)) := by
  have hcoefR := cgmyCornerGamma_tendsto σ
  -- The coefficient crosses into ℂ as the coercion of a REAL product, whereas
  -- `cgmyExponent` carries the split form `↑C_Y * ↑(Γ(−Y))`: `Function.comp_def`
  -- unfolds the transport and `Complex.ofReal_mul` pushes the cast through the
  -- product. Both are needed -- `simpa` alone leaves the composed function alone.
  have hcoef : Tendsto (fun Y : ℝ => (cgmyCornerC σ Y : ℂ) * (Real.Gamma (-Y) : ℂ))
      (𝓝[<] (2 : ℝ)) (𝓝 (((σ ^ 2 / 4 : ℝ) : ℂ))) := by
    have h := (Complex.continuous_ofReal.tendsto (σ ^ 2 / 4)).comp hcoefR
    simpa [Function.comp_def, Complex.ofReal_mul] using h
  have hbr := cgmyBracket_tendsto G M hG (by linarith : 0 < M) v hv₁ hv₂
  have hprod := hcoef.mul hbr
  have hmain : Tendsto (fun Y : ℝ => cgmyExponent (cgmyCornerC σ Y) G M Y v) (𝓝[<] (2 : ℝ))
      (𝓝 (((σ ^ 2 / 4 : ℝ) : ℂ) *
        (-2 * v ^ 2 + 2 * Complex.I * ((G - M : ℝ) : ℂ) * v))) := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards with Y
    unfold cgmyExponent
    ring
  convert hmain using 1
  push_cast
  ring

/-! ## §4 route A: the algebraic forward normalization -/

/-- The cumulant at the numéraire converges to `(σ²/2)(G−M+1)`: the real
route `κ_Y(1) = C_Y Γ(−Y)[(M−1)^Y − M^Y + (G+1)^Y − G^Y]` — not the complex
exponent at `v = −i` — with `M > 1` keeping the base `M − 1` off zero. -/
theorem cgmyCornerCumulant_one_tendsto (σ G M : ℝ) (hG : 0 < G) (hM : 1 < M) :
    Tendsto (fun Y : ℝ => cgmyCumulant (cgmyCornerC σ Y) G M Y 1) (𝓝[<] (2 : ℝ))
      (𝓝 ((σ ^ 2 / 2) * (G - M + 1))) := by
  have hcoef := cgmyCornerGamma_tendsto σ
  have hM1 : Tendsto (fun Y : ℝ => (M - 1) ^ Y) (𝓝[<] (2 : ℝ)) (𝓝 ((M - 1) ^ (2 : ℝ))) := by
    have hc : ContinuousAt (fun Y : ℝ => (M - 1) ^ Y) (2 : ℝ) :=
      Real.continuousAt_const_rpow (a := M - 1) (b := 2) (by linarith : M - 1 ≠ 0)
    exact hc.continuousWithinAt.tendsto
  have hMp : Tendsto (fun Y : ℝ => M ^ Y) (𝓝[<] (2 : ℝ)) (𝓝 (M ^ (2 : ℝ))) := by
    have hc : ContinuousAt (fun Y : ℝ => M ^ Y) (2 : ℝ) :=
      Real.continuousAt_const_rpow (a := M) (b := 2) (by linarith : M ≠ 0)
    exact hc.continuousWithinAt.tendsto
  have hG1 : Tendsto (fun Y : ℝ => (G + 1) ^ Y) (𝓝[<] (2 : ℝ)) (𝓝 ((G + 1) ^ (2 : ℝ))) := by
    have hc : ContinuousAt (fun Y : ℝ => (G + 1) ^ Y) (2 : ℝ) :=
      Real.continuousAt_const_rpow (a := G + 1) (b := 2) (by linarith : G + 1 ≠ 0)
    exact hc.continuousWithinAt.tendsto
  have hGp : Tendsto (fun Y : ℝ => G ^ Y) (𝓝[<] (2 : ℝ)) (𝓝 (G ^ (2 : ℝ))) := by
    have hc : ContinuousAt (fun Y : ℝ => G ^ Y) (2 : ℝ) :=
      Real.continuousAt_const_rpow (a := G) (b := 2) (by linarith : G ≠ 0)
    exact hc.continuousWithinAt.tendsto
  have hbr : Tendsto
      (fun Y : ℝ => (M - 1) ^ Y - M ^ Y + (G + 1) ^ Y - G ^ Y) (𝓝[<] (2 : ℝ))
      (𝓝 ((M - 1) ^ (2 : ℝ) - M ^ (2 : ℝ) + (G + 1) ^ (2 : ℝ) - G ^ (2 : ℝ))) :=
    ((hM1.sub hMp).add hG1).sub hGp
  have hprod := hcoef.mul hbr
  have hmain : Tendsto (fun Y : ℝ => cgmyCumulant (cgmyCornerC σ Y) G M Y 1) (𝓝[<] (2 : ℝ))
      (𝓝 ((σ ^ 2 / 4) *
        ((M - 1) ^ (2 : ℝ) - M ^ (2 : ℝ) + (G + 1) ^ (2 : ℝ) - G ^ (2 : ℝ)))) := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards with Y
    unfold cgmyCumulant
    ring
  convert hmain using 1
  simp
  ring

/-- The forward normalization delivers the carry EXACTLY, at every `Y` in
scope and for every `r, q`: `Ψ_Y(−i) = r − q`. This consumes BRIEF_011's
`cgmyExponent_strip` (`1 < M` places the numéraire `u = 1` in the strip) and
is then `i·b_Y·(−i) = b_Y` plus `ring`. It is an algebraic identity about a
deterministic correction, not a statement that a risk-neutral CGMY measure
exists. -/
theorem cornerForward_numeraire (σ G M Y r q : ℝ) (hG : 0 < G) (hM : 1 < M) :
    cornerForwardExponent σ G M Y r q (-Complex.I) = ((r - q : ℝ) : ℂ) := by
  have hnum := cgmyExponent_strip (cgmyCornerC σ Y) G M Y 1 hG (by linarith : 0 < M)
    (by linarith : -G < (1 : ℝ)) hM
  have hnum' : cgmyExponent (cgmyCornerC σ Y) G M Y (-Complex.I) =
      ((cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) := by
    simpa [cgmyCumulant] using hnum
  unfold cornerForwardExponent
  rw [hnum']
  have hImul : Complex.I * ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) *
      (-Complex.I) = ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) := by
    calc
      Complex.I * ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) * (-Complex.I)
          = ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) *
              (Complex.I * (-Complex.I)) := by ring
      _ = ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) := by
        rw [mul_neg, Complex.I_mul_I]
        ring
  rw [hImul]
  push_cast
  ring

/-- The numéraire at factor level (5): `exp (τ Ψ_Y(−i)) = exp (τ (r−q))`, the
route-A twin of BRIEF_013's `esscher_drift_factor`. -/
theorem cornerForwardFactor_numeraire (σ G M Y τ r q : ℝ) (hG : 0 < G) (hM : 1 < M) :
    Complex.exp ((τ : ℂ) * cornerForwardExponent σ G M Y r q (-Complex.I)) =
      Complex.exp ((τ : ℂ) * ((r - q : ℝ) : ℂ)) := by
  rw [cornerForward_numeraire σ G M Y r q hG hM]

/-- ROUTE A (6): the forward-normalized exponent tends to the risk-neutral
GBM exponent `i(r−q−σ²/2)v − (σ²/2)v²`. The unwanted `G − M` of (3) cancels
against the limit of `−κ_Y(1)`; what survives is the carry `r − q` and the
Itô correction `σ²/2`. Pointwise in `v`, on the same strip as (3). -/
theorem cornerForwardExponent_tendsto (σ G M r q : ℝ) (hG : 0 < G) (hM : 1 < M)
    (v : ℂ) (hv₁ : -M < v.im) (hv₂ : v.im < G) :
    Tendsto (fun Y : ℝ => cornerForwardExponent σ G M Y r q v) (𝓝[<] (2 : ℝ))
      (𝓝 (Complex.I * ((r - q - σ ^ 2 / 2 : ℝ) : ℂ) * v -
        ((σ ^ 2 / 2 : ℝ) : ℂ) * v ^ 2)) := by
  have hψ := cgmyCornerExponent_tendsto σ G M hG hM v hv₁ hv₂
  have hκ := cgmyCornerCumulant_one_tendsto σ G M hG hM
  have hbR : Tendsto (fun Y : ℝ => r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1)
      (𝓝[<] (2 : ℝ)) (𝓝 (r - q - (σ ^ 2 / 2) * (G - M + 1))) :=
    tendsto_const_nhds.sub hκ
  have hbC : Tendsto (fun Y : ℝ => ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ))
      (𝓝[<] (2 : ℝ)) (𝓝 (((r - q - (σ ^ 2 / 2) * (G - M + 1) : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.tendsto (r - q - (σ ^ 2 / 2) * (G - M + 1))).comp hbR
  have hbterm : Tendsto
      (fun Y : ℝ => Complex.I * ((r - q - cgmyCumulant (cgmyCornerC σ Y) G M Y 1 : ℝ) : ℂ) * v)
      (𝓝[<] (2 : ℝ))
      (𝓝 (Complex.I * ((r - q - (σ ^ 2 / 2) * (G - M + 1) : ℝ) : ℂ) * v)) :=
    (tendsto_const_nhds.mul hbC).mul tendsto_const_nhds
  have hsum := hψ.add hbterm
  have hmain : Tendsto (fun Y : ℝ => cornerForwardExponent σ G M Y r q v) (𝓝[<] (2 : ℝ))
      (𝓝 ((-((σ ^ 2 / 2 : ℝ) : ℂ) * v ^ 2 +
          Complex.I * ((σ ^ 2 / 2 : ℝ) : ℂ) * ((G - M : ℝ) : ℂ) * v) +
        Complex.I * ((r - q - (σ ^ 2 / 2) * (G - M + 1) : ℝ) : ℂ) * v)) := by
    apply Filter.Tendsto.congr' _ hsum
    filter_upwards with Y
    unfold cornerForwardExponent
    ring
  convert hmain using 1
  push_cast
  ring

/-- ROUTE A (7): the factor converges to BRIEF_005's own
`gbmCharFactor ((r−q−σ²/2)τ) ((σ²/2)τ) v` — the landed GBM factor, not a new
function that could be defined to make the comparison true. Continuity of
`Complex.exp` does the transport; the identification of the limit with
`gbmCharFactor` is `unfold` + `ring` on the exponent. -/
theorem cornerForwardFactor_tendsto (σ G M τ r q : ℝ) (hG : 0 < G) (hM : 1 < M)
    (v : ℂ) (hv₁ : -M < v.im) (hv₂ : v.im < G) :
    Tendsto (fun Y : ℝ => Complex.exp ((τ : ℂ) * cornerForwardExponent σ G M Y r q v))
      (𝓝[<] (2 : ℝ))
      (𝓝 (gbmCharFactor ((r - q - σ ^ 2 / 2) * τ) ((σ ^ 2 / 2) * τ) v)) := by
  have hE := cornerForwardExponent_tendsto σ G M r q hG hM v hv₁ hv₂
  have hτE : Tendsto (fun Y : ℝ => (τ : ℂ) * cornerForwardExponent σ G M Y r q v)
      (𝓝[<] (2 : ℝ))
      (𝓝 ((τ : ℂ) * (Complex.I * ((r - q - σ ^ 2 / 2 : ℝ) : ℂ) * v -
        ((σ ^ 2 / 2 : ℝ) : ℂ) * v ^ 2))) :=
    tendsto_const_nhds.mul hE
  have hexp : Tendsto
      (fun Y : ℝ => Complex.exp ((τ : ℂ) * cornerForwardExponent σ G M Y r q v))
      (𝓝[<] (2 : ℝ))
      (𝓝 (Complex.exp ((τ : ℂ) * (Complex.I * ((r - q - σ ^ 2 / 2 : ℝ) : ℂ) * v -
        ((σ ^ 2 / 2 : ℝ) : ℂ) * v ^ 2)))) :=
    (Complex.continuous_exp.tendsto _).comp hτE
  convert hexp using 1
  unfold gbmCharFactor
  congr 1
  push_cast
  ring

/-! ## §5 route B: the named zero-carry Esscher selection -/

/-- `θ₀ = (M−G−1)/2` is admissible (`1 < G + M`, the same condition under
which the admissible interval is nonempty in BRIEF_013), so BRIEF_013's
theorems apply to it verbatim. Recorded separately because route B needs the
membership as a hypothesis of two landed theorems, not as a fact about a
root the corner approximates. -/
theorem cornerEsscherZero_mem (G M : ℝ) (hGM : 1 < G + M) :
    esscherThetaZero G M ∈ Ioo (-G) (M - 1) := by
  unfold esscherThetaZero
  constructor <;> linarith

/-- The zero-carry numéraire at the named selection, at factor level: at the
shifted rates `(G+θ₀, M−θ₀)` the factor at `v = −i` is exactly `1`. This is
`esscher_drift_factor` with `r = q = 0`, whose drift hypothesis is
`esscherDriftMap_zero` — the SAME parameter solves the Esscher equation at
every `Y`, so no limiting root and no approximated solution enters. -/
theorem cornerEsscherZero_numeraire (σ G M Y τ : ℝ) (hG : 0 < G) (hM : 1 < M)
    (hGM : 1 < G + M) :
    cgmyCharFactor (cgmyCornerC σ Y) (G + esscherThetaZero G M) (M - esscherThetaZero G M) Y τ
      (-Complex.I) = 1 := by
  have hθ := cornerEsscherZero_mem G M hGM
  have hfac := esscher_drift_factor (cgmyCornerC σ Y) G M Y τ 0 0 (esscherThetaZero G M) hG
    (by linarith : 0 < M) hθ
    (by simpa using (esscherDriftMap_zero (cgmyCornerC σ Y) G M Y))
  simpa using hfac

/-- The same statement at exponent level: the tilted exponent vanishes at
`v = −i`. `esscherExponent_neg_I_eq` (BRIEF_013) turns the tilted exponent
into the delivered drift, and `esscherDriftMap_zero` says that drift is `0`. -/
theorem cornerEsscherZero_exponent (σ G M Y : ℝ) (hG : 0 < G) (hM : 1 < M)
    (hGM : 1 < G + M) :
    esscherExponent (cgmyExponent (cgmyCornerC σ Y) G M Y) (esscherThetaZero G M)
      (-Complex.I) = 0 := by
  have hθ := cornerEsscherZero_mem G M hGM
  rw [esscherExponent_neg_I_eq (cgmyCornerC σ Y) G M Y (esscherThetaZero G M) hG
    (by linarith : 0 < M) hθ, esscherDriftMap_zero]
  norm_num

/-- ROUTE B (8): at `θ₀` the tilted exponent converges to the zero-carry GBM
exponent `−(σ²/2)v² − i(σ²/2)v`, with NO drift correction. The proof consumes
BRIEF_013's `esscher_cgmy_shift` (the tilt IS the same exponent at shifted
rates, at every `Y`) and then §3 at those rates: `G′ − M′ = −1`, so the
`i(σ²/2)(G′−M′)v` of (3) is the Itô correction itself. The strip hypotheses
are the SHIFTED ones — the shift moves the rates, so a `v` legal for `(G, M)`
need not be legal for `(G′, M′)`. -/
theorem cornerEsscherZero_tendsto (σ G M : ℝ) (hG : 0 < G) (hM : 1 < M) (hGM : 1 < G + M)
    (v : ℂ) (hv₁ : -(M - esscherThetaZero G M) < v.im) (hv₂ : v.im < G + esscherThetaZero G M) :
    Tendsto
      (fun Y : ℝ => esscherExponent (cgmyExponent (cgmyCornerC σ Y) G M Y)
        (esscherThetaZero G M) v)
      (𝓝[<] (2 : ℝ))
      (𝓝 (-((σ ^ 2 / 2 : ℝ) : ℂ) * v ^ 2 - Complex.I * ((σ ^ 2 / 2 : ℝ) : ℂ) * v)) := by
  have hG' : 0 < G + esscherThetaZero G M := by
    unfold esscherThetaZero
    linarith
  have hM' : 1 < M - esscherThetaZero G M := by
    unfold esscherThetaZero
    linarith
  have hlim := cgmyCornerExponent_tendsto σ (G + esscherThetaZero G M)
    (M - esscherThetaZero G M) hG' hM' v hv₁ hv₂
  have hmain : Tendsto
      (fun Y : ℝ => esscherExponent (cgmyExponent (cgmyCornerC σ Y) G M Y)
        (esscherThetaZero G M) v)
      (𝓝[<] (2 : ℝ))
      (𝓝 (-((σ ^ 2 / 2 : ℝ) : ℂ) * v ^ 2 +
        Complex.I * ((σ ^ 2 / 2 : ℝ) : ℂ) *
          (((G + esscherThetaZero G M) - (M - esscherThetaZero G M) : ℝ) : ℂ) * v)) := by
    apply Filter.Tendsto.congr' _ hlim
    filter_upwards with Y
    exact (congr_fun (esscher_cgmy_shift (cgmyCornerC σ Y) G M Y (esscherThetaZero G M)) v).symm
  convert hmain using 1
  unfold esscherThetaZero
  push_cast
  ring

/-- (9): the attainable drift half-width collapses to `(σ²/2)(G+M−1)`. Proved
from the BODY of BRIEF_013's `esscherDriftBound` and the coefficient limit of
§2 — not from an independent bound — because the point is that the corner
shrinks the range the STRIP already describes: the edge bracket
`(G+M)^Y − (G+M−1)^Y − 1 → 2(G+M−1)`. A general-carry Esscher theorem would
need `θ_Y → θ_GBM` on top of this and is out of scope. -/
theorem cornerEsscherBound_tendsto (σ G M : ℝ) (hGM : 1 < G + M) :
    Tendsto (fun Y : ℝ => esscherDriftBound (cgmyCornerC σ Y) G M Y) (𝓝[<] (2 : ℝ))
      (𝓝 ((σ ^ 2 / 2) * (G + M - 1))) := by
  have hcoef : Tendsto (fun Y : ℝ => |cgmyCornerC σ Y * Real.Gamma (-Y)|) (𝓝[<] (2 : ℝ))
      (𝓝 (σ ^ 2 / 4)) := by
    have hn := (cgmyCornerGamma_tendsto σ).norm
    simpa [Real.norm_eq_abs, abs_of_nonneg (by nlinarith [sq_nonneg σ] : 0 ≤ σ ^ 2 / 4)]
      using hn
  have hp1 : Tendsto (fun Y : ℝ => (G + M) ^ Y) (𝓝[<] (2 : ℝ)) (𝓝 ((G + M) ^ (2 : ℝ))) := by
    have hc : ContinuousAt (fun Y : ℝ => (G + M) ^ Y) (2 : ℝ) :=
      Real.continuousAt_const_rpow (a := G + M) (b := 2) (by linarith : G + M ≠ 0)
    exact hc.continuousWithinAt.tendsto
  have hp2 : Tendsto (fun Y : ℝ => (G + M - 1) ^ Y) (𝓝[<] (2 : ℝ))
      (𝓝 ((G + M - 1) ^ (2 : ℝ))) := by
    have hc : ContinuousAt (fun Y : ℝ => (G + M - 1) ^ Y) (2 : ℝ) :=
      Real.continuousAt_const_rpow (a := G + M - 1) (b := 2) (by linarith : G + M - 1 ≠ 0)
    exact hc.continuousWithinAt.tendsto
  have hinner : Tendsto (fun Y : ℝ => (G + M) ^ Y - (G + M - 1) ^ Y - 1) (𝓝[<] (2 : ℝ))
      (𝓝 ((G + M) ^ (2 : ℝ) - (G + M - 1) ^ (2 : ℝ) - 1)) :=
    (hp1.sub hp2).sub tendsto_const_nhds
  have hbr : Tendsto (fun Y : ℝ => |(G + M) ^ Y - (G + M - 1) ^ Y - 1|) (𝓝[<] (2 : ℝ))
      (𝓝 (2 * (G + M - 1))) := by
    have hn : Tendsto (fun Y : ℝ => ‖(G + M) ^ Y - (G + M - 1) ^ Y - 1‖) (𝓝[<] (2 : ℝ))
        (𝓝 (‖(G + M) ^ (2 : ℝ) - (G + M - 1) ^ (2 : ℝ) - 1‖)) := hinner.norm
    -- Two shapes matter here, and both are decided by what `simp` does to the
    -- goal before this `have` is used as a rewrite rule: the real NORM is
    -- simplified to `| |`, and `Real.rpow_two` is a simp lemma, so the limit
    -- value arrives as `|(G+M)^2 − (G+M−1)^2 − 1|` with a NATURAL power.
    -- An `hval` phrased with `‖ ‖` or with `^ (2 : ℝ)` therefore does not match
    -- the very goal it was written to discharge.
    have hval : |(G + M) ^ 2 - (G + M - 1) ^ 2 - 1| = 2 * (G + M - 1) := by
      have hiden : (G + M) ^ 2 - (G + M - 1) ^ 2 - 1 = 2 * (G + M - 1) := by ring
      have hpos : 0 < (G + M) ^ 2 - (G + M - 1) ^ 2 - 1 := by
        rw [hiden]
        linarith
      rw [abs_of_pos hpos]
      ring
    simpa [Real.norm_eq_abs, hval] using hn
  have hprod := hcoef.mul hbr
  have hmain : Tendsto (fun Y : ℝ => esscherDriftBound (cgmyCornerC σ Y) G M Y) (𝓝[<] (2 : ℝ))
      (𝓝 ((σ ^ 2 / 4) * (2 * (G + M - 1)))) := by
    apply Filter.Tendsto.congr' _ hprod
    filter_upwards with Y
    unfold esscherDriftBound
    ring
  convert hmain using 1
  ring

end BSM
