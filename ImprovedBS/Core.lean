/-
  ImprovedBS.Core — the BSM theorem stack (T1..T6) in Lean 4 + mathlib.

  STATUS CONVENTION (enforced mechanically by scripts/lean_lint.py, which
  needs no toolchain, and by the `lake build` job in .github/workflows/lean.yml):

    [BUILT] = proof script present, no `sorry`
    [TODO]  = statement is the agreed contract, proof deferred (`sorry`)

  The lint job hard-fails on ANY `sorry` in the T1..T4 node (the BRIEF_001 and
  BRIEF_003 deliverables) and ratchets the repo-wide `sorry` count against
  .github/lean_lint_baseline.json, so deferred nodes cannot silently grow.
  As of BRIEF_003 that baseline is empty: T1..T4 are all [BUILT].

  IMPORTANT — what was fixed here, and why
  ----------------------------------------
  The previous version of this file (Lean/core/bsm_theorems.lean) defined

      d2    := d1 - sigma * Real.sqrt tau
      bsPut := bsCall - S*e^{-q*tau} + K*e^{-r*tau}

  With those definitions T1 and T2 are true *by construction*: both proofs
  reduce to `unfold <def>; ring`, and T2 never touches the identity it is
  supposed to be about, namely Phi(x) + Phi(-x) = 1. A green build on that
  file would have certified nothing. The definitions below are therefore
  INDEPENDENT — `d2` and `bsPut` each get their own explicit closed form —
  matching docs/01_baseline.md §2 and experiments/black_scholes.py, which was
  changed the same way. The numeric oracle and this file agree to ~1e-15.

  `t3_delta_identity` also carried a FALSE statement: with mathlib's
  `a / 0 = 0` and `Real.sqrt 0 = 0`, taking sigma = 0 collapses
  d1 = d2 = 0 and the claim degenerates to S*e^{-q*tau}*phi(0) =
  K*e^{-r*tau}*phi(0), which fails for S ≠ K (e.g. S=2, K=1, r=q=0 gives
  0.797885 vs 0.398942). It now carries the hypotheses it needs.

  HYPOTHESIS DISCIPLINE
  ---------------------
  Wherever the oracle guards its inputs (`bs_price` raises ValueError for
  tau <= 0 and sigma <= 0), the Lean statement carries the matching
  hypothesis. Degenerate cases are not "extra generality"; under `div_zero`
  they are a different mathematics, and silently relying on that convention
  is how a false statement gets committed.
-/

-- `import Mathlib`, deliberately. Narrow imports are better practice -- they
-- document what a theorem rests on and cost less elaboration time -- but they
-- can only be verified by a toolchain, and this tree is authored in
-- environments that have none. Two narrow paths guessed by hand
-- (`Mathlib.Analysis.SpecialFunctions.Erf`, `Mathlib.Data.Real.Pi`) cost three
-- consecutive red CI runs. Narrowing this list is a legitimate follow-up for
-- someone who can run `lake build`; do not do it blind.
import Mathlib

-- `Real.exp`, `Real.log`, `Real.sqrt` and division on `Real` are all
-- noncomputable, and `lake build` emits C, so every definition in this file
-- that touches them has to be marked. Rather than annotate six defs (and miss
-- the seventh), the whole file is a noncomputable section.
noncomputable section

-- Everything below lives in `namespace BSM`. Without it the declarations land
-- in the ROOT namespace, which for a library is not acceptable: `Phi`, `phi`,
-- `d1`, `d2` and `erf` are far too generic to claim globally, and any
-- downstream file importing this one would collide with them. Note that the
-- module name (`ImprovedBS.Core`) is NOT a namespace -- the fully qualified
-- name of a declaration is determined by the enclosing `namespace` command,
-- so `#print axioms ImprovedBS.t1_d1_minus_d2` does not resolve. The first
-- green `lake build` of this repository was followed by exactly that failure in
-- the CI audit step.
namespace BSM

-- --------------------------------------------------------------------------
-- Notation (identical to docs/01_baseline.md and experiments/black_scholes.py)
--
--   S     : spot,            K    : strike,      K > 0
--   tau   : T - t,           tau > 0
--   r, q  : risk-free rate and dividend yield (annualized decimals)
--   sigma : volatility,      sigma > 0
--   Phi   : standard normal CDF, via the `erf` defined below
--   phi   : standard normal PDF
--
-- Argument order is (S K tau r q sigma) throughout, and
-- experiments/black_scholes.py's internal helpers use the same order.
-- NOTE the public Python `bs_price(S, K, T, t, r, s, q)` puts `s` before `q`;
-- that boundary is pinned by tests/test_bs.py::test_public_api_argument_order.
-- --------------------------------------------------------------------------

/-!
### The error function

**Mathlib v4.34.0 has no `Real.erf`.** There is no
`Mathlib/Analysis/SpecialFunctions/Erf.lean` in the v4.34.0 tree (checked
against all 9112 `.lean` files), and `erf_neg` does not exist. `docs/04`
previously asserted both as available dependencies; that was wrong, and it is
corrected there.

So `erf` is defined here, from the interval integral of the Gaussian. That is
enough for everything T1 and T2 need: the *oddness* of `erf`, which is what
put-call parity actually rests on. T3 and T4 need more — the *value* of the
Gaussian integral, to identify `Phi` with `∫_{(-∞, x]} phi` — and that is
imported from `integral_gaussian_Ioi` in exactly one place,
`integral_phi_Iic_zero` (see the "Analytic infrastructure" section).

If mathlib ever grows `Real.erf`, this section should be deleted in favour of
it and `Phi_add_Phi_neg` re-pointed at `Real.erf_neg`.
-/

/-- The error function, `erf x = (2/sqrt pi) * ∫ t in 0..x, exp (-(t^2))`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..x, Real.exp (-(t ^ 2))

/-- The Gaussian `t ↦ exp (-(t^2))` is even. Everything about the symmetry of
the normal distribution in this file reduces to this one line. -/
theorem exp_neg_sq_even (t : ℝ) : Real.exp (-((-t) ^ 2)) = Real.exp (-(t ^ 2)) := by
  congr 1
  ring

/-- **Oddness of `erf`**: `erf (-x) = -erf (x)`.

Proved by the substitution `t ↦ -t` on the interval integral
(`intervalIntegral.integral_comp_neg`), the evenness of the integrand, and the
orientation flip `intervalIntegral.integral_symm`. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  -- `integral_comp_neg` takes `a` and `b` IMPLICITLY; passing them positionally
  -- gives "Function expected at ... but this term has type ... = ...".
  have hcomp : ∫ t in (0:ℝ)..x, Real.exp (-(t ^ 2))
      = ∫ t in (-x)..(0:ℝ), Real.exp (-(t ^ 2)) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => Real.exp (-(u ^ 2))) (a := (0:ℝ)) (b := x)
    -- h : ∫ t in 0..x, exp(-((-t)^2)) = ∫ t in -x..-0, exp(-(t^2))
    -- simp discharges the evenness of the integrand and `-0 = 0` at once.
    simpa [exp_neg_sq_even] using h
  have hkey : ∫ t in (0:ℝ)..(-x), Real.exp (-(t ^ 2))
      = -∫ t in (0:ℝ)..x, Real.exp (-(t ^ 2)) := by
    rw [intervalIntegral.integral_symm, hcomp]
  simp only [erf, hkey]
  ring

/-- Standard normal CDF. `Phi x = (1 + erf (x / sqrt 2)) / 2`. -/
def Phi (x : ℝ) : ℝ := (1 + erf (x / Real.sqrt 2)) / 2

/-- Standard normal PDF. `phi x = exp (-(x^2)/2) / sqrt (2 pi)`. -/
def phi (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

/-- The upper BSM argument, from its own explicit formula. -/
def d1 (S K tau r q sigma : ℝ) : ℝ :=
  (Real.log (S / K) + (r - q + sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)

/-- The lower BSM argument, from its OWN explicit formula.

Deliberately *not* `d1 - sigma * Real.sqrt tau`: that would make `t1` a
definitional tautology. The two expressions are equal, and `t1_d1_minus_d2`
is the theorem saying so. -/
def d2 (S K tau r q sigma : ℝ) : ℝ :=
  (Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)

/-- BSM European call price. -/
def bsCall (S K tau r q sigma : ℝ) : ℝ :=
  S * Real.exp (-q * tau) * Phi (d1 S K tau r q sigma)
    - K * Real.exp (-r * tau) * Phi (d2 S K tau r q sigma)

/-- BSM European put price, from its OWN closed form.

Deliberately *not* `bsCall - S*e^{-q*tau} + K*e^{-r*tau}`: that would make
`t2_put_call_parity` a definitional tautology and would never exercise
`Phi_add_Phi_neg`, which is the actual content of parity. -/
def bsPut (S K tau r q sigma : ℝ) : ℝ :=
  K * Real.exp (-r * tau) * Phi (-(d2 S K tau r q sigma))
    - S * Real.exp (-q * tau) * Phi (-(d1 S K tau r q sigma))

-- --------------------------------------------------------------------------
-- The hinge lemma. Everything about parity goes through here.
-- --------------------------------------------------------------------------

/-- **Odd symmetry of the normal CDF**: `Phi x + Phi (-x) = 1`.

This is the analytic content of put-call parity (T2). It is the lemma the
BRIEF_001 acceptance bar demands be cited: "the parity identity is not
guaranteed by the algebra of `Phi` alone — it follows from `Φ(x) + Φ(−x) = 1`".
Unconditional: it is a statement about `erf` alone. -/
theorem Phi_add_Phi_neg (x : ℝ) : Phi x + Phi (-x) = 1 := by
  have hneg : (-x) / Real.sqrt 2 = -(x / Real.sqrt 2) := by ring
  simp only [Phi, hneg, erf_neg]
  ring

/-- `Phi` is complementary under negation, in the form `ring`/`linarith` want. -/
theorem Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x := by
  linarith [Phi_add_Phi_neg x]

-- --------------------------------------------------------------------------
-- T1  [BUILT]  d1 - d2 = sigma * sqrt tau
-- --------------------------------------------------------------------------

/-- **T1.** `d1 - d2 = sigma * sqrt tau`, between two independently written
expressions. Hypotheses mirror the oracle's guards (`tau > 0`, `sigma > 0`).

Remark on degeneracy: with `d2` defined independently, this identity also
holds *unconditionally* under mathlib's `a / 0 = 0` convention (at
`sigma = 0`, `tau = 0`, or `tau < 0` both sides collapse to `0`). We do not
state it that way, because a theorem whose truth rests on a division-by-zero
convention is not the theorem the finance means. -/
theorem t1_d1_minus_d2 (S K tau r q sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    d1 S K tau r q sigma - d2 S K tau r q sigma = sigma * Real.sqrt tau := by
  have hsqrt : Real.sqrt tau ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htau)
  have hD : sigma * Real.sqrt tau ≠ 0 := mul_ne_zero hsigma hsqrt
  have hsq : Real.sqrt tau * Real.sqrt tau = tau := Real.mul_self_sqrt (le_of_lt htau)
  have hsq' : sigma * Real.sqrt tau * (sigma * Real.sqrt tau) = sigma ^ 2 * tau :=
    calc sigma * Real.sqrt tau * (sigma * Real.sqrt tau)
        = (sigma * sigma) * (Real.sqrt tau * Real.sqrt tau) := by ring
      _ = sigma ^ 2 * tau := by rw [hsq, ← pow_two]
  have key : (Real.log (S / K) + (r - q + sigma ^ 2 / 2) * tau)
      - (Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau) = sigma ^ 2 * tau := by ring
  -- `show` rather than `simp only [d1, d2, ...]`: simp left the two fractions
  -- uncombined (CI reported `sub_div` and `key` as unused simp arguments), and
  -- `rw` is deterministic where `simp` normalizes behind our back.
  show (Real.log (S / K) + (r - q + sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)
      - (Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)
      = sigma * Real.sqrt tau
  -- `← sub_div`, not `sub_div`. In mathlib v4.34.0 the lemma is oriented
  --   (a - b) / c = a / c - b / c
  -- i.e. it SPLITS a fraction; this goal needs the two fractions COMBINED, so
  -- the rewrite has to run backwards. CI reported the mismatch directly:
  --   Did not find an occurrence of the pattern (?a - ?b) / ?c
  -- which is the lemma's own left-hand side and the fastest possible way to see
  -- that the orientation is the other way round.
  --
  -- `div_eq_iff`, not `eq_div_iff_mul_eq`: the division is on the LEFT here.
  rw [← sub_div, key, div_eq_iff hD]
  exact hsq'.symm

-- --------------------------------------------------------------------------
-- T2  [BUILT]  put-call parity
-- --------------------------------------------------------------------------

/-- **T2.** Put-call parity for the BSM closed forms:

    bsPut = bsCall - S * e^{-q*tau} + K * e^{-r*tau}

Unconditional — it is a consequence of `Phi_add_Phi_neg` and nothing else, so
it holds even in the degenerate parameter regimes. The proof cites the
symmetry lemma at both `d1` and `d2`, as the brief requires. -/
theorem t2_put_call_parity (S K tau r q sigma : ℝ) :
    bsPut S K tau r q sigma
      = bsCall S K tau r q sigma - S * Real.exp (-q * tau) + K * Real.exp (-r * tau) := by
  -- `linarith` FAILS here, and it is worth recording why: the goal contains
  -- `K * exp(-r*tau) * Phi(-(d2 ...))`, a *product* of two atoms, so the goal is
  -- not linear in them. Rewriting `Phi (-x)` to `1 - Phi x` first makes it a
  -- ring identity in the atoms S, K, exp(-q*tau), exp(-r*tau), Phi(d1), Phi(d2).
  -- The odd-symmetry content still comes from `Phi_add_Phi_neg`, via `Phi_neg`.
  simp only [bsPut, bsCall, Phi_neg]
  ring

/-- Parity in the traded form: the call minus the put is the discounted
forward-spread. Restated from `t2_put_call_parity` so the ledger can point at
the identity practitioners actually quote. -/
theorem t2_put_call_parity_spread (S K tau r q sigma : ℝ) :
    bsCall S K tau r q sigma - bsPut S K tau r q sigma
      = S * Real.exp (-q * tau) - K * Real.exp (-r * tau) := by
  linarith [t2_put_call_parity S K tau r q sigma]

-- --------------------------------------------------------------------------
-- Analytic infrastructure for T3 and T4
-- --------------------------------------------------------------------------

/-!
### The Gaussian density, and `Phi` as an integral

Everything T3 and T4 need about the normal law is packaged here, and it is
less than one might expect:

* `phi_add` — the **tilting identity** `e^{a u + a²/2} · φ(u + a) = φ(u)`,
  i.e. completing the square. With `u = d2`, `a = σ√τ` this *is* T3, and it is
  also the pointwise fact behind the positivity of the option price.
* `Phi_eq_integral_Iic` — `Φ(x) = ∫_{(-∞, x]} φ`. This is the one place the
  **value** of the Gaussian integral enters (`integral_gaussian_Ioi`): it
  identifies the `1/2` in `Φ = (1 + erf(·/√2))/2` with `∫_{(-∞, 0]} φ`.
* `Phi_nonneg`, `Phi_le_one` — immediate from the representation and `Phi_neg`.
* `Phi_le_exp_mul_Phi_add` — `Φ(x) ≤ e^{a x + a²/2} · Φ(x + a)` for `a ≥ 0`,
  obtained by integrating `phi_add` over `(-∞, x]`. With `x = d2`, `a = σ√τ`
  this is `bsCall ≥ 0`; with `x = -d1` it is `bsPut ≥ 0`. **This, not
  monotonicity of `Φ`, is the content of the T4 lower bound** — see the T4
  doc-comment for why the previously recorded route could not work.

`d1_exponent` / `d2_exponent` / `forward_eq` are the three lines of
exp/log/sqrt algebra that connect the abstract statements to the BSM
parameters; they are shared by T3 and both halves of T4.
-/

/-- `phi` is even. -/
theorem phi_neg (x : ℝ) : phi (-x) = phi x := by
  have h : (-x) ^ 2 = x ^ 2 := by ring
  simp only [phi, h]

/-- `phi` is non-negative. -/
theorem phi_nonneg (x : ℝ) : 0 ≤ phi x := by
  unfold phi
  positivity

/-- `phi` in the shape mathlib's Gaussian lemmas use, `exp (-b * x^2)` with `b = 1/2`. -/
theorem phi_eq_gauss (u : ℝ) :
    phi u = Real.exp (-(1 / 2 : ℝ) * u ^ 2) / Real.sqrt (2 * Real.pi) := by
  have h : -(u ^ 2) / 2 = -(1 / 2 : ℝ) * u ^ 2 := by ring
  unfold phi
  rw [h]

/-- `phi` is integrable on `ℝ` — `integrable_exp_neg_mul_sq`, scaled. -/
theorem phi_integrable : MeasureTheory.Integrable phi := by
  have h : phi = fun u => Real.exp (-(1 / 2 : ℝ) * u ^ 2) / Real.sqrt (2 * Real.pi) :=
    funext phi_eq_gauss
  rw [h]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).div_const _

/-- **The tilting identity**: `exp (a u + a²/2) * phi (u + a) = phi u`.

Completing the square, `-(u+a)²/2 + a u + a²/2 = -u²/2`. This is the whole of
T3 once `u = d2` and `a = σ√τ` (see `t3_delta_identity`), and it is the
pointwise inequality behind the positivity of the BSM price
(see `Phi_le_exp_mul_Phi_add`). -/
theorem phi_add (u a : ℝ) : Real.exp (a * u + a ^ 2 / 2) * phi (u + a) = phi u := by
  unfold phi
  have h : Real.exp (a * u + a ^ 2 / 2) * Real.exp (-((u + a) ^ 2) / 2)
      = Real.exp (-(u ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← h]
  ring

/-- The substitution `t = u / √2` in the `erf` integral: `erf (x/√2) = 2 ∫₀ˣ phi`. -/
theorem erf_div_sqrt_two (x : ℝ) : erf (x / Real.sqrt 2) = 2 * ∫ u in (0:ℝ)..x, phi u := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- `integral_comp_div`: ∫ u in 0..x, f (u / c) = c • ∫ t in 0/c..x/c, f t
  have hsubst : ∫ u in (0:ℝ)..x, Real.exp (-(u ^ 2) / 2)
      = Real.sqrt 2 * ∫ t in (0:ℝ)..(x / Real.sqrt 2), Real.exp (-(t ^ 2)) := by
    have h := intervalIntegral.integral_comp_div (a := (0:ℝ)) (b := x)
      (fun t : ℝ => Real.exp (-(t ^ 2))) h2.ne'
    simp only [zero_div, smul_eq_mul] at h
    rw [← h]
    congr 1
    funext u
    congr 1
    rw [div_pow, hsq]
    ring
  have hphi : ∫ u in (0:ℝ)..x, phi u
      = (∫ u in (0:ℝ)..x, Real.exp (-(u ^ 2) / 2)) / Real.sqrt (2 * Real.pi) := by
    show ∫ u in (0:ℝ)..x, Real.exp (-(u ^ 2) / 2) / Real.sqrt (2 * Real.pi) = _
    exact intervalIntegral.integral_div _ _
  rw [erf, hphi, hsubst, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) Real.pi,
    mul_div_mul_left _ _ h2.ne']
  ring

/-- `Phi x = 1/2 + ∫₀ˣ phi`. Still an interval integral; the `1/2` is identified
with a tail integral in `Phi_eq_integral_Iic`. -/
theorem Phi_eq_half_add_integral (x : ℝ) : Phi x = 1 / 2 + ∫ u in (0:ℝ)..x, phi u := by
  rw [Phi, erf_div_sqrt_two]
  ring

/-- `∫_{(-∞, 0]} phi = 1/2`. Reflect `(-∞, 0]` onto `(0, ∞)` (`integral_comp_neg_Ioi`,
`phi` is even) and read off `integral_gaussian_Ioi`. This is the only use of
the **value** of the Gaussian integral in the T1–T4 stack. -/
theorem integral_phi_Iic_zero : ∫ u in Set.Iic (0:ℝ), phi u = 1 / 2 := by
  have hrefl : ∫ u in Set.Iic (0:ℝ), phi u = ∫ u in Set.Ioi (0:ℝ), phi u := by
    have h := integral_comp_neg_Ioi (0:ℝ) phi
    simp only [neg_zero, phi_neg] at h
    exact h.symm
  have hgauss : ∫ u in Set.Ioi (0:ℝ), Real.exp (-(1 / 2 : ℝ) * u ^ 2)
      = Real.sqrt (2 * Real.pi) / 2 := by
    have h := integral_gaussian_Ioi (1 / 2 : ℝ)
    have h2 : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
    rw [h2] at h
    exact h
  have hphi : phi = fun u => Real.exp (-(1 / 2 : ℝ) * u ^ 2) / Real.sqrt (2 * Real.pi) :=
    funext phi_eq_gauss
  have hne : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [hrefl, hphi, MeasureTheory.integral_div, hgauss, div_div,
    mul_comm (2:ℝ) (Real.sqrt (2 * Real.pi)), ← div_div, div_self hne]

/-- **`Phi` is the distribution function of `phi`**: `Phi x = ∫_{(-∞, x]} phi`.

`intervalIntegral.integral_Iic_sub_Iic` splits `∫_{(-∞,x]} = ∫_{(-∞,0]} + ∫₀ˣ`,
and the two pieces are `integral_phi_Iic_zero` and `Phi_eq_half_add_integral`. -/
theorem Phi_eq_integral_Iic (x : ℝ) : Phi x = ∫ u in Set.Iic x, phi u := by
  have hsub : (∫ u in Set.Iic x, phi u) - ∫ u in Set.Iic (0:ℝ), phi u
      = ∫ u in (0:ℝ)..x, phi u :=
    intervalIntegral.integral_Iic_sub_Iic phi_integrable.integrableOn
      phi_integrable.integrableOn
  rw [Phi_eq_half_add_integral, ← hsub, integral_phi_Iic_zero]
  ring

/-- `0 ≤ Phi x`. -/
theorem Phi_nonneg (x : ℝ) : 0 ≤ Phi x := by
  rw [Phi_eq_integral_Iic]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic (fun u _ => phi_nonneg u)

/-- `Phi x ≤ 1`, from `Phi_nonneg` at `-x` and the odd symmetry `Phi_neg`. -/
theorem Phi_le_one (x : ℝ) : Phi x ≤ 1 := by
  have h := Phi_nonneg (-x)
  rw [Phi_neg] at h
  linarith

/-- Translation invariance of a half-line integral,
`∫_{(-∞, c]} f (u + a) du = ∫_{(-∞, c + a]} f`. Mathlib v4.34.0 has the reflection
(`integral_comp_neg_Iic`) but not the translation; this is the same proof with
`Homeomorph.addRight` in place of `Homeomorph.neg`. -/
theorem integral_comp_add_right_Iic (f : ℝ → ℝ) (c a : ℝ) :
    ∫ u in Set.Iic c, f (u + a) = ∫ v in Set.Iic (c + a), f v := by
  have A : MeasurableEmbedding fun u : ℝ => u + a :=
    (Homeomorph.addRight a).measurableEmbedding
  have h := MeasurableEmbedding.setIntegral_map (μ := MeasureTheory.volume) A f
    (Set.Iic (c + a))
  -- `map_add_right_eq_self` lives in `MeasureTheory`, not `MeasureTheory.Measure`
  -- (checked against the v4.34.0 source: Mathlib/MeasureTheory/Group/Measure.lean).
  rw [MeasureTheory.map_add_right_eq_self
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) a] at h
  have hs : (fun u : ℝ => u + a) ⁻¹' Set.Iic (c + a) = Set.Iic c := by
    ext u
    simp
  rw [h, hs]

/-- **The positivity inequality**: for `a ≥ 0`,
`Phi x ≤ exp (a x + a²/2) * Phi (x + a)`.

Integrate the tilting identity: on `(-∞, x]`,
`phi u = e^{a u + a²/2} phi (u + a) ≤ e^{a x + a²/2} phi (u + a)`, and
`∫_{(-∞, x]} phi (u + a) du = Phi (x + a)` by translation. In the BSM variables
(`x = d2`, `a = σ√τ`) the factor `e^{a x + a²/2}` is exactly the ratio of the
discounted forward to the discounted strike (`d2_exponent`, `forward_eq`), so
this says `K e^{-rτ} Φ(d2) ≤ S e^{-qτ} Φ(d1)`, i.e. `bsCall ≥ 0`. It is the
lognormal martingale property in disguise. -/
theorem Phi_le_exp_mul_Phi_add (x a : ℝ) (ha : 0 ≤ a) :
    Phi x ≤ Real.exp (a * x + a ^ 2 / 2) * Phi (x + a) := by
  rw [Phi_eq_integral_Iic x, Phi_eq_integral_Iic (x + a),
    ← integral_comp_add_right_Iic phi x a, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_mono_on phi_integrable.integrableOn
    ((phi_integrable.comp_add_right a).const_mul (Real.exp (a * x + a ^ 2 / 2))).integrableOn
    measurableSet_Iic ?_
  intro u hu
  have hu' : u ≤ x := Set.mem_Iic.mp hu
  show phi u ≤ Real.exp (a * x + a ^ 2 / 2) * phi (u + a)
  rw [← phi_add u a]
  refine mul_le_mul_of_nonneg_right ?_ (phi_nonneg _)
  exact Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hu' ha])

/-- `σ√τ · d2 + (σ√τ)²/2 = ln(S/K) + (r − q)τ`: the exponent that turns the
discounted strike into the discounted forward. Needs only `σ√τ ≠ 0`, so it is
stated under T3's hypotheses (`sigma ≠ 0`), not T4's (`0 < sigma`). -/
theorem d2_exponent (S K tau r q sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    sigma * Real.sqrt tau * d2 S K tau r q sigma + (sigma * Real.sqrt tau) ^ 2 / 2
      = Real.log (S / K) + (r - q) * tau := by
  have hne : sigma * Real.sqrt tau ≠ 0 := mul_ne_zero hsigma (Real.sqrt_pos.mpr htau).ne'
  have h1 : Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau
      = d2 S K tau r q sigma * (sigma * Real.sqrt tau) := by
    apply (div_eq_iff hne).mp
    rfl
  have h2 : (sigma * Real.sqrt tau) ^ 2 = sigma ^ 2 * tau := by
    rw [mul_pow, Real.sq_sqrt htau.le]
  rw [mul_comm (sigma * Real.sqrt tau) (d2 S K tau r q sigma), ← h1, h2]
  ring

/-- `σ√τ · d1 − (σ√τ)²/2 = ln(S/K) + (r − q)τ`: the `d1` twin of `d2_exponent`,
used for the put side. -/
theorem d1_exponent (S K tau r q sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    sigma * Real.sqrt tau * d1 S K tau r q sigma - (sigma * Real.sqrt tau) ^ 2 / 2
      = Real.log (S / K) + (r - q) * tau := by
  have hne : sigma * Real.sqrt tau ≠ 0 := mul_ne_zero hsigma (Real.sqrt_pos.mpr htau).ne'
  have h1 : Real.log (S / K) + (r - q + sigma ^ 2 / 2) * tau
      = d1 S K tau r q sigma * (sigma * Real.sqrt tau) := by
    apply (div_eq_iff hne).mp
    rfl
  have h2 : (sigma * Real.sqrt tau) ^ 2 = sigma ^ 2 * tau := by
    rw [mul_pow, Real.sq_sqrt htau.le]
  rw [mul_comm (sigma * Real.sqrt tau) (d1 S K tau r q sigma), ← h1, h2]
  ring

/-- The discounted strike times `e^{ln(S/K) + (r − q)τ}` is the discounted
forward: `K e^{-rτ} · e^{ln(S/K) + (r-q)τ} = S e^{-qτ}`. -/
theorem forward_eq (S K tau r q : ℝ) (hS : 0 < S) (hK : 0 < K) :
    K * Real.exp (-r * tau) * Real.exp (Real.log (S / K) + (r - q) * tau)
      = S * Real.exp (-q * tau) := by
  have hKS : K * (S / K) = S := by
    rw [← mul_div_assoc, mul_comm K S, mul_div_assoc, div_self hK.ne', mul_one]
  have harg : -r * tau + (Real.log (S / K) + (r - q) * tau)
      = Real.log (S / K) + -q * tau := by
    ring
  rw [mul_assoc, ← Real.exp_add, harg, Real.exp_add, Real.exp_log (div_pos hS hK),
    ← mul_assoc, hKS]

-- --------------------------------------------------------------------------
-- T3  [BUILT]  the delta identity
-- --------------------------------------------------------------------------

/-- **T3.** `S * e^{-q*tau} * phi(d1) = K * e^{-r*tau} * phi(d2)`.

This is the analytic hinge for the greeks and for the martingale bridge, and
(via the chain rule) the cancellation that makes the BSM PDE residual vanish
— so T5 is proved *through* T3, not independently of it. See docs/04.

CORRECTED HYPOTHESES. The previous statement carried only `0 < S` and `0 < K`
and was **false**: at `sigma = 0`, mathlib's `a / 0 = 0` and `Real.sqrt 0 = 0`
force `d1 = d2 = 0`, and the claim becomes `S*e^{-q*tau}*phi(0) =
K*e^{-r*tau}*phi(0)`, which fails whenever `S*e^{-q*tau} ≠ K*e^{-r*tau}`
(concretely: S=2, K=1, r=q=0, sigma=0 gives 0.797885 ≠ 0.398942). The
hypotheses below are the ones the proof actually consumes:

* `0 < S`, `0 < K` — so `Real.log (S/K)` is the genuine logarithm and
  `exp (log (S/K)) = S/K` (`forward_eq`);
* `sigma ≠ 0`, `0 < tau` — so `sigma * Real.sqrt tau ≠ 0` and
  `Real.sqrt tau ^ 2 = tau` (`d2_exponent`).

Proof, as landed: T1 gives `d1 = d2 + σ√τ`; the tilting identity `phi_add` at
`u = d2`, `a = σ√τ` reads `e^{σ√τ·d2 + (σ√τ)²/2} · phi d1 = phi d2`;
`d2_exponent` identifies the exponent with `ln(S/K) + (r − q)τ`; `forward_eq`
turns `K e^{-rτ}` times that exponential into `S e^{-qτ}`. (The route recorded
earlier — `d1² − d2² = 2 ln(S/K) + 2(r−q)τ` — is the same computation
written as a difference of squares.) -/
theorem t3_delta_identity (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)
      = K * Real.exp (-r * tau) * phi (d2 S K tau r q sigma) := by
  have hd1 : d1 S K tau r q sigma = d2 S K tau r q sigma + sigma * Real.sqrt tau := by
    have := t1_d1_minus_d2 S K tau r q sigma htau hsigma
    linarith
  have hphi := phi_add (d2 S K tau r q sigma) (sigma * Real.sqrt tau)
  rw [d2_exponent S K tau r q sigma htau hsigma, ← hd1] at hphi
  rw [← hphi, ← forward_eq S K tau r q hS hK]
  ring

-- --------------------------------------------------------------------------
-- T4  [BUILT]  no-arbitrage bounds
-- --------------------------------------------------------------------------

/-- **Positivity of the call**: `0 ≤ bsCall`. Multiply `Phi_le_exp_mul_Phi_add`
at `x = d2`, `a = σ√τ` by `K e^{-rτ} ≥ 0` and use `d2_exponent` + `forward_eq`
to recognise `K e^{-rτ} e^{σ√τ d2 + (σ√τ)²/2}` as `S e^{-qτ}`; T1 supplies
`d2 + σ√τ = d1`. -/
theorem bsCall_nonneg (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    0 ≤ bsCall S K tau r q sigma := by
  have ha : 0 ≤ sigma * Real.sqrt tau := mul_nonneg hsigma.le (Real.sqrt_nonneg _)
  have hd1 : d1 S K tau r q sigma = d2 S K tau r q sigma + sigma * Real.sqrt tau := by
    have := t1_d1_minus_d2 S K tau r q sigma htau hsigma.ne'
    linarith
  have hineq := Phi_le_exp_mul_Phi_add (d2 S K tau r q sigma) (sigma * Real.sqrt tau) ha
  rw [d2_exponent S K tau r q sigma htau hsigma.ne', ← hd1] at hineq
  -- hineq : Phi d2 ≤ exp (ln(S/K) + (r-q)τ) * Phi d1
  have hD : 0 ≤ K * Real.exp (-r * tau) := mul_nonneg hK.le (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hineq hD
  rw [← mul_assoc, forward_eq S K tau r q hS hK] at hmul
  -- hmul : K e^{-rτ} Phi d2 ≤ S e^{-qτ} Phi d1
  unfold bsCall
  linarith

/-- **Positivity of the put**: `0 ≤ bsPut`. The same inequality at `x = -d1`,
`a = σ√τ`: now the exponent is `-(ln(S/K) + (r − q)τ)` (`d1_exponent`) and
`S e^{-qτ}` times that exponential is `K e^{-rτ}` (`forward_eq`, inverted);
T1 supplies `-d1 + σ√τ = -d2`. -/
theorem bsPut_nonneg (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    0 ≤ bsPut S K tau r q sigma := by
  have ha : 0 ≤ sigma * Real.sqrt tau := mul_nonneg hsigma.le (Real.sqrt_nonneg _)
  have hd2 : -(d1 S K tau r q sigma) + sigma * Real.sqrt tau = -(d2 S K tau r q sigma) := by
    have := t1_d1_minus_d2 S K tau r q sigma htau hsigma.ne'
    linarith
  have harg : sigma * Real.sqrt tau * -(d1 S K tau r q sigma) + (sigma * Real.sqrt tau) ^ 2 / 2
      = -(Real.log (S / K) + (r - q) * tau) := by
    rw [← d1_exponent S K tau r q sigma htau hsigma.ne']
    ring
  have hineq := Phi_le_exp_mul_Phi_add (-(d1 S K tau r q sigma)) (sigma * Real.sqrt tau) ha
  rw [harg, hd2] at hineq
  -- hineq : Phi (-d1) ≤ exp (-(ln(S/K) + (r-q)τ)) * Phi (-d2)
  have hF : 0 ≤ S * Real.exp (-q * tau) := mul_nonneg hS.le (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hineq hF
  have hFD : S * Real.exp (-q * tau) * Real.exp (-(Real.log (S / K) + (r - q) * tau))
      = K * Real.exp (-r * tau) := by
    rw [← forward_eq S K tau r q hS hK, mul_assoc, ← Real.exp_add]
    simp
  rw [← mul_assoc, hFD] at hmul
  -- hmul : S e^{-qτ} Phi (-d1) ≤ K e^{-rτ} Phi (-d2)
  unfold bsPut
  linarith

/-- **T4.** No-arbitrage bounds on the call:

    max (S e^{-q*tau} - K e^{-r*tau}) 0 ≤ bsCall ≤ S e^{-q*tau}

Previously this node existed only as a row in README/docs tables; it had no
Lean statement at all, so nothing in the tree could contradict the claim that
it was "stated". It was stated in BRIEF_001's correction and is proved here.

**The proof route recorded here before BRIEF_003 was wrong, and it is worth
saying exactly how.** It read: "the lower bound follows from
`bsCall ≥ S e^{-qτ} Φ(d1) − K e^{-rτ} Φ(d1)` once `Φ` is monotone and
`d1 ≥ d2`." Write `F = S e^{-qτ}`, `D = K e^{-rτ}`. Monotonicity gives
`bsCall ≥ (F − D) Φ(d1)`, and `max (F − D) 0 ≤ bsCall` needs **both**
`bsCall ≥ 0` and `bsCall ≥ F − D`. In every regime the monotonicity bound
delivers only the half that is *not* binding: if `F ≥ D` it gives `bsCall ≥ 0`
but not `≥ F − D`; if `F < D` it gives `bsCall ≥ F − D` but not `≥ 0`
(S=100, K=120, τ=1, r=q=0, σ=0.2: `bsCall ≈ 2.15` while `(F − D) Φ(d1) ≈ −4.17`).
No amount of `0 ≤ Φ ≤ 1` plus monotonicity closes that gap, because the lower
bound is the statement that the BSM price is the discounted expectation of a
*non-negative payoff* — `bsCall ≥ 0` and (by parity) `bsPut ≥ 0` — and that
needs the *integral* structure of `Φ`, not just its range.

What the proof actually rests on:

* upper bound: `Phi_nonneg` (drop `K e^{-rτ} Φ(d2) ≥ 0`) and `Phi_le_one`;
* `0 ≤ bsCall`: `bsCall_nonneg`, i.e. `Phi_le_exp_mul_Phi_add` at `x = d2`;
* `F − D ≤ bsCall`: parity (`t2_put_call_parity`) and `bsPut_nonneg`, i.e. the
  same inequality at `x = −d1`.

The *value* of the Gaussian integral enters exactly once, in
`integral_phi_Iic_zero`; everything else is the tilting identity `phi_add`
integrated over a half-line. Monotonicity of `Φ` is never used.

The numeric shadow of this theorem is
`tests/test_bs.py::test_value_bounds`, which checks it on a 6-point grid. -/
theorem t4_call_bounds (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0
      ≤ bsCall S K tau r q sigma ∧
    bsCall S K tau r q sigma ≤ S * Real.exp (-q * tau) := by
  have hF : 0 ≤ S * Real.exp (-q * tau) := mul_nonneg hS.le (Real.exp_pos _).le
  have hD : 0 ≤ K * Real.exp (-r * tau) := mul_nonneg hK.le (Real.exp_pos _).le
  have hc := bsCall_nonneg S K tau r q sigma hS hK htau hsigma
  have hp := bsPut_nonneg S K tau r q sigma hS hK htau hsigma
  have hpar := t2_put_call_parity S K tau r q sigma
  refine ⟨max_le (by linarith) hc, ?_⟩
  have h1 : S * Real.exp (-q * tau) * Phi (d1 S K tau r q sigma) ≤ S * Real.exp (-q * tau) :=
    mul_le_of_le_one_right hF (Phi_le_one _)
  have h2 : 0 ≤ K * Real.exp (-r * tau) * Phi (d2 S K tau r q sigma) :=
    mul_nonneg hD (Phi_nonneg _)
  unfold bsCall
  linarith

/-- **T4 (put side).** The mirrored bounds, obtained from the call bounds by
parity (T2) — so this is a corollary, not an independent analytic claim: every
inequality below is `t4_call_bounds` plus `t2_put_call_parity` and `linarith`. -/
theorem t4_put_bounds (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :
    max (K * Real.exp (-r * tau) - S * Real.exp (-q * tau)) 0
      ≤ bsPut S K tau r q sigma ∧
    bsPut S K tau r q sigma ≤ K * Real.exp (-r * tau) := by
  obtain ⟨hlo, hhi⟩ := t4_call_bounds S K tau r q sigma hS hK htau hsigma
  have hpar := t2_put_call_parity S K tau r q sigma
  have h0 : 0 ≤ bsCall S K tau r q sigma := le_trans (le_max_right _ _) hlo
  have h1 : S * Real.exp (-q * tau) - K * Real.exp (-r * tau) ≤ bsCall S K tau r q sigma :=
    le_trans (le_max_left _ _) hlo
  exact ⟨max_le (by linarith) (by linarith), by linarith⟩

-- --------------------------------------------------------------------------
-- T5  [BUILT]  the closed form solves the BSM PDE
-- --------------------------------------------------------------------------

/-!
### Why T5 is proved in `(S, tau)` and not in `x = Real.log S`

`docs/04`'s spine section originally argued for reducing to the heat equation
in `x = Real.log S` before differentiating ("doing it in `S` coordinates buys
nothing and costs every `1/S` factor by hand"). That is wrong for *this*
theorem, and the correction is a computation rather than a preference. See
BRIEF_006 for the full argument; the short form:

write `V = F * Phi(d1) - D * Phi(d2)` with `F = S * e^{-q*tau}` and
`D = K * e^{-r*tau}`. The two actions the chain rule needs are

    dd1/dS = dd2/dS = 1/(S * sigma * sqrt tau)   -- T1 read in S: `d1 - d2` is S-constant
    dd1/dtau - dd2/dtau = sigma/(2 * sqrt tau)   -- T1 read in tau: differentiate both sides

and T3 cancels the `phi`-terms *in S*, where they enter with equal and opposite
coefficients. So the `S^2 * V_SS` term costs exactly ONE division-clearing
lemma, not one per `1/S`: T1 and T3 supply the actions. The `x = log S` route
replaces that lemma with a change-of-variable transfer plus a second statement
of the PDE in the new gauge, and leaves the `1/sqrt tau` structure of the
tau-derivative exactly as it is -- more work for less machine-checked contract.
What it genuinely buys (constant coefficients, convolution with the Gaussian
kernel, uniqueness) is T6 sub-goal (3)'s content, not T5's.

The spine's *content* claim is unchanged and is what this section implements:

    T5  =  T3  +  chain rule  +  `HasDerivAt Phi phi`

`scripts/lean_lint.py`'s `[SPINE]` check now enforces that route structurally,
because a brute-force differentiation of `erf` composed with a log-rational
would prove the same theorem while duplicating T3.
-/

/-- **`erf` is differentiable**, with derivative `(2/sqrt pi) * e^{-x^2}`: the
right-endpoint derivative of the interval integral that defines `erf`
(`intervalIntegral.integral_hasDerivAt_right`, the interval-integral FTC),
scaled by the constant `2/sqrt pi`. Everything T1-T4 needed about `erf` was
its *oddness*; T5 needs its derivative, and mathlib v4.34.0 still has no
`Real.erf`, so it is derived here rather than imported. -/
theorem hasDerivAt_erf (x : ℝ) :
    HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(x ^ 2))) x := by
  have hcont : Continuous fun t : ℝ => Real.exp (-(t ^ 2)) := by continuity
  have hFTC : HasDerivAt (fun u : ℝ => ∫ t in (0:ℝ)..u, Real.exp (-(t ^ 2)))
      (Real.exp (-(x ^ 2))) x :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 x)
      (hcont.stronglyMeasurableAtFilter MeasureTheory.volume (nhds x)) hcont.continuousAt
  -- `erf` *is* the constant multiple of that integral, so the goal's function is
  -- this lambda up to unfolding. Carry that unfolding as an explicit `funext`
  -- equation -- the `rw [erf]` that T1-T4 already use -- instead of leaving a
  -- `simp`-style check to push a `noncomputable def` through a `HasDerivAt` goal.
  have hfun : erf = fun u : ℝ => (2 / Real.sqrt Real.pi) * ∫ t in (0:ℝ)..u, Real.exp (-(t ^ 2)) := by
    funext u
    rw [erf]
  rw [hfun]
  exact hFTC.const_mul (2 / Real.sqrt Real.pi)

/-- **`Phi' = phi`** -- the one genuinely new analytic input T5 needs, and the
only place in the tree where the Gaussian normalization has to be carried
through a derivative. `Phi` is `(1 + erf (x / sqrt 2)) / 2`, so the chain rule
gives `(2/sqrt pi) * e^{-(x/sqrt 2)^2} * (1/sqrt 2) / 2`, and the two algebra
steps are `(x/sqrt 2)^2 = x^2/2` and `(2/sqrt pi)(1/sqrt 2)/2 =
1/sqrt (2*pi)`. -/
theorem hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := by
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hinner : HasDerivAt (fun y : ℝ => y / Real.sqrt 2) (1 / Real.sqrt 2) x :=
    (hasDerivAt_id' (x := x)).div_const (Real.sqrt 2)
  have herf : HasDerivAt (fun y : ℝ => erf (y / Real.sqrt 2))
      ((2 / Real.sqrt Real.pi) * Real.exp (-((x / Real.sqrt 2) ^ 2)) * (1 / Real.sqrt 2)) x := by
    -- `comp` is stated for the *composite* `erf ∘ (· / √2)`. Elaborate it with no
    -- expected type, so the outer function is read off `hasDerivAt_erf`'s own type
    -- (`h₂ = erf`) instead of being solved for against the goal's lambda form; then
    -- carry the unfolding between the two forms as an explicit `funext` equation
    -- (`Function.comp_apply` is a rewrite, not a defeq step).
    have hcomp := (hasDerivAt_erf (x / Real.sqrt 2)).comp x hinner
    have hfun : (erf ∘ fun y : ℝ => y / Real.sqrt 2) = fun y : ℝ => erf (y / Real.sqrt 2) := by
      funext y
      simp only [Function.comp_apply]
    rw [hfun] at hcomp
    exact hcomp
  have hmain : HasDerivAt (fun y : ℝ => (1 + erf (y / Real.sqrt 2)) / 2)
      ((2 / Real.sqrt Real.pi) * Real.exp (-((x / Real.sqrt 2) ^ 2)) * (1 / Real.sqrt 2) / 2) x :=
    (((hasDerivAt_const (x := x) (c := (1 : ℝ))).add herf).div_const 2).congr_deriv (by ring)
  have hval : (2 / Real.sqrt Real.pi) * Real.exp (-((x / Real.sqrt 2) ^ 2)) * (1 / Real.sqrt 2) / 2
      = phi x := by
    have hsq : (x / Real.sqrt 2) ^ 2 = x ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hexp : Real.exp (-((x / Real.sqrt 2) ^ 2)) = Real.exp (-(x ^ 2) / 2) := by
      rw [hsq]
      congr 1
      ring
    rw [hexp, phi, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    -- The one place the two Gaussian normalizations meet. Clearing the four
    -- denominators (`sqrt pi`, `sqrt 2`, the numeral `2`, and `sqrt 2 * sqrt pi`)
    -- leaves a *commutativity*: `2 * E * (sqrt 2 * sqrt pi) = 2 * E * sqrt 2 * sqrt pi`.
    -- Note what is NOT needed: no `Real.sq_sqrt`/`mul_self_sqrt` rewrite appears
    -- anywhere in T5, because the sqrt factors cancel as quotients (`a / sqrt 2 *
    -- sqrt 2 = a`, licensed by `sqrt 2 ≠ 0`), never as squares.
    have hsqrt2pi : Real.sqrt 2 * Real.sqrt Real.pi ≠ 0 := mul_ne_zero h2 hpi
    -- As in the four division-clearing lemmas below, `field_simp` normalizes what
    -- it produced and already closes the goal; a following `ring` would be
    -- `No goals to be solved`.
    field_simp
  have hPhi : HasDerivAt (fun y : ℝ => (1 + erf (y / Real.sqrt 2)) / 2) (phi x) x :=
    hmain.congr_deriv hval
  -- `Phi` *is* that lambda -- but the goal's occurrence of `Phi` is unapplied, and
  -- `simp only [Phi]` matches the *applied* equation `Phi y = …`, so it cannot
  -- rewrite it. Carry the unfolding as an explicit `funext` equation instead.
  have hfun : Phi = fun y : ℝ => (1 + erf (y / Real.sqrt 2)) / 2 := by
    funext y
    simp only [Phi]
  rw [hfun]
  exact hPhi

/-- **The spot derivative of the shared `d1`/`d2` shape.** For
`x : (Real.log (x / K) + c) / (sigma * sqrt tau)` the derivative at `S` is
`1 / (S * sigma * sqrt tau)`: the `sigma * sqrt tau` scaling is constant in
`x`, and `d/dx (Real.log (x / K)) = 1 / x`.

Instantiating `c` gives `dd1/dS = dd2/dS = 1/(S * sigma * sqrt tau)` -- **the
two spot actions agree** -- which is the first half of what T3 cancels, and it
is why the `S`-coordinate route needs one division-clearing lemma rather than
one per `1/S`. -/
theorem hasDerivAt_d_spot (K tau sigma c S : ℝ) (hK : 0 < K) (htau : 0 < tau)
    (hsigma : sigma ≠ 0) (hS : 0 < S) :
    HasDerivAt (fun x : ℝ => (Real.log (x / K) + c) / (sigma * Real.sqrt tau))
      (1 / (S * sigma * Real.sqrt tau)) S := by
  have hsqrt : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr htau).ne'
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x / K)) (1 / S) S := by
    have hinner : HasDerivAt (fun x : ℝ => x / K) (1 / K) S :=
      (hasDerivAt_id' (x := S)).div_const K
    refine ((Real.hasDerivAt_log (div_ne_zero hS.ne' hK.ne')).comp S hinner).congr_deriv ?_
    -- `(S / K)⁻¹ * (1 / K) = 1 / S`: `inv_div` first, so no inverse-of-a-quotient
    -- survives to be guessed at; then two quotients cancel.
    rw [inv_div]
    -- `field_simp` normalizes what it produces and already closes this goal; a
    -- following `ring` would be `No goals to be solved`.
    field_simp
  have hnum : HasDerivAt (fun x : ℝ => Real.log (x / K) + c) (1 / S) S :=
    (hlog.add (hasDerivAt_const (x := S) (c := c))).congr_deriv (by ring)
  -- `(1/S) / (sigma*sqrt tau) = 1 / (S*sigma*sqrt tau)`: the same cancellation the
  -- `S`-coordinate route is often accused of costing "by hand" for every `1/S`.
  have hden : sigma * Real.sqrt tau ≠ 0 := mul_ne_zero hsigma hsqrt
  have hden' : S * sigma * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (mul_ne_zero hS.ne' hsigma) hsqrt
  refine (hnum.div_const (sigma * Real.sqrt tau)).congr_deriv ?_
  field_simp

/-- Arithmetic core of the tau-derivative of the shared `d1`/`d2` shape: the
quotient-rule expression, cleaned. `sqrt tau` is abstracted to `s` and the
*only* relation the ring step needs is handed in as the hypothesis `s ^ 2 =
tau` -- which is exactly `Real.sq_sqrt htau.le` at the use site, so the two
never drift apart. -/
theorem d_tau_quotient_eq (A c sigma s tau : ℝ) (hs : s ^ 2 = tau) (hs0 : s ≠ 0)
    (hsigma : sigma ≠ 0) :
    (c * (sigma * s) - (A + c * tau) * (sigma * (1 / (2 * s)))) / (sigma * s) ^ 2
      = (c - A / tau) / (2 * sigma * s) := by
  have htau : tau ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero 2 hs0
  have hDs : (sigma * s) ^ 2 ≠ 0 := by
    rw [mul_pow]
    exact mul_ne_zero (pow_ne_zero 2 hsigma) (pow_ne_zero 2 hs0)
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  have h2s : (2 : ℝ) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
  have h2ss : (2 : ℝ) * sigma * s ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hsigma) hs0
  -- Everything the quotient rule produced is a quotient; clear them all at once
  -- (`τ` for the `A / τ` factor, `(σ s)^2`, `2 σ s` for the two sides, `2 s` for
  -- the middle term), then the remaining goal is a polynomial identity.
  field_simp
  rw [← hs]
  ring

/-- **The tau-derivative of the shared `d1`/`d2` shape**: for
`u : (A + c * u) / (sigma * sqrt u)` the derivative at `tau` is
`(c - A / tau) / (2 * sigma * sqrt tau)`. The quotient rule
(`HasDerivAt.div`) produces the expression `d_tau_quotient_eq` cleans.

Instantiating `c` gives `dd1/dtau` and `dd2/dtau`; their *difference* is
`d1_tau_sub_d2_tau` below, which is what T5's `phi`-terms collapse to. -/
theorem hasDerivAt_d_tau (A c tau sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    HasDerivAt (fun u : ℝ => (A + c * u) / (sigma * Real.sqrt u))
      ((c - A / tau) / (2 * sigma * Real.sqrt tau)) tau := by
  have hsqrt : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr htau).ne'
  have hnum : HasDerivAt (fun u : ℝ => A + c * u) c tau :=
    ((hasDerivAt_const (x := tau) (c := A)).add
      ((hasDerivAt_id' (x := tau)).const_mul c)).congr_deriv (by ring)
  have hden : HasDerivAt (fun u : ℝ => sigma * Real.sqrt u)
      (sigma * (1 / (2 * Real.sqrt tau))) tau :=
    -- `hasDerivAt_sqrt`'s point is implicit and its hypothesis is `x ≠ 0`, so the
    -- proof handed in fixes the point: `hsqrt : √tau ≠ 0` would instantiate it at
    -- `√tau` (derivative `1/(2*√√tau)`), so hand it `htau.ne'` and let `x = tau`.
    (Real.hasDerivAt_sqrt htau.ne').const_mul sigma
  refine ((hnum.div hden (mul_ne_zero hsigma hsqrt)).congr_deriv ?_)
  exact d_tau_quotient_eq A c sigma (Real.sqrt tau) tau (Real.sq_sqrt htau.le) hsqrt hsigma

/-- **The tau-actions of `d1` and `d2` differ by exactly `sigma / (2 * sqrt
tau)`** -- T1 (`d1 - d2 = sigma * sqrt tau`) differentiated in `tau`. This is
the second half of T3's cancellation: with the tilting identity
`S e^{-q*tau} phi(d1) = K e^{-r*tau} phi(d2)`, the two `phi`-terms of
`dV/dtau` combine into `S e^{-q*tau} phi(d1)` times this difference, and the
resulting `sigma / (2 * sqrt tau)` is exactly what the `(sigma^2/2) S^2 V_SS`
term contributes to the operator. -/
theorem d1_tau_sub_d2_tau (S K tau r q sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    (r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau) / (2 * sigma * Real.sqrt tau)
      - (r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau) / (2 * sigma * Real.sqrt tau)
      = sigma / (2 * Real.sqrt tau) := by
  have hsqrt : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr htau).ne'
  rw [← sub_div]
  have hnum : (r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
      - (r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau) = sigma ^ 2 := by ring
  rw [hnum]
  have hd : (2 : ℝ) * sigma * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hsigma) hsqrt
  have hd' : (2 : ℝ) * Real.sqrt tau ≠ 0 := mul_ne_zero two_ne_zero hsqrt
  field_simp

/-- **T5, the delta.** `dV/dS = e^{-q*tau} Phi(d1)` for the closed form, with
**T3 doing the work**: the chain rule gives

    e^{-q*tau} Phi(d1) + [S e^{-q*tau} phi(d1) - K e^{-r*tau} phi(d2)] / (S sigma sqrt tau)

and the bracket is zero by `t3_delta_identity`, because `dd1/dS = dd2/dS`.
Differentiating `erf` composed with the log-rational directly would prove the
same thing while duplicating T3; the proof below cites it instead, and
`scripts/lean_lint.py`'s `[SPINE]` check enforces the citation. -/
theorem t5_delta (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    deriv (fun x => bsCall x K tau r q sigma) S
      = Real.exp (-q * tau) * Phi (d1 S K tau r q sigma) := by
  have hsqrt : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr htau).ne'
  have hd1S : HasDerivAt (fun x : ℝ => d1 x K tau r q sigma)
      (1 / (S * sigma * Real.sqrt tau)) S := by
    simpa only [d1] using
      hasDerivAt_d_spot K tau sigma ((r - q + sigma ^ 2 / 2) * tau) S hK htau hsigma hS
  have hd2S : HasDerivAt (fun x : ℝ => d2 x K tau r q sigma)
      (1 / (S * sigma * Real.sqrt tau)) S := by
    simpa only [d2] using
      hasDerivAt_d_spot K tau sigma ((r - q - sigma ^ 2 / 2) * tau) S hK htau hsigma hS
  have hΦ1 : HasDerivAt (fun x : ℝ => Phi (d1 x K tau r q sigma))
      (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau))) S := by
    -- `comp` returns the *composite* `Phi ∘ d1`. Elaborate it with no expected
    -- type, so the outer function is read off `hasDerivAt_Phi`'s own type
    -- (`h₂ = Phi`) instead of being solved for against the goal's lambda form; then
    -- carry the unfolding between the two forms as an explicit `funext` equation.
    have hcomp := (hasDerivAt_Phi (d1 S K tau r q sigma)).comp S hd1S
    have hfun : (Phi ∘ fun x : ℝ => d1 x K tau r q sigma)
        = fun x : ℝ => Phi (d1 x K tau r q sigma) := by
      funext x
      simp only [Function.comp_apply]
    rw [hfun] at hcomp
    exact hcomp
  have hΦ2 : HasDerivAt (fun x : ℝ => Phi (d2 x K tau r q sigma))
      (phi (d2 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau))) S := by
    have hcomp := (hasDerivAt_Phi (d2 S K tau r q sigma)).comp S hd2S
    have hfun : (Phi ∘ fun x : ℝ => d2 x K tau r q sigma)
        = fun x : ℝ => Phi (d2 x K tau r q sigma) := by
      funext x
      simp only [Function.comp_apply]
    rw [hfun] at hcomp
    exact hcomp
  have hF : HasDerivAt (fun x : ℝ => x * Real.exp (-q * tau)) (Real.exp (-q * tau)) S := by
    simpa using (hasDerivAt_id' (x := S)).mul_const (Real.exp (-q * tau))
  have hP : HasDerivAt (fun x : ℝ => x * Real.exp (-q * tau) * Phi (d1 x K tau r q sigma))
      (Real.exp (-q * tau) * Phi (d1 S K tau r q sigma)
        + (S * Real.exp (-q * tau))
          * (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))) S :=
    hF.mul hΦ1
  have hQ : HasDerivAt (fun x : ℝ => K * Real.exp (-r * tau) * Phi (d2 x K tau r q sigma))
      ((K * Real.exp (-r * tau))
        * (phi (d2 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))) S :=
    hΦ2.const_mul (K * Real.exp (-r * tau))
  have hclean : (Real.exp (-q * tau) * Phi (d1 S K tau r q sigma)
        + (S * Real.exp (-q * tau))
          * (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau))))
      - (K * Real.exp (-r * tau))
          * (phi (d2 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))
      = Real.exp (-q * tau) * Phi (d1 S K tau r q sigma) := by
    have hzero : (S * Real.exp (-q * tau))
          * (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))
        - (K * Real.exp (-r * tau))
          * (phi (d2 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau))) = 0 := by
      have hT3 := t3_delta_identity S K tau r q sigma hS hK htau hsigma
      have hfac : (S * Real.exp (-q * tau))
            * (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))
          - (K * Real.exp (-r * tau))
            * (phi (d2 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))
          = (S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)
              - K * Real.exp (-r * tau) * phi (d2 S K tau r q sigma))
              * (1 / (S * sigma * Real.sqrt tau)) := by ring
      have hcancel : S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)
          - K * Real.exp (-r * tau) * phi (d2 S K tau r q sigma) = 0 := by
        rw [hT3]
        ring
      rw [hfac, hcancel, zero_mul]
    linarith
  have hgoal : HasDerivAt (fun x : ℝ => bsCall x K tau r q sigma)
      (Real.exp (-q * tau) * Phi (d1 S K tau r q sigma)) S :=
    (hP.sub hQ).congr_deriv hclean
  exact hgoal.deriv

/-- **T5, the gamma.** `d^2V/dS^2 = e^{-q*tau} phi(d1) / (S sigma sqrt tau)`,
which is `Phi' = phi` applied to the delta: on a neighbourhood of `S` the
function `x : deriv (bsCall) x` *is* `x : e^{-q*tau} Phi (d1 x)` by
`t5_delta`, so `HasDerivAt.congr_of_eventuallyEq` moves the derivative across
and `hasDerivAt_Phi` finishes it. No T3 here -- T3 was spent on the delta. -/
theorem t5_gamma (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    deriv (fun x => deriv (fun y => bsCall y K tau r q sigma) x) S
      = Real.exp (-q * tau) * phi (d1 S K tau r q sigma) / (S * sigma * Real.sqrt tau) := by
  have hsqrt : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr htau).ne'
  have hd1S : HasDerivAt (fun x : ℝ => d1 x K tau r q sigma)
      (1 / (S * sigma * Real.sqrt tau)) S := by
    simpa only [d1] using
      hasDerivAt_d_spot K tau sigma ((r - q + sigma ^ 2 / 2) * tau) S hK htau hsigma hS
  have hΦ1 : HasDerivAt (fun x : ℝ => Phi (d1 x K tau r q sigma))
      (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau))) S := by
    -- `comp` returns the *composite* `Phi ∘ d1`. Elaborate it with no expected
    -- type, so the outer function is read off `hasDerivAt_Phi`'s own type
    -- (`h₂ = Phi`) instead of being solved for against the goal's lambda form; then
    -- carry the unfolding between the two forms as an explicit `funext` equation.
    have hcomp := (hasDerivAt_Phi (d1 S K tau r q sigma)).comp S hd1S
    have hfun : (Phi ∘ fun x : ℝ => d1 x K tau r q sigma)
        = fun x : ℝ => Phi (d1 x K tau r q sigma) := by
      funext x
      simp only [Function.comp_apply]
    rw [hfun] at hcomp
    exact hcomp
  have hdelta : HasDerivAt (fun x : ℝ => Real.exp (-q * tau) * Phi (d1 x K tau r q sigma))
      (Real.exp (-q * tau)
        * (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))) S :=
    hΦ1.const_mul (Real.exp (-q * tau))
  have hloc : (fun x => deriv (fun y => bsCall y K tau r q sigma) x)
      =ᶠ[nhds S] (fun x => Real.exp (-q * tau) * Phi (d1 x K tau r q sigma)) := by
    filter_upwards [Ioo_mem_nhds hS (by linarith : S < 2 * S)] with x hx
    exact t5_delta x K tau r q sigma hx.1 hK htau hsigma
  have hmain : HasDerivAt (fun x => deriv (fun y => bsCall y K tau r q sigma) x)
      (Real.exp (-q * tau)
        * (phi (d1 S K tau r q sigma) * (1 / (S * sigma * Real.sqrt tau)))) S :=
    hdelta.congr_of_eventuallyEq hloc
  rw [hmain.deriv]
  ring

/-- **T5, the tau-derivative.** The closed form differentiated in `tau`, from
the chain rule plus **both halves of T3's cancellation**:

    dV/dtau = -q F Phi(d1) + r D Phi(d2) + (sigma/(2 sqrt tau)) F phi(d1)

with `F = S e^{-q*tau}`, `D = K e^{-r*tau}`: the two `phi`-terms combine, by
`t3_delta_identity`, into `F phi(d1)` times the tau-action difference
`d1_tau_sub_d2_tau = sigma/(2 sqrt tau)`.

Stated as `HasDerivAt` rather than as a `deriv` value because the
calendar-time form of T5 (`t5_bsCall_pde`) differentiates the *composite*
`t : V(S, T - t)`, which needs the chain rule, not a value at a point. -/
theorem t5_tau (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    HasDerivAt (fun u => bsCall S K u r q sigma)
      (-q * (S * Real.exp (-q * tau) * Phi (d1 S K tau r q sigma))
        + r * (K * Real.exp (-r * tau) * Phi (d2 S K tau r q sigma))
        + (sigma / (2 * Real.sqrt tau))
            * (S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma))) tau := by
  have hsqrt : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr htau).ne'
  have hd1 : HasDerivAt (fun u : ℝ => d1 S K u r q sigma)
      ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau) / (2 * sigma * Real.sqrt tau)) tau := by
    simpa only [d1] using
      hasDerivAt_d_tau (Real.log (S / K)) (r - q + sigma ^ 2 / 2) tau sigma htau hsigma
  have hd2 : HasDerivAt (fun u : ℝ => d2 S K u r q sigma)
      ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau) / (2 * sigma * Real.sqrt tau)) tau := by
    simpa only [d2] using
      hasDerivAt_d_tau (Real.log (S / K)) (r - q - sigma ^ 2 / 2) tau sigma htau hsigma
  have hΦ1 : HasDerivAt (fun u : ℝ => Phi (d1 S K u r q sigma))
      (phi (d1 S K tau r q sigma)
        * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau) / (2 * sigma * Real.sqrt tau))) tau := by
    -- the composition-form bridge again, in `u` instead of `x`
    have hcomp := (hasDerivAt_Phi (d1 S K tau r q sigma)).comp tau hd1
    have hfun : (Phi ∘ fun u : ℝ => d1 S K u r q sigma)
        = fun u : ℝ => Phi (d1 S K u r q sigma) := by
      funext u
      simp only [Function.comp_apply]
    rw [hfun] at hcomp
    exact hcomp
  have hΦ2 : HasDerivAt (fun u : ℝ => Phi (d2 S K u r q sigma))
      (phi (d2 S K tau r q sigma)
        * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau) / (2 * sigma * Real.sqrt tau))) tau := by
    have hcomp := (hasDerivAt_Phi (d2 S K tau r q sigma)).comp tau hd2
    have hfun : (Phi ∘ fun u : ℝ => d2 S K u r q sigma)
        = fun u : ℝ => Phi (d2 S K u r q sigma) := by
      funext u
      simp only [Function.comp_apply]
    rw [hfun] at hcomp
    exact hcomp
  have hF : HasDerivAt (fun u : ℝ => S * Real.exp (-q * u)) (-q * (S * Real.exp (-q * tau))) tau := by
    have hlin : HasDerivAt (fun u : ℝ => -q * u) (-q) tau := by
      simpa using (hasDerivAt_id' (x := tau)).const_mul (-q)
    exact ((hlin.exp).const_mul S).congr_deriv (by ring)
  have hD : HasDerivAt (fun u : ℝ => K * Real.exp (-r * u)) (-r * (K * Real.exp (-r * tau))) tau := by
    have hlin : HasDerivAt (fun u : ℝ => -r * u) (-r) tau := by
      simpa using (hasDerivAt_id' (x := tau)).const_mul (-r)
    exact ((hlin.exp).const_mul K).congr_deriv (by ring)
  have hP : HasDerivAt (fun u : ℝ => S * Real.exp (-q * u) * Phi (d1 S K u r q sigma))
      ((-q * (S * Real.exp (-q * tau))) * Phi (d1 S K tau r q sigma)
        + (S * Real.exp (-q * tau))
          * (phi (d1 S K tau r q sigma)
            * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
                / (2 * sigma * Real.sqrt tau)))) tau :=
    hF.mul hΦ1
  have hQ : HasDerivAt (fun u : ℝ => K * Real.exp (-r * u) * Phi (d2 S K u r q sigma))
      ((-r * (K * Real.exp (-r * tau))) * Phi (d2 S K tau r q sigma)
        + (K * Real.exp (-r * tau))
          * (phi (d2 S K tau r q sigma)
            * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau)
                / (2 * sigma * Real.sqrt tau)))) tau :=
    hD.mul hΦ2
  have hclean : ((-q * (S * Real.exp (-q * tau))) * Phi (d1 S K tau r q sigma)
        + (S * Real.exp (-q * tau))
          * (phi (d1 S K tau r q sigma)
            * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
                / (2 * sigma * Real.sqrt tau))))
      - ((-r * (K * Real.exp (-r * tau))) * Phi (d2 S K tau r q sigma)
        + (K * Real.exp (-r * tau))
          * (phi (d2 S K tau r q sigma)
            * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau)
                / (2 * sigma * Real.sqrt tau))))
      = -q * (S * Real.exp (-q * tau) * Phi (d1 S K tau r q sigma))
        + r * (K * Real.exp (-r * tau) * Phi (d2 S K tau r q sigma))
        + (sigma / (2 * Real.sqrt tau))
            * (S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)) := by
    have hT3 := t3_delta_identity S K tau r q sigma hS hK htau hsigma
    have hV := d1_tau_sub_d2_tau S K tau r q sigma htau hsigma
    have hφ : (S * Real.exp (-q * tau))
          * (phi (d1 S K tau r q sigma)
            * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
                / (2 * sigma * Real.sqrt tau)))
        - (K * Real.exp (-r * tau))
          * (phi (d2 S K tau r q sigma)
            * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau)
                / (2 * sigma * Real.sqrt tau)))
        = (sigma / (2 * Real.sqrt tau))
            * (S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)) := by
      have hp : (S * Real.exp (-q * tau))
            * (phi (d1 S K tau r q sigma)
              * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
                  / (2 * sigma * Real.sqrt tau)))
          = (S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma))
              * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
                  / (2 * sigma * Real.sqrt tau)) := by ring
      have hq : (K * Real.exp (-r * tau))
            * (phi (d2 S K tau r q sigma)
              * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau)
                  / (2 * sigma * Real.sqrt tau)))
          = (K * Real.exp (-r * tau) * phi (d2 S K tau r q sigma))
              * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau)
                  / (2 * sigma * Real.sqrt tau)) := by ring
      -- the shared factor sits on the LEFT of both products, so factor it with
      -- `← mul_sub`, not `← sub_mul`.
      rw [hp, hq, hT3.symm, ← mul_sub, hV]
      ring
    have hsplit : ((-q * (S * Real.exp (-q * tau))) * Phi (d1 S K tau r q sigma)
          + (S * Real.exp (-q * tau))
            * (phi (d1 S K tau r q sigma)
              * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
                  / (2 * sigma * Real.sqrt tau))))
        - ((-r * (K * Real.exp (-r * tau))) * Phi (d2 S K tau r q sigma)
          + (K * Real.exp (-r * tau))
            * (phi (d2 S K tau r q sigma)
              * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau)
                  / (2 * sigma * Real.sqrt tau))))
        = ((-q * (S * Real.exp (-q * tau))) * Phi (d1 S K tau r q sigma)
            - (-r * (K * Real.exp (-r * tau))) * Phi (d2 S K tau r q sigma))
          + ((S * Real.exp (-q * tau))
              * (phi (d1 S K tau r q sigma)
                * ((r - q + sigma ^ 2 / 2 - Real.log (S / K) / tau)
                    / (2 * sigma * Real.sqrt tau)))
            - (K * Real.exp (-r * tau))
              * (phi (d2 S K tau r q sigma)
                * ((r - q - sigma ^ 2 / 2 - Real.log (S / K) / tau)
                    / (2 * sigma * Real.sqrt tau)))) := by ring
    rw [hsplit, hφ]
    ring
  -- `bsCall` unfolds to the lambda form, while `HasDerivAt.sub` produced the `Pi`
  -- form `(fun u ↦ …) - fun u ↦ …`. Rewrite the goal's *function* along an explicit
  -- `funext` equation, so the two sides are the same term instead of asking a
  -- `simpa`-style check to unfold `bsCall` and the `Pi` subtraction.
  have hPi : ((fun u : ℝ => S * Real.exp (-q * u) * Phi (d1 S K u r q sigma))
        - (fun u : ℝ => K * Real.exp (-r * u) * Phi (d2 S K u r q sigma)))
      = fun u : ℝ => bsCall S K u r q sigma := by
    funext u
    simp only [Pi.sub_apply, bsCall]
  rw [← hPi]
  exact (hP.sub hQ).congr_deriv hclean

/-- **T5, the `tau`-gauge form.** `V_t + (r - q) S V_S + (sigma^2/2) S^2 V_SS
= r V` for the closed form, with `tau = T - t` kept fixed and `V_t` written as
`-dV/dtau` (the chain rule for `t : T - t`, whose derivative is `-1`). -/
theorem t5_bsCall_pde_tau (S K tau r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :
    -deriv (fun u => bsCall S K u r q sigma) tau
      + (r - q) * S * deriv (fun x => bsCall x K tau r q sigma) S
      + (sigma ^ 2 / 2) * S ^ 2
          * deriv (fun x => deriv (fun y => bsCall y K tau r q sigma) x) S
      = r * bsCall S K tau r q sigma := by
  have hsqrt : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr htau).ne'
  have hΘ : deriv (fun u => bsCall S K u r q sigma) tau
      = -q * (S * Real.exp (-q * tau) * Phi (d1 S K tau r q sigma))
        + r * (K * Real.exp (-r * tau) * Phi (d2 S K tau r q sigma))
        + (sigma / (2 * Real.sqrt tau))
            * (S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)) :=
    (t5_tau S K tau r q sigma hS hK htau hsigma).deriv
  have hΔ := t5_delta S K tau r q sigma hS hK htau hsigma
  have hΓ := t5_gamma S K tau r q sigma hS hK htau hsigma
  -- the Euler action in `S`: the `S^2 V_SS` term equals `(sigma/(2 sqrt tau)) F phi(d1)`,
  -- which is exactly the term the tau-derivative contributed. One division, one lemma.
  have hEuler : (sigma ^ 2 / 2) * S ^ 2
      * (Real.exp (-q * tau) * phi (d1 S K tau r q sigma) / (S * sigma * Real.sqrt tau))
      = (sigma / (2 * Real.sqrt tau))
          * (S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)) := by
    have hden : S * sigma * Real.sqrt tau ≠ 0 :=
      mul_ne_zero (mul_ne_zero hS.ne' hsigma) hsqrt
    have h2t : (2 : ℝ) * Real.sqrt tau ≠ 0 := mul_ne_zero two_ne_zero hsqrt
    field_simp
  rw [hΘ, hΔ, hΓ]
  unfold bsCall
  rw [← hEuler]
  ring

/-- **T5.** The closed form solves the BSM PDE

    V_t + (r - q) * S * V_S + (sigma^2 / 2) * S^2 * V_SS = r * V

in calendar time, which is the form `docs/04` states and the form
`tests/test_bs.py::test_pde_residual_vanishes` checks numerically: `V` is
`(S, t) : bsCall S K (T - t) r q sigma`, so `V_t` here is an honest `deriv` in
`t` (not a re-labelled `-dV/dtau`), and `V_S`, `V_SS` are spot derivatives at
`tau = T - t`. The proof is the chain rule for `t : T - t` applied to
`t5_bsCall_pde_tau`; the hypothesis `0 < T - t` is the oracle's guard on
`tau`. -/
theorem t5_bsCall_pde (S K T t r q sigma : ℝ)
    (hS : 0 < S) (hK : 0 < K) (hTt : 0 < T - t) (hsigma : sigma ≠ 0) :
    deriv (fun u => bsCall S K (T - u) r q sigma) t
      + (r - q) * S * deriv (fun x => bsCall x K (T - t) r q sigma) S
      + (sigma ^ 2 / 2) * S ^ 2
          * deriv (fun x => deriv (fun y => bsCall y K (T - t) r q sigma) x) S
      = r * bsCall S K (T - t) r q sigma := by
  -- `const_sub` is stated for `fun x => c - f x`, which is the goal's function
  -- literally; `HasDerivAt.sub` only gives the `Pi` form `(fun x ↦ T) - fun x ↦ x`.
  have hinner : HasDerivAt (fun u : ℝ => T - u) (-1) t :=
    (hasDerivAt_id' (x := t)).const_sub T
  have hVt : deriv (fun u => bsCall S K (T - u) r q sigma) t
      = -deriv (fun u => bsCall S K u r q sigma) (T - t) := by
    -- the chain rule for `t ↦ T - t` (`HasDerivAt.comp`, not a re-gauging): the
    -- outer derivative is `t5_tau`'s, the inner one is `-1`. Both `deriv`s are
    -- rewritten -- the composite's by `hcomp`, the pointwise value's by `hτ`.
    have hτ := t5_tau S K (T - t) r q sigma hS hK hTt hsigma
    have hcomp := hτ.comp t hinner
    -- `hcomp` is stated for the *composite*; the goal differentiates the lambda form
    -- of the same function, so rewrite the function along a `funext` equation first.
    have hfun : (fun u : ℝ => bsCall S K (T - u) r q sigma)
        = (fun u : ℝ => bsCall S K u r q sigma) ∘ fun u : ℝ => T - u := by
      funext u
      simp only [Function.comp_apply]
    rw [hfun, hcomp.deriv, hτ.deriv]
    ring
  rw [hVt]
  exact t5_bsCall_pde_tau S K (T - t) r q sigma hS hK hTt hsigma

/-!
--------------------------------------------------------------------------
T6  [IN PROGRESS — research]  the Fourier pricing kernel survives a wider
                       increment law — sub-goal (b) below LANDED GREEN as
                       BRIEF_005 (PR #6, run 35536031936): see
                       ImprovedBS/Fourier.lean
--------------------------------------------------------------------------

RESTATED. The previous formulation ("transport (Fourier) kernel survives
a-stable increments") is **not reachable as written**, and it is worth being
explicit about why before anyone spends a brief on it.

If `X_tau` is a pure symmetric alpha-stable law with `alpha < 2`, then
`P(X_tau > x) ~ c * x^(-alpha)`, so

    E[exp X_tau] = ∫ e^x · c x^(-alpha) dx = ∞.

Hence `S_T = S_0 * exp(X_tau)` has **infinite first moment** and cannot
satisfy the risk-neutral martingale condition `E[S_T] = S_0 * e^{r*tau}`.
There is no equivalent martingale measure inside the exponential-Lévy ansatz,
so the Carr–Madan / Lewis Fourier integral never becomes well defined: the
pricing contour cannot be placed in a moment strip that does not exist. The
obstruction is at the *moment* step, not the *kernel* step.

The repair keeps everything the direction actually wants (algebraic tails, BS
as a limit) and is standard: **temper** the Lévy measure. In the CGMY /
Boyarchenko–Levendorskii family the Lévy density carries an `e^{-lambda*|x|}`
damping, which restores the exponential moment at the cost of one extra
parameter `lambda`, with the alpha-stable law recovered as `lambda → 0` and BS
as the `alpha = 2` corner.

So the theorem to aim at is not "stable increments still transport" but:

    **T6 (target).** Let `X` be a Lévy process with characteristic exponent
    `psi` affine in `tau`, and let the damping strip
    `{u : ℝ | E[exp (u * X_tau)] < ∞}` contain the pricing contour and `-1`
    (the martingale/numéraire point, i.e. `psi(-i) = -i*r*tau` after the
    drift is fixed). Then the Carr–Madan integral

        V = e^{-r*tau} / (2*pi) * ∫ e^{-i*u*tau} · fhat(u + i*alpha) ·
            exp(tau * psi(u + i*alpha)) du

    is absolutely convergent, real-valued on real payoffs, and agrees with
    `e^{-r*tau} * E[(S_T - K)⁺]`. GBM is the case `psi(u) = i*u*(r-q) -
    sigma^2*u^2/2` (alpha = 2, lambda = 0).

Provable sub-goals, in increasing order of commitment:
  (a) the moment-strip condition `⇔` finiteness of `E[exp(u * X_tau)]` for a
      tempered-stable exponent — this is where the alpha-stable obstruction
      above gets *proved* rather than asserted, and it is a theorem about a
      concrete integral, not about finance;
  (b) absolute convergence of the Carr–Madan integrand on a contour strictly
      inside the strip — **LANDED GREEN** as BRIEF_005 (PR #6, run
      35536031936): `integrable_exp_neg_abs_rpow`,
      `carrMadanKernel_integrable`, `carrMadan_price_integrable` and the
      two GBM instances in ImprovedBS/Fourier.lean, with the CGMY-decay
      hypothesis appearing only as a hypothesis;
  (c) agreement with the risk-neutral expectation, i.e. Fourier inversion
      against the payoff transform.

See docs/03_research.md D1, which carries the falsifier (fitted `alpha`
concentrating in `(1.3, 1.9)` and being materially *less* moneyness-dependent
than the GBM `sigma` it replaces).
-/

end BSM
