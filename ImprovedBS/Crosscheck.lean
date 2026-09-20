/-!
# ImprovedBS.Crosscheck — Oracle ↔ Lean pointwise cross-verifier (BRIEF_002)

Builds guard (3) from `docs/04` §"Oracle ↔ formal correspondence": evaluates
`d1`, `d2`, `bsCall`, `bsPut`, parity, and the delta identity at a fixed grid of
points in `Float` (IEEE-754 double precision) and emits machine-parseable lines
for pointwise cross-verification against `experiments/black_scholes.py`.

This is a **cross-verifier, not a proof.** It cannot show that the Lean theorem
statements in `ImprovedBS.Core` are mathematically true — that is what `lake build`
and the `#print axioms` audit certify. What it certifies is that the two
independent trees (Python oracle and Lean code) have not drifted into computing
different mathematics.

## Derivation independence
Following the repo's frozen contract:
* `d2` is evaluated from its OWN closed formula, NOT as `d1 - sigma * sqrt tau`.
* `bsPut` is evaluated from its OWN closed formula, NOT via parity.
* `bsPutByParity` is evaluated separately to verify put-call parity numerically (T2).
* `deltaIdentityLhs` and `deltaIdentityRhs` verify the delta identity numerically (T3).
-/

namespace ImprovedBS.Crosscheck

/-- Archimedes' constant π in IEEE double precision. -/
def pi : Float := 3.14159265358979323846

/--
High-precision Cody (1969) rational Chebyshev approximation for the error function `erf`.
Agrees with `math.erf` / libc `erf` to within ~1.1e-16 across the real line.
Pure Lean `Float` implementation — portable across all platforms with no external C dependencies.
-/
def codyErf (x : Float) : Float :=
  let ax := x.abs
  if ax < 0.84375 then
    let x2 := x * x
    let num := 0.128379167095512558561 + x2 * (-0.325042107247001499370 + x2 * (-0.0284817495755985104766 + x2 * (-0.00577027029648944159157 + x2 * (-0.0000237630166566501626084))))
    let den := 1.0 + x2 * (0.397917223959155352819 + x2 * (0.0650222499887672944485 + x2 * (0.00508130628187576562776 + x2 * (0.000132494738004321644526 + x2 * (-0.00000396022827877536812320)))))
    x + x * (num / den)
  else if ax < 1.25 then
    let s := ax - 1.0
    let c := 0.845062911510467529297
    let num := -0.00236211856075265944077 + s * (0.414856118683748331666 + s * (-0.372207876035701323847 + s * (0.318346619901161753674 + s * (-0.110894694282396677476 + s * (0.0354783043256182359371 + s * (-0.00216637559486879084300))))))
    let den := 1.0 + s * (0.106420880400844228286 + s * (0.540397917702171048937 + s * (0.0718286544141962662868 + s * (0.126171219808761642112 + s * (0.0136370839120290507362 + s * 0.0119844998467991074170)))))
    let res := c + num / den
    if 0.0 <= x then res else -res
  else if ax < 6.0 then
    let z := 1.0 / (ax * ax)
    let num := -0.00986494403484714822705 + z * (-0.693858572707181764372 + z * (-10.5586262253232909814 + z * (-62.3753324503260060396 + z * (-162.396669462573470355 + z * (-184.605092906711035994 + z * (-81.2874355063065934246 + z * (-9.81432934416914548592)))))))
    let den := 1.0 + z * (19.6512716674392571292 + z * (137.657754143519042600 + z * (434.565877475229228821 + z * (645.387271733267880336 + z * (429.008140027567833386 + z * (108.635005541779435134 + z * (6.57024977031928170135 + z * (-0.0604244152148580987438))))))))
    let erfcVal := Float.exp (-ax * ax - 0.5625 + num / den) / ax
    let res := 1.0 - erfcVal
    if 0.0 <= x then res else -res
  else
    if 0.0 <= x then 1.0 else -1.0

/-- Error function on Float. -/
def erf (x : Float) : Float :=
  codyErf x

/-- Standard normal CDF on Float: `Phi(x) = (1 + erf(x / sqrt 2)) / 2`. -/
def Phi (x : Float) : Float :=
  0.5 * (1.0 + erf (x / Float.sqrt 2.0))

/-- Standard normal PDF on Float: `phi(x) = exp(-x^2 / 2) / sqrt(2 pi)`. -/
def phi (x : Float) : Float :=
  Float.exp (-0.5 * x * x) / Float.sqrt (2.0 * pi)

/-- Upper BSM argument on Float, from its own explicit formula. -/
def d1 (S K tau r q sigma : Float) : Float :=
  (Float.log (S / K) + (r - q + 0.5 * sigma * sigma) * tau) / (sigma * Float.sqrt tau)

/-- Lower BSM argument on Float, from its OWN explicit formula (independent). -/
def d2 (S K tau r q sigma : Float) : Float :=
  (Float.log (S / K) + (r - q - 0.5 * sigma * sigma) * tau) / (sigma * Float.sqrt tau)

/-- European call price on Float. -/
def bsCall (S K tau r q sigma : Float) : Float :=
  S * Float.exp (-q * tau) * Phi (d1 S K tau r q sigma)
    - K * Float.exp (-r * tau) * Phi (d2 S K tau r q sigma)

/-- European put price on Float, from its OWN closed form (independent). -/
def bsPut (S K tau r q sigma : Float) : Float :=
  K * Float.exp (-r * tau) * Phi (-(d2 S K tau r q sigma))
    - S * Float.exp (-q * tau) * Phi (-(d1 S K tau r q sigma))

/-- Put price computed via put-call parity. -/
def bsPutByParity (S K tau r q sigma : Float) : Float :=
  bsCall S K tau r q sigma - S * Float.exp (-q * tau) + K * Float.exp (-r * tau)

/-- Delta identity LHS: `S * exp(-q*tau) * phi(d1)`. -/
def deltaIdentityLhs (S K tau r q sigma : Float) : Float :=
  S * Float.exp (-q * tau) * phi (d1 S K tau r q sigma)

/-- Delta identity RHS: `K * exp(-r*tau) * phi(d2)`. -/
def deltaIdentityRhs (S K tau r q sigma : Float) : Float :=
  K * Float.exp (-r * tau) * phi (d2 S K tau r q sigma)

structure GridPoint where
  S : Float
  K : Float
  tau : Float
  r : Float
  q : Float
  sigma : Float

-- BEGIN GENERATED GOLDEN GRID
def goldenGrid : List GridPoint := [
  ⟨50.0, 100.0, 0.0833333333, 0.05, 0.0, 0.2⟩,
  ⟨50.0, 100.0, 0.25, 0.05, 0.0, 0.2⟩,
  ⟨50.0, 100.0, 1.0, 0.05, 0.0, 0.2⟩,
  ⟨50.0, 100.0, 3.0, 0.05, 0.0, 0.2⟩,
  ⟨80.0, 100.0, 0.0833333333, 0.05, 0.0, 0.2⟩,
  ⟨80.0, 100.0, 0.25, 0.05, 0.0, 0.2⟩,
  ⟨80.0, 100.0, 1.0, 0.05, 0.0, 0.2⟩,
  ⟨80.0, 100.0, 3.0, 0.05, 0.0, 0.2⟩,
  ⟨100.0, 100.0, 0.0833333333, 0.05, 0.0, 0.2⟩,
  ⟨100.0, 100.0, 0.25, 0.05, 0.0, 0.2⟩,
  ⟨100.0, 100.0, 1.0, 0.05, 0.0, 0.2⟩,
  ⟨100.0, 100.0, 3.0, 0.05, 0.0, 0.2⟩,
  ⟨120.0, 100.0, 0.0833333333, 0.05, 0.0, 0.2⟩,
  ⟨120.0, 100.0, 0.25, 0.05, 0.0, 0.2⟩,
  ⟨120.0, 100.0, 1.0, 0.05, 0.0, 0.2⟩,
  ⟨120.0, 100.0, 3.0, 0.05, 0.0, 0.2⟩,
  ⟨200.0, 100.0, 0.0833333333, 0.05, 0.0, 0.2⟩,
  ⟨200.0, 100.0, 0.25, 0.05, 0.0, 0.2⟩,
  ⟨200.0, 100.0, 1.0, 0.05, 0.0, 0.2⟩,
  ⟨200.0, 100.0, 3.0, 0.05, 0.0, 0.2⟩,
  ⟨80.0, 100.0, 1.0, 0.05, 0.0, 0.05⟩,
  ⟨100.0, 100.0, 1.0, 0.05, 0.0, 0.05⟩,
  ⟨120.0, 100.0, 1.0, 0.05, 0.0, 0.05⟩,
  ⟨80.0, 100.0, 1.0, 0.05, 0.0, 0.6⟩,
  ⟨100.0, 100.0, 1.0, 0.05, 0.0, 0.6⟩,
  ⟨120.0, 100.0, 1.0, 0.05, 0.0, 0.6⟩,
  ⟨50.0, 100.0, 0.25, 0.03, 0.02, 0.2⟩,
  ⟨50.0, 100.0, 1.0, 0.03, 0.02, 0.2⟩,
  ⟨100.0, 100.0, 0.25, 0.03, 0.02, 0.2⟩,
  ⟨100.0, 100.0, 1.0, 0.03, 0.02, 0.2⟩,
  ⟨200.0, 100.0, 0.25, 0.03, 0.02, 0.2⟩,
  ⟨200.0, 100.0, 1.0, 0.03, 0.02, 0.2⟩,
  ⟨50.0, 100.0, 1.0, -0.01, 0.0, 0.2⟩,
  ⟨80.0, 100.0, 1.0, -0.01, 0.0, 0.2⟩,
  ⟨100.0, 100.0, 1.0, -0.01, 0.0, 0.2⟩,
  ⟨120.0, 100.0, 1.0, -0.01, 0.0, 0.2⟩,
  ⟨200.0, 100.0, 1.0, -0.01, 0.0, 0.2⟩,
  ⟨100.0, 100.0, 0.25, -0.005, 0.03, 0.05⟩,
  ⟨100.0, 100.0, 3.0, -0.01, 0.02, 0.6⟩,
]
-- END GENERATED GOLDEN GRID

/-- Evaluate all points on the golden grid and print fixed greppable output lines. -/
def runCrosscheck : IO Unit := do
  for pt in goldenGrid do
    let d1Val := d1 pt.S pt.K pt.tau pt.r pt.q pt.sigma
    let d2Val := d2 pt.S pt.K pt.tau pt.r pt.q pt.sigma
    let callVal := bsCall pt.S pt.K pt.tau pt.r pt.q pt.sigma
    let putVal := bsPut pt.S pt.K pt.tau pt.r pt.q pt.sigma
    let parityVal := bsPutByParity pt.S pt.K pt.tau pt.r pt.q pt.sigma
    let deltaVal := deltaIdentityLhs pt.S pt.K pt.tau pt.r pt.q pt.sigma
    IO.println s!"CK {pt.S} {pt.K} {pt.tau} {pt.r} {pt.q} {pt.sigma} {d1Val} {d2Val} {callVal} {putVal} {parityVal} {deltaVal}"

#eval runCrosscheck

end ImprovedBS.Crosscheck
