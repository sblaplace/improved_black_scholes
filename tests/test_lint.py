#!/usr/bin/env python3
"""
Mutation harness for the LINT -- proves `scripts/lean_lint.py` is a falsifier
about the Lean tree, not a decoration that reports OK.

Why this file exists
-------------------
`tests/test_mutants.py` applies the repo's rule ("a green check is only evidence
if it could have been red") to the oracle, and `ImprovedBS/Core.lean` applies it
to the proofs. The one artefact with *authority over the Lean tree* that had no
falsifier of its own was the linter: 20 KB of regexes over a proof assistant's
source, gating the `lake build` job via `needs: lint`, deciding "is `d2` defined
from `d1`", "does parity cite the symmetry lemma", "is the ratchet honest".
Nothing tested it. That asymmetry is the actual unverified pillar of this repo
-- not the numeric oracle, which the theorems never import.

How it works
------------
Each entry below is a plausible way to make the Lean tree *look* honest while it
is not: the original `d2 := d1 - sigma * sqrt tau` sin, a `sorry` in a protected
node, a re-baselined `deferred` map, an `axiom` (a `sorry` that survives `lake
build`), a deleted `REQUIRED` theorem, a hollowed-out oracle, and -- the one no
lane could previously see -- a protected theorem *re-stated as `True`*, which
builds, has no `sorryAx`, keeps its name, and says nothing. The last entry aims
at the one thing no *content* check can see at all: T5's delta re-deriving the
`phi`-bracket that T3 exists to supply. Every statement survives that edit, the
build is still honest, and the only false thing left is docs/04's claim about
*how* T5 is proved -- which is what `[SPINE]` is for.

Each is applied to a throwaway copy of the repository, `scripts/lean_lint.py`
is run against that copy in a subprocess, and the mutant must be KILLED by a
specific check (matched on its `[TAG]`), not merely by any failure. A mutant
killed by the wrong check means the check it was aimed at is decorative.

Three things this harness is NOT
--------------------------------
* It does not run `lake build`; the linter's contract is toolchain-free, so
  testing it must be too. Soundness of a proof stays with `lake build` + the
  `#print axioms` audit, and *statement truth* is what `scripts/pin_statements.py`
  adds on top -- which is what the `[PINS]` mutants below exercise.
* It is not a lint style checker. Every mutant is a claim about the
  *mathematics the tree certifies*, not about formatting.
* It does not only test that the lint says NO. `CONTROLS` are edits that are
  legitimate and must stay GREEN: a marker word inside a comment, a proof
  rewritten onto different lines with the same statement, and parity reproved
  via `erf_neg` directly (the same odd symmetry, one step closer to its source).
  A guard that rejects honest work is a guard that gets switched off.

Run:  python3 tests/test_lint.py     (stdlib only, ~8s, no Lean toolchain)
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, os.path.join(ROOT, "scripts"))

CORE = "ImprovedBS/Core.lean"
ORACLE = "experiments/black_scholes.py"
CROSSCHECK = "ImprovedBS/Crosscheck.lean"
SKELETON = "ImprovedBS/Skeleton.lean"
NONUNIQ = "ImprovedBS/NonUniqueness.lean"
ESSCHER = "ImprovedBS/Esscher.lean"
CORNER = "ImprovedBS/Corner.lean"
PARETO = "ImprovedBS/ParetoWitness.lean"
GOLDEN = "tests/golden_statements.json"
BASELINE = ".github/lean_lint_baseline.json"

# Scratch notes for the __main__ runner (pytest warns if a test returns a value).
LAST_NOTE: dict = {}

# Anchor: the statement of T4 exactly as it is committed.
T4_STATEMENT = (
    "theorem t4_call_bounds (S K tau r q sigma : ℝ)\n"
    "    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :\n"
    "    max (S * Real.exp (-q * tau) - K * Real.exp (-r * tau)) 0\n"
    "      ≤ bsCall S K tau r q sigma ∧\n"
    "    bsCall S K tau r q sigma ≤ S * Real.exp (-q * tau) := by"
)
T2_PROOF = "  simp only [bsPut, bsCall, Phi_neg]\n  ring"

MUTANTS = [
    # ---- the two original sins of this repository (see Core.lean's header) ----
    {
        "name": "L1 d2 defined from d1 -- makes T1 true by construction",
        "file": CORE,
        "from": "def d2 (S K tau r q sigma : ℝ) : ℝ :=\n"
                "  (Real.log (S / K) + (r - q - sigma ^ 2 / 2) * tau) / (sigma * Real.sqrt tau)",
        "to": "def d2 (S K tau r q sigma : ℝ) : ℝ :=\n"
              "  d1 S K tau r q sigma - sigma * Real.sqrt tau",
        "tag": "[INDEPENDENCE]",
    },
    {
        "name": "L2 bsPut defined from bsCall -- makes T2 tautological",
        "file": CORE,
        "from": "def bsPut (S K tau r q sigma : ℝ) : ℝ :=\n"
                "  K * Real.exp (-r * tau) * Phi (-(d2 S K tau r q sigma))\n"
                "    - S * Real.exp (-q * tau) * Phi (-(d1 S K tau r q sigma))",
        "to": "def bsPut (S K tau r q sigma : ℝ) : ℝ :=\n"
              "  bsCall S K tau r q sigma - S * Real.exp (-q * tau) + K * Real.exp (-r * tau)",
        "tag": "[INDEPENDENCE]",
    },
    {
        "name": "L3 parity proven without any odd-symmetry witness",
        "file": CORE,
        "from": T2_PROOF,
        "to": "  unfold bsPut bsCall\n  ring",
        "tag": "[INDEPENDENCE]",
    },
    # ---- deferred-proof markers, in a protected node and in a merely-required one ----
    {
        "name": "L4 sorry in a PROTECTED theorem",
        "file": CORE,
        "from": T2_PROOF,
        "to": "  sorry",
        "tag": "[PROTECTED]",
    },
    {
        "name": "L5 native_decide in a PROTECTED theorem (a `sorry` in expensive clothing)",
        "file": CORE,
        "from": "  obtain ⟨hlo, hhi⟩ := t4_call_bounds S K tau r q sigma hS hK htau hsigma",
        "to": "  native_decide",
        "tag": "[PROTECTED]",
    },
    {
        "name": "L6 sorry in a def that is REQUIRED but not PROTECTED -- the ratchet must catch it",
        "file": CORE,
        "from": "def Phi (x : ℝ) : ℝ := (1 + erf (x / Real.sqrt 2)) / 2",
        "to": "def Phi (x : ℝ) : ℝ := sorry",
        "tag": "[RATCHET]",
    },
    {
        "name": "L7 an axiom added -- a sorry that survives lake build silently",
        "file": CORE,
        "from": "end BSM",
        "to": "axiom bsm_plausible : True\n\nend BSM",
        "tag": "[AXIOMS]",
    },
    {
        "name": "L8 deleting a landed theorem (the cheapest way to pass a lint)",
        "file": CORE,
        "from": "theorem t3_delta_identity (S K tau r q sigma : ℝ)",
        "to": "theorem t3_delta_identity_retired (S K tau r q sigma : ℝ)",
        "tag": "[REQUIRED]",
    },
    {
        # A baseline entry alone is inert -- it only matters if a marker exists. So the
        # cheat is the *pair*: grant yourself a budget, then use it in a landed node.
        "name": "L9 landed node re-baselined to permit a sorry",
        "file": BASELINE,
        "json_set": {"deferred": {"t4_call_bounds": 1}},
        "also_apply": [{"file": CORE, "from": T2_PROOF, "to": "  sorry", "name": "L9b"}],
        "tag": "[PROTECTED]",
        "why": "PROTECTED must ignore the baseline entirely: a landed node cannot be "
               "moved back into the deferred budget by editing a JSON file.",
    },
    {
        "name": "L10 a new deferred node added without touching the baseline",
        "file": CORE,
        "from": "end BSM",
        "to": "-- T5 (queued): statement placeholder with a deferred proof\n"
              "theorem t5_pde_sketch : True := by\n  sorry\n\nend BSM",
        "tag": "[RATCHET]",
    },
    # ---- the oracle side of the correspondence ----
    {
        "name": "M-oracle-1 d2 rebuilt from d1 inside the oracle -- Lean and Python diverge",
        "file": ORACLE,
        "from": "    d2 = (log_m + (r - q - 0.5 * s * s) * tau) / den",
        "to": "    d2 = d1 - s * sq",
        "tag": "[ORACLE SYNC]",
    },
    {
        "name": "M-oracle-2 put derived from parity inside the oracle",
        "file": ORACLE,
        "from": "    return K * math.exp(-r * tau) * norm_cdf(-d2) - S * math.exp(-q * tau) * norm_cdf(-d1)",
        "to": "    return bs_put_by_parity(S, K, tau, r, q, s)",
        "tag": "[ORACLE SYNC]",
    },
    {
        "name": "M-oracle-3 oracle hollowed out (only prohibitions were checked before 2026-09)",
        "file": ORACLE,
        "from": "def bs_put_by_parity",
        "to": "def _unused_bs_put_by_parity",
        "tag": "[ORACLE SYNC]",
    },
    {
        "name": "M-oracle-4 oracle deleted wholesale",
        "file": ORACLE,
        "delete": True,
        "tag": "[ORACLE SYNC]",
    },
    # ---- the Float twin: guard (3) must EMIT both sides of T3, not just define them ----
    {
        "name": "CC1 twin prints the delta identity's LHS twice (the C6 item 4 defect, verbatim)",
        "file": CROSSCHECK,
        "from": "    let deltaRhsVal := deltaIdentityRhs pt.S pt.K pt.tau pt.r pt.q pt.sigma",
        "to":   "    let deltaRhsVal := deltaIdentityLhs pt.S pt.K pt.tau pt.r pt.q pt.sigma",
        "tag": "[CROSSCHECK SYNC]",
        "why": "Numerically invisible to the Python comparator: the two sides agree "
               "to ~7e-15 inside the oracle, far under the 1e-12 tolerance, so a "
               "stream that prints the LHS twice passes every numeric comparison. "
               "Only the source-level requirement that `runCrosscheck` reference "
               "`deltaIdentityRhs` can see it -- which is exactly why the guard is "
               "structural and not another numeric comparison.",
    },
    {
        "name": "CC2 deltaIdentityRhs definition deleted outright",
        "file": CROSSCHECK,
        "from": "/-- Delta identity RHS: `K * exp(-r*tau) * phi(d2)`. -/\n"
                "def deltaIdentityRhs (S K tau r q sigma : Float) : Float :=\n"
                "  K * Float.exp (-r * tau) * phi (d2 S K tau r q sigma)\n",
        "to": "",
        "tag": "[CROSSCHECK SYNC]",
    },
    # ---- statement pins: what nothing else could see ----
    {
        "name": "P1 T4 hollowed into `True` -- builds, no sorryAx, says nothing",
        "file": CORE,
        "from": T4_STATEMENT,
        "to": "theorem t4_call_bounds (S K tau r q sigma : ℝ)\n"
              "    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :\n"
              "    True := by",
        "tag": "[PINS]",
    },
    {
        "name": "P2 a hypothesis dropped from T3 (the bug this stack actually shipped once)",
        "file": CORE,
        "from": "theorem t3_delta_identity (S K tau r q sigma : ℝ)\n"
                "    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :",
        "to": "theorem t3_delta_identity (S K tau r q sigma : ℝ)\n"
              "    (hK : 0 < K) (htau : 0 < tau) (hsigma : sigma ≠ 0) :",
        "tag": "[PINS]",
    },
    {
        "name": "P3 def-body spec change: Phi's normalization divisor",
        "file": CORE,
        "from": "def Phi (x : ℝ) : ℝ := (1 + erf (x / Real.sqrt 2)) / 2",
        "to": "def Phi (x : ℝ) : ℝ := (1 + erf (x / Real.sqrt 2)) / 3",
        "tag": "[PINS]",
    },
    {
        "name": "P4 theorem quietly converted to def (leaves the checked stack)",
        "file": CORE,
        "from": "theorem t1_d1_minus_d2 (S K tau r q sigma : ℝ)",
        "to": "def t1_d1_minus_d2 (S K tau r q sigma : ℝ)",
        "tag": "[PINS]",
    },
    {
        "name": "P5 duplicate shadow declaration after the real one (last-wins dict poisoning)",
        "file": CORE,
        "from": "end BSM",
        "to": "theorem t4_call_bounds (S K tau r q sigma : ℝ)\n"
              "    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) : True :=\n"
              "  trivial\n\nend BSM",
        "tag": "[PINS]",
    },
    {
        "name": "P6 pins artifact deleted (refusing to invent a baseline)",
        "file": GOLDEN,
        "delete": True,
        "tag": "[PINS]",
    },
    {
        "name": "P7 pins artifact shrunk by dropping the interesting entry",
        "file": GOLDEN,
        "json_drop": "BSM.t4_call_bounds",
        "tag": "[PINS]",
    },
    {
        # Was KNOWN_LOCAL_GAPS[0] ("the local layer cannot see this; only CI's elab
        # can"). It added cross_layer_check(), whose whole job is this skew: layer 1
        # regenerated, layer 2 left behind. Moved here per that test's own
        # instruction -- if a gap closes, the mutant must go red until it is moved.
        "name": "P8 hollow T4 and regenerate layer 1, leaving the elaborated pin stale",
        "file": CORE,
        "from": T4_STATEMENT,
        "to": "theorem t4_call_bounds (S K tau r q sigma : ℝ)\n"
              "    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :\n"
              "    True := by",
        "also_rewrite_pins": True,
        "tag": "[PINS]",
    },
    # ---- the route, not the claim: every check above is about *what* the tree
    # says. `[SPINE]` is the only one about *how* a node gets there, and the
    # cheat it exists to see is the one that costs the reader the most: T5
    # proved by brute force, duplicating T1's `S`-action and T3's cancellation
    # inside its own proof, leaving the "dependency spine" a diagram of a
    # dependency that is not actually used. Note what the other lanes say about
    # this edit: the statement is untouched (`[PINS]` is proof-blind by design),
    # nothing is deferred, no marker appeared, nothing was deleted. If `[SPINE]`
    # does not fire, nothing does.
    {
        "name": "S1 T5's delta re-derives the phi-bracket instead of consuming T3",
        "file": CORE,
        "from": "      have hT3 := t3_delta_identity S K tau r q sigma hS hK htau hsigma",
        "to": "      have hT3 : S * Real.exp (-q * tau) * phi (d1 S K tau r q sigma)\n"
              "          - K * Real.exp (-r * tau) * phi (d2 S K tau r q sigma) = 0 := by\n"
              "        unfold phi d1 d2 erf\n"
              "        field_simp\n"
              "        ring",
        "tag": "[SPINE]",
        "why": "The proof body is where a spine is either consumed or re-derived, and "
               "a proof body is exactly what `[PINS]` cannot see (`--write` would "
               "regenerate layer 1 byte-identically). The mutant *looks* like honest "
               "local work -- a `have` with the same conclusion, proved from the "
               "definitions -- which is precisely the drift docs/04 warns about: the "
               "route is what makes T3 load-bearing, so a T5 that stops citing it "
               "leaves T3 as an orphan and the spine as a claim about a dependency "
               "graph nobody traverses.",
    },
    # ---- BRIEF_009's route, one layer down: `[SKELETON]` is [SPINE]'s twin at
    # the model-free layer. Both cheats leave every statement untouched and
    # every proof honest-looking; what they break is the *route* the abstraction
    # needs to certify anything.
    {
        "name": "K1 model-free put bounds re-derived without the parity cite",
        "file": SKELETON,
        "from": "  have hpar := model_free_put_call_parity S K tau r q X hX hE",
        "to": "  have hpar := model_free_parity_gap X K r tau hX",
        "tag": "[SKELETON]",
        "why": "`model_free_put_bounds` is the T4'-via-T2 mirror: parity + call "
               "bounds + linarith, no new integration. Deriving the needed fact "
               "locally from the unfixed gap identity (or from the payoffs) is "
               "the same drift `[SPINE]` catches at T5 -- the route is what makes "
               "the parity theorem load-bearing for every later law that inherits "
               "the put bounds by instantiation.",
    },
    {
        "name": "K2 t4 via_skeleton shortcut-circuited through t4_call_bounds itself",
        "file": SKELETON,
        "from": "  exact lognormal_call_bounds S K tau r q sigma hS.le hK.le htau.le",
        "to": "  exact t4_call_bounds S K tau r q sigma hS hK htau hsigma",
        "tag": "[SKELETON]",
        "why": "The `via_skeleton` nodes are the wire test that the model-free "
               "layer is hooked up to the closed form. A re-derivation that "
               "consumes the very theorem it re-derives is vacuous -- the "
               "abstraction would be graded by its own conclusion -- which is "
               "the sin `d2 := d1 - sigma*sqrt(tau)` committed at the "
               "definition level, one layer up. Note what the other lanes say "
               "about this edit: statement untouched, nothing deferred, no "
               "marker, nothing deleted. Only `[SKELETON]` can see it.",
    },
    {
        "name": "C1 pricing kernel on wrong line: u + iα instead of u − i(α+1) (C12)",
        "file": "ImprovedBS/Pricing.lean",
        "from": "def cmPriceKernel (φ : ℂ → ℂ) (α u : ℝ) : ℂ :=\n  φ (↑u - ↑(α + 1) * Complex.I) * (cmDenom α u)⁻¹",
        "to": "def cmPriceKernel (φ : ℂ → ℂ) (α u : ℝ) : ℂ :=\n  φ (↑u + ↑α * Complex.I) * (cmDenom α u)⁻¹",
        "tag": "[CONTOUR]",
        "why": "BRIEF_010's correction C12: the tree's kernel sits on `u + iα` "
               "while the price inverts from `u − i(α+1)`. Swapping the contour "
               "back would make the pricing identity false with a green build — "
               "74.2% relative error at the test point — and no other lane can "
               "see which line a def names, only that it exists. Only [CONTOUR] "
               "can see it, which is exactly why the check exists.",
    },
    {
        "name": "C2 CGMY decay hypothesis strengthened to the `min (G, M)` spelling (C14)",
        "file": "ImprovedBS/CGMY.lean",
        "from": "(hMG : α + 1 < M) (hτ : 0 ≤ τ) :",
        "to": "(hMG : α + 1 < min G M) (hτ : 0 ≤ τ) :",
        "tag": "[CGMY]",
        "why": "BRIEF_011's correction C14: on the pricing contour `v = u − i(α+1)` "
               "the branch condition is `α + 1 < M` because `M − iv = (M − (α+1)) − iu`, "
               "while `G + iv = (G + α+1) + iu` is in the right half plane for free. "
               "`G` binds only the OLD line `v = u + iα`, where `Re(G + iv) = G − α` "
               "(`cgmyOldContour_base_right_re`). The `min (G, M)` spelling that docs/03 "
               "§D1 and docs/04's queue used is therefore a strictly stronger hypothesis "
               "the mathematics does not need — a green build would still certify the "
               "decay, but the claim would be about a smaller model class than CGMY. "
               "Statement-level drift like this is invisible to `lake build`, to "
               "`#print axioms` (the theorem is still true, under a stronger hypothesis) "
               "and to the oracle; only [CGMY] can see it.",
    },
    # ---- BRIEF_012, the non-uniqueness witness. Three ways to keep the module
    # green while it stops being the witness. N1 and N3 regenerate the pins the
    # way an author without a toolchain would, so `[PINS]` stays green and the
    # only lane left that can object is `[NONUNIQ]`; N2 is proof-only and the
    # pins are proof-blind by design.
    {
        "name": "N1 trinomialMeasure collapsed to a single Dirac atom (A = B, theorem vacuous)",
        "file": NONUNIQ,
        "from": "  ENNReal.ofReal p₁ • Measure.dirac s₁ + ENNReal.ofReal p₂ • Measure.dirac s₂\n"
                "    + ENNReal.ofReal p₃ • Measure.dirac s₃",
        "to": "  ENNReal.ofReal (p₁ + p₂ + p₃) • Measure.dirac s₂",
        "also_rewrite_pins": True,
        "tag": "[NONUNIQ]",
        "why": "With one atom every three-point law on the witness spots is the "
               "same law, so `witnessMeasureA = witnessMeasureB`, the two prices "
               "coincide and the headline's `≠` clauses are simply false -- the "
               "build goes red, honestly. But a def body is pinned whole, and an "
               "author who regenerates the pins has a green `[PINS]` and a "
               "one-line `def` that reads plausibly; the witness lives or dies on "
               "the atom count, which only [NONUNIQ] reads.",
    },
    {
        "name": "N2 witnessA_parity re-derived from max_sub_swap_eq instead of citing BRIEF_009",
        "file": NONUNIQ,
        "from": "      = 1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1) :=\n"
                "  model_free_put_call_parity 1 1 1 0 0 id witnessA_integrable witnessA_drift",
        "to": "      = 1 * Real.exp (-0 * 1) - 1 * Real.exp (-0 * 1) := by\n"
              "  have hpt : ∀ s : ℝ, max (1 - id s) 0 = max (id s - 1) 0 - id s + 1 := fun s =>\n"
              "    max_sub_swap_eq (id s) 1\n"
              "  unfold modelFreeCall modelFreePut\n"
              "  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), witnessMeasureA_integral,\n"
              "    witnessMeasureA_integral]\n"
              "  simp only [id_eq]\n"
              "  norm_num [witnessSpotLo, witnessSpotMid, witnessSpotHi]",
        "tag": "[NONUNIQ]",
        "why": "Parity at a three-point law is a finite-sum identity; proved by "
               "direct computation from BRIEF_007's pointwise `max_sub_swap_eq` it "
               "is just as TRUE, builds, has no sorryAx and leaves the statement "
               "byte-identical. But the theorem is a claim about BRIEF_009's "
               "skeleton -- that the layer's parity and bounds hold at A and B and "
               "still do not pin the price -- and a private re-derivation says "
               "nothing about that layer. Statement untouched, nothing deferred, "
               "nothing deleted: only the citation check in [NONUNIQ] can see it.",
    },
    {
        "name": "N3 headline weakened: the price `≠` clause dropped (two measures, no disagreement)",
        "file": NONUNIQ,
        "from": "      modelFreeCall witnessMeasureB id 1 0 1 ≤ 1 * Real.exp (-0 * 1)) ∧\n"
                "    modelFreeCall witnessMeasureA id 1 0 1 ≠ modelFreeCall witnessMeasureB id 1 0 1 :=\n"
                "  ⟨witnessA_prob, witnessB_prob, witnessA_ne_B, witness_equivalent, witnessA_drift,\n"
                "    witnessB_drift, witnessA_parity, witnessB_parity, witnessA_bounds, witnessB_bounds,\n"
                "    witnessCall_ne⟩",
        "to": "      modelFreeCall witnessMeasureB id 1 0 1 ≤ 1 * Real.exp (-0 * 1)) :=\n"
              "  ⟨witnessA_prob, witnessB_prob, witnessA_ne_B, witness_equivalent, witnessA_drift,\n"
              "    witnessB_drift, witnessA_parity, witnessB_parity, witnessA_bounds, witnessB_bounds⟩",
        "also_rewrite_pins": True,
        "tag": "[NONUNIQ]",
        "why": "Every remaining conjunct is true and proved by the same named "
               "lemmas, so the build is green and the pins, regenerated, agree "
               "with the tree. What is gone is the theorem: two admissible "
               "measures that happen to agree on the price would satisfy every "
               "clause left, and `static_skeleton_does_not_select_measure` would "
               "no longer say that the skeleton fails to select anything. The "
               "headline is a conjunction precisely so that each clause is a "
               "regex away from being missed; [NONUNIQ] holds the list.",
    },
    # ---- BRIEF_013: the named Esscher measure (BSM-2 kit item 3) ----
    # The two guards [ESSCHER] watches are exactly the two a reviewer checks:
    # the shift must be DERIVED, not defined (the C1 tautology class), and the
    # pricing integrability must be CONSUMED from BRIEF_011, not re-proved
    # (the route-commitment class).
    {
        "name": "E1 esscherExponent hollowed: the shift defined AS the shifted CGMY form",
        "file": ESSCHER,
        "from": "def esscherExponent (ψ : ℂ → ℂ) (θ : ℝ) (v : ℂ) : ℂ :=\n"
                "  ψ (v - (θ : ℂ) * Complex.I) - ψ (-(θ : ℂ) * Complex.I)",
        "to": "def esscherExponent (ψ : ℂ → ℂ) (θ : ℝ) (v : ℂ) : ℂ :=\n"
              "  cgmyExponent 1 (0 + θ) (2 - θ) 1 v",
        "tag": "[ESSCHER]",
        "why": "With the tilt DEFINED as the shifted CGMY form, "
               "`esscher_cgmy_shift` is an `rfl` tautology: the family "
               "closure -- the whole algebraic content of the Esscher "
               "transform -- is assumed in the definition and certifies "
               "nothing (C1 item 1 reloaded). The guard is clause 1 of "
               "[ESSCHER]: the body must apply the GENERAL `ψ` at `v − ↑θ·I` "
               "and subtract `ψ` at `−↑θ·I`, and must never mention "
               "`cgmyExponent`. The mutant need not build to make the point; "
               "the lint is text over the tree.",
    },
    {
        "name": "E2 tilted integrability re-derived from the abstract interface",
        "file": ESSCHER,
        "from": "  refine cgmy_cmPriceKernel_integrable C (G + θ) (M - θ) Y τ α hC ?_ ?_ hY hY₂ hY₁ hα\n"
                "    hcontour hτ",
        "to": "  exact cmPriceKernel_integrable hα",
        "tag": "[ESSCHER]",
        "why": "Pricing at the Esscher measure is a claim that the TILTED law "
               "plugs into the machine BRIEF_011 already built -- the "
               "integrability must be `cgmy_cmPriceKernel_integrable` CITED at "
               "the shifted rates `(G+θ, M−θ)`. Re-deriving it from the "
               "abstract `cmPriceKernel_integrable` inside the module is the "
               "[CGMY] route-commitment cheat one level up: equally true, and "
               "equally silent about which landed theorem does the work. The "
               "statement is untouched and every pin stays green; only the "
               "citation check in [ESSCHER] clause 2 can see it.",
    },
    {
        "name": "E3 headline weakened: the admissible interval's nonemptiness `1 < G + M` dropped",
        "file": ESSCHER,
        "from": "    (hGM : 1 < G + M) (hd : |r - q| < esscherDriftBound C G M Y) :\n"
                "    ∃! θ : ℝ, θ ∈ Ioo (-G) (M - 1) ∧ esscherDriftMap C G M Y θ = r - q := by",
        "to": "    (hGM : 1 ≤ G + M) (hd : |r - q| < esscherDriftBound C G M Y) :\n"
              "    ∃! θ : ℝ, θ ∈ Ioo (-G) (M - 1) ∧ esscherDriftMap C G M Y θ = r - q := by",
        "also_rewrite_pins": True,
        "tag": "[ESSCHER]",
        "why": "`1 < G + M` is exactly the nonemptiness of the admissible "
               "interval `(-G, M-1)` -- at `G + M = 1` it is empty and the "
               "`∃!` claim is simply false, so weakening `<` to `≤` is not a "
               "generalization but a broken theorem. The brief's canary "
               "`G = 0.3, M = 0.5` is the number the hypothesis exists for; "
               "an author who regenerates the pins has a self-consistent "
               "layer 1 and a green build in their head. Only clause 3 of "
               "[ESSCHER] reads the hypothesis list.",
    },
    # ---- BRIEF_014: the normalized CGMY -> GBM corner (BSM-2 kit item 6) ----
    # One clause per cheat, plus one for the property the whole brief turns on.
    # None of these decides whether Corner.lean builds; each decides whether it
    # says the thing correction C17 says it must say. That is the distinction
    # the harness exists to keep visible: a check that only fires when the tree
    # is broken is not a check, it is a build error with better prose.
    {
        "name": "G1 corner scale without the half: `σ²(2−Y)` instead of `(σ²/2)(2−Y)`",
        "file": CORNER,
        "from": "def cgmyCornerC (σ Y : ℝ) : ℝ := (σ ^ 2 / 2) * (2 - Y)",
        "to": "def cgmyCornerC (σ Y : ℝ) : ℝ := σ ^ 2 * (2 - Y)",
        "tag": "[CORNER]",
        "why": "The half is the difference between a HALF-variance and a "
               "variance, and nothing else in the file objects: the pole still "
               "cancels (`C_Y Γ(−Y) → σ²/2` is finite), the limits still exist, "
               "the drift correction is still exact, and the factor still "
               "converges -- to a GBM with TWICE the intended variance. That "
               "is the quietest possible wrong answer, and the oracle canary "
               "for it (M22, measured at 1.257 against a 1e-3 tolerance) is a "
               "number, not a proof. Clause 1 of [CORNER] is what says which "
               "scale the corner runs on.",
    },
    {
        "name": "G2 pole cancellation re-derived from the recurrence, `cgmyGamma_two_sub_eq` uncited",
        "file": CORNER,
        "from": "  have htwo : Real.Gamma (2 - Y) = Real.Gamma (-Y) * Y * (Y - 1) :=\n"
                "    (cgmyGamma_two_sub_eq Y hYpos hY₂ hYne).symm",
        "to": "  have htwo : Real.Gamma (2 - Y) = Real.Gamma (-Y) * Y * (Y - 1) := by\n"
              "    rw [show 2 - Y = (1 - Y) + 1 by ring,\n"
              "      Real.Gamma_add_one (by linarith : 1 - Y ≠ 0),\n"
              "      show 1 - Y = (-Y) + 1 by ring,\n"
              "      Real.Gamma_add_one (by linarith : -Y ≠ 0)]\n"
              "    ring",
        "tag": "[CORNER]",
        "why": "Two honest `Real.Gamma_add_one` steps instead of one citation "
               "of BRIEF_013 -- the identity is the same, the proof is "
               "self-contained, and the file now rests on nothing that was "
               "landed. That is the route-commitment cheat at the one place "
               "BRIEF_014 actually consumes a predecessor: the correction C17 "
               "claims this pole cancellation is what makes the corner work, "
               "and a module that re-derives it makes that claim folklore. "
               "Clause 2 of [CORNER] holds the citation list.",
    },
    {
        "name": "G3 factor limit re-targeted at a hand-written exponential instead of `gbmCharFactor`",
        "file": CORNER,
        "from": "      (𝓝 (gbmCharFactor ((r - q - σ ^ 2 / 2) * τ) ((σ ^ 2 / 2) * τ) v)) := by",
        "to": "      (𝓝 (Complex.exp (Complex.I * ((((r - q - σ ^ 2 / 2) * τ : ℝ)) : ℂ) * v -\n"
              "        ((((σ ^ 2 / 2) * τ : ℝ)) : ℂ) * v ^ 2))) := by",
        "tag": "[CORNER]",
        "why": "The C1 sin one level up: a limit whose TARGET is written out "
               "in the statement can be made true by choosing the target, and "
               "`gbmCharFactor` is BRIEF_005's own landed GBM factor precisely "
               "so that the corner has to land on something that already "
               "existed. The hand-written exponential is the same function -- "
               "that is what makes it invisible to every check but clause 3, "
               "which reads the target.",
    },
    {
        "name": "G4 route B proved by term algebra, `esscher_cgmy_shift` uncited",
        "file": CORNER,
        "from": "    exact (congr_fun (esscher_cgmy_shift (cgmyCornerC σ Y) G M Y (esscherThetaZero G M)) v).symm",
        "to": "    simp [esscherExponent, cgmyExponent]",
        "tag": "[CORNER]",
        "why": "The whole content of route B is that the tilt IS the same "
               "exponent at shifted rates -- at every Y, with no limiting "
               "argument. Redoing it by term algebra inside Corner.lean makes "
               "BRIEF_013's `esscher_cgmy_shift` decoration: true, uncited, "
               "and unavailable to the next brief that needs to know which "
               "landed theorem the shifted strip comes from. Clause 4 of "
               "[CORNER] is the only reader.",
    },
    {
        "name": "G5 the corner taken as a TWO-SIDED limit, `𝓝[<] 2` -> `𝓝 2`",
        "file": CORNER,
        "from": "      (𝓝[<] (2 : ℝ))\n"
                "      (𝓝 (-2 * v ^ 2 + 2 * Complex.I * ((G - M : ℝ) : ℂ) * v)) := by",
        "to": "      (𝓝 (2 : ℝ))\n"
              "      (𝓝 (-2 * v ^ 2 + 2 * Complex.I * ((G - M : ℝ) : ℂ) * v)) := by",
        "tag": "[CORNER]",
        "why": "This is correction C17 itself. `Γ(−Y)` has a pole at `Y = 2`, "
               "so a two-sided limit does not exist -- and in Lean's tag it "
               "would not fail loudly either, since `Real.Gamma (-2)` is "
               "DEFINED (as 0) rather than undefined, which is exactly how the "
               "false `Y = 2` statement in the old docs survived so long. A "
               "one-sided filter is the only thing in the statement that "
               "says so. Clause 4 of [CORNER] reads every limit's filter.",
    },
    {
        "name": "W1 Pareto obstruction re-proved privately, Levy.lean uncited",
        "file": PARETO,
        "from": "  exact exp_moment_infinite_of_tail_lower_bound (paretoMeasure t r) r (t ^ r) t\n"
                "    (pareto_tail_const_pos ht) (pareto_tail_lower_bound ht hr)",
        "to": "  exact my_divergence (paretoMeasure t r) r (t ^ r) t\n"
              "    (pareto_tail_const_pos ht) (pareto_tail_lower_bound ht hr)",
        "tag": "[PARETO]",
        "why": "The witness exists to exercise Levy.lean's obstruction at a real "
               "law. Proving Pareto's infinite moment by any other route is true "
               "and builds, and leaves `htail` exactly as undischarged as before. "
               "Clause 1 of [PARETO] holds the citation.",
    },
    {
        "name": "W2 tail bound at a shifted index, `x ^ (-r)` -> `x ^ (-(r + 1))`",
        "file": PARETO,
        "from": "    ∀ x ≥ t, ENNReal.ofReal (t ^ r * x ^ (-r)) ≤ paretoMeasure t r (Set.Ici x) :=",
        "to": "    ∀ x ≥ t, ENNReal.ofReal (t ^ r * x ^ (-(r + 1))) ≤ paretoMeasure t r (Set.Ici x) :=",
        "tag": "[PARETO]",
        "why": "A weaker bound (a faster-decaying power) is still true for x >= t >= 1 "
               "and still discharges SOME `htail` -- at index r + 1, not at the law's "
               "own shape. Clause 2 of [PARETO] reads the constant and the index.",
    },
    {
        "name": "W3 a hand-rolled second Pareto law via `withDensity`",
        "file": PARETO,
        "from": "open MeasureTheory ProbabilityTheory Filter\nopen scoped ENNReal Topology\n",
        "to": "open MeasureTheory ProbabilityTheory Filter\nopen scoped ENNReal Topology\n\n"
              "def myPareto (r : ℝ) : Measure ℝ :=\n"
              "  volume.withDensity (fun x => ENNReal.ofReal (r * x ^ (-(r + 1))))\n",
        "tag": "[PARETO]",
        "why": "C13 originally proposed exactly this; BRIEF_015 F1 found mathlib ships "
               "the reviewed law. A second density is a second specification the "
               "tree must pin and trust. Clause 3 of [PARETO] forbids it.",
    },
    {
        "name": "W4 headline weakened to the `←` half, C7 dropped",
        "file": PARETO,
        "from": "      ∃ c x₀ : ℝ, 0 < c ∧ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x))\n"
                "    ↔ 0 < α := by",
        "to": "      ∃ c x₀ : ℝ, 0 < c ∧ ∀ x ≥ x₀, ENNReal.ofReal (c * x ^ (-α)) ≤ μ (Set.Ici x))\n"
              "    ∨ 0 < α := by",
        "tag": "[PARETO]",
        "why": "The `↔` is what makes the witness a characterization. Weakened, the "
               "statement is trivially true (`Or.inr`) at every positive α and says "
               "nothing about α <= 0 -- C7 would be prose again. Clause 4 of "
               "[PARETO] reads the connective.",
    },
]

# Attacks the toolchain-free lanes provably CANNOT see, kept as
# expected-to-SURVIVE so the limit is asserted rather than assumed. If one of
# these ever starts getting killed locally, that is news worth a red here: move
# the entry into MUTANTS and say so in docs/04, rather than letting the
# documentation quietly overstate what `lint` guarantees.
KNOWN_LOCAL_GAPS = [
    {
        # The residual boundary, stated exactly. Layer 2's *content* can only be
        # produced by a toolchain, so a forgery that is self-consistent on disk
        # passes every lane that can run here. It cannot pass CI, because CI
        # re-elaborates instead of re-reading: `#check @BSM.t4_call_bounds` really
        # prints the bound, and a committed `: True` is a diff.
        "name": "P9 hollow T4 and hand-forge BOTH layers into self-consistency",
        "file": CORE,
        "from": T4_STATEMENT,
        "to": "theorem t4_call_bounds (S K tau r q sigma : ℝ)\n"
              "    (hS : 0 < S) (hK : 0 < K) (htau : 0 < tau) (hsigma : 0 < sigma) :\n"
              "    True := by",
        "also_apply": [
            {"file": GOLDEN, "json_hollow_t4_forgery": True},
        ],
        # ...and layer 1 regenerated, so nothing on disk is stale. The order that
        # buys this: the JSON extra is applied first, then the Core.lean edit, then
        # --write re-pins layer 1 while *preserving* the elab block (that is what
        # --write does, so a toolchain-less author cannot drop layer 2 by
        # accident). Result: a fully self-consistent artifact describing a theorem
        # that no longer bounds a price.
        "also_rewrite_pins": True,
    },
]

# Edits that are legitimate. The lint must stay GREEN on every one of them:
# over-strict guards get disabled, and a disabled guard protects nothing.
CONTROLS = [
    {
        "name": "C1 marker words inside comments are not proofs",
        "file": CORE,
        "from": "theorem Phi_add_Phi_neg (x : ℝ) : Phi x + Phi (-x) = 1 := by",
        "to": "theorem Phi_add_Phi_neg (x : ℝ) : Phi x + Phi (-x) = 1 := by\n"
              "  -- this proof used to be a sorry, and someone wrote `admit` in a note\n"
              "  /-! native_decide appears in this prose about the ratchet -/",
        "why": "strip_comments must handle line and nested block comments, or the "
               "marker scan becomes a grep that punishes documentation and trains "
               "people to write prose without the word it forbids.",
    },
    {
        "name": "C2 proof reformatted, statement untouched",
        "file": CORE,
        "from": "theorem t1_d1_minus_d2 (S K tau r q sigma : ℝ) (htau : 0 < tau) (hsigma : sigma ≠ 0) :\n"
                "    d1 S K tau r q sigma - d2 S K tau r q sigma = sigma * Real.sqrt tau := by",
        "to": "theorem t1_d1_minus_d2 (S K tau r q sigma : ℝ) (htau : 0 < tau)\n"
              "    (hsigma : sigma ≠ 0) : d1 S K tau r q sigma - d2 S K tau r q sigma\n"
              "      = sigma * Real.sqrt tau := by",
        "why": "The pin is whitespace-normalized precisely so that re-wrapping a "
               "statement is free. A pin sensitive to line breaks would be regenerated "
               "on every style edit, and a regenerated pin is an unchecked pin.",
    },
    {
        "name": "C3 parity reproved from erf_neg directly",
        "file": CORE,
        "from": T2_PROOF,
        "to": "  simp only [bsPut, bsCall, Phi, erf_neg]\n  ring",
        "why": "`Phi` IS `(1 + erf (x/sqrt 2))/2`, so citing `erf_neg` is odd symmetry "
               "one step closer to the source, not a dodge. The guard constrains the "
               "content used, not the preferred lemma name -- a lint that rejects this "
               "proof will be loosened the first time it fires on real work.",
    },
    {
        "name": "C4 oracle renamed in a way that keeps every anchor",
        "file": ORACLE,
        "from": "def bs_price(S, K, T, t, r, s, q=0.0, option=\"call\"):",
        "to": "def bs_price(  # public signature frozen; see module docstring\n    S, K, T, t, r, s, q=0.0, option=\"call\"):",
        "why": "Guard against the anchor check being a fragile substring match on "
               "formatting: it must assert structure, not exact layout.",
    },
    {
        "name": "C5 a new node deferred the documented way",
        "file": CORE,
        "from": "end BSM",
        "to": "theorem t5_pde_sketch : True := by\n  sorry\n\nend BSM",
        "also_apply": [{"file": BASELINE, "json_set": {"deferred": {"t5_pde_sketch": 1}}}],
        "why": "The ratchet is a ratchet, not a ban: a brief that lands a node with an "
               "explicitly deferred proof and a matching baseline entry is legitimate "
               "work. If this control went red, the baseline file would be dead weight "
               "and every brief would be forced to land a full proof in one PR.",
    },
]

# `also_apply` entries are applied to the same working copy, in order.


# ---------------------------------------------------------------- plumbing

def _copy(dst: str) -> str:
    shutil.copytree(
        ROOT,
        dst,
        ignore=shutil.ignore_patterns(".git", ".lake", "__pycache__", "*.log", "*.egg-info"),
    )
    return dst


def _apply(work: str, mut: dict) -> None:
    for extra in mut.get("also_apply", []):
        _apply(work, extra)
    path = os.path.join(work, mut["file"])
    if mut.get("delete"):
        os.remove(path)
        return
    if mut["file"].endswith(".json"):
        data = json.load(open(path, encoding="utf-8"))
        if "json_set" in mut:
            for k, v in mut["json_set"].items():
                if v is None:
                    data.pop(k, None)
                else:
                    data[k] = v
        if "json_drop" in mut:
            data.get("pins", {}).pop(mut["json_drop"], None)
        if mut.get("json_hollow_t4_forgery"):
            # Make the artifact self-consistent with the hollowed claim, the way an
            # author with no toolchain *could*: layer 1 says `True`, so layer 2 must
            # be edited to say `True` too. Everything else in `elab` is discarded,
            # which is itself the tell -- but only CI can read the tell.
            pins = data.get("pins", {})
            data["elab"] = {
                "BSM.t4_call_bounds": {
                    "type": "BSM.t4_call_bounds : True",
                    "axioms": "'BSM.t4_call_bounds' depends on axioms: "
                              "[propext, Classical.choice, Quot.sound]",
                }
            }
            data["pins"] = pins
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(data, fh, indent=2, ensure_ascii=False)
            fh.write("\n")
        return
    src = open(path, encoding="utf-8").read()
    assert mut["from"] in src, f"anchor vanished from {mut['file']} for {mut['name']}"
    mutated = src.replace(mut["from"], mut["to"], 1)
    assert mutated != src, f"mutation was a no-op for {mut['name']}"
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(mutated)
    # The reviewable-diff trap needs the pins regenerated, done with the tree in
    # its mutated state, which is exactly what an author would commit.
    if mut.get("also_rewrite_pins"):
        subprocess.run(
            [sys.executable, "scripts/pin_statements.py", "--write"],
            cwd=work,
            capture_output=True,
            text=True,
            check=True,
        )


def _run_lint(work: str) -> tuple[int, str]:
    proc = subprocess.run(
        [sys.executable, "scripts/lean_lint.py"], cwd=work, capture_output=True, text=True
    )
    return proc.returncode, proc.stdout + proc.stderr


def _lint_copy(mut: dict | None) -> tuple[int, str]:
    with tempfile.TemporaryDirectory() as tmp:
        work = _copy(os.path.join(tmp, "tree"))
        if mut is not None:
            _apply(work, mut)
        return _run_lint(work)


# ---------------------------------------------------------------- the tests

def test_baseline_is_green():
    """Guard: the whole harness is meaningless unless the *unmutated* lint passes.

    If the lint were red on the clean tree, every mutant below would be "killed"
    for free. This is the same guard test_mutants.py runs against the oracle.
    """
    rc, out = _lint_copy(None)
    assert rc == 0, f"lean_lint.py is red on the unmutated tree:\n{out}"
    LAST_NOTE["test_baseline_is_green"] = out.strip().splitlines()[-1]


def test_mutation_anchors_exist():
    """Guard: every anchor must be present in the committed source.

    A mutant whose anchor has been edited away is a silent no-op, and 35 silent
    no-ops read exactly like 35 kills.
    """
    missing = []
    for mut in MUTANTS + CONTROLS + KNOWN_LOCAL_GAPS:
        if mut.get("delete") or mut["file"].endswith(".json"):
            continue
        src = open(os.path.join(ROOT, mut["file"]), encoding="utf-8").read()
        if mut["from"] not in src:
            missing.append(f"{mut['name']}  (in {mut['file']})")
    assert not missing, (
        "mutation anchors no longer present -- update them, do not delete them:\n  "
        + "\n  ".join(missing)
    )


def test_every_mutant_is_killed_by_its_check():
    """Each cheat must be caught by the check aimed at it, not by luck."""
    survivors, wrong = [], []
    for mut in MUTANTS:
        rc, out = _lint_copy(mut)
        if rc == 0:
            survivors.append(mut["name"])
            continue
        if mut["tag"] not in out:
            wrong.append(f"{mut['name']}: expected {mut['tag']}, got\n{out.strip()}")
    assert not survivors, (
        "MUTANTS SURVIVED -- the lint cannot see these cheats:\n  " + "\n  ".join(survivors)
    )
    assert not wrong, "mutants caught by the WRONG check:\n  " + "\n  ".join(wrong)


def test_known_local_gaps_stay_open():
    """Assert the *limits* of the toolchain-free lanes, so they are documented, not folklore.

    These attacks are expected to pass the local lint. They are not safe -- they
    are caught one layer up, by the CI-only `elab` pin in
    tests/golden_statements.json: an author who regenerates the `statement` field
    still has to explain a `#check @BSM.t4_call_bounds` that now prints `: True`.
    Stating the boundary mechanically is the point. If this test goes red, the
    local layer got stronger: move the entry into MUTANTS and update docs/04.
    """
    for gap in KNOWN_LOCAL_GAPS:
        rc, out = _lint_copy(gap)
        assert rc == 0, (
            f"{gap['name']} is now caught locally -- the gap closed. Move it into "
            f"MUTANTS and record which check did it.\n{out.strip()}"
        )
    LAST_NOTE["test_known_local_gaps_stay_open"] = f"{len(KNOWN_LOCAL_GAPS)} gap(s) still open by design"


def test_legitimate_edits_stay_green():
    """The lint must not punish honest work: comments, reformatting, better proofs."""
    red = []
    for ctl in CONTROLS:
        rc, out = _lint_copy(ctl)
        if rc != 0:
            red.append(f"{ctl['name']}\n{out.strip()}")
    assert not red, (
        "the lint went RED on legitimate edits (over-strict guards get switched off):\n\n  "
        + "\n\n  ".join(red)
    )


def test_pin_set_covers_the_lints_own_stack():
    """The pinned key set must equal REQUIRED | PROTECTED.

    Both sides of that equality matter: a protected theorem missing from the pins
    is unpinnable, and a pin whose name has drifted out of REQUIRED/PROTECTED
    means someone edited a list rather than a proof.
    """
    import lean_lint as LL

    want = {f"BSM.{n}" for n in (set(LL.REQUIRED) | set(LL.PROTECTED))}
    got = set(json.load(open(os.path.join(ROOT, GOLDEN), encoding="utf-8")).get("pins", {}))
    assert want == got, f"pins vs lint lists differ: only-pinned={sorted(got - want)}, " \
                        f"only-in-lists={sorted(want - got)}. Run " \
                        "`python3 scripts/pin_statements.py --write` and update " \
                        "REQUIRED/PROTECTED deliberately."


def test_lint_fails_when_pins_are_unreadable():
    """A sub-check that cannot run must be a red, not a silent skip.

    `lean_lint.py` imports `pin_statements` lazily inside main(). If that import
    or the check raises, the failure must reach the report -- a lint whose
    strongest new guard can vanish on an exception is worse than no guard,
    because it advertises coverage that is not there.
    """
    with tempfile.TemporaryDirectory() as tmp:
        work = _copy(os.path.join(tmp, "tree"))
        p = os.path.join(work, "scripts", "pin_statements.py")
        with open(p, "a", encoding="utf-8") as fh:
            fh.write("\nraise RuntimeError('simulated import-time breakage')\n")
        rc, out = _run_lint(work)
    assert rc != 0 and "[PINS]" in out, (
        "pin check raised and the lint still reported OK -- the guard is optional"
    )


if __name__ == "__main__":
    import traceback

    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    fails = 0
    for fn in fns:
        try:
            LAST_NOTE.clear()
            fn()
            note = LAST_NOTE.get(fn.__name__, "")
            print(f"  ok  {fn.__name__}" + (f"   [{note}]" if note else ""))
        except Exception:
            fails += 1
            print(f"FAIL  {fn.__name__}")
            traceback.print_exc()
    print(
        f"\n{len(fns)-fails}/{len(fns)} passed  "
        f"({len(MUTANTS)} lint mutants seeded, {len(CONTROLS)} must-stay-green controls)"
    )
    sys.exit(1 if fails else 0)
