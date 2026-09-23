#!/usr/bin/env python3
"""
Lint for the Lean tree. **Needs no Lean toolchain**, so it runs in CI on any
runner and in any sandbox -- including ones where elan cannot be installed.

This exists because the repo's grading rule ("a `sorry` anywhere in the parity
/ d1-d2 node is an automatic reject", BRIEF_001) is a *syntactic* rule, and
syntactic rules should be checked syntactically. `lake build` is the authority
on whether a proof is correct; this script is the authority on whether the tree
is honestly labelled. Both lanes run in .github/workflows/lean.yml.

Checks
------
1. NAMESPACE      no `.lean` file under a top-level `Lean/` directory (that
                  makes the module `Lean.core.*` and squats the elaborator's
                  own namespace).
2. REQUIRED       every theorem in the committed stack must still be declared.
                  Stops the easiest way to make a lint pass: delete the theorem.
3. PROTECTED      zero `sorry`/`admit`/`native_decide` in the landed nodes: T1/T2
                  (the BRIEF_001 deliverable) and T3/T4 with their infrastructure
                  (BRIEF_003). Automatic reject.
4. RATCHET        repo-wide, the set of declarations containing a deferred-proof
                  marker must be a subset of the committed baseline, and the
                  total count must not exceed it. You may discharge a `sorry`;
                  you may not add one, and you may not move one from a deferred
                  node into a protected one.
5. AXIOMS         no new top-level `axiom` command outside the allowlist. An
                  `axiom` is a `sorry` that survives `lake build` silently.
6. INDEPENDENCE   the anti-vacuity guard, mirroring tests/test_mutants.py:
                  `d2` must not be defined in terms of `d1`, and `bsPut` must
                  not be defined in terms of `bsCall`. If either is, then T1 and
                  T2 are true by construction and a green build certifies
                  nothing. This is the check that would have caught the original
                  version of this file.
7. ORACLE SYNC    the Lean `def`s and the Python oracle must use the same
                  arithmetic: both `d1`/`d2` from independent explicit formulas,
                  both puts from an independent closed form. Guards against the
                  two trees drifting into proving different mathematics.
8. CROSSCHECK SYNC the Float twin in ImprovedBS/Crosscheck.lean keeps its own
                  independent derivations, its embedded golden grid stays in
                  sync with tests/golden_grid.json, and `runCrosscheck` actually
                  emits BOTH sides of T3's delta identity: the twin once defined
                  `deltaIdentityRhs` and never printed it, so guard (3)
                  cross-checked the LHS against the oracle's LHS and never
                  tested T3's equation (benchmarks/LEDGER.md, C6 item 4).
9. PINS           every protected declaration still *says* what
                  tests/golden_statements.json says it says (see
                  scripts/pin_statements.py). This is the anti-hollowing guard:
                  `lake build` proves a theorem is correct, and only this check
                  notices when a theorem has been quietly changed into `True`.
10. SPINE         docs/04's dependency spine commits T5 to a route -- T3 + chain
                  rule + `Phi' = phi` -- and nothing else in the tree can see a
                  route change. The T5 node must cite `t3_delta_identity` and
                  `hasDerivAt_Phi`, and `t5_delta` itself must cite T3: a
                  brute-force differentiation of `erf` composed with the
                  log-rational proves the same residual while duplicating T3's
                  cancellation (and T1's `S`-action), which is exactly the drift
                  docs/04's "spine, not six unrelated chores" is about. A mutant
                  is seeded for it in tests/test_lint.py.
11. SKELETON      BRIEF_009's route commitments at the model-free layer. The
                  put bounds must cite the parity theorem (T4'-via-T2 mirror),
                  and the `*_via_skeleton` re-derivations must consume the
                  model-free layer and must not cite the closed-form proofs they
                  re-derive -- otherwise "the widening preserves the skeleton"
                  would be graded by the very theorems it underpins, and a green
                  build would certify nothing. Two mutants in tests/test_lint.py.
13. CGMY          BRIEF_011's correction C14 and its two route commitments. The
                  exponent must be the two-base `Gamma(-Y)` form; the decay must
                  be DISCHARGED by consuming BRIEF_010's `cmPriceKernel_integrable`
                  at an explicit threshold (not re-derived); and the landed
                  statements must carry `alpha + 1 < M`, never the `min (G, M)`
                  spelling of docs/03 §D1 -- `G` constrains only the old
                  `u + i alpha` line. One mutant in tests/test_lint.py.
12. CONTOUR       BRIEF_010's correction C12: the pricing kernel `cmPriceKernel`
                  must be on the pricing line `u − i(α+1)`, not the `u + iα`
                  line of `carrMadanKernel`, and `cmPriceIntegral` must be the
                  thing `carrMadan_eq_modelFreeCall` consumes. One mutant in
                  tests/test_lint.py.

Exit status is non-zero on any failure, with every failure printed.

Usage:  python3 scripts/lean_lint.py                    # from the repo root
        python3 scripts/lean_lint.py --explain          # print the baseline and stop
        python3 scripts/lean_lint.py --write-baseline   # re-record the ratchet

`--write-baseline` is a deliberate, reviewable act: it records the CURRENT
deferred-proof markers as the new ceiling. Use it when landing a brief whose
scope explicitly defers nodes (e.g. T5), never to make a failing lint pass.
The diff of .github/lean_lint_baseline.json is the audit trail. It refuses to
write anything while any other check is red, so a re-baseline cannot be used to
legitimise a tree that is failing for a different reason.
"""

from __future__ import annotations

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE_PATH = os.path.join(ROOT, ".github", "lean_lint_baseline.json")
ORACLE_PATH = os.path.join(ROOT, "experiments", "black_scholes.py")

# Declarations that must exist in the tree (name -> file).
REQUIRED = {
    "Phi": "ImprovedBS/Core.lean",
    "phi": "ImprovedBS/Core.lean",
    "d1": "ImprovedBS/Core.lean",
    "d2": "ImprovedBS/Core.lean",
    "bsCall": "ImprovedBS/Core.lean",
    "bsPut": "ImprovedBS/Core.lean",
    "erf": "ImprovedBS/Core.lean",
    "erf_neg": "ImprovedBS/Core.lean",
    "exp_neg_sq_even": "ImprovedBS/Core.lean",
    "Phi_add_Phi_neg": "ImprovedBS/Core.lean",
    "Phi_neg": "ImprovedBS/Core.lean",
    "t1_d1_minus_d2": "ImprovedBS/Core.lean",
    "t2_put_call_parity": "ImprovedBS/Core.lean",
    "t2_put_call_parity_spread": "ImprovedBS/Core.lean",
    "t3_delta_identity": "ImprovedBS/Core.lean",
    "t4_call_bounds": "ImprovedBS/Core.lean",
    "t4_put_bounds": "ImprovedBS/Core.lean",
    # BRIEF_003 infrastructure: phi/Phi as integrals, and the positivity lemma
    # that carries the T4 lower bound. Listed so that "prove T4 by deleting the
    # lemma that makes it non-trivial" is not an option.
    "phi_neg": "ImprovedBS/Core.lean",
    "phi_nonneg": "ImprovedBS/Core.lean",
    "phi_integrable": "ImprovedBS/Core.lean",
    "phi_add": "ImprovedBS/Core.lean",
    "integral_phi_Iic_zero": "ImprovedBS/Core.lean",
    "Phi_eq_integral_Iic": "ImprovedBS/Core.lean",
    "Phi_nonneg": "ImprovedBS/Core.lean",
    "Phi_le_one": "ImprovedBS/Core.lean",
    "Phi_le_exp_mul_Phi_add": "ImprovedBS/Core.lean",
    "d1_exponent": "ImprovedBS/Core.lean",
    "d2_exponent": "ImprovedBS/Core.lean",
    "forward_eq": "ImprovedBS/Core.lean",
    "bsCall_nonneg": "ImprovedBS/Core.lean",
    "bsPut_nonneg": "ImprovedBS/Core.lean",
    # BRIEF_004 (T6, sub-goal 1): the moment obstruction. §1 of Levy.lean is the
    # analysis (a power tail lower bound forces an infinite exponential moment),
    # §2 is the modelling claim that consumes it. Listed so that "prove the
    # obstruction by deleting the theorem" is not an option, and so the pins
    # cover the statements that carry the result.
    "ofReal_mul_tail_le_lintegral_exp_add": "ImprovedBS/Levy.lean",
    "lintegral_exp_add_eq_top_of_tail_lower_bound": "ImprovedBS/Levy.lean",
    "lintegral_exp_eq_top_of_tail_lower_bound": "ImprovedBS/Levy.lean",
    "exp_moment_infinite_add_of_tail_lower_bound": "ImprovedBS/Levy.lean",
    "exp_moment_infinite_of_tail_lower_bound": "ImprovedBS/Levy.lean",
    "spot_not_integrable_of_tail_lower_bound": "ImprovedBS/Levy.lean",
    "no_drift_makes_spot_integrable": "ImprovedBS/Levy.lean",
    # BRIEF_005 (T6, sub-goal 2): absolute convergence of the tempered
    # Carr–Madan contour. The two halves that make up the result plus the join:
    # `integrable_exp_neg_abs_rpow` is the model side (the two-sided tempered
    # tail integrates), `cmDenom_u4_le`/`cmDenom_ne_zero` the payoff side (the
    # denominator's modulus has an exact quartic lower bound and no zero on the
    # real contour), `carrMadanKernel_integrable`/`carrMadan_price_integrable`
    # the joining domination, and the two `gbm_*` theorems the fully
    # machine-checked instance through which classical Fourier pricing enters
    # this repository. The four `def`s are listed too: a definition is the
    # specification, and hollowing one changes every statement above it. Listed
    # so that "prove integrability by deleting the theorem" is not an option.
    "cmDenom": "ImprovedBS/Fourier.lean",
    "carrMadanKernel": "ImprovedBS/Fourier.lean",
    "carrMadanPhase": "ImprovedBS/Fourier.lean",
    "gbmCharFactor": "ImprovedBS/Fourier.lean",
    "integrable_exp_neg_abs_rpow": "ImprovedBS/Fourier.lean",
    "cmDenom_u4_le": "ImprovedBS/Fourier.lean",
    "cmDenom_ne_zero": "ImprovedBS/Fourier.lean",
    "carrMadanKernel_integrable": "ImprovedBS/Fourier.lean",
    "carrMadan_price_integrable": "ImprovedBS/Fourier.lean",
    "gbm_carrMadanKernel_integrable": "ImprovedBS/Fourier.lean",
    "gbm_carrMadan_price_integrable": "ImprovedBS/Fourier.lean",
    # BRIEF_006 (T5): the closed form solves the BSM PDE. The analytic input
    # (`hasDerivAt_erf` from the interval-integral FTC, and `hasDerivAt_Phi`),
    # the shared argument shape (`hasDerivAt_d_spot`, `d_tau_quotient_eq`,
    # `hasDerivAt_d_tau`, `d1_tau_sub_d2_tau`), the three derivatives of the
    # price and the two forms of the identity. Listed so that "prove the PDE by
    # deleting the lemma that cancels the `phi`-terms" is not an option -- and
    # the [SPINE] check below pins the *route*, so that "prove it by
    # re-differentiating `erf ∘ log-rational`" is not one either.
    "hasDerivAt_erf": "ImprovedBS/Core.lean",
    "hasDerivAt_Phi": "ImprovedBS/Core.lean",
    "hasDerivAt_d_spot": "ImprovedBS/Core.lean",
    "d_tau_quotient_eq": "ImprovedBS/Core.lean",
    "hasDerivAt_d_tau": "ImprovedBS/Core.lean",
    "d1_tau_sub_d2_tau": "ImprovedBS/Core.lean",
    "t5_delta": "ImprovedBS/Core.lean",
    "t5_gamma": "ImprovedBS/Core.lean",
    "t5_tau": "ImprovedBS/Core.lean",
    "t5_bsCall_pde_tau": "ImprovedBS/Core.lean",
    "t5_bsCall_pde": "ImprovedBS/Core.lean",
    # BRIEF_007 (T6, sub-goal 3a): the closed form IS the discounted risk-neutral
    # expectation. §1 of RiskNeutral.lean is the Gaussian bridge (`phi`/`Phi`
    # identified with mathlib's `gaussianPDFReal 0 1`/`gaussianReal 0 1`, so the
    # pinned definitions stay put), §2 the tilted Gaussian integrals (the T3
    # tilting identity in lognormal form and the partial expectation it gives),
    # §3 the payoff as the indicator of the exercise region, §4 the theorems:
    # the call and put identities, the drift condition `E[S_T] = S e^{(r-q)τ}`,
    # and the same identity against `gaussianReal 0 1` and the lognormal law.
    # Listed so that "prove the expectation identity by deleting the bridge" or
    # "by weakening `0 < σ` to `σ ≠ 0`" is a diff, not an option.
    "phi_eq_gaussianPDFReal": "ImprovedBS/RiskNeutral.lean",
    "Phi_eq_gaussianReal_Iic": "ImprovedBS/RiskNeutral.lean",
    "integral_gaussianReal_eq_integral_mul_phi": "ImprovedBS/RiskNeutral.lean",
    "integral_phi": "ImprovedBS/RiskNeutral.lean",
    "exp_mul_phi_eq": "ImprovedBS/RiskNeutral.lean",
    "integrable_exp_mul_phi": "ImprovedBS/RiskNeutral.lean",
    "integral_exp_mul_phi": "ImprovedBS/RiskNeutral.lean",
    "integral_phi_Ioi": "ImprovedBS/RiskNeutral.lean",
    "integral_phi_sub_Ioi": "ImprovedBS/RiskNeutral.lean",
    "integral_exp_mul_phi_Ioi": "ImprovedBS/RiskNeutral.lean",
    "sigma_sqrt_tau_mul_d2": "ImprovedBS/RiskNeutral.lean",
    "spot_sub_strike_eq": "ImprovedBS/RiskNeutral.lean",
    "max_spot_sub_strike_mul_phi": "ImprovedBS/RiskNeutral.lean",
    "max_sub_swap_eq": "ImprovedBS/RiskNeutral.lean",
    "integrable_spot_mul_phi": "ImprovedBS/RiskNeutral.lean",
    "integral_spot_mul_phi_eq_forward": "ImprovedBS/RiskNeutral.lean",
    "integrable_max_spot_sub_strike_mul_phi": "ImprovedBS/RiskNeutral.lean",
    "bsCall_eq_riskNeutral_expectation": "ImprovedBS/RiskNeutral.lean",
    "bsPut_eq_riskNeutral_expectation": "ImprovedBS/RiskNeutral.lean",
    "bsCall_eq_gaussianReal_expectation": "ImprovedBS/RiskNeutral.lean",
    "bsCall_eq_lognormal_expectation": "ImprovedBS/RiskNeutral.lean",
    # T6 sub-goal 3b (BRIEF_008): Fourier inversion and real-valuedness
    "carrMadanInversion": "ImprovedBS/Inversion.lean",
    "carrMadanInversion_integrand_integrable": "ImprovedBS/Inversion.lean",
    "gbm_carrMadanInversion_integrable": "ImprovedBS/Inversion.lean",
    "dampedCallPrice": "ImprovedBS/Inversion.lean",
    "dampedCallPrice_log_eq": "ImprovedBS/Inversion.lean",
    "undamped_dampedCallPrice": "ImprovedBS/Inversion.lean",
    "fourierInversion_dampedCallPrice": "ImprovedBS/Inversion.lean",
    "fourierInversion_dampedCallPrice_at": "ImprovedBS/Inversion.lean",
    "carrMadan_inversion_eq_lognormal_expectation": "ImprovedBS/Inversion.lean",
    "carrMadan_inversion_eq_bsCall": "ImprovedBS/Inversion.lean",
    "carrMadan_inversion_im_eq_zero": "ImprovedBS/Inversion.lean",
    "carrMadan_inversion_eq_re": "ImprovedBS/Inversion.lean",
    "carrMadan_inversion_re_eq_bsCall": "ImprovedBS/Inversion.lean",
    # BRIEF_009: the model-free skeleton (parity + bounds at the expectation level)
    "modelFreeCall": "ImprovedBS/Skeleton.lean",
    "modelFreePut": "ImprovedBS/Skeleton.lean",
    "integrable_call_payoff": "ImprovedBS/Skeleton.lean",
    "integrable_put_payoff": "ImprovedBS/Skeleton.lean",
    "model_free_parity_gap": "ImprovedBS/Skeleton.lean",
    "model_free_put_call_parity": "ImprovedBS/Skeleton.lean",
    "model_free_call_nonneg": "ImprovedBS/Skeleton.lean",
    "model_free_call_bounds": "ImprovedBS/Skeleton.lean",
    "model_free_put_bounds": "ImprovedBS/Skeleton.lean",
    "integrable_gaussianReal_iff": "ImprovedBS/Skeleton.lean",
    "lognormal_parity_gap": "ImprovedBS/Skeleton.lean",
    "lognormal_call_bounds": "ImprovedBS/Skeleton.lean",
    "t2_spread_via_skeleton": "ImprovedBS/Skeleton.lean",
    "t4_call_bounds_via_skeleton": "ImprovedBS/Skeleton.lean",
    # BRIEF_010: T6 at any strip law + contour correction C12
    "cmPriceKernel": "ImprovedBS/Pricing.lean",
    "contourCharFun": "ImprovedBS/Pricing.lean",
    "cmPriceIntegral": "ImprovedBS/Pricing.lean",
    "strikeTransform": "ImprovedBS/Pricing.lean",
    "dampedModelFreeCall": "ImprovedBS/Pricing.lean",
    "fourierCM": "ImprovedBS/Pricing.lean",
    "cmPriceKernel_eq_shift": "ImprovedBS/Pricing.lean",
    "gbm_contourCharFun_eq": "ImprovedBS/Pricing.lean",
    "gbmCharFactor_pricing_continuous": "ImprovedBS/Pricing.lean",
    "gbmCharFactor_pricing_norm": "ImprovedBS/Pricing.lean",
    "cmPriceKernel_integrable": "ImprovedBS/Pricing.lean",
    "gbm_cmPriceKernel_integrable": "ImprovedBS/Pricing.lean",
    "cmDenom_factor": "ImprovedBS/Pricing.lean",
    "integral_Ioi_cexp_neg_mul_eq_inv": "ImprovedBS/Pricing.lean",
    "ofReal_exp_eq_cexp": "ImprovedBS/Pricing.lean",
    "norm_cexp_I_mul_ofReal": "ImprovedBS/Pricing.lean",
    "strikeTransform_eq": "ImprovedBS/Pricing.lean",
    "integrable_strikeTransform": "ImprovedBS/Pricing.lean",
    "dampedModelFreeCall_eq_dampedCallPrice": "ImprovedBS/Pricing.lean",
    "continuous_dampedModelFreeCall": "ImprovedBS/Pricing.lean",
    "integrable_dampedModelFreeCall_of_exp_moment": "ImprovedBS/Pricing.lean",
    "fourierDampedModelFreeCall_eq": "ImprovedBS/Pricing.lean",
    "fourierCM_eq_fourier": "ImprovedBS/Pricing.lean",
    "fourierCM_inversion": "ImprovedBS/Pricing.lean",
    "cmPriceIntegral_eq_damped_modelFreeCall": "ImprovedBS/Pricing.lean",
    "carrMadan_eq_modelFreeCall": "ImprovedBS/Pricing.lean",
    "cmPriceIntegrand_reflect": "ImprovedBS/Pricing.lean",
    "carrMadan_im_eq_zero": "ImprovedBS/Pricing.lean",
    "carrMadan_eq_re": "ImprovedBS/Pricing.lean",
    "carrMadan_re_eq_modelFreeCall": "ImprovedBS/Pricing.lean",
    "gbm_carrMadan_eq_bsCall": "ImprovedBS/Pricing.lean",
    # BRIEF_011 (BSM-2 kit items 1-2): the concrete CGMY exponent, its Levy
    # measure and the tempered strip that discharges BRIEF_010's (H-decay).
    # The four `def`s are listed because a definition is the specification:
    # hollowing `cgmyExponent` (say, to `0`) would leave every theorem above it
    # true and every claim about the model empty. `cgmyTemperedRate`,
    # `cgmyTemperedCorrection`, `cgmyTemperedConstant` and
    # `cgmyDecayThreshold` are exactly the constants the bound quotes, so a
    # weakened rate is a diff here and not a silent strengthening of the
    # hypotheses. Listed so that "prove the decay by deleting the theorem" is
    # not an option.
    "cgmyExponent": "ImprovedBS/CGMY.lean",
    "cgmyCharFactor": "ImprovedBS/CGMY.lean",
    "cgmyContour": "ImprovedBS/CGMY.lean",
    "cgmyTemperedRate": "ImprovedBS/CGMY.lean",
    "cgmyTemperedCorrection": "ImprovedBS/CGMY.lean",
    "cgmyTemperedConstant": "ImprovedBS/CGMY.lean",
    "cgmyDecayThreshold": "ImprovedBS/CGMY.lean",
    "cgmyLevyDensity": "ImprovedBS/CGMY.lean",
    "cgmyCharFactor_add": "ImprovedBS/CGMY.lean",
    "cgmyExponent_contour": "ImprovedBS/CGMY.lean",
    "cgmyOldContour_base_right_re": "ImprovedBS/CGMY.lean",
    "cgmy_tempered_prod_neg": "ImprovedBS/CGMY.lean",
    "cgmy_tempered_rate_neg_eq": "ImprovedBS/CGMY.lean",
    "cgmy_cpow_re_ge_of_lt_one": "ImprovedBS/CGMY.lean",
    "cgmy_cpow_re_le_of_one_le": "ImprovedBS/CGMY.lean",
    "cgmyExponent_contour_re": "ImprovedBS/CGMY.lean",
    "cgmyExponent_contour_re_le": "ImprovedBS/CGMY.lean",
    "cgmyExponent_contour_re_le_half": "ImprovedBS/CGMY.lean",
    "cgmy_contour_decay": "ImprovedBS/CGMY.lean",
    "cgmy_contour_continuous": "ImprovedBS/CGMY.lean",
    "cgmy_cmPriceKernel_integrable": "ImprovedBS/CGMY.lean",
    "cgmy_contour_mem_strip": "ImprovedBS/CGMY.lean",
    "cgmy_numeraire_strip": "ImprovedBS/CGMY.lean",
    "cgmyExponent_strip": "ImprovedBS/CGMY.lean",
    "cgmy_levy_sq_integrable": "ImprovedBS/CGMY.lean",
    "cgmy_levy_far_moment": "ImprovedBS/CGMY.lean",
}

# Zero deferred-proof markers allowed. The T1/T2 node per BRIEF_001; the T3/T4
# node and its infrastructure per BRIEF_003. A landed theorem never goes back
# to `sorry` -- that is the whole point of the ratchet.
PROTECTED = {
    # T1/T2 (BRIEF_001)
    "erf",
    "erf_neg",
    "exp_neg_sq_even",
    "Phi_add_Phi_neg",
    "Phi_neg",
    "t1_d1_minus_d2",
    "t2_put_call_parity",
    "t2_put_call_parity_spread",
    # T3/T4 (BRIEF_003)
    "phi_neg",
    "phi_nonneg",
    "phi_integrable",
    "phi_add",
    "integral_phi_Iic_zero",
    "Phi_eq_integral_Iic",
    "Phi_nonneg",
    "Phi_le_one",
    "Phi_le_exp_mul_Phi_add",
    "d1_exponent",
    "d2_exponent",
    "forward_eq",
    "bsCall_nonneg",
    "bsPut_nonneg",
    "t3_delta_identity",
    "t4_call_bounds",
    "t4_put_bounds",
    # T6 sub-goal 1 (BRIEF_004): the moment obstruction. Landed, so a `sorry`
    # here is an automatic reject -- and the pins cover the seven statements, so
    # hollowing one is a diff too.
    "ofReal_mul_tail_le_lintegral_exp_add",
    "lintegral_exp_add_eq_top_of_tail_lower_bound",
    "lintegral_exp_eq_top_of_tail_lower_bound",
    "exp_moment_infinite_add_of_tail_lower_bound",
    "exp_moment_infinite_of_tail_lower_bound",
    "spot_not_integrable_of_tail_lower_bound",
    "no_drift_makes_spot_integrable",
    # T6 sub-goal 2 (BRIEF_005): absolute convergence of the tempered contour.
    # The same ratchet posture: the integrability theorems below are the result
    # this node landed, so a `sorry` in any of them reverts the node outright.
    "integrable_exp_neg_abs_rpow",
    "cmDenom_u4_le",
    "cmDenom_ne_zero",
    "carrMadanKernel_integrable",
    "carrMadan_price_integrable",
    "gbm_carrMadanKernel_integrable",
    "gbm_carrMadan_price_integrable",
    # T5 (BRIEF_006): the same ratchet posture. `t5_delta`/`t5_gamma`/`t5_tau`
    # are the steps the PDE's proof consumes and `t5_bsCall_pde` is the node's
    # claim, so a `sorry` in any of them reverts the node outright. The two
    # analytic inputs (`hasDerivAt_erf`, `hasDerivAt_Phi`) and the four
    # argument-shape lemmas are landed results too, and the [SPINE] check is
    # only meaningful while they are real.
    "hasDerivAt_erf",
    "hasDerivAt_Phi",
    "hasDerivAt_d_spot",
    "d_tau_quotient_eq",
    "hasDerivAt_d_tau",
    "d1_tau_sub_d2_tau",
    "t5_delta",
    "t5_gamma",
    "t5_tau",
    "t5_bsCall_pde_tau",
    "t5_bsCall_pde",
    # T6 sub-goal 3a (BRIEF_007): the same ratchet posture. The two
    # `*_eq_riskNeutral_expectation` theorems are the node's claim, the two
    # measure-theoretic forms restate it against mathlib's laws, and the
    # bridge/tilting/payoff lemmas are the landed steps it consumes, so a
    # `sorry` in any of them reverts the node outright.
    "phi_eq_gaussianPDFReal",
    "Phi_eq_gaussianReal_Iic",
    "integral_gaussianReal_eq_integral_mul_phi",
    "integral_phi",
    "exp_mul_phi_eq",
    "integrable_exp_mul_phi",
    "integral_exp_mul_phi",
    "integral_phi_Ioi",
    "integral_phi_sub_Ioi",
    "integral_exp_mul_phi_Ioi",
    "sigma_sqrt_tau_mul_d2",
    "spot_sub_strike_eq",
    "max_spot_sub_strike_mul_phi",
    "max_sub_swap_eq",
    "integrable_spot_mul_phi",
    "integral_spot_mul_phi_eq_forward",
    "integrable_max_spot_sub_strike_mul_phi",
    "bsCall_eq_riskNeutral_expectation",
    "bsPut_eq_riskNeutral_expectation",
    "bsCall_eq_gaussianReal_expectation",
    "bsCall_eq_lognormal_expectation",
    # T6 sub-goal 3b (BRIEF_008): Fourier inversion and real-valuedness
    "carrMadanInversion_integrand_integrable",
    "gbm_carrMadanInversion_integrable",
    "dampedCallPrice_log_eq",
    "undamped_dampedCallPrice",
    "fourierInversion_dampedCallPrice",
    "fourierInversion_dampedCallPrice_at",
    "carrMadan_inversion_eq_lognormal_expectation",
    "carrMadan_inversion_eq_bsCall",
    "carrMadan_inversion_im_eq_zero",
    "carrMadan_inversion_eq_re",
    "carrMadan_inversion_re_eq_bsCall",
    # BRIEF_009: the model-free skeleton
    "modelFreeCall",
    "modelFreePut",
    "integrable_call_payoff",
    "integrable_put_payoff",
    "model_free_parity_gap",
    "model_free_put_call_parity",
    "model_free_call_nonneg",
    "model_free_call_bounds",
    "model_free_put_bounds",
    "integrable_gaussianReal_iff",
    "lognormal_parity_gap",
    "lognormal_call_bounds",
    "t2_spread_via_skeleton",
    "t4_call_bounds_via_skeleton",
    # BRIEF_010: T6 at any strip law + contour correction C12
    "cmPriceKernel",
    "contourCharFun",
    "cmPriceIntegral",
    "strikeTransform",
    "dampedModelFreeCall",
    "fourierCM",
    "cmPriceKernel_eq_shift",
    "gbm_contourCharFun_eq",
    "gbmCharFactor_pricing_continuous",
    "gbmCharFactor_pricing_norm",
    "cmPriceKernel_integrable",
    "gbm_cmPriceKernel_integrable",
    "cmDenom_factor",
    "integral_Ioi_cexp_neg_mul_eq_inv",
    "ofReal_exp_eq_cexp",
    "norm_cexp_I_mul_ofReal",
    "strikeTransform_eq",
    "integrable_strikeTransform",
    "dampedModelFreeCall_eq_dampedCallPrice",
    "continuous_dampedModelFreeCall",
    "integrable_dampedModelFreeCall_of_exp_moment",
    "fourierDampedModelFreeCall_eq",
    "fourierCM_eq_fourier",
    "fourierCM_inversion",
    "cmPriceIntegral_eq_damped_modelFreeCall",
    "carrMadan_eq_modelFreeCall",
    "cmPriceIntegrand_reflect",
    "carrMadan_im_eq_zero",
    "carrMadan_eq_re",
    "carrMadan_re_eq_modelFreeCall",
    "gbm_carrMadan_eq_bsCall",
    # BRIEF_011: the CGMY node is landed sorry-free from the start
    "cgmyExponent",
    "cgmyCharFactor",
    "cgmyContour",
    "cgmyTemperedRate",
    "cgmyTemperedCorrection",
    "cgmyTemperedConstant",
    "cgmyDecayThreshold",
    "cgmyLevyDensity",
    "cgmyCharFactor_add",
    "cgmyExponent_contour",
    "cgmyOldContour_base_right_re",
    "cgmy_tempered_prod_neg",
    "cgmy_tempered_rate_neg_eq",
    "cgmy_cpow_re_ge_of_lt_one",
    "cgmy_cpow_re_le_of_one_le",
    "cgmyExponent_contour_re",
    "cgmyExponent_contour_re_le",
    "cgmyExponent_contour_re_le_half",
    "cgmy_contour_decay",
    "cgmy_contour_continuous",
    "cgmy_cmPriceKernel_integrable",
    "cgmy_contour_mem_strip",
    "cgmy_numeraire_strip",
    "cgmyExponent_strip",
    "cgmy_levy_sq_integrable",
    "cgmy_levy_far_moment",
}

# The T5 node, in dependency order, and the two citations docs/04's spine
# commits T5 to: `t3_delta_identity` (the cancellation the chain rule consumes)
# and `hasDerivAt_Phi` (the one new analytic input). Checked in [SPINE].
T5_NODE = (
    "t5_delta",
    "t5_gamma",
    "t5_tau",
    "t5_bsCall_pde_tau",
    "t5_bsCall_pde",
)
SPINE_WITNESSES = ("t3_delta_identity", "hasDerivAt_Phi")

# BRIEF_009's route commitments, checked in [SKELETON]. The model-free layer's
# put bounds must be the parity corollary (the T4'-via-T2 mirror: parity + call
# bounds + linarith, no new integration), and the closed-form re-derivations
# `*_via_skeleton` must go THROUGH the model-free layer -- citing one of
# SKELETON_WITNESSES -- and must NOT cite the closed-form proofs they
# re-derive, or the abstraction certifies nothing (it would be graded by the
# very theorems it is supposed to underpin). Bodies are comment-stripped, so
# the honest doc-comments that name the forbidden proofs do not trip this.
SKELETON_PUT_BOUNDS = "model_free_put_bounds"
SKELETON_PARITY_WITNESS = "model_free_put_call_parity"
SKELETON_VIA_NODES = ("t2_spread_via_skeleton", "t4_call_bounds_via_skeleton")
SKELETON_WITNESSES = (
    "model_free_put_call_parity",
    "model_free_call_bounds",
    "lognormal_parity_gap",
    "lognormal_call_bounds",
)
SKELETON_FORBIDDEN = (
    "t2_put_call_parity",
    "t2_put_call_parity_spread",
    "t4_call_bounds",
    "t4_put_bounds",
    "bsCall_nonneg",
    "bsPut_nonneg",
    "Phi_le_exp_mul_Phi_add",
)

# A `sorry` that survives `lake build` is an axiom. Allow none by default.
AXIOM_ALLOWLIST: set[str] = set()

# Any one of these in a parity proof means the odd symmetry of the normal law was
# actually used. See the INDEPENDENCE check for why three names and not one.
ODD_SYMMETRY_WITNESSES = frozenset({"Phi_add_Phi_neg", "Phi_neg", "erf_neg"})

MARKERS = ("sorry", "admit", "native_decide")

# Structural anchors the [ORACLE SYNC] prohibitions apply to. Checked for
# *presence*: the independence checks are "must not mention parity"-style
# negations, and a negation with nothing to negate is a pass, which is how a
# hollowed-out oracle would otherwise keep the lint job green.
ORACLE_ANCHORS = (
    "def norm_cdf(",
    "def norm_pdf(",
    "def _d1d2(",
    "def bs_call(",
    "def bs_put(",
    "def bs_put_by_parity(",
    "def bs_price(",
    "def bs_pde_residual(",
    # the independent d2 expression itself: T1's numerical content is a claim
    # about *this* line, so its absence means T1 is no longer being checked.
    "(log_m + (r - q - 0.5 * s * s) * tau) / den",
)

# Optional modifiers: `noncomputable def erf ...` must be seen as a declaration,
# otherwise a `sorry` hidden inside it escapes the ratchet entirely.
DECL_RE = re.compile(
    r"^(?:(?:noncomputable|unsafe|partial|private|protected|irreducible_def)\s+)*"
    r"(theorem|lemma|def|instance|example|axiom|structure|class|abbrev)\s+"
    r"(?:\{[^}]*\}\s*)?([A-Za-z_][\w.']*)",
    re.MULTILINE,
)


def strip_comments(src: str) -> str:
    """Blank out Lean comments, preserving offsets so line numbers stay correct.

    Handles nested block comments (`/- ... -/`) and line comments (`--`).
    Doc-strings (`/-!`, `/--`) are comments too and get blanked; declarations
    are re-found in the stripped text, so nothing is lost.
    """
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth > 0:
            if out[i] != "\n":
                out[i] = " "
            i += 1
        else:
            i += 1
    return "".join(out)


def declarations(clean: str) -> list[tuple[str, str, int, str]]:
    """Return [(kind, name, line, body)] for every top-level declaration."""
    hits = list(DECL_RE.finditer(clean))
    result = []
    for idx, m in enumerate(hits):
        end = hits[idx + 1].start() if idx + 1 < len(hits) else len(clean)
        body = clean[m.start() : end]
        line = clean[: m.start()].count("\n") + 1
        result.append((m.group(1), m.group(2), line, body))
    return result


def lean_files() -> list[str]:
    found = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [
            d
            for d in dirnames
            if d not in {".git", ".lake", "node_modules", "__pycache__"} and not d.startswith(".")
        ]
        for f in filenames:
            if f.endswith(".lean"):
                found.append(os.path.relpath(os.path.join(dirpath, f), ROOT))
    return sorted(found)


def main() -> int:
    explain = "--explain" in sys.argv
    failures: list[str] = []
    notes: list[str] = []

    files = lean_files()
    if not files:
        print("FATAL: no .lean files found under", ROOT)
        return 2

    baseline = {"deferred": {}, "axioms": []}
    if os.path.exists(BASELINE_PATH):
        baseline = json.load(open(BASELINE_PATH))
    else:
        failures.append(f"[BASELINE] {os.path.relpath(BASELINE_PATH, ROOT)} is missing")

    decls_by_file: dict[str, list] = {}
    for rel in files:
        src = open(os.path.join(ROOT, rel), encoding="utf-8").read()
        clean = strip_comments(src)
        decls_by_file[rel] = declarations(clean)

        # 1. namespace squatting
        if rel.split(os.sep)[0] == "Lean":
            failures.append(
                f"[NAMESPACE] {rel}: a .lean file under a top-level Lean/ directory makes the "
                f"module Lean.* and squats the elaborator's namespace. Use ImprovedBS/."
            )

    all_decls = {name: (rel, kind, line, body)
                 for rel, ds in decls_by_file.items() for kind, name, line, body in ds}

    if explain:
        print("baseline:", json.dumps(baseline, indent=2))
        print("declarations found:")
        for rel, ds in decls_by_file.items():
            for kind, name, line, _ in ds:
                print(f"  {rel}:{line:<5} {kind} {name}")
        return 0

    # 2. required declarations still present
    for name, rel in REQUIRED.items():
        ds = decls_by_file.get(rel, [])
        found_in_rel = any(n == name for _, n, _, _ in ds)
        if not found_in_rel:
            found_elsewhere = [
                f for f, items in decls_by_file.items() if any(n == name for _, n, _, _ in items)
            ]
            if not found_elsewhere:
                failures.append(
                    f"[REQUIRED] `{name}` is not declared anywhere (expected in {rel}). "
                    f"Deleting a theorem is not a way to make this lint pass."
                )
            else:
                notes.append(f"[REQUIRED] `{name}` moved: expected {rel}, found {found_elsewhere}")

    # 3 + 4. deferred-proof markers
    found_deferred: dict[str, int] = {}
    for rel, ds in sorted(decls_by_file.items()):
        for kind, name, line, body in ds:
            hits = []
            for marker in MARKERS:
                # word-boundary match, so `sorryAx`-free text like `nosorry` is not caught
                hits += [m for m in re.finditer(rf"\b{marker}\b", body)]
            if not hits:
                continue
            found_deferred[name] = found_deferred.get(name, 0) + len(hits)
            where = ", ".join(
                f"line {line + body[: h.start()].count(chr(10))}" for h in hits[:3]
            )
            if name in PROTECTED:
                failures.append(
                    f"[PROTECTED] `{name}` ({rel}:{line}) contains "
                    f"{', '.join(sorted({h.group(0) for h in hits}))} at {where}. "
                    f"This is a landed node (T1/T2 per BRIEF_001, T3/T4 per BRIEF_003): "
                    f"an automatic reject."
                )

    base_deferred = baseline.get("deferred", {})
    new_names = sorted(set(found_deferred) - set(base_deferred))
    if new_names:
        failures.append(
            "[RATCHET] deferred-proof markers appeared in declarations not in the baseline: "
            + ", ".join(new_names)
            + f". Baseline allows: {sorted(base_deferred) or '(none)'}."
        )
    for name, count in sorted(found_deferred.items()):
        allowed = base_deferred.get(name)
        if allowed is not None and count > allowed:
            failures.append(
                f"[RATCHET] `{name}` has {count} markers, baseline allows {allowed}."
            )
    total_now, total_base = sum(found_deferred.values()), sum(base_deferred.values())
    if total_now > total_base:
        failures.append(f"[RATCHET] total markers {total_now} > baseline {total_base}")
    notes.append(
        f"[RATCHET] deferred markers: {total_now}/{total_base} budget "
        f"in {sorted(found_deferred) or '(no declarations)'}"
    )

    # 5. axioms
    axioms = sorted(
        name for name, (_, kind, _, _) in all_decls.items() if kind == "axiom"
    )
    unexpected = [a for a in axioms if a not in set(baseline.get("axioms", [])) | AXIOM_ALLOWLIST]
    if unexpected:
        failures.append(
            "[AXIOMS] new top-level axiom(s): " + ", ".join(unexpected)
            + ". An axiom is a `sorry` that survives `lake build` silently."
        )

    # 6. independence / anti-vacuity
    core = decls_by_file.get("ImprovedBS/Core.lean", [])
    bodies = {name: body for _, name, _, body in core}

    def def_body(name: str) -> str:
        """The right-hand side of `def name ... := <rhs>`, comments stripped."""
        b = bodies.get(name)
        if b is None:
            failures.append(f"[INDEPENDENCE] `def {name}` not found in ImprovedBS/Core.lean")
            return ""
        return b.split(":=", 1)[1] if ":=" in b else ""

    d2_rhs = def_body("d2")
    if re.search(r"\bd1\b", d2_rhs):
        failures.append(
            "[INDEPENDENCE] `d2` is defined in terms of `d1`. Then "
            "`t1_d1_minus_d2` is true by construction (`unfold d2; ring`) and a "
            "green build certifies nothing. Give d2 its own explicit formula."
        )
    put_rhs = def_body("bsPut")
    if re.search(r"\bbsCall\b", put_rhs):
        failures.append(
            "[INDEPENDENCE] `bsPut` is defined in terms of `bsCall`. Then "
            "`t2_put_call_parity` is true by construction and never exercises "
            "`Phi_add_Phi_neg`, which is the actual content of parity."
        )
    # and the converse: parity must be reachable from the symmetry lemma
    if "Phi_add_Phi_neg" in bodies and "t2_put_call_parity" in bodies:
        # Any of these witnesses *is* the odd symmetry of the normal law:
        # `Phi_add_Phi_neg` (Phi x + Phi (-x) = 1), `Phi_neg` (Phi (-x) = 1 - Phi x,
        # proved from it), or `erf_neg` -- `Phi` is defined as (1 + erf (x/sqrt 2))/2,
        # so citing `erf_neg` is odd symmetry applied one step closer to the source.
        # What must not happen is a parity proof that cites no symmetry at all.
        #
        # Matching the *content* rather than one preferred *name* is deliberate. A
        # guard that rejects a legitimate proof (`simp only [bsPut, bsCall, Phi,
        # erf_neg]` proves T2 and is arguably the more honest route) is a guard
        # that will get loosened or switched off the first time it fires on real
        # work -- and then it protects nothing. Pin the requirement, not the style.
        cited = set(re.findall(r"\w+", bodies["t2_put_call_parity"]))
        if not (ODD_SYMMETRY_WITNESSES & cited):
            failures.append(
                "[INDEPENDENCE] `t2_put_call_parity` cites none of "
                f"{sorted(ODD_SYMMETRY_WITNESSES)}. BRIEF_001 requires the odd-symmetry "
                "identity to be *used*, not merely to exist: without it parity is not a "
                "claim about the normal law at all."
            )
    else:
        failures.append("[INDEPENDENCE] `Phi_add_Phi_neg` or `t2_put_call_parity` is missing")

    # 7. oracle sync
    if os.path.exists(ORACLE_PATH):
        orc = open(ORACLE_PATH, encoding="utf-8").read()

        # Positive anchors first. Every other ORACLE SYNC check below is a
        # prohibition ("bs_put must not mention parity"), and a set of
        # prohibitions is satisfied by an empty file: hollow out or rename the
        # oracle and the sync check goes green while checking nothing. So the
        # structure the prohibitions apply to has to be *asserted present*, the
        # way tests/test_mutants.py asserts its mutation anchors exist.
        missing = [a for a in ORACLE_ANCHORS if a not in orc]
        if missing:
            failures.append(
                "[ORACLE SYNC] experiments/black_scholes.py is missing "
                + ", ".join(missing)
                + ". The independence checks below are prohibitions on these bodies; "
                "if the bodies are gone the checks are vacuous, so this is a red rather "
                "than a pass. (The oracle lane would also be red, but the lint job runs "
                "without it and must not depend on that.)"
            )

        def py_body(fn: str) -> str:
            """Body of `def fn(...)`, with `#` comments removed."""
            if f"def {fn}(" not in orc:
                return ""
            chunk = orc.split(f"def {fn}(", 1)[1].split("\ndef ", 1)[0]
            return re.sub(r"#.*", "", chunk)

        if "bs_put_by_parity" in py_body("bs_put"):
            failures.append(
                "[ORACLE SYNC] experiments/black_scholes.py derives `bs_put` from parity, "
                "while ImprovedBS/Core.lean defines `bsPut` independently. The two trees "
                "would then be checking different claims."
            )
        if re.search(r"return\s+d1,\s*d1\s*-", py_body("_d1d2")):
            failures.append(
                "[ORACLE SYNC] the oracle's `_d1d2` returns `d1 - s*sq` as d2, while the "
                "Lean `d2` is independent. Align them (docs/01 is the source of truth)."
            )
        notes.append("[ORACLE SYNC] oracle and Lean tree agree on independent derivations")
    else:
        failures.append(f"[ORACLE SYNC] {ORACLE_PATH} not found")

    # 8. crosscheck sync (BRIEF_002)
    crosscheck_path = os.path.join(ROOT, "ImprovedBS", "Crosscheck.lean")
    if os.path.exists(crosscheck_path):
        cc_decls = decls_by_file.get("ImprovedBS/Crosscheck.lean", [])
        cc_bodies = {name: body for _, name, _, body in cc_decls}

        def cc_def_body(name: str) -> str:
            b = cc_bodies.get(name)
            if b is None:
                failures.append(f"[CROSSCHECK SYNC] `def {name}` not found in ImprovedBS/Crosscheck.lean")
                return ""
            return b.split(":=", 1)[1] if ":=" in b else ""

        cc_d2_rhs = cc_def_body("d2")
        if re.search(r"\bd1\b", cc_d2_rhs):
            failures.append(
                "[CROSSCHECK SYNC] ImprovedBS/Crosscheck.lean defines `d2` via `d1` (tautological)"
            )
        cc_put_rhs = cc_def_body("bsPut")
        if re.search(r"\bbsCall\b|\bbsPutByParity\b", cc_put_rhs):
            failures.append(
                "[CROSSCHECK SYNC] ImprovedBS/Crosscheck.lean defines `bsPut` via `bsCall` or `bsPutByParity`"
            )

        # Check that d1 and d2 have matching signs for volatility term
        if "+" not in cc_def_body("d1"):
            failures.append("[CROSSCHECK SYNC] ImprovedBS/Crosscheck.lean `d1` missing `+` in volatility term")
        if "-" not in cc_def_body("d2"):
            failures.append("[CROSSCHECK SYNC] ImprovedBS/Crosscheck.lean `d2` missing `-` in volatility term")

        # Both sides of T3's delta identity must actually be emitted by the
        # twin. Numerically this is NOT the Python comparator's job to catch:
        # the two sides agree within the oracle to ~7e-15 on the grid, far
        # inside the 1e-12 tolerance, so a twin that printed the LHS twice
        # would pass the numeric comparison. What sees the difference is the
        # source: does `runCrosscheck` reference `deltaIdentityRhs` at all
        # (defining it without printing it was ledger C6 item 4)?
        for side in ("deltaIdentityLhs", "deltaIdentityRhs"):
            cc_def_body(side)  # records a `[CROSSCHECK SYNC]` failure if the def is missing
        cc_run_body = cc_def_body("runCrosscheck")
        if cc_run_body != "":
            for side in ("deltaIdentityLhs", "deltaIdentityRhs"):
                if side not in cc_run_body:
                    failures.append(
                        f"[CROSSCHECK SYNC] ImprovedBS/Crosscheck.lean `runCrosscheck` never references "
                        f"`{side}` -- `{side}` can be defined without ever being emitted, in which "
                        "case the cross-verifier compares the delta identity's LHS against the "
                        "oracle's LHS and never checks T3's equation across trees "
                        "(benchmarks/LEDGER.md, C6 item 4)"
                    )

        # Check grid consistency against tests/golden_grid.json
        sys.path.insert(0, os.path.join(ROOT, "scripts"))
        try:
            import gen_grid
            pts = gen_grid.load_and_validate_grid()
            if not gen_grid.check_crosscheck_file(pts):
                failures.append(
                    "[CROSSCHECK SYNC] ImprovedBS/Crosscheck.lean embedded grid does not match tests/golden_grid.json"
                )
        except Exception as e:
            failures.append(f"[CROSSCHECK SYNC] grid check failed: {e}")

        notes.append("[CROSSCHECK SYNC] Crosscheck.lean independent derivations & golden grid verified")

    # 9. statement pins -- the anti-hollowing guard
    #    Every check above can be satisfied by a *vacuous* theorem: `theorem
    #    t4_call_bounds ... : True := trivial` has no `sorry`, cites nothing it
    #    should not, keeps its name, and builds. Nothing else in the repo can see
    #    that the claim is gone -- the oracle has no idea what a Lean statement is.
    #    So compare each protected declaration against the text committed in
    #    tests/golden_statements.json, which needs no toolchain. See
    #    scripts/pin_statements.py for why theorems pin their statement and defs
    #    pin their whole body.
    sys.path.insert(0, os.path.join(ROOT, "scripts"))
    try:
        import pin_statements

        pin_failures = pin_statements.check()
    except Exception as e:  # a sub-check that cannot run is a failure, not a pass
        pin_failures = [f"[PINS] pin check failed to run: {e!r}"]
    if pin_failures:
        failures.extend(pin_failures)
    else:
        notes.append(
            "[PINS] every protected statement matches tests/golden_statements.json "
            "(elaborated-type pins are checked in the build job, not here)"
        )

    # 10. spine -- docs/04 claims *how* T5 is proved, and nothing above can see
    #     that claim change. A brute-force differentiation of `erf` composed
    #     with the log-rational proves the same residual identity while
    #     duplicating T1's `S`-action and T3's cancellation -- the exact drift
    #     "the spine, not six unrelated chores" is about. So: the node's
    #     declarations must exist, the node must cite both inputs the spine
    #     names, and `t5_delta` -- the step whose proof *is* T3's cancellation
    #     -- must cite T3 rather than re-derive it.
    spine_failures: list[str] = []
    t5_missing = [n for n in T5_NODE if n not in bodies]
    if t5_missing:
        spine_failures.append(
            "[SPINE] the T5 node is missing declaration(s) in ImprovedBS/Core.lean: "
            + ", ".join(t5_missing)
            + ". docs/04's spine states T5 = T3 + chain rule + `Phi' = phi`; the "
            "route can only be checked while the node exists."
        )
    else:
        cited = "\n".join(bodies[n] for n in T5_NODE)
        for witness in SPINE_WITNESSES:
            if not re.search(rf"\b{re.escape(witness)}\b", cited):
                spine_failures.append(
                    f"[SPINE] the T5 node never cites `{witness}`. docs/04 pins T5's "
                    "route to T3 + chain rule + `Phi' = phi`; a proof that gets the "
                    "residual without either input has changed the route (and almost "
                    "certainly duplicated T3's cancellation). Cite it, or change "
                    "docs/04's spine and this check in the same PR."
                )
        if not re.search(r"\bt3_delta_identity\b", bodies["t5_delta"]):
            spine_failures.append(
                "[SPINE] `t5_delta` does not cite `t3_delta_identity`. T3 is *what "
                "makes* the delta identity -- the `phi`-bracket is zero by T3 -- so "
                "this is the one step whose proof must consume T3, not re-derive the "
                "cancellation from scratch."
            )
    if spine_failures:
        failures.extend(spine_failures)
    else:
        notes.append(
            "[SPINE] T5 cites `t3_delta_identity` and `hasDerivAt_Phi`: the route "
            "docs/04 states (T3 + chain rule + `Phi' = phi`) holds"
        )

    # 11. skeleton -- BRIEF_009's route commitments at the model-free layer.
    #     (a) `model_free_put_bounds` must cite `model_free_put_call_parity`:
    #     the put bounds are the parity corollary (T4'-via-T2 one layer down),
    #     not an independent integration. (b) each `*_via_skeleton` node must
    #     cite a model-free witness and must not cite the closed-form proof it
    #     re-derives -- the vacuity guard on the abstraction: a re-derivation
    #     that leans on T2/T4 proves the layer is hooked up to nothing. Bodies
    #     are comment-stripped (declarations() runs on strip_comments output),
    #     so the doc-comments that *discuss* the forbidden names stay legal.
    skeleton_failures: list[str] = []
    skel_bodies = {name: body for name, (_, _, _, body) in all_decls.items()}
    putb = skel_bodies.get(SKELETON_PUT_BOUNDS)
    if putb is None:
        skeleton_failures.append(
            "[SKELETON] `model_free_put_bounds` is missing from the tree. The "
            "model-free layer's put bounds are the parity corollary docs/03 §D1 "
            "item 5 instantiates at every later law; the route can only be "
            "checked while the declaration exists."
        )
    elif not re.search(rf"\b{re.escape(SKELETON_PARITY_WITNESS)}\b", putb):
        skeleton_failures.append(
            "[SKELETON] `model_free_put_bounds` does not cite "
            "`model_free_put_call_parity`. The put bounds are parity + call "
            "bounds + `linarith` (the `t4_put_bounds` route one layer down), "
            "not an independent integration: re-deriving them from the payoffs "
            "breaks the chain every later law is supposed to inherit. Cite the "
            "parity theorem, or change BRIEF_009 and this check in the same PR."
        )
    for node in SKELETON_VIA_NODES:
        b = skel_bodies.get(node)
        if b is None:
            skeleton_failures.append(
                f"[SKELETON] `{node}` is missing from the tree. These nodes are "
                "the wire test that the model-free layer is hooked up to the "
                "closed form; without them the abstraction is ungraded."
            )
            continue
        if not any(re.search(rf"\b{re.escape(w)}\b", b) for w in SKELETON_WITNESSES):
            skeleton_failures.append(
                f"[SKELETON] `{node}` cites none of the model-free layer "
                "(" + ", ".join(f"`{w}`" for w in SKELETON_WITNESSES) + "). A "
                "`via_skeleton` node must consume the abstraction it is "
                "grading, or it is just a second copy of the old proof."
            )
        for bad in SKELETON_FORBIDDEN:
            if re.search(rf"\b{re.escape(bad)}\b", b):
                skeleton_failures.append(
                    f"[SKELETON] `{node}` cites `{bad}`. The `via_skeleton` "
                    "nodes exist to RE-DERIVE the closed-form claims through "
                    "the model-free layer; a proof that consumes the very "
                    "theorem it re-derives (or its analytic spine) makes the "
                    "abstraction vacuous. Route: the model-free witnesses plus "
                    "the BRIEF_007 expectation bridge, and nothing else."
                )
    if skeleton_failures:
        failures.extend(skeleton_failures)
    else:
        notes.append(
            "[SKELETON] `model_free_put_bounds` rides parity; the `via_skeleton` "
            "nodes consume the model-free layer and not the closed-form proofs"
        )

    # 12. contour -- BRIEF_010's correction C12. The pricing kernel must be on
    #     the pricing line `u − i(α+1)`, not the `u + iα` line of `carrMadanKernel`.
    #     And `cmPriceIntegral` must be the thing `carrMadan_eq_modelFreeCall`
    #     consumes, otherwise the triangle would be proved at the wrong line.
    contour_failures: list[str] = []
    pricing_path = os.path.join(ROOT, "ImprovedBS", "Pricing.lean")
    if os.path.exists(pricing_path):
        pricing_src = open(pricing_path, encoding="utf-8").read()
        pricing_clean = strip_comments(pricing_src)
        pricing_decls = declarations(pricing_clean)
        pricing_bodies = {name: body for _, name, _, body in pricing_decls}
        cm_body = pricing_bodies.get("cmPriceKernel", "")
        if cm_body == "":
            contour_failures.append("[CONTOUR] `cmPriceKernel` not found in ImprovedBS/Pricing.lean")
        else:
            # Must be defined with `- ↑(α + 1) * Complex.I` (pricing line) and NOT `+ ↑α * Complex.I`
            # Check for the pricing line pattern: minus and (α + 1) and Complex.I
            if not re.search(r"-\s*↑\s*\(\s*α\s*\+\s*1\s*\)\s*\*\s*Complex\.I", cm_body):
                contour_failures.append(
                    "[CONTOUR] `cmPriceKernel` must be defined with `- ↑(α + 1) * Complex.I` "
                    "(the pricing contour `v = u − i(α+1)`), not `+ ↑α * Complex.I` (C12). "
                    f"Body: {cm_body[:200]}"
                )
            if re.search(r"\+\s*↑α\s*\*\s*Complex\.I", cm_body) and "2 * α + 1" not in cm_body:
                # Allow the shift identity to mention +α in its RHS, but not in cmPriceKernel's own RHS
                # The def body is `φ (↑u - ↑(α+1)*I) * ...` so it should NOT contain `+ ↑α * I`
                # as the contour. We already checked for minus pattern, but also forbid plus alone.
                if "- ↑(α + 1)" not in cm_body:
                    contour_failures.append(
                        "[CONTOUR] `cmPriceKernel` appears to use `+ ↑α * Complex.I` "
                        "instead of the pricing line (C12)."
                    )
        # cmPriceIntegral must be consumed by carrMadan_eq_modelFreeCall
        eq_body = pricing_bodies.get("carrMadan_eq_modelFreeCall", "")
        if eq_body == "":
            contour_failures.append("[CONTOUR] `carrMadan_eq_modelFreeCall` not found")
        else:
            if "cmPriceIntegral" not in eq_body:
                contour_failures.append(
                    "[CONTOUR] `carrMadan_eq_modelFreeCall` must consume `cmPriceIntegral` "
                    "(the pricing integral in tree's normalization), otherwise the triangle "
                    "is not proved at the corrected contour."
                )
        # carrMadanKernel must still be on the old line (guard against editing landed def)
        fourier_path = os.path.join(ROOT, "ImprovedBS", "Fourier.lean")
        if os.path.exists(fourier_path):
            fourier_src = open(fourier_path, encoding="utf-8").read()
            fourier_clean = strip_comments(fourier_src)
            fourier_decls = declarations(fourier_clean)
            fourier_bodies = {name: body for _, name, _, body in fourier_decls}
            old_body = fourier_bodies.get("carrMadanKernel", "")
            if old_body != "" and "↑α * Complex.I" not in old_body:
                contour_failures.append(
                    "[CONTOUR] `carrMadanKernel` in Fourier.lean no longer contains "
                    "`↑α * Complex.I` — it must stay on the old line; only `cmPriceKernel` "
                    "is on the pricing line (C12)."
                )
    else:
        contour_failures.append("[CONTOUR] ImprovedBS/Pricing.lean not found")

    if contour_failures:
        failures.extend(contour_failures)
    else:
        notes.append("[CONTOUR] pricing kernel on `u − i(α+1)` and consumed by triangle")

    # [CGMY] BRIEF_011: the concrete CGMY exponent must (1) be defined with the
    # two tempered bases, (2) DISCHARGE BRIEF_010's (H-decay) by consuming
    # `cmPriceKernel_integrable` rather than re-deriving integrability, and
    # (3) carry the CORRECTED contour condition `alpha + 1 < M` -- never the
    # `min (G, M)` spelling of docs/03 §D1 and docs/04's queue (correction C14:
    # `G` does not constrain the pricing line at all; it binds only the old
    # `u + i alpha` line, which `cgmyOldContour_base_right_re` records). A
    # strengthened hypothesis the mathematics does not need is the exact drift
    # this check exists to catch, and it cannot be caught by `lake build`.
    cgmy_path = os.path.join(ROOT, "ImprovedBS", "CGMY.lean")
    if not os.path.exists(cgmy_path):
        failures.append("[CGMY] ImprovedBS/CGMY.lean not found")
    else:
        cgmy_decls = declarations(strip_comments(open(cgmy_path, encoding="utf-8").read()))
        cgmy_bodies = {name: body for _, name, _, body in cgmy_decls}
        cgmy_failures: list[str] = []

        def cgmy_stmt(name: str) -> str:
            body = cgmy_bodies.get(name, "")
            if body == "":
                cgmy_failures.append(f"[CGMY] `{name}` not found")
                return ""
            return body.split(":=")[0]

        # (1) the exponent itself
        exp_body = cgmy_bodies.get("cgmyExponent", "")
        if exp_body == "":
            cgmy_failures.append("[CGMY] `cgmyExponent` not found")
        else:
            for pat, why in (
                (r"Real\.Gamma\s*\(\s*-Y\s*\)", "`Gamma(-Y)` prefactor"),
                (r"Real\.Gamma", "the Gamma function"),
                (r"-\s*Complex\.I\s*\*\s*v", "the `M - iv` base"),
                (r"\+\s*Complex\.I\s*\*\s*v", "the `G + iv` base"),
            ):
                if not re.search(pat, exp_body):
                    cgmy_failures.append(
                        f"[CGMY] `cgmyExponent` must contain {why} (pattern {pat!r})."
                    )

        # (2) the decay instantiation consumes BRIEF_010's theorem
        inst_body = cgmy_bodies.get("cgmy_cmPriceKernel_integrable", "")
        if inst_body == "":
            cgmy_failures.append("[CGMY] `cgmy_cmPriceKernel_integrable` not found")
        else:
            if "cmPriceKernel_integrable" not in inst_body:
                cgmy_failures.append(
                    "[CGMY] `cgmy_cmPriceKernel_integrable` must cite `cmPriceKernel_integrable`: "
                    "BRIEF_011's job is to DISCHARGE BRIEF_010's (H-decay) at the concrete "
                    "exponent, not to re-derive kernel integrability."
                )
            if "cgmyDecayThreshold" not in inst_body:
                cgmy_failures.append(
                    "[CGMY] `cgmy_cmPriceKernel_integrable` must supply the explicit "
                    "`cgmyDecayThreshold` as the tail bound's `u₀`."
                )

        # (3) the corrected condition, and no `min (G, M)` regression
        for name in ("cgmyExponent_contour_re_le", "cgmyExponent_contour_re_le_half",
                     "cgmy_contour_decay", "cgmy_cmPriceKernel_integrable"):
            stmt = cgmy_stmt(name)
            if stmt == "":
                continue
            if re.search(r"min\s*\(?\s*(G|M)\b", stmt):
                cgmy_failures.append(
                    f"[CGMY] `{name}`'s statement mentions a `min` over `G`/`M`: the "
                    "corrected contour condition is `alpha + 1 < M` alone (C14). `G` "
                    "constrains the OLD line `u + i alpha`, not the pricing line."
                )
            if not re.search(r"α\s*\+\s*1\s*<\s*M", stmt):
                cgmy_failures.append(
                    f"[CGMY] `{name}` must carry the corrected contour condition "
                    "`α + 1 < M`."
                )
        # the old-line witness must stay in the tree
        old_stmt = cgmy_stmt("cgmyOldContour_base_right_re")
        if old_stmt != "" and not re.search(r"G\s*-\s*α", old_stmt):
            cgmy_failures.append(
                "[CGMY] `cgmyOldContour_base_right_re` must state `Re(G + iv) = G - α` "
                "on the old line: it is the C14 witness."
            )

        if cgmy_failures:
            failures.extend(cgmy_failures)
        else:
            notes.append(
                "[CGMY] exponent at `Γ(-Y)[(M-iv)^Y - M^Y + (G+iv)^Y - G^Y]`, "
                "decay at `α + 1 < M` (C14), instantiated through `cmPriceKernel_integrable`"
            )

    if "--write-baseline" in sys.argv:
        if failures:
            print(
                "REFUSING to write baseline: the tree has other lint failures. A re-baseline "
                "records the deferred-proof budget; it is not a way to legitimise a tree that "
                "is red for a different reason.\n"
                + "\n".join("  - " + f for f in failures[:8])
            )
            return 1
        protected_hits = sorted(set(found_deferred) & PROTECTED)
        if protected_hits:
            print(
                "REFUSING to write baseline: a protected (landed) node still contains "
                "deferred-proof markers: " + ", ".join(protected_hits) + "\n"
                "A baseline must never legitimise a `sorry` in a protected declaration."
            )
            return 1
        payload = {
            "_read_this": (
                "Ratchet ceiling for deferred-proof markers (sorry / admit / native_decide) "
                "in the Lean tree, enforced by scripts/lean_lint.py. A declaration may "
                "appear here only if its brief explicitly defers it. Lower a count when a "
                "proof lands; never raise one to make CI pass. Landed nodes "
                "(PROTECTED in lean_lint.py) may never appear here at all."
            ),
            "_generated_by": "python3 scripts/lean_lint.py --write-baseline",
            "deferred": {k: found_deferred[k] for k in sorted(found_deferred)},
            "axioms": axioms,
        }
        os.makedirs(os.path.dirname(BASELINE_PATH), exist_ok=True)
        with open(BASELINE_PATH, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2)
            fh.write("\n")
        print(
            f"wrote {os.path.relpath(BASELINE_PATH, ROOT)}: "
            f"{sum(found_deferred.values())} marker(s) across "
            f"{len(found_deferred)} declaration(s): {sorted(found_deferred)}"
        )
        return 0

    for n in notes:
        print("  note:", n)
    if failures:
        print()
        for f in failures:
            print("FAIL", f)
        print(f"\n{len(failures)} lint failure(s)")
        return 1
    print(f"\nlean lint: OK ({len(files)} .lean file(s), {len(all_decls)} declarations)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
