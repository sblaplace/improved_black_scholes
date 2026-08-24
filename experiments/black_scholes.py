"""
Black-Scholes baseline formulas, used ONLY as a numerical handrail for the
formal theory (Lean 4). Kept deliberately dependency-free (stdlib math only)
so it audits trivially: it is a *sanity oracle*, not the artifact.

For notation and the formal statements, see docs/01_baseline.md and Lean/
core/ Theorems.

All times in years, all rates/vols annualized decimals (not percent).
"""

from __future__ import annotations

import math

# ---------------------------------------------------------------- normal


def norm_cdf(x: float) -> float:
    """Phi(x) = 1/2 (1 + erf(x/sqrt 2))."""
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def norm_pdf(x: float) -> float:
    """phi(x) = exp(-x^2/2)/sqrt(2 pi)."""
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


# ---------------------------------------------------------------- core
# Closed form for a European option under geometric Brownian motion.
#
#   tau = T - t > 0                      (years to expiry)
#   d1  = ( ln(S/K) + (r - q + s^2/2) tau ) / (s sqrt tau)
#   d2  = d1 - s sqrt tau
#   C   = S e^{-q tau} N(d1) - K e^{-r tau} N(d2)
#   P   = C - S e^{-q tau} + K e^{-r tau}             <- put-call parity


def _d1d2(S: float, K: float, tau: float, r: float, s: float, q: float):
    sq = math.sqrt(tau)
    d1 = (math.log(S / K) + (r - q + 0.5 * s * s) * tau) / (s * sq)
    return d1, d1 - s * sq


def bs_price(S, K, T, t, r, s, q=0.0, option="call"):
    """BSM European price. Raises ValueError on illegal (tau,s)."""
    tau = T - t
    if tau <= 0.0:
        raise ValueError("tau = T - t must be > 0 (use exercise payoffs at maturity directly)")
    if s <= 0.0:
        raise ValueError("sigma must be > 0")
    if option not in ("call", "put"):
        raise ValueError("option must be 'call' or 'put'")

    disc_s, disc_k = math.exp(-q * tau), math.exp(-r * tau)

    # degenerate limits
    if S <= 0.0:
        return 0.0 if option == "call" else max(K * disc_k, 0.0)
    if K <= 0.0:
        return S * disc_s if option == "call" else 0.0

    d1, d2 = _d1d2(S, K, tau, r, s, q)
    C = S * disc_s * norm_cdf(d1) - K * disc_k * norm_cdf(d2)
    if option == "call":
        return C
    return C - S * disc_s + K * disc_k  # put via parity


# ---------------------------------------------------------------- PDE self-consistency
# The closed form should satisfy, for a dividend-yield-q underlying,
#
#   V_t + (r - q) S V_S + (s^2/2) S^2 V_SS = r V      (BSM diffusion equation)
#
# This finite-difference residual is an independent *numerical* falsifier of
# the formula: if it is not ~0 the closed form is misderived.  (The analytic
# identity is the Lean formal target; this just keeps it honest.)


def bs_pde_residual(S, K, T, t, r, s, q=0.0, option="call", h=1e-3):
    """Central finite differences for V_t + (r-q)S V_S + (s^2/2) S^2 V_SS - r V."""
    if T - t <= 0.0 or s <= 0.0 or S - h <= 0.0:
        return float("nan")

    def V(x, tt):
        return bs_price(x, K, T, tt, r, s, q, option)

    # time derivative: central in calendar time t
    V_t = (V(S, t + h) - V(S, t - h)) / (2.0 * h)
    # first & second spot derivatives (central)
    V_S = (V(S + h, t) - V(S - h, t)) / (2.0 * h)
    V_SS = (V(S + h, t) - 2.0 * V(S, t) + V(S - h, t)) / (h * h)
    residual = V_t + (r - q) * S * V_S + 0.5 * s * s * S * S * V_SS - r * V(S, t)
    return residual