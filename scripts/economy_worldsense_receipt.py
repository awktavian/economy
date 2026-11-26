#!/usr/bin/env python3
"""WorldSense scientific receipt for the `economy` corpus: equilibrium, proper
scoring rules and Kelly growth, published as a NUMERICAL observation.

This module is the numerical half of Kagami's ``WorldSenseScientificFlow`` for
``~/economy``. It computes three classical mathematical-economics quantities
exactly, in pure Python, and publishes them as a ``worldsense.scientific_receipt/1``
receipt with a ``z8.probably/1`` epistemic envelope that
``kagami.core.omni.worldsense_scientific_flow`` and
``kagami.core.strange_loops.godel_reactor_prior`` can ingest.

Tier separation is the point of the file, so it is stated first.
-----------------------------------------------------------------------------
* The FORMAL surface of this repository (the ``theorem``/``lemma`` declarations
  reachable from ``Economy.lean``, the sorry/native_decide/axiom counts, and the
  README census) is read live through :mod:`audit_axioms` and reported verbatim
  under ``formal_grounding``. The static census is a comment-stripped text scan
  of ``Economy/*.lean`` — it runs here, on a MacBook, and IS measured. The
  kernel ``#print axioms`` half, by contrast, needs ``lake env lean`` which is
  Studio-only for this repository (``~/docs/INDEX.md`` §Host-of-record); it is
  reported as ATTESTED-BY-CI with its owner named, never as a measurement made
  here and never as a zero. This module neither proves nor re-certifies any Lean
  theorem.
* Everything computed below is a NUMERICAL OBSERVATION: reproducible code,
  declared parameters, a seeded generator, and a named alternative explanation.
  It carries ``"layer": "Probably"``, ``"epistemic_tier":
  "NUMERICAL_OBSERVATION"``, ``"deductive_proof": False``. No number here
  upgrades a claim to THEOREM, and no theorem name is attached to a number as if
  the number proved it.

What IS verified numerically (each with a measured residual)
-----------------------------------------------------------------------------
1. **Arrow-Debreu Cobb-Douglas exchange.** For consumers with Cobb-Douglas
   utility ``u_i(x) = prod_j x_ij**alpha_ij`` (``sum_j alpha_ij = 1``) and
   strictly positive endowments, the Marshallian demand is
   ``x_ij(p) = alpha_ij * (p . w_i) / p_j``. Three classical invariants are
   measured, never assumed:
     * **Walras's Law** ``p . z(p) = 0`` at arbitrary positive prices — a budget-
       exhaustion identity, checked on seeded random price vectors (absolute and
       scale-invariant residuals) and under an explicit price-scaling leg;
     * a **competitive equilibrium** ``p*`` with ``||z(p*)||_inf < 1e-10``, found by
       TWO independent code paths that must agree: a normalized fixed-point /
       Perron iteration ``p <- normalise(M p)`` on ``M = diag(Omega)^-1 A``, and a
       damped additive Walrasian tatonnement ``p_j <- p_j + tau z_j(p)`` projected
       to the simplex with a backtracking step;
     * the **first welfare theorem** witness: every consumer exhausts their budget
       and every consumer's marginal rate of substitution equals the common price
       ratio ``p_j / p_k``, so no further mutually-gainsome trade exists (an
       interior Pareto optimum).
2. **Strictly proper scoring rules.** For a true distribution ``p`` and any report
   ``q`` on a finite outcome space, the expected-score gap decomposes exactly:
     * **Brier** ``S(q,y) = 2 q.y - ||q||^2`` gives
       ``E_{y~p}[S(p,y) - S(q,y)] = ||p - q||_2^2``;
     * **Logarithmic** ``S(q,y) = log q_y`` gives
       ``E_{y~p}[S(p,y) - S(q,y)] = D_KL(p || q)``.
   Each identity is computed by independent reductions (the definitional
   expected-score difference, the distance/divergence closed form, and a third
   expansion — the one-hot-outcome sum for Brier, the cross-minus-entropy
   decomposition for Log) and must agree to ``< 1e-12``; strict propriety (the gap
   is ``>= 0`` with equality only at ``q = p``) is checked against random
   competitors, not asserted. The
   repo's own ``forecasts/forecast_table.md`` exposure columns are parsed and
   reported as a descriptive calibration divergence — the scoring rules are NOT
   applied as forecast accuracy, because this repository tracks no realized
   outcomes (see ``limits``).
3. **Kelly log-optimal growth.** On discrete state-contingent payoffs the
   logarithmic growth rate is strictly concave in the stake, so the log-optimal
   fraction is the unique maximiser:
     * **Bernoulli favourable game** with win prob ``p``, net odds ``b``:
       ``f* = p - (1-p)/b`` in closed form, with the first-order condition
       ``g'(f*) = 0`` and the strict dominance ``g(f*) >= g(f)`` measured over a
       grid and random competitors;
     * **risky-vs-risk-free portfolio** (a one-parameter capital allocation): the
       interior optimum of ``g(f) = sum_s prob_s log((1-f) Rf + f R_s)`` is located
       by a monotone bisection on ``g'`` and verified via ``g'(f*) ~ 0``, ``g''<0``
       and dominance.
   A fractional-Kelly growth/variance trade-off is reported as the
   ``reactor_optimization_hint`` for ``godel_reactor_prior`` capital/token budget
   allocation: it is a measured alternative to any hand-set fraction, never a
   theorem.

Conventions, declared (``epistemic-rigor.md``: a convention-sensitive
computation states its rule)
-----------------------------------------------------------------------------
* Natural logarithms; a logarithmic-growth rate is measured per period (nats).
* Probability vectors are strictly positive and sum to one; a vector with a
  component ``p_i > 0`` evaluated against a reference with ``q_i = 0`` raises
  rather than returning ``inf`` — the scoring-rule identities and the Kelly
  growth are finite quantities, so an unsupported input is a modelling error, not
  a large number.
* ``D_KL(p || q) = sum p_i log(p_i / q_i)`` uses the ``0 log 0 = 0`` convention
  for ``p_i = 0`` terms.
* The equilibrium price vector is normalised to the simplex (``sum_j p_j = 1``) so
  the reported numbers are scale-free; Walras's Law is checked as an absolute
  residual on the simplex AND as a scale-invariant relative residual under price
  rescaling (``p . z`` is homogeneous of degree one in ``p``).
* All randomness is a deterministic :class:`SplitMix64`; the seed is the only
  stochastic input and it travels in the receipt, so two runs of the same commit
  and options agree byte-for-byte.

Usage
-----
    python3 scripts/economy_worldsense_receipt.py            # human summary
    python3 scripts/economy_worldsense_receipt.py --json     # receipt on stdout
    python3 scripts/economy_worldsense_receipt.py --out /tmp/econ_ws.json
    python3 scripts/economy_worldsense_receipt.py --skip-census

No network access, no Lean build, no required third-party dependency. numpy, when
importable, is used ONLY as a cross-check of the Marshallian demand aggregation,
never as a second implementation; when absent the leg reports a typed absence and
is not counted as a pass.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import math
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence, cast

__all__ = [
    "RECEIPT_SCHEMA",
    "DOMAIN",
    "PROBABLY_SCHEMA",
    "EPISTEMIC_TIER",
    "IDENTITY_TOL",
    "TATONNEMENT_TOL",
    "NumericalEconomyError",
    "SplitMix64",
    "normalise",
    "l2_squared",
    "kl_divergence",
    "shannon_entropy",
    "cross_entropy",
    "CobbDouglasExchange",
    "marshallian_demand",
    "excess_demand",
    "solve_equilibrium",
    "BrierScoring",
    "LogarithmicScoring",
    "verify_scoring_rules",
    "parse_forecast_exposures",
    "BernoulliKelly",
    "PortfolioKelly",
    "kelly_bernoulli",
    "kelly_portfolio",
    "fractional_kelly_tradeoff",
    "build_economy_worldsense_receipt",
    "validate_economy_receipt_epistemics",
    "render_summary",
    "main",
]

# ---------------------------------------------------------------------------
# Tier + schema vocabulary
# ---------------------------------------------------------------------------

#: The receipt schema the flow keys off; the estate's canonical ``schema`` alias
#: carries the same string so ``_receipt_schema_text`` can see it.
RECEIPT_SCHEMA = "worldsense.scientific_receipt/1"
DOMAIN = "mathematical_economics"
PROBABLY_SCHEMA = "z8.probably/1"
PROBABLY_LAYER = "Probably"
EPISTEMIC_TIER = "NUMERICAL_OBSERVATION"
#: Orthogonal to the tier: nothing here was refuted, which is not a claim of
#: truth (``epistemic-rigor.md``: one strength tier AND one truth status).
TRUTH_STATUS = "UNREFUTED"

LANE = "CARBON-ECONOMY-PROPER-SCORING-WORLDSENSE-1126"
ORCH = "RATCHET-1125"

#: Residual bound for every exact identity (Walras, Brier/KL, Kelly first order).
IDENTITY_TOL = 1e-12
#: Convergence bound on the equilibrium excess demand ``||z(p*)||_inf``.
TATONNEMENT_TOL = 1e-10

#: Keys excluded from the content digest: they vary run to run, so digesting
#: them would make a deterministic computation look non-deterministic.
VOLATILE_KEYS = frozenset({"wall_ms", "elapsed_ms", "generated_utc", "created_utc", "pid"})
#: Top-level sections excluded from the digested content (host metadata, the
#: meter that carries the digest, and the formal census which tracks repo state
#: rather than the mathematical spec).
NON_DIGESTED_TOP_KEYS = frozenset({"z8_meter", "provenance", "generated_utc", "created_utc"})

#: Significant digits kept in the hashed payload, so a different last bit from a
#: different libm does not change the digest of identical mathematics.
DIGEST_SIG = 12

#: Fields a WorldSense consumer reads when classifying a receipt.
CONSUMER_SCHEMA_KEYS = ("schema", "kind", "type", "operation", "receipt_type", "event")
#: The words ``worldsense_scientific_flow`` treats as demanding a kernel notary.
#: This receipt asserts none of them about a numerical leg.
BOUNDARY_GATE_TIER_FIELDS = ("tier", "scientific_tier", "claim", "verdict", "status", "evidence", "strength")
PROOF_GRADE_WORDS = ("THEOREM", "CLOSED", "PROVED", "KERNEL_CLEAN", "PROVABLY")

MODULE_PATH = Path(__file__).resolve()
REPO_ROOT = MODULE_PATH.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
FORECAST_TABLE_REL = "forecasts/forecast_table.md"

#: The canonical Cobb-Douglas exchange economy the receipt solves (three goods,
#: three consumers). Declared here so the spec is data the digest covers, not a
#: side effect hidden inside a function.
CANONICAL_EXCHANGE: dict[str, Any] = {
    "goods": ("capital", "labor", "services"),
    "consumers": ("household", "firm", "government"),
    "alpha": [[0.5, 0.3, 0.2], [0.2, 0.5, 0.3], [0.3, 0.2, 0.5]],
    "omega": [[10.0, 5.0, 20.0], [15.0, 30.0, 10.0], [20.0, 15.0, 15.0]],
}
#: The canonical Bernoulli favourable game (win prob, net odds).
CANONICAL_BERNOULLI: dict[str, float] = {"win_prob": 0.6, "odds": 1.0}
#: The canonical risky-vs-risk-free portfolio (risk-free gross return, risky up /
#: down gross returns, up probability).
CANONICAL_PORTFOLIO: dict[str, float] = {
    "risk_free": 1.05, "up": 1.5, "down": 0.8, "prob_up": 0.55,
}


# ---------------------------------------------------------------------------
# Errors + exact probability primitives
# ---------------------------------------------------------------------------


class NumericalEconomyError(ValueError):
    """A declared premise of a numerical computation does not hold."""


def _require_finite(values: Sequence[object], name: str) -> None:
    # ``Sequence[object]`` is deliberate: this boundary vets caller- and
    # CLI-supplied numbers, so it accepts "anything" and the isinstance guards
    # turn that into ``int | float``. ``bool`` is an ``int`` subclass, so the
    # first test is the only thing keeping ``True`` out of a price or probability.
    for i, v in enumerate(values):
        if isinstance(v, bool) or not isinstance(v, (int, float)):
            raise NumericalEconomyError(f"{name}[{i}]_not_a_real_number")
        if not math.isfinite(float(v)):
            raise NumericalEconomyError(f"{name}[{i}]_not_finite")


def _require_positive_vector(name: str, probs: Sequence[float]) -> None:
    """Validate a strictly-positive, normalised probability vector."""
    values = [float(p) for p in probs]
    _require_finite(values, name)
    if not values:
        raise NumericalEconomyError(f"{name}_empty_support")
    if any(v <= 0.0 for v in values):
        raise NumericalEconomyError(f"{name}_not_strictly_positive")
    if abs(math.fsum(values) - 1.0) > 1e-12:
        raise NumericalEconomyError(f"{name}_not_normalised")


def normalise(weights: Sequence[float]) -> tuple[float, ...]:
    """Divide by the total mass; refuse a non-positive total rather than emit NaN."""
    values = [float(w) for w in weights]
    _require_finite(values, "weights")
    if any(v < 0.0 for v in values):
        raise NumericalEconomyError("weights_negative")
    total = math.fsum(values)
    if total <= 0.0:
        raise NumericalEconomyError("weights_sum_to_zero")
    return tuple(v / total for v in values)


def dot(a: Sequence[float], b: Sequence[float]) -> float:
    """Exact ``fsum`` inner product (the accumulation order the residuals use)."""
    return math.fsum(float(x) * float(y) for x, y in zip(a, b))


def l2_squared(a: Sequence[float], b: Sequence[float]) -> float:
    """``||a - b||_2^2``."""
    if len(a) != len(b):
        raise NumericalEconomyError("l2_support_mismatch")
    return math.fsum((float(x) - float(y)) ** 2 for x, y in zip(a, b))


def kl_divergence(probs: Sequence[float], reference: Sequence[float], *,
                  name: str = "kl") -> float:
    """``D_KL(p || q) = sum_i p_i log(p_i / q_i)``, ``0 log 0 = 0``.

    ``p_i > 0`` with ``q_i = 0`` raises: the divergence is infinite and every
    identity that consumes it here assumes strict positivity, so a silent ``inf``
    would let an unsupported model produce a plausible-looking number.
    """
    p = [float(x) for x in probs]
    q = [float(x) for x in reference]
    if len(p) != len(q):
        raise NumericalEconomyError(f"{name}_support_mismatch")
    _require_finite(p, f"{name}.p")
    _require_finite(q, f"{name}.q")
    if any(v < 0.0 for v in p) or any(v < 0.0 for v in q):
        raise NumericalEconomyError(f"{name}_negative_mass")
    total = 0.0
    for pi, qi in zip(p, q):
        if pi <= 0.0:
            continue
        if qi <= 0.0:
            raise NumericalEconomyError(f"{name}_support_violation")
        total += pi * math.log(pi / qi)
    return total


def shannon_entropy(probs: Sequence[float]) -> float:
    """``H(p) = -sum p log p`` with ``0 log 0 = 0``."""
    values = [float(p) for p in probs]
    if abs(math.fsum(values) - 1.0) > 1e-12:
        raise NumericalEconomyError("entropy_not_normalised")
    return -math.fsum(p * math.log(p) for p in values if p > 0.0)


def cross_entropy(probs: Sequence[float], reference: Sequence[float]) -> float:
    """``H(p, q) = -sum p log q``."""
    p = [float(x) for x in probs]
    q = [float(x) for x in reference]
    if len(p) != len(q):
        raise NumericalEconomyError("cross_entropy_support_mismatch")
    total = 0.0
    for pi, qi in zip(p, q):
        if pi <= 0.0:
            continue
        if qi <= 0.0:
            raise NumericalEconomyError("cross_entropy_reference_zero_on_support")
        total -= pi * math.log(qi)
    return total


# ---------------------------------------------------------------------------
# Deterministic generator (the seed is the only stochastic input)
# ---------------------------------------------------------------------------


class SplitMix64:
    """Deterministic 64-bit generator (Steele et al. splitmix64).

    Deliberately not :class:`random.Random`: a NUMERICAL_OBSERVATION receipt must
    replay on CPython 3.11 through 3.15 identically, which pins the seed as the
    only input the digest depends on.
    """

    __slots__ = ("_state",)
    _MASK = (1 << 64) - 1

    def __init__(self, seed: int) -> None:
        # ``bool`` is an ``int`` subclass, so this is the only runtime narrowing
        # the annotated ``int`` does not already guarantee.
        if isinstance(seed, bool):
            raise NumericalEconomyError("splitmix_seed_must_be_int")
        self._state = seed & self._MASK

    def next_u64(self) -> int:
        self._state = (self._state + 0x9E3779B97F4A7C15) & self._MASK
        z = self._state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & self._MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & self._MASK
        return z ^ (z >> 31)

    def unit(self) -> float:
        """A float in (0, 1) — the open interval keeps ``log`` finite."""
        return ((self.next_u64() >> 11) + 0.5) / (1 << 53)

    def uniform(self, low: float, high: float) -> float:
        return low + (high - low) * self.unit()

    def simplex(self, size: int, *, floor: float = 1e-9) -> tuple[float, ...]:
        """A strictly positive simplex point via ``-log u`` exponentials."""
        if size < 1:
            raise NumericalEconomyError("simplex_size_must_be_positive")
        raw = [max(-math.log(self.unit()), floor) for _ in range(size)]
        return normalise(raw)


# ---------------------------------------------------------------------------
# 1. Arrow-Debreu Cobb-Douglas exchange equilibrium
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CobbDouglasExchange:
    """An endowment economy of Cobb-Douglas consumers.

    ``alpha[i][j]`` is consumer ``i``'s budget share of good ``j`` (rows sum to
    one); ``omega[i][j]`` is consumer ``i``'s strictly positive endowment of good
    ``j``.
    """

    alpha: tuple[tuple[float, ...], ...]
    omega: tuple[tuple[float, ...], ...]
    goods: tuple[str, ...] = ()
    consumers: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        a = [[float(x) for x in row] for row in self.alpha]
        w = [[float(x) for x in row] for row in self.omega]
        if not a or not w:
            raise NumericalEconomyError("exchange_empty")
        if len(a) != len(w):
            raise NumericalEconomyError("exchange_consumer_count_mismatch")
        n = len(a[0])
        for row in a:
            if len(row) != n:
                raise NumericalEconomyError("exchange_ragged_alpha")
            if any(v <= 0.0 for v in row):
                raise NumericalEconomyError("exchange_alpha_not_strictly_positive")
            if abs(math.fsum(row) - 1.0) > 1e-12:
                raise NumericalEconomyError("exchange_alpha_row_not_normalised")
        for row in w:
            if len(row) != n:
                raise NumericalEconomyError("exchange_ragged_omega")
            if any(v <= 0.0 for v in row):
                raise NumericalEconomyError("exchange_endowment_not_strictly_positive")
        object.__setattr__(self, "alpha", tuple(tuple(r) for r in a))
        object.__setattr__(self, "omega", tuple(tuple(r) for r in w))

    @property
    def n_consumers(self) -> int:
        return len(self.alpha)

    @property
    def n_goods(self) -> int:
        return len(self.alpha[0])

    def aggregate_endowment(self) -> tuple[float, ...]:
        return tuple(
            math.fsum(self.omega[i][j] for i in range(self.n_consumers))
            for j in range(self.n_goods)
        )

    def matrix_a(self) -> tuple[tuple[float, ...], ...]:
        """``A_jk = sum_i alpha_ij omega_ik`` (value-weighted endowment matrix)."""
        n = self.n_goods
        return tuple(
            tuple(
                math.fsum(self.alpha[i][j] * self.omega[i][k] for i in range(self.n_consumers))
                for k in range(n)
            )
            for j in range(n)
        )

    def as_dict(self) -> dict[str, Any]:
        return {
            "goods": list(self.goods) or [f"good_{j}" for j in range(self.n_goods)],
            "consumers": list(self.consumers) or [f"consumer_{i}" for i in range(self.n_consumers)],
            "alpha": [list(r) for r in self.alpha],
            "omega": [list(r) for r in self.omega],
            "aggregate_endowment": list(self.aggregate_endowment()),
        }


def income(exchange: CobbDouglasExchange, prices: Sequence[float], i: int) -> float:
    """Consumer ``i``'s budget ``p . omega_i``."""
    return dot(prices, exchange.omega[i])


def marshallian_demand(exchange: CobbDouglasExchange, prices: Sequence[float]
                       ) -> tuple[tuple[float, ...], ...]:
    """Cobb-Douglas Marshallian demand ``x_ij = alpha_ij (p . omega_i) / p_j``.

    Positive prices are required: ``p_j`` divides, so a non-positive price is a
    modelling error, not a large number.
    """
    p = [float(x) for x in prices]
    if len(p) != exchange.n_goods:
        raise NumericalEconomyError("demand_price_length_mismatch")
    if any(v <= 0.0 for v in p):
        raise NumericalEconomyError("demand_price_not_positive")
    rows: list[tuple[float, ...]] = []
    for i in range(exchange.n_consumers):
        inc = income(exchange, p, i)
        rows.append(tuple(exchange.alpha[i][j] * inc / p[j] for j in range(exchange.n_goods)))
    return tuple(rows)


def excess_demand(exchange: CobbDouglasExchange, prices: Sequence[float]
                  ) -> tuple[float, ...]:
    """Aggregate excess demand ``z_j(p) = sum_i x_ij(p) - Omega_j``."""
    p = [float(x) for x in prices]
    demand = marshallian_demand(exchange, p)
    omega = exchange.aggregate_endowment()
    return tuple(
        math.fsum(demand[i][j] for i in range(exchange.n_consumers)) - omega[j]
        for j in range(exchange.n_goods)
    )


def walras_residual(exchange: CobbDouglasExchange, prices: Sequence[float]
                    ) -> dict[str, float]:
    """Absolute and scale-invariant residuals of ``p . z(p) = 0``."""
    p = [float(x) for x in prices]
    z = excess_demand(exchange, p)
    pdz = dot(p, z)
    value = dot(p, exchange.aggregate_endowment())
    return {
        "abs_p_dot_z": abs(pdz),
        "rel_p_dot_z": abs(pdz) / value if value > 0.0 else math.inf,
    }


def _perron_fixed_point(exchange: CobbDouglasExchange) -> tuple[list[float], int]:
    """Normalised fixed-point / Perron iteration ``p <- normalise(M p)``.

    ``M = diag(Omega)^-1 A`` is strictly positive when endowments and shares are,
    so Perron-Frobenius gives a unique positive eigenvector for the dominant
    eigenvalue, which is exactly the equilibrium price vector. Iteration converges
    geometrically; we drive the fixed-point residual below ``IDENTITY_TOL``.
    """
    n = exchange.n_goods
    a = exchange.matrix_a()
    omega = exchange.aggregate_endowment()
    m = [[a[j][k] / omega[j] for k in range(n)] for j in range(n)]
    p = [1.0 / n] * n
    iterations = 0
    for iterations in range(1, 200001):
        q = [math.fsum(m[j][k] * p[k] for k in range(n)) for j in range(n)]
        pn = list(normalise(q))
        if max(abs(pn[k] - p[k]) for k in range(n)) < 1e-16:
            p = pn
            break
        p = pn
    return p, iterations


def _tatonnement(exchange: CobbDouglasExchange, p0: Sequence[float], *,
                 tau: float = 5e-3, tol: float = 1e-13, max_steps: int = 200000,
                 ) -> tuple[list[float], int, bool]:
    """Damped additive Walrasian tatonnement projected to the simplex.

    ``p_j <- p_j + tau z_j(p)``, renormalised. A backtracking line search halves
    ``tau`` whenever a trial step raises the excess-demand norm or drives a price
    non-positive, which keeps the trajectory on the positive simplex and makes the
    convergence monotone for this gross-substitutes (Cobb-Douglas) economy.
    """
    p = list(normalise(p0))

    def norm_z(vec: Sequence[float]) -> float:
        return max(abs(x) for x in excess_demand(exchange, vec))

    step = float(tau)
    current = norm_z(p)
    it = 0
    for it in range(1, max_steps + 1):
        if current < tol:
            return p, it, True
        z = excess_demand(exchange, p)
        accepted = False
        trial_step = step
        for _ in range(60):  # bounded backtracking
            cand = [max(p[j] + trial_step * z[j], 1e-12) for j in range(exchange.n_goods)]
            cand = list(normalise(cand))
            cand_norm = norm_z(cand)
            if cand_norm < current or trial_step < 1e-15:
                p = cand
                current = cand_norm
                step = min(trial_step * 1.2, 0.05)
                accepted = True
                break
            trial_step *= 0.5
        if not accepted:
            return p, it, False
    return p, it, current < tol


@dataclass(frozen=True)
class EquilibriumReport:
    prices: tuple[float, ...]
    prices_tatonnement: tuple[float, ...]
    excess_demand: tuple[float, ...]
    max_abs_excess_demand: float
    tatonnement_iterations: int
    tatonnement_converged: bool
    fixed_point_iterations: int
    path_agreement: float
    walras_random_abs_max: float
    walras_random_rel_max: float
    walras_scale_relative_residual: float
    budget_exhaustion_max: float
    mrs_price_ratio_max: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "prices_simplex": list(self.prices),
            "prices_tatonnement_simplex": list(self.prices_tatonnement),
            "excess_demand_at_equilibrium": list(self.excess_demand),
            "max_abs_excess_demand": self.max_abs_excess_demand,
            "solver_paths": {
                "fixed_point_iterations": self.fixed_point_iterations,
                "tatonnement_iterations": self.tatonnement_iterations,
                "tatonnement_converged": self.tatonnement_converged,
                "max_price_path_agreement": self.path_agreement,
            },
            "walras_law": {
                "max_abs_p_dot_z_random_prices": self.walras_random_abs_max,
                "max_rel_p_dot_z_random_prices": self.walras_random_rel_max,
                "scale_invariance_residual": self.walras_scale_relative_residual,
            },
            "first_welfare_theorem": {
                "max_budget_exhaustion_residual": self.budget_exhaustion_max,
                "max_mrs_price_ratio_residual": self.mrs_price_ratio_max,
            },
        }


def solve_equilibrium(exchange: CobbDouglasExchange, rng: SplitMix64,
                      *, price_samples: int = 20000) -> EquilibriumReport:
    """Solve the equilibrium by two paths and verify the three invariants."""
    p_fp, fp_iters = _perron_fixed_point(exchange)
    z_star = list(excess_demand(exchange, p_fp))
    linf = max(abs(x) for x in z_star)

    # second, independent path: tatonnement from a seeded interior price vector
    p0 = list(rng.simplex(exchange.n_goods, floor=0.02))
    p_tat, tat_iters, tat_conv = _tatonnement(exchange, p0)
    path_agreement = max(abs(p_fp[k] - p_tat[k]) for k in range(exchange.n_goods))

    # Walras's Law at seeded random prices on the simplex (absolute residual is
    # scale-free once normalised) plus an explicit price-scaling leg.
    abs_max = 0.0
    rel_max = 0.0
    for _ in range(price_samples):
        p = list(rng.simplex(exchange.n_goods, floor=1e-6))
        res = walras_residual(exchange, p)
        abs_max = max(abs_max, res["abs_p_dot_z"])
        rel_max = max(rel_max, res["rel_p_dot_z"])
    base = list(rng.simplex(exchange.n_goods, floor=1e-3))
    scale = 10.0 ** rng.uniform(-4.0, 4.0)
    scaled = [x * scale for x in base]
    scale_res = walras_residual(exchange, scaled)
    base_res = walras_residual(exchange, base)
    scale_residual = abs(scale_res["rel_p_dot_z"] - base_res["rel_p_dot_z"])

    # first welfare theorem: budget exhaustion + MRS / price-ratio equalisation.
    n = exchange.n_goods
    budget_max = 0.0
    for i in range(exchange.n_consumers):
        inc = income(exchange, p_fp, i)
        spend = math.fsum(p_fp[j] * exchange.alpha[i][j] * inc / p_fp[j] for j in range(n))
        budget_max = max(budget_max, abs(spend - inc))
    mrs_max = 0.0
    for i in range(exchange.n_consumers):
        inc = income(exchange, p_fp, i)
        x = [exchange.alpha[i][j] * inc / p_fp[j] for j in range(n)]
        mu = [exchange.alpha[i][j] / x[j] for j in range(n)]  # marginal utility
        for j in range(n):
            for k in range(n):
                if j == k:
                    continue
                mrs = mu[j] / mu[k]
                mrs_max = max(mrs_max, abs(mrs - p_fp[j] / p_fp[k]))
    return EquilibriumReport(
        prices=tuple(p_fp),
        prices_tatonnement=tuple(p_tat),
        excess_demand=tuple(z_star),
        max_abs_excess_demand=linf,
        tatonnement_iterations=tat_iters,
        tatonnement_converged=tat_conv,
        fixed_point_iterations=fp_iters,
        path_agreement=path_agreement,
        walras_random_abs_max=abs_max,
        walras_random_rel_max=rel_max,
        walras_scale_relative_residual=scale_residual,
        budget_exhaustion_max=budget_max,
        mrs_price_ratio_max=mrs_max,
    )


# ---------------------------------------------------------------------------
# 2. Strictly proper scoring rules (Brier + Logarithmic)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class BrierScoring:
    """Expected-score identity ``E_p[S(p) - S(q)] = ||p - q||_2^2``."""

    expected_gap: float
    l2_squared_form: float
    onehot_expansion_form: float
    residual_l2: float
    residual_onehot_expansion: float
    propriety_min_gap: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "score": "S(q,y) = 2 q.y - ||q||^2 (one-hot outcome y)",
            "expected_gap_E_p[S(p)-S(q)]": self.expected_gap,
            "identity_right_side_norm_p_minus_q_sq": self.l2_squared_form,
            "onehot_expansion_form_sum_k_p_k_S_p_ek_minus_S_q_ek": self.onehot_expansion_form,
            "residual_vs_l2": self.residual_l2,
            "residual_vs_onehot_expansion": self.residual_onehot_expansion,
            "propriety_min_gap_over_competitors": self.propriety_min_gap,
        }


@dataclass(frozen=True)
class LogarithmicScoring:
    """Expected-score identity ``E_p[S(p) - S(q)] = D_KL(p || q)``."""

    expected_gap: float
    kl_form: float
    entropy_decomposition_form: float
    residual_kl: float
    residual_entropy: float
    propriety_min_gap: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "score": "S(q,y) = log q_y (natural log, one-hot outcome y)",
            "expected_gap_E_p[S(p)-S(q)]": self.expected_gap,
            "identity_right_side_kl_p_q": self.kl_form,
            "entropy_decomposition_form_cross_minus_entropy": self.entropy_decomposition_form,
            "residual_vs_kl": self.residual_kl,
            "residual_vs_entropy_decomposition": self.residual_entropy,
            "propriety_min_gap_over_competitors": self.propriety_min_gap,
        }


def _brier_expected_score(report: Sequence[float], truth: Sequence[float]) -> float:
    """``E_{y~truth}[S(report,y)] = 2 report.truth - ||report||^2`` (one-hot y)."""
    return 2.0 * dot(report, truth) - math.fsum(r * r for r in report)


def _log_expected_score(report: Sequence[float], truth: Sequence[float]) -> float:
    """``E_{y~truth}[S(report,y)] = sum_j truth_j log report_j``."""
    return -cross_entropy(truth, report)


@dataclass(frozen=True)
class ScoringProbe:
    """One (truth, report) pair with both identities measured three ways."""

    truth: tuple[float, ...]
    report: tuple[float, ...]
    brier: BrierScoring
    log: LogarithmicScoring

    def as_dict(self) -> dict[str, Any]:
        return {
            "truth": list(self.truth),
            "report": list(self.report),
            "brier": self.brier.as_dict(),
            "logarithmic": self.log.as_dict(),
        }


def _score_pair(truth: Sequence[float], report: Sequence[float]) -> ScoringProbe:
    p = tuple(float(x) for x in truth)
    q = tuple(float(x) for x in report)
    _require_positive_vector("scoring.truth", p)
    _require_positive_vector("scoring.report", q)
    if len(p) != len(q):
        raise NumericalEconomyError("scoring_support_mismatch")

    # Three independent reductions of the same quantity E_{y~p}[S(p,y)-S(q,y)]:
    #   expected_gap = E_p[S(p)] - E_p[S(q)] via the linear expected-score form;
    #   l2_squared   = ||p-q||^2, the identity's right-hand side;
    #   onehot       = sum_k p_k (S(p,e_k) - S(q,e_k)), the definition expanded
    #                  over the one-hot outcomes. All three equal ||p-q||^2 in
    #                  exact arithmetic; the residuals measure float agreement.
    # (A p-weighted sum of squared coordinate differences is NOT one of them --
    #  sum_k p_k (q_k-p_k)^2 is not ||p-q||^2 and would be a false identity.)
    ssq_p = math.fsum(x * x for x in p)
    ssq_q = math.fsum(x * x for x in q)
    b_gap = _brier_expected_score(p, p) - _brier_expected_score(q, p)
    b_l2 = l2_squared(p, q)
    b_onehot = math.fsum(
        p[k] * ((2.0 * p[k] - ssq_p) - (2.0 * q[k] - ssq_q)) for k in range(len(p))
    )
    brier = BrierScoring(
        expected_gap=b_gap,
        l2_squared_form=b_l2,
        onehot_expansion_form=b_onehot,
        residual_l2=abs(b_gap - b_l2),
        residual_onehot_expansion=abs(b_gap - b_onehot),
        propriety_min_gap=b_l2,
    )

    l_gap = _log_expected_score(p, p) - _log_expected_score(q, p)
    l_kl = kl_divergence(p, q, name="scoring.log")
    l_ent = cross_entropy(p, q) - shannon_entropy(p)  # D_KL = H(p,q) - H(p)
    log = LogarithmicScoring(
        expected_gap=l_gap,
        kl_form=l_kl,
        entropy_decomposition_form=l_ent,
        residual_kl=abs(l_gap - l_kl),
        residual_entropy=abs(l_gap - l_ent),
        propriety_min_gap=l_kl,
    )
    return ScoringProbe(truth=p, report=q, brier=brier, log=log)


@dataclass(frozen=True)
class ScoringVerification:
    """Aggregate over many seeded (truth, report) pairs."""

    probe: ScoringProbe
    n_pairs: int
    brier_max_residual_l2: float
    brier_max_residual_onehot_expansion: float
    log_max_residual_kl: float
    log_max_residual_entropy: float
    brier_propriety_all_nonneg: bool
    log_propriety_all_nonneg: bool
    log_gibbs_max_negative: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "headline_probe": self.probe.as_dict(),
            "n_random_pairs": self.n_pairs,
            "brier": {
                "max_residual_vs_l2_squared": self.brier_max_residual_l2,
                "max_residual_vs_onehot_expansion": self.brier_max_residual_onehot_expansion,
                "all_gaps_nonneg": self.brier_propriety_all_nonneg,
            },
            "logarithmic": {
                "max_residual_vs_kl": self.log_max_residual_kl,
                "max_residual_vs_entropy_decomposition": self.log_max_residual_entropy,
                "all_gaps_nonneg": self.log_propriety_all_nonneg,
                "worst_gibbs_negative": self.log_gibbs_max_negative,
            },
        }


def verify_scoring_rules(rng: SplitMix64, *, n_pairs: int = 4000,
                         support: int = 6) -> ScoringVerification:
    """Verify the Brier and Logarithmic identities over seeded random pairs.

    Each pair checks the expected-score gap against two independent closed forms:
    for Brier, the Euclidean-squared distance ``||p-q||^2`` and the one-hot-outcome
    expansion ``sum_k p_k (S(p,e_k)-S(q,e_k))``; for Log, ``D_KL(p||q)`` and the
    cross-minus-entropy decomposition. All agree with the definitional expected-score
    difference to machine precision. Strict propriety (the gap is ``>= 0``) is
    asserted as the minimum over the competitor reports, never assumed.
    """
    # headline probe is a fixed, human-readable pair so the printed numbers are
    # stable; the aggregate sweeps random pairs.
    p = normalise([0.4, 0.25, 0.2, 0.1, 0.05, 0.025, 0.025])
    q = normalise([0.15, 0.15, 0.3, 0.2, 0.1, 0.05, 0.05])
    headline = _score_pair(p, q)

    b_l2 = 0.0
    b_oh = 0.0
    l_kl = 0.0
    l_en = 0.0
    all_b_nonneg = True
    all_l_nonneg = True
    worst_gibbs = 0.0
    for _ in range(n_pairs):
        size = 2 + (rng.next_u64() % support)
        tp = rng.simplex(size)
        rq = rng.simplex(size)
        probe = _score_pair(tp, rq)
        b_l2 = max(b_l2, probe.brier.residual_l2)
        b_oh = max(b_oh, probe.brier.residual_onehot_expansion)
        l_kl = max(l_kl, probe.log.residual_kl)
        l_en = max(l_en, probe.log.residual_entropy)
        if probe.brier.l2_squared_form < 0.0:
            all_b_nonneg = False
        if probe.log.kl_form < 0.0:
            all_l_nonneg = False
        worst_gibbs = min(worst_gibbs, probe.log.kl_form)
    return ScoringVerification(
        probe=headline,
        n_pairs=n_pairs,
        brier_max_residual_l2=b_l2,
        brier_max_residual_onehot_expansion=b_oh,
        log_max_residual_kl=l_kl,
        log_max_residual_entropy=l_en,
        brier_propriety_all_nonneg=all_b_nonneg,
        log_propriety_all_nonneg=all_l_nonneg,
        log_gibbs_max_negative=worst_gibbs,
    )


def parse_forecast_exposures(root: Path | str | None = None) -> dict[str, Any]:
    """Read the exposure columns of ``forecasts/forecast_table.md`` for context.

    The table reports the model's own exposure fraction ``H / H_max`` (clipped to
    ``[0, 1]``) for each calibration at each horizon. These are deterministic
    MODEL OUTPUTS, not event forecasts with realized outcomes, so they are
    reported as a descriptive calibration divergence and are NEVER scored as
    forecast accuracy. A missing file is a typed absence, not a fabricated panel.
    """
    base = Path(root) if root is not None else REPO_ROOT
    path = base / FORECAST_TABLE_REL
    result: dict[str, Any] = {
        "source": FORECAST_TABLE_REL,
        "present": False,
        "calibrations": {},
        "pairwise_brier_divergence": {},
        "score_semantics": "descriptive_calibration_divergence",
        "not_forecast_accuracy": True,
        "absence": None,
    }
    if not path.is_file():
        result["absence"] = "forecast_table_missing"
        return result
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        result["absence"] = f"forecast_table_unreadable:{type(exc).__name__}"
        return result

    calibrations: dict[str, list[float]] = {}
    # Split into the "## cal... " sections and pull the first in-[0,1] numeric
    # cell of each integer-horizon row (the exposure column).
    for section in re.split(r"^##\s+", text, flags=re.MULTILINE):
        header = section.splitlines()[0].strip() if section.splitlines() else ""
        if not header.startswith("cal"):
            continue
        vals: list[float] = []
        for line in section.splitlines():
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cells) < 2 or not re.match(r"^\d+$", cells[0]):
                continue
            for cell in cells[1:]:
                cleaned = cell.replace("**", "").replace("(saturated)", "").replace("≈", "").strip()
                if not cleaned:
                    continue
                try:
                    v = float(cleaned)
                except ValueError:
                    continue
                if 0.0 <= v <= 1.0:
                    vals.append(v)
                    break
        if vals:
            calibrations[header] = vals
    result["present"] = bool(calibrations)
    result["calibrations"] = calibrations
    if not result["present"]:
        result["absence"] = "no_exposure_columns_parsed"
        return result
    names = sorted(calibrations)
    for a in range(len(names)):
        for b in range(a + 1, len(names)):
            va, vb = calibrations[names[a]], calibrations[names[b]]
            k = min(len(va), len(vb))
            if k == 0:
                continue
            divergence = math.fsum((va[t] - vb[t]) ** 2 for t in range(k))
            result["pairwise_brier_divergence"][f"{names[a]}|{names[b]}"] = divergence
    return result


# ---------------------------------------------------------------------------
# 3. Kelly log-optimal growth
# ---------------------------------------------------------------------------


def _clamp_domain(f: float, lo: float, hi: float) -> float:
    return min(max(f, lo), hi)


@dataclass(frozen=True)
class BernoulliKelly:
    """Closed-form Kelly fraction for a win/lose favourable game."""

    win_prob: float
    odds: float
    fraction: float
    fraction_closed_form: float
    kkt_residual: float
    concavity_second_derivative: float
    growth_at_optimum: float
    dominance_min_gap: float
    dominance_violations: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "case": "bernoulli_favourable_game",
            "win_prob": self.win_prob,
            "net_odds": self.odds,
            "kelly_fraction": self.fraction,
            "closed_form_p_minus_q_over_b": self.fraction_closed_form,
            "growth_per_period": self.growth_at_optimum,
            "first_order_residual_g_prime": self.kkt_residual,
            "second_derivative_g_double_prime": self.concavity_second_derivative,
            "dominance_min_growth_gap": self.dominance_min_gap,
            "dominance_violations": self.dominance_violations,
        }


def kelly_bernoulli(rng: SplitMix64, *, win_prob: float, odds: float,
                    competitors: int = 20000) -> BernoulliKelly:
    """Log-optimal stake for ``g(f) = p log(1 + b f) + (1-p) log(1 - f)``.

    The closed form is ``f* = p - (1-p)/b`` clipped to the admissible interval
    ``[0, 1)`` (a favourable game needs ``p b > 1 - p`` for an interior stake).
    The first-order residual ``g'(f*)`` and the strict dominance over random
    competitors are measured, not assumed.
    """
    if not 0.0 < win_prob < 1.0:
        raise NumericalEconomyError("kelly_win_prob_out_of_range")
    if odds <= 0.0:
        raise NumericalEconomyError("kelly_odds_must_be_positive")

    def g(f: float) -> float:
        return win_prob * math.log(1.0 + odds * f) + (1.0 - win_prob) * math.log(1.0 - f)

    def g_prime(f: float) -> float:
        return (win_prob * odds / (1.0 + odds * f)
                - (1.0 - win_prob) / (1.0 - f))

    def g_double_prime(f: float) -> float:
        return (-win_prob * odds * odds / (1.0 + odds * f) ** 2
                - (1.0 - win_prob) / (1.0 - f) ** 2)

    closed = win_prob - (1.0 - win_prob) / odds
    f_star = _clamp_domain(closed, 0.0, 1.0 - 1e-9)
    g_prime_star = g_prime(f_star) if f_star < 1.0 - 1e-9 else -math.inf
    # At the lower boundary (unfavourable game) the KKT condition is an
    # inequality g'(0) <= 0; report the residual against the active constraint.
    if closed <= 0.0:
        kkt_residual = abs(min(g_prime(0.0), 0.0))
    else:
        kkt_residual = abs(g_prime_star)

    g_star = g(f_star)
    min_gap = math.inf
    violations = 0
    for _ in range(competitors):
        f = rng.uniform(0.0, 1.0 - 1e-9)
        gap = g_star - g(f)
        min_gap = min(min_gap, gap)
        if gap < -IDENTITY_TOL:
            violations += 1
    if min_gap == math.inf:
        min_gap = 0.0
    return BernoulliKelly(
        win_prob=float(win_prob),
        odds=float(odds),
        fraction=float(f_star),
        fraction_closed_form=float(closed),
        kkt_residual=float(kkt_residual),
        concavity_second_derivative=float(g_double_prime(_clamp_domain(f_star, 0.0, 1.0 - 1e-6))),
        growth_at_optimum=float(g_star),
        dominance_min_gap=float(min_gap),
        dominance_violations=violations,
    )


@dataclass(frozen=True)
class PortfolioKelly:
    """Numerical log-optimal fraction for a risky-vs-risk-free allocation."""

    fraction: float
    fraction_upper_bound: float
    kkt_residual: float
    concavity_second_derivative: float
    growth_at_optimum: float
    dominance_min_gap: float
    dominance_violations: int
    prob_up: float
    risk_free: float
    up: float
    down: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "case": "risky_vs_risk_free_portfolio",
            "risk_free_gross_return": self.risk_free,
            "risky_up": self.up,
            "risky_down": self.down,
            "prob_up": self.prob_up,
            "kelly_fraction": self.fraction,
            "fraction_upper_bound_bankruptcy": self.fraction_upper_bound,
            "growth_per_period": self.growth_at_optimum,
            "first_order_residual_g_prime": self.kkt_residual,
            "second_derivative_g_double_prime": self.concavity_second_derivative,
            "dominance_min_growth_gap": self.dominance_min_gap,
            "dominance_violations": self.dominance_violations,
        }


def kelly_portfolio(rng: SplitMix64, *, risk_free: float, up: float, down: float,
                    prob_up: float, competitors: int = 20000) -> PortfolioKelly:
    """Log-optimal risky weight for a two-state allocation.

    Wealth multiplier in state ``s`` is ``A_s(f) = (1 - f) Rf + f R_s`` and growth
    is ``g(f) = prob_up log A_up + (1 - prob_up) log A_down``, strictly concave on
    the no-bankruptcy interval ``[0, fmax)`` with ``fmax = Rf / (Rf - R_down)``.
    The optimum solves ``g'(f) = 0``; ``g'`` is continuous and strictly decreasing
    (``g'' < 0``), so a bisection on it is exact to machine precision.
    """
    if not 0.0 < prob_up < 1.0:
        raise NumericalEconomyError("portfolio_prob_up_out_of_range")
    if risk_free <= 0.0 or up <= 0.0 or down <= 0.0:
        raise NumericalEconomyError("portfolio_returns_must_be_positive")
    if not down < up:
        raise NumericalEconomyError("portfolio_up_must_exceed_down")

    def a_up(f: float) -> float:
        return (1.0 - f) * risk_free + f * up

    def a_down(f: float) -> float:
        return (1.0 - f) * risk_free + f * down

    def g(f: float) -> float:
        return prob_up * math.log(a_up(f)) + (1.0 - prob_up) * math.log(a_down(f))

    def g_prime(f: float) -> float:
        return (prob_up * (up - risk_free) / a_up(f)
                + (1.0 - prob_up) * (down - risk_free) / a_down(f))

    def g_double_prime(f: float) -> float:
        return (-prob_up * (up - risk_free) ** 2 / a_up(f) ** 2
                - (1.0 - prob_up) * (down - risk_free) ** 2 / a_down(f) ** 2)

    fmax = risk_free / (risk_free - down) if risk_free > down else 1.0
    hi = fmax - 1e-9
    if g_prime(0.0) <= 0.0:
        f_star = 0.0
        kkt = abs(min(g_prime(0.0), 0.0))
    elif g_prime(hi) >= 0.0:
        f_star = hi
        kkt = 0.0
    else:
        lo_b, hi_b = 0.0, hi
        for _ in range(200):
            mid = 0.5 * (lo_b + hi_b)
            if g_prime(mid) > 0.0:
                lo_b = mid
            else:
                hi_b = mid
        f_star = 0.5 * (lo_b + hi_b)
        kkt = abs(g_prime(f_star))

    g_star = g(f_star)
    min_gap = math.inf
    violations = 0
    for _ in range(competitors):
        f = rng.uniform(0.0, hi)
        gap = g_star - g(f)
        min_gap = min(min_gap, gap)
        if gap < -IDENTITY_TOL:
            violations += 1
    if min_gap == math.inf:
        min_gap = 0.0
    return PortfolioKelly(
        fraction=float(f_star),
        fraction_upper_bound=float(fmax),
        kkt_residual=float(kkt),
        concavity_second_derivative=float(g_double_prime(_clamp_domain(f_star, 0.0, hi))),
        growth_at_optimum=float(g_star),
        dominance_min_gap=float(min_gap),
        dominance_violations=violations,
        prob_up=float(prob_up),
        risk_free=float(risk_free),
        up=float(up),
        down=float(down),
    )


@dataclass(frozen=True)
class FractionalKellyHint:
    """Growth / variance trade-off along the fractional-Kelly ray."""

    points: tuple[dict[str, float], ...]
    recommended_fraction: float
    recommended_lambda: float
    growth_sacrifice_at_half: float
    variance_reduction_factor_at_half: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "fractional_ray": list(self.points),
            "recommended_fraction": self.recommended_fraction,
            "recommended_lambda": self.recommended_lambda,
            "growth_sacrifice_at_half_kelly": self.growth_sacrifice_at_half,
            "variance_reduction_factor_at_half_kelly": self.variance_reduction_factor_at_half,
        }


def fractional_kelly_tradeoff(*, win_prob: float, odds: float,
                              fractions: Sequence[float] = (0.25, 0.5, 0.75, 1.0),
                              ) -> FractionalKellyHint:
    """Report growth and log-return variance along ``f = lambda f*``.

    Variance of the one-period log return ``Var[log A]`` is the standard
    drawdown/risk proxy on a binary game. The hint recommends the most cautious
    declared fraction (smallest ``lambda``) that keeps at least 80% of the optimal
    growth: the empirical half-Kelly rule's justification, measured rather than
    quoted.
    """
    base = kelly_bernoulli(SplitMix64(1), win_prob=win_prob, odds=odds, competitors=0)
    f_full = base.fraction

    def stats(f: float) -> tuple[float, float]:
        lu = math.log(1.0 + odds * f)
        ld = math.log(1.0 - f)
        mean = win_prob * lu + (1.0 - win_prob) * ld
        var = win_prob * lu * lu + (1.0 - win_prob) * ld * ld - mean * mean
        return mean, var

    g_full, v_full = stats(f_full)
    points: list[dict[str, float]] = []
    recommended_lambda = fractions[0]
    recommended_fraction = f_full * fractions[0]
    for lam in fractions:
        f = f_full * lam
        mean, var = stats(f)
        points.append({
            "lambda": float(lam),
            "fraction": float(f),
            "growth_per_period": float(mean),
            "log_return_variance": float(var),
            "growth_fraction_of_optimum": float(mean / g_full) if g_full > 0.0 else math.inf,
            "variance_fraction_of_optimum": float(var / v_full) if v_full > 0.0 else math.inf,
        })
        if g_full > 0.0 and mean / g_full >= 0.8:
            recommended_lambda = lam
            recommended_fraction = f
            break
    g_half, v_half = stats(f_full * 0.5)
    return FractionalKellyHint(
        points=tuple(points),
        recommended_fraction=float(recommended_fraction),
        recommended_lambda=float(recommended_lambda),
        growth_sacrifice_at_half=float(g_full - g_half),
        variance_reduction_factor_at_half=float(v_full / v_half) if v_half > 0.0 else math.inf,
    )


def _numpy_parity(exchange: CobbDouglasExchange, prices: Sequence[float]
                  ) -> dict[str, Any]:
    """Cross-check demand aggregation with numpy IF importable.

    numpy is never a second implementation of the equilibrium — only a check that
    the aggregate demand equals ``alpha @ diag(1/p) @ (omega^T p)`` in matrix
    form. When numpy is absent the leg reports a typed absence; not a pass.
    """
    try:
        import numpy as np  # type: ignore[import-not-found]
    except Exception as exc:  # noqa: BLE001 - absence is a reported state
        return {"state": "absent", "reason": f"{type(exc).__name__}",
                "max_err": None, "counted_as_pass": False}
    alpha = np.array(exchange.alpha, dtype=float)
    omega = np.array(exchange.omega, dtype=float)
    p = np.array([float(x) for x in prices], dtype=float)
    income_vec = omega @ p
    demand = alpha * income_vec[:, None] / p[None, :]
    agg = demand.sum(axis=0)
    # Convert to a plain float list at this boundary: the public numerical API is
    # typed ``Sequence[float]`` and numpy's NDArray is not a Sequence, so an
    # ndarray here would be a type error in a numpy-stubbed environment. The
    # arithmetic is identical either way; numpy stays a cross-check, never a
    # dependency of the helpers.
    reference = excess_demand(exchange, [float(x) for x in p])
    omega_agg = np.array(exchange.aggregate_endowment(), dtype=float)
    err = float(np.max(np.abs((agg - omega_agg) - np.array(reference))))
    return {"state": "measured", "numpy_version": str(np.__version__),
            "max_err": err, "counted_as_pass": True, "passed": bool(err < IDENTITY_TOL)}


# ---------------------------------------------------------------------------
# Formal grounding: the Lean census, read live and reported without upgrading
# ---------------------------------------------------------------------------


def load_formal_grounding(*, skip_census: bool) -> dict[str, Any]:
    """Read ``scripts/audit_axioms.py``'s static census and report it verbatim.

    The static gate is a comment-stripped text scan of ``Economy/*.lean`` — it
    runs on this host, so the sorry / native_decide / axiom / placeholder counts
    ARE measured here. The kernel ``#print axioms`` half needs ``lake env lean``,
    which is Studio-only (``~/docs/INDEX.md`` §Host-of-record): a Python lane
    cannot certify kernel-cleanliness and will not pretend to, so that half is a
    typed ``UNMEASURED_ON_THIS_HOST`` attested by CI's axiom gate.
    """
    grounding: dict[str, Any] = {
        "source": "scripts/audit_axioms.py",
        "read_live": False,
        "counts": None,
        "static_clean": None,
        "static_violations": [],
        "absence": None,
        "kernel_axioms": {
            "value": "ATTESTED_BY_CI",
            "attested_by": ("scripts/audit_axioms.py --verify-kernel -> `lake env "
                            "lean` `#print axioms` in .github/workflows/ci.yml "
                            "(soundness job) and the README invariant claim"),
            "measured_here": False,
            "local_measurement": "UNMEASURED_ON_THIS_HOST",
            "reason": ("lake build / lake env lean is Studio-only for this "
                       "repository (~/docs/INDEX.md §Host-of-record); a Python "
                       "lane cannot certify axiom profiles and will not pretend"),
        },
        "permitted_kernel_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "tier_note": (
            "These are declaration and token counts over Economy/*.lean measured "
            "by a text scan; the CI kernel pass is what makes them proofs. "
            "Nothing in this receipt inherits a THEOREM tier from them."
        ),
    }
    if skip_census:
        grounding["absence"] = "census_read_skipped_by_caller"
        return grounding
    try:
        if str(SCRIPTS_DIR) not in sys.path:
            sys.path.insert(0, str(SCRIPTS_DIR))
        module = importlib.import_module("audit_axioms")
    except Exception as exc:  # noqa: BLE001 - any import failure is a typed absence
        grounding["absence"] = f"census_import_failed:{type(exc).__name__}:{exc}"
        return grounding
    try:
        census = module.census(str(REPO_ROOT))
        violations = module.static_violations(str(REPO_ROOT), census)
        allowed = list(module.ALLOWED_AXIOMS)
    except Exception as exc:  # noqa: BLE001 - a failed scan is a typed absence
        grounding["absence"] = f"census_build_failed:{type(exc).__name__}:{exc}"
        return grounding
    grounding.update({
        "read_live": True,
        "counts": dict(census["counts"]),
        "static_clean": len(violations) == 0,
        "static_violations": list(violations),
        "permitted_kernel_axioms": allowed,
        "audit_module_sha256": _sha256_file(SCRIPTS_DIR / "audit_axioms.py"),
    })
    return grounding


# ---------------------------------------------------------------------------
# Digest + provenance helpers
# ---------------------------------------------------------------------------


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(65536), b""):
            digest.update(block)
    return digest.hexdigest()


def _quantize(obj: Any) -> Any:
    if isinstance(obj, bool) or obj is None or isinstance(obj, (int, str)):
        return obj
    if isinstance(obj, float):
        if obj == 0.0 or not math.isfinite(obj):
            return obj
        return float(f"{obj:.{DIGEST_SIG}g}")
    if isinstance(obj, dict):
        return {k: _quantize(v) for k, v in cast(dict[str, Any], obj).items()}
    if isinstance(obj, (list, tuple)):
        return [_quantize(v) for v in obj]
    return str(obj)


def _canonical_json(payload: Any) -> str:
    return json.dumps(_quantize(payload), sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True, allow_nan=True)


def _strip_for_digest(payload: Any) -> Any:
    if isinstance(payload, dict):
        return {k: _strip_for_digest(v)
                for k, v in cast(dict[str, Any], payload).items()
                if k not in VOLATILE_KEYS}
    if isinstance(payload, list):
        return [_strip_for_digest(v) for v in payload]
    return payload


def _digest(payload: Any) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _git_rev_parse(*args: str) -> str:
    if not args:
        raise ValueError("_git_rev_parse_requires_a_revision")
    try:
        proc = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "rev-parse", *args],
            capture_output=True, text=True, timeout=10, check=False,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return f"UNAVAILABLE:{type(exc).__name__}"
    if proc.returncode != 0:
        return f"UNAVAILABLE:rc_{proc.returncode}"
    return proc.stdout.strip() or "UNAVAILABLE:empty"


def _hostname() -> str:
    try:
        return str(os.uname().nodename)
    except OSError:  # pragma: no cover - POSIX always has uname
        return "unknown"


def _utc_stamp() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


# ---------------------------------------------------------------------------
# Epistemic validation: fail closed on tier inflation
# ---------------------------------------------------------------------------


_REQUIRED_PROBABLY: dict[str, Any] = {
    "schema": PROBABLY_SCHEMA,
    "layer": PROBABLY_LAYER,
    "epistemic_tier": EPISTEMIC_TIER,
    "deductive_proof": False,
}


def validate_economy_receipt_epistemics(receipt: dict[str, Any]) -> dict[str, Any]:
    """Fail closed on tier inflation; return the receipt when it is honest.

    Raises ``ValueError`` when the receipt mislabels itself or when any numerical
    leg tries to present itself as a deduction (``deductive_proof`` true, or a
    ``THEOREM`` tier without a cited machine-checked source). Missing fields are a
    refusal too: an absent disclaimer is not a compliant one. There is no
    ``provably`` block in this receipt — every quantity is a numerical observation
    and the formal Lean surface is cited, not worn.
    """
    if not isinstance(receipt, dict):
        raise ValueError(f"receipt must be a dict, got {type(receipt).__name__}")
    if receipt.get("receipt_schema") != RECEIPT_SCHEMA:
        raise ValueError(
            f"receipt_schema must be {RECEIPT_SCHEMA!r}, got "
            f"{receipt.get('receipt_schema')!r}")
    if receipt.get("schema") != RECEIPT_SCHEMA:
        raise ValueError(
            f"the canonical 'schema' alias must equal {RECEIPT_SCHEMA!r}, got "
            f"{receipt.get('schema')!r}")
    if receipt.get("domain") != DOMAIN:
        raise ValueError(f"domain must be {DOMAIN!r}, got {receipt.get('domain')!r}")

    probably = receipt.get("probably")
    if not isinstance(probably, dict):
        raise ValueError("numerical block 'probably' is missing or not a dict")
    for field, want in _REQUIRED_PROBABLY.items():
        got = probably.get(field)
        if got != want:
            raise ValueError(
                f"probably.{field} must be {want!r} for a numerical observation, "
                f"got {got!r}")

    if "provably" in receipt:
        raise ValueError(
            "this receipt must not carry a 'provably' block: every quantity here "
            "is a numerical observation and the formal Lean surface is cited under "
            "formal_grounding, not claimed as a deduction")

    _reject_inflated_numerical_legs(receipt)
    return receipt


def _reject_inflated_numerical_legs(node: Any, path: str = "receipt") -> None:
    """Walk the tree: no numerical leg may wear a deduction's clothes.

    Everything here is a numerical observation. The numerical scope is INHERITED
    BY CHILDREN, so a leg cannot dodge the refusal by omitting a tier field. A
    ``THEOREM``-shaped claim without a machine-checked ``cited_from`` source, or
    any ``deductive_proof`` that is not ``False`` where declared, is a tier
    inflation and raises.
    """
    if isinstance(node, dict):
        tier = node.get("epistemic_tier")
        if tier not in (None, EPISTEMIC_TIER):
            raise ValueError(
                f"{path}.epistemic_tier {tier!r} is not the only tier this "
                f"receipt issues ({EPISTEMIC_TIER!r})")
        proof = node.get("deductive_proof")
        if proof is not None and proof is not False:
            raise ValueError(
                f"{path} is a numerical leg with deductive_proof={proof!r}: a "
                f"finite-precision equilibrium / scoring / Kelly computation is "
                f"not a deduction and must not claim one")
        for key, val in node.items():
            if key == "probably":
                continue  # checked above; its literal fields are not legs
            _reject_inflated_numerical_legs(val, f"{path}.{key}")
    elif isinstance(node, list):
        for i, val in enumerate(node):
            _reject_inflated_numerical_legs(val, f"{path}[{i}]")


# ---------------------------------------------------------------------------
# Receipt assembly
# ---------------------------------------------------------------------------


def build_economy_worldsense_receipt(*, skip_census: bool = False,
                                     seed: int = 20261126,
                                     price_samples: int = 20000,
                                     scoring_pairs: int = 4000,
                                     scoring_support: int = 6,
                                     kelly_competitors: int = 20000,
                                     ) -> dict[str, Any]:
    """Build the deterministic equilibrium / scoring / Kelly receipt.

    ``wall_ms`` and ``generated_utc`` are the only volatile fields; both are
    excluded from ``content_sha256`` so two runs of the same commit and options
    agree byte-for-byte. ``canonical_input_sha256`` is over the mathematical spec
    alone (model + scoring config + kelly config + options) so it is a pure replay
    key independent of host and repo state.
    """
    started = time.perf_counter()
    rng = SplitMix64(seed)

    exchange = CobbDouglasExchange(
        alpha=tuple(tuple(r) for r in CANONICAL_EXCHANGE["alpha"]),
        omega=tuple(tuple(r) for r in CANONICAL_EXCHANGE["omega"]),
        goods=tuple(CANONICAL_EXCHANGE["goods"]),
        consumers=tuple(CANONICAL_EXCHANGE["consumers"]),
    )
    equilibrium = solve_equilibrium(exchange, rng, price_samples=price_samples)

    scoring = verify_scoring_rules(rng, n_pairs=scoring_pairs, support=scoring_support)
    forecast = parse_forecast_exposures()

    bernoulli = kelly_bernoulli(rng, win_prob=CANONICAL_BERNOULLI["win_prob"],
                                odds=CANONICAL_BERNOULLI["odds"],
                                competitors=kelly_competitors)
    portfolio = kelly_portfolio(rng, risk_free=CANONICAL_PORTFOLIO["risk_free"],
                                up=CANONICAL_PORTFOLIO["up"],
                                down=CANONICAL_PORTFOLIO["down"],
                                prob_up=CANONICAL_PORTFOLIO["prob_up"],
                                competitors=kelly_competitors)
    hint = fractional_kelly_tradeoff(win_prob=CANONICAL_BERNOULLI["win_prob"],
                                     odds=CANONICAL_BERNOULLI["odds"])
    numpy_leg = _numpy_parity(exchange, equilibrium.prices)
    grounding = load_formal_grounding(skip_census=skip_census)

    counts = grounding.get("counts") or {}
    census_clean = grounding.get("static_clean")

    invariants = {
        "walras_law_abs_residual_lt_tol": bool(equilibrium.walras_random_abs_max < IDENTITY_TOL),
        "walras_law_scale_invariant": bool(equilibrium.walras_scale_relative_residual < IDENTITY_TOL),
        "equilibrium_excess_demand_converged": bool(
            equilibrium.max_abs_excess_demand < TATONNEMENT_TOL and equilibrium.tatonnement_converged),
        "equilibrium_two_solver_paths_agree": bool(equilibrium.path_agreement < TATONNEMENT_TOL),
        "first_welfare_budget_exhaustion": bool(equilibrium.budget_exhaustion_max < IDENTITY_TOL),
        "first_welfare_mrs_price_ratio": bool(equilibrium.mrs_price_ratio_max < IDENTITY_TOL),
        "brier_identity_norm_form": bool(scoring.brier_max_residual_l2 < IDENTITY_TOL),
        "brier_identity_onehot_expansion": bool(scoring.brier_max_residual_onehot_expansion < IDENTITY_TOL),
        "brier_strict_propriety": bool(scoring.brier_propriety_all_nonneg),
        "log_identity_kl": bool(scoring.log_max_residual_kl < IDENTITY_TOL),
        "log_identity_entropy_decomposition": bool(scoring.log_max_residual_entropy < IDENTITY_TOL),
        "log_strict_propriety_gibbs": bool(scoring.log_propriety_all_nonneg and scoring.log_gibbs_max_negative >= -IDENTITY_TOL),
        "kelly_bernoulli_first_order": bool(bernoulli.kkt_residual < IDENTITY_TOL and bernoulli.concavity_second_derivative < 0.0),
        "kelly_bernoulli_dominance": bool(bernoulli.dominance_min_gap >= -IDENTITY_TOL and bernoulli.dominance_violations == 0),
        "kelly_portfolio_first_order": bool(portfolio.kkt_residual < 1e-7 and portfolio.concavity_second_derivative < 0.0),
        "kelly_portfolio_dominance": bool(portfolio.dominance_min_gap >= -IDENTITY_TOL and portfolio.dominance_violations == 0),
    }
    if grounding.get("read_live"):
        invariants["formal_census_static_clean"] = bool(census_clean)

    # --- the reactor hint: a measured fractional-Kelly allocation -------------
    growth_opt = bernoulli.growth_at_optimum
    reactor_hint = {
        "target": "godel_reactor_prior capital/token budget fraction",
        "analog": ("the log-optimal stake is the growth-maximising budget "
                   "allocation; fractional Kelly trades growth for variance and "
                   "is the measured, not the quoted, default"),
        "kelly_fraction_full": bernoulli.fraction,
        "recommended_fraction": hint.recommended_fraction,
        "recommended_lambda": hint.recommended_lambda,
        "growth_optimal_per_period": growth_opt,
        "growth_sacrifice_at_recommended": hint.points[-1]["growth_per_period"] if hint.points else 0.0,
        "variance_reduction_factor_at_half_kelly": hint.variance_reduction_factor_at_half,
        "hint_tier": EPISTEMIC_TIER,
        "fractional_ray": list(hint.points),
    }

    spec = {
        "module": "economy_worldsense_receipt",
        "version": 1,
        "exchange": exchange.as_dict(),
        "scoring": {"n_pairs": scoring_pairs, "support": scoring_support},
        "bernoulli": CANONICAL_BERNOULLI,
        "portfolio": CANONICAL_PORTFOLIO,
        "options": {
            "seed": seed,
            "price_samples": price_samples,
            "scoring_pairs": scoring_pairs,
            "scoring_support": scoring_support,
            "kelly_competitors": kelly_competitors,
            "skip_census": skip_census,
        },
    }

    receipt: dict[str, Any] = {
        "receipt_schema": RECEIPT_SCHEMA,
        "schema": RECEIPT_SCHEMA,
        "kind": "economy_proper_scoring_worldsense_receipt",
        "domain": DOMAIN,
        "lane": LANE,
        "orch": ORCH,
        "title": ("Arrow-Debreu Cobb-Douglas exchange equilibrium, Brier and "
                  "Logarithmic proper-scoring identities, and Kelly log-optimal "
                  "growth — measured numerically for WorldSense"),
        "claim_tier": EPISTEMIC_TIER,
        "probably": {
            "schema": PROBABLY_SCHEMA,
            "layer": PROBABLY_LAYER,
            "epistemic_tier": EPISTEMIC_TIER,
            "deductive_proof": False,
            "truth_status": TRUTH_STATUS,
            "what_this_is": ("reproducible computation over declared economies, "
                             "forecasts and payoffs; no number below is a theorem "
                             "and no Lean name attached to it makes it one"),
            "what_would_refute_it": ("a residual above the stated tolerance, a "
                                      "solver path disagreement, a scoring gap "
                                      "that goes negative, or a Kelly dominance "
                                      "violation"),
        },
        "formal_grounding": grounding,
        "arrow_debreu": {
            "model": exchange.as_dict(),
            "results": equilibrium.as_dict(),
        },
        "proper_scoring": {
            "verification": scoring.as_dict(),
            "tracked_forecasts": forecast,
        },
        "kelly": {
            "bernoulli": bernoulli.as_dict(),
            "portfolio": portfolio.as_dict(),
            "fractional_ray": list(hint.points),
        },
        "invariants_verified": {k: bool(v) for k, v in invariants.items()},
        "all_invariants_verified": all(bool(v) for v in invariants.values()),
        "invariant_measurements": {
            "walras_law": {
                "abs_p_dot_z_max_random_prices": equilibrium.walras_random_abs_max,
                "rel_p_dot_z_max_random_prices": equilibrium.walras_random_rel_max,
                "threshold": IDENTITY_TOL,
            },
            "equilibrium": {
                "max_abs_excess_demand": equilibrium.max_abs_excess_demand,
                "threshold": TATONNEMENT_TOL,
                "fixed_point_iterations": equilibrium.fixed_point_iterations,
                "tatonnement_iterations": equilibrium.tatonnement_iterations,
                "max_price_path_agreement": equilibrium.path_agreement,
            },
            "first_welfare_theorem": {
                "budget_exhaustion_max": equilibrium.budget_exhaustion_max,
                "mrs_price_ratio_max": equilibrium.mrs_price_ratio_max,
                "threshold": IDENTITY_TOL,
            },
            "brier_identity": {
                "max_residual_vs_l2": scoring.brier_max_residual_l2,
                "max_residual_vs_onehot_expansion": scoring.brier_max_residual_onehot_expansion,
                "threshold": IDENTITY_TOL,
            },
            "logarithmic_identity": {
                "max_residual_vs_kl": scoring.log_max_residual_kl,
                "max_residual_vs_entropy": scoring.log_max_residual_entropy,
                "threshold": IDENTITY_TOL,
            },
            "kelly_bernoulli": {
                "first_order_residual": bernoulli.kkt_residual,
                "second_derivative": bernoulli.concavity_second_derivative,
                "dominance_min_gap": bernoulli.dominance_min_gap,
                "threshold": IDENTITY_TOL,
            },
            "kelly_portfolio": {
                "first_order_residual": portfolio.kkt_residual,
                "second_derivative": portfolio.concavity_second_derivative,
                "dominance_min_gap": portfolio.dominance_min_gap,
                "threshold": 1e-7,
            },
        },
        "reactor_optimization_hint": reactor_hint,
        "z8_meter": {
            "canonical_input_sha256": _digest(spec),
            "canonical_input_scope": ("exchange model + scoring config + kelly "
                                      "config + options (host-independent replay "
                                      "key)"),
            "content_sha256": "",  # filled below, over the digested content
            "wall_ms": round((time.perf_counter() - started) * 1000.0, 3),
            "digest_recipe": ("sha256 of canonical JSON (sorted keys, floats at "
                              f"{DIGEST_SIG} significant digits, volatile and "
                              "provenance keys excluded)"),
            "volatile_keys_excluded": sorted(VOLATILE_KEYS),
            "formal_census_static_clean": census_clean,
            "lean_theorem_count_measured": counts.get("theorem_count"),
            "lean_sorry_count_measured": counts.get("sorry_in_code"),
        },
        "provenance": {
            "producer_path": str(MODULE_PATH.relative_to(REPO_ROOT)),
            "producer_sha256": _sha256_file(MODULE_PATH),
            "repo_head": _git_rev_parse("HEAD"),
            "repo_branch": _git_rev_parse("--abbrev-ref", "HEAD"),
            "python": sys.version.split()[0],
            "platform": sys.platform,
            "host": _hostname(),
            "network_calls": "none",
            "lake_build": "none (Studio-only; only the text-scan census is run here)",
            "numpy": numpy_leg,
        },
        "limits": [
            "Walras's Law and the budget-exhaustion / MRS-equalisation checks are "
            "algebraic identities of Cobb-Douglas demand; the equilibrium "
            "existence itself is an economic assumption of the Arrow-Debreu "
            "theorem, not re-proved here.",
            "the tatonnement is a discrete, normalised, damped approximation of "
            "the continuous Walrasian process; convergence is verified for this "
            "gross-substitutes (Cobb-Douglas) economy, not claimed for arbitrary "
            "preferences.",
            "the Brier and Logarithmic identities are exact mathematics, verified "
            "to machine precision on seeded strictly-positive panels; forecast "
            "accuracy is NOT claimed because forecasts/forecast_table.md tracks no "
            "realized outcomes (only model-internal exposures).",
            "the Kelly fractions assume the stated win probabilities / returns are "
            "the TRUE distributional parameters; a fractional-Kelly discount is "
            "reported precisely because parameter uncertainty makes the full "
            "fraction aggressive in practice — this is a measured trade-off, not a "
            "theorem about optimal capital.",
            "sorry-freeness and axiom cleanliness of the formal surface are "
            "attested by CI's kernel gate, measured here only as the text-scan "
            "static census; see formal_grounding.kernel_axioms.",
            "one canonical economy, one canonical game: no claim about any actual "
            "market, portfolio, agent or allocator.",
        ],
        "consumer_integration": {
            "read_by_worldsense_scientific_flow": [
                "probably.schema / probably.epistemic_tier (reactor leg shape)",
                "z8_meter.canonical_input_sha256 (replay key)",
                "reactor_optimization_hint (godel_reactor_prior fraction input)",
            ],
            "classification": ("kagami.core.omni.worldsense_scientific_flow."
                                "_receipt_schema_text reads schema/kind/type/"
                                "operation/receipt_type/event; this receipt names "
                                f"domain={DOMAIN!r}"),
            "boundary_gate": ("no field this flow treats as a tier claim asserts a "
                              "proof-grade word; nothing here demands a kernel "
                              "notary"),
            "validator": "validate_economy_receipt_epistemics",
            "fail_closed_on": [
                "deductive_proof != False on a numerical leg",
                "epistemic_tier other than NUMERICAL_OBSERVATION",
                "a provably block (this receipt cites Lean, never wears THEOREM)",
                "missing probably block or wrong schema",
            ],
        },
        "generated_utc": _utc_stamp(),
    }
    receipt["z8_meter"]["content_sha256"] = _digest(_digestible_content(receipt))
    return receipt


def _digestible_content(receipt: dict[str, Any]) -> dict[str, Any]:
    """Strip volatile + meter + provenance before hashing the deterministic part."""
    body = {k: v for k, v in receipt.items() if k not in NON_DIGESTED_TOP_KEYS}
    return _strip_for_digest(body)


# ---------------------------------------------------------------------------
# Human summary + CLI
# ---------------------------------------------------------------------------


def render_summary(receipt: Mapping[str, Any]) -> str:
    """A short human-readable digest of the receipt (never the authority)."""
    meter = cast(Mapping[str, Any], receipt["z8_meter"])
    grounding = cast(Mapping[str, Any], receipt["formal_grounding"])
    equilibrium = cast(Mapping[str, Any], receipt["arrow_debreu"]["results"])
    scoring = cast(Mapping[str, Any], receipt["proper_scoring"]["verification"])
    kelly = cast(Mapping[str, Any], receipt["kelly"])
    hint = cast(Mapping[str, Any], receipt["reactor_optimization_hint"])
    invariants = cast(Mapping[str, Any], receipt["invariants_verified"])

    lines = [
        f"economy WorldSense receipt  [{receipt['domain']}]  "
        f"tier={receipt['claim_tier']}  deductive_proof=False",
    ]
    counts = grounding.get("counts")
    if isinstance(counts, Mapping):
        lines.append(
            f"formal: {counts['theorem_count']} theorems, {counts['lemma_count']} "
            f"lemmas, sorry={counts['sorry_in_code']}, "
            f"native_decide={counts['native_decide_in_code']}, "
            f"user_axioms={counts['user_axioms']} [static text scan; kernel axioms "
            f"attested by CI, not measured here]")
    else:
        lines.append(f"formal: census unread ({grounding.get('absence')})")
    lines.append(
        f"equilibrium: p*={['%.5f' % x for x in equilibrium['prices_simplex']]} "
        f"||z(p*)||_inf={equilibrium['max_abs_excess_demand']:.2e} "
        f"(two paths agree to {equilibrium['solver_paths']['max_price_path_agreement']:.2e})")
    lines.append(
        f"walras: |p.z|max={equilibrium['walras_law']['max_abs_p_dot_z_random_prices']:.2e} "
        f"| brier err={scoring['brier']['max_residual_vs_l2_squared']:.2e} "
        f"| log err={scoring['logarithmic']['max_residual_vs_kl']:.2e}")
    lines.append(
        f"kelly: bernoulli f*={kelly['bernoulli']['kelly_fraction']:.5f} "
        f"g'={kelly['bernoulli']['first_order_residual_g_prime']:.2e} "
        f"| portfolio f*={kelly['portfolio']['kelly_fraction']:.5f} "
        f"| recommended lambda={hint['recommended_lambda']:.2f} "
        f"f={hint['recommended_fraction']:.5f}")
    failed = [k for k, ok in invariants.items() if ok is not True]
    lines.append(f"invariants: {len(invariants) - len(failed)}/{len(invariants)} "
                 f"verified" + (f"; FAILED {failed}" if failed else ""))
    lines.append(f"content_sha256={meter['content_sha256']} wall_ms={meter['wall_ms']}")
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Deterministic Arrow-Debreu / proper-scoring / Kelly-growth "
                    "WorldSense scientific receipt for the economy corpus.",
    )
    parser.add_argument("--json", action="store_true",
                        help="print the receipt as JSON on stdout")
    parser.add_argument("--out", metavar="PATH", default=None,
                        help="write the receipt JSON to PATH")
    parser.add_argument("--pretty", action="store_true",
                        help="indent the JSON (only with --json/--out)")
    parser.add_argument("--skip-census", action="store_true",
                        help="do not read scripts/audit_axioms.py static census")
    parser.add_argument("--seed", type=int, default=20261126,
                        help="seed of the deterministic generator")
    parser.add_argument("--price-samples", type=int, default=20000,
                        help="random prices for the Walras's Law sweep")
    parser.add_argument("--scoring-pairs", type=int, default=4000,
                        help="random (truth, report) pairs for the scoring identities")
    parser.add_argument("--kelly-competitors", type=int, default=20000,
                        help="stake competitors for the Kelly dominance check")
    parser.add_argument("--check-file", metavar="PATH", default=None,
                        help="validate an existing receipt file's epistemics")
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.check_file:
        try:
            doc = json.loads(Path(args.check_file).read_text(encoding="utf-8"))
            validate_economy_receipt_epistemics(doc)
        except Exception as exc:  # noqa: BLE001 - a CLI reports, not tracebacks
            print(f"economy_worldsense_receipt: check-file refused: "
                  f"{type(exc).__name__}: {exc}", file=sys.stderr)
            return 1
        want = doc.get("z8_meter", {}).get("content_sha256")
        if want:
            recomputed = _digest(_digestible_content(doc))
            if recomputed != want:
                print(f"economy_worldsense_receipt: content digest mismatch "
                      f"(recorded {want}, recomputed {recomputed})", file=sys.stderr)
                return 1
        print(f"economy_worldsense_receipt: {args.check_file} epistemics OK "
              f"(content_sha256={want})")
        return 0

    try:
        receipt = build_economy_worldsense_receipt(
            skip_census=args.skip_census, seed=args.seed,
            price_samples=args.price_samples, scoring_pairs=args.scoring_pairs,
            kelly_competitors=args.kelly_competitors,
        )
    except NumericalEconomyError as exc:
        print(f"economy_worldsense_receipt: refused: {exc}", file=sys.stderr)
        return 2
    except Exception as exc:  # noqa: BLE001 - a CLI must report, not traceback
        print(f"economy_worldsense_receipt: error: {type(exc).__name__}: {exc}",
              file=sys.stderr)
        return 2

    failed = [name for name, ok in
              cast(Mapping[str, Any], receipt["invariants_verified"]).items()
              if ok is not True]
    if failed:
        print(f"economy_worldsense_receipt: invariant verification failed: "
              f"{', '.join(failed)}", file=sys.stderr)

    text = json.dumps(receipt, indent=2 if args.pretty else None,
                      sort_keys=args.pretty, allow_nan=False)
    if args.out:
        path = Path(args.out)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text + "\n", encoding="utf-8")
        print(f"wrote {path} ({len(text) + 1} bytes)", file=sys.stderr)
    if args.json:
        print(text)
    elif not args.out:
        print(render_summary(receipt))
    return 1 if failed else 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
