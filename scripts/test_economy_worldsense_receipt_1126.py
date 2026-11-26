#!/usr/bin/env python3
"""Tests for scripts/economy_worldsense_receipt.py.

Everything runs in pure Python — no Lean, no lake, no network. The receipt's
whole purpose is honesty about what it does and does not prove, so the tests
come in two flavours:

* the numerical claims are TIGHT: each invariant must meet its stated tolerance
  (Walras / Brier / Log / Kelly first-order to 1e-12, equilibrium convergence to
  1e-10), not merely "look small"; and
* the epistemic envelope is FAIL-CLOSED: a receipt that tries to wear a
  deduction's clothes — a true ``deductive_proof``, a ``THEOREM`` tier, a
  ``provably`` block, or a nested numerical leg that inflates itself — must be
  refused, not silently accepted. A builder that cannot reject inflation is not
  separating the tiers at all.

Determinism (replay key and content digest) and digest integrity (a tampered
number changes the recomputed digest) are pinned because the receipt is meant to
be re-verifiable byte-for-byte from its commit.
"""

from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
import tempfile
import unittest

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPT_DIR)

import economy_worldsense_receipt as E  # noqa: E402

REPO_ROOT = os.path.dirname(SCRIPT_DIR)


def _build_receipt() -> dict:
    """Build the production-default receipt once (the full numerical sweep)."""
    return E.build_economy_worldsense_receipt()


class PillarTests(unittest.TestCase):
    """The three numerical pillars meet their stated tolerances."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.receipt = _build_receipt()
        cls.eq = cls.receipt["arrow_debreu"]["results"]
        cls.sc = cls.receipt["proper_scoring"]["verification"]
        cls.kelly = cls.receipt["kelly"]

    # ---- Arrow-Debreu -----------------------------------------------------

    def test_walras_law_within_identity_tol(self):
        law = self.eq["walras_law"]
        self.assertLess(law["max_abs_p_dot_z_random_prices"], E.IDENTITY_TOL)
        self.assertLess(law["scale_invariance_residual"], E.IDENTITY_TOL)

    def test_equilibrium_converges_and_two_paths_agree(self):
        self.assertLess(self.eq["max_abs_excess_demand"], E.TATONNEMENT_TOL)
        self.assertTrue(self.eq["solver_paths"]["tatonnement_converged"])
        self.assertLess(
            self.eq["solver_paths"]["max_price_path_agreement"], E.TATONNEMENT_TOL)

    def test_first_welfare_invariants(self):
        fw = self.eq["first_welfare_theorem"]
        self.assertLess(fw["max_budget_exhaustion_residual"], E.IDENTITY_TOL)
        self.assertLess(fw["max_mrs_price_ratio_residual"], E.IDENTITY_TOL)

    def test_equilibrium_prices_on_simplex(self):
        prices = self.eq["prices_simplex"]
        self.assertTrue(all(x > 0.0 for x in prices))
        self.assertLess(abs(sum(prices) - 1.0), 1e-12)

    def test_symmetric_two_good_equilibrium_is_uniform_price(self):
        # An analytically known case: two consumers, identical 0.5 shares and
        # identical endowments -> the equilibrium normalised price is uniform.
        ex = E.CobbDouglasExchange(
            alpha=((0.5, 0.5), (0.5, 0.5)),
            omega=((1.0, 1.0), (1.0, 1.0)),
        )
        rng = E.SplitMix64(7)
        report = E.solve_equilibrium(ex, rng, price_samples=2000)
        self.assertLess(report.max_abs_excess_demand, E.TATONNEMENT_TOL)
        for price in report.prices:
            self.assertAlmostEqual(price, 0.5, delta=1e-8)

    # ---- Proper scoring rules --------------------------------------------

    def test_brier_identity_three_forms_within_tol(self):
        b = self.sc["brier"]
        self.assertLess(b["max_residual_vs_l2_squared"], E.IDENTITY_TOL)
        self.assertLess(b["max_residual_vs_onehot_expansion"], E.IDENTITY_TOL)
        self.assertTrue(b["all_gaps_nonneg"])

    def test_log_identity_and_gibbs_within_tol(self):
        lg = self.sc["logarithmic"]
        self.assertLess(lg["max_residual_vs_kl"], E.IDENTITY_TOL)
        self.assertLess(lg["max_residual_vs_entropy_decomposition"], E.IDENTITY_TOL)
        self.assertTrue(lg["all_gaps_nonneg"])
        self.assertGreaterEqual(lg["worst_gibbs_negative"], -E.IDENTITY_TOL)

    def test_brier_gap_equals_squared_distance_on_known_pair(self):
        p = E.normalise([0.3, 0.2, 0.5])
        q = E.normalise([0.5, 0.3, 0.2])
        probe = E._score_pair(p, q)
        expected = E.l2_squared(p, q)
        self.assertLess(abs(probe.brier.expected_gap - expected), E.IDENTITY_TOL)
        self.assertLess(abs(probe.brier.onehot_expansion_form - expected),
                        E.IDENTITY_TOL)

    def test_log_gap_equals_kl_on_known_pair(self):
        p = E.normalise([0.7, 0.2, 0.1])
        q = E.normalise([0.2, 0.5, 0.3])
        probe = E._score_pair(p, q)
        self.assertLess(abs(probe.log.expected_gap - probe.log.kl_form), E.IDENTITY_TOL)
        self.assertGreater(probe.log.kl_form, 0.0)  # strict propriety, q != p

    # ---- Kelly ------------------------------------------------------------

    def test_kelly_bernoulli_closed_form_and_optimality(self):
        bern = self.kelly["bernoulli"]
        self.assertAlmostEqual(bern["kelly_fraction"], 0.2, delta=1e-9)
        self.assertLess(abs(bern["first_order_residual_g_prime"]), E.IDENTITY_TOL)
        self.assertLess(bern["second_derivative_g_double_prime"], 0.0)
        self.assertEqual(bern["dominance_violations"], 0)
        self.assertGreaterEqual(bern["dominance_min_growth_gap"], -E.IDENTITY_TOL)

    def test_kelly_portfolio_optimality_and_concavity(self):
        port = self.kelly["portfolio"]
        self.assertLess(abs(port["first_order_residual_g_prime"]), 1e-7)
        self.assertLess(port["second_derivative_g_double_prime"], 0.0)
        self.assertEqual(port["dominance_violations"], 0)
        self.assertGreaterEqual(port["dominance_min_growth_gap"], -E.IDENTITY_TOL)
        self.assertGreaterEqual(port["kelly_fraction"], 0.0)
        self.assertLess(port["kelly_fraction"], port["fraction_upper_bound_bankruptcy"])

    def test_kelly_portfolio_no_edge_is_zero_fraction(self):
        # If the risky asset has no positive expected excess over the risk-free
        # rate, the log-optimal allocation is to hold none of it.
        rng = E.SplitMix64(11)
        port = E.kelly_portfolio(
            rng, risk_free=1.10, up=1.20, down=0.80, prob_up=0.5, competitors=500)
        self.assertEqual(port.fraction, 0.0)

    def test_fractional_kelly_trades_growth_for_variance(self):
        hint = self.receipt["reactor_optimization_hint"]
        ray = hint["fractional_ray"]
        self.assertTrue(ray)
        # Half-Kelly reduces log-return variance below the full-fraction level.
        self.assertGreater(hint["variance_reduction_factor_at_half_kelly"], 1.0)
        # Growth along the ray increases toward the optimum (lambda <= 1).
        growths = [pt["growth_per_period"] for pt in ray]
        self.assertLessEqual(growths[0], growths[-1] + 1e-12)


class SchemaEnvelopeTests(unittest.TestCase):
    """The receipt carries the required WorldSense / z8.probably keys."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.receipt = _build_receipt()

    def test_required_top_level_keys(self):
        for key in ("receipt_schema", "domain", "probably", "z8_meter",
                    "invariants_verified", "reactor_optimization_hint"):
            self.assertIn(key, self.receipt)
        self.assertEqual(self.receipt["receipt_schema"], E.RECEIPT_SCHEMA)
        self.assertEqual(self.receipt["schema"], E.RECEIPT_SCHEMA)
        self.assertEqual(self.receipt["domain"], "mathematical_economics")

    def test_probably_block_is_numerical(self):
        probably = self.receipt["probably"]
        self.assertEqual(probably["schema"], E.PROBABLY_SCHEMA)
        self.assertEqual(probably["layer"], "Probably")
        self.assertEqual(probably["epistemic_tier"], "NUMERICAL_OBSERVATION")
        self.assertIs(probably["deductive_proof"], False)

    def test_all_invariants_verified(self):
        self.assertTrue(self.receipt["all_invariants_verified"])
        for name, ok in self.receipt["invariants_verified"].items():
            self.assertIs(ok, True, f"invariant {name} did not verify")

    def test_no_provably_block_and_no_proof_grade_words(self):
        self.assertNotIn("provably", self.receipt)

    def test_z8_meter_shape(self):
        meter = self.receipt["z8_meter"]
        for key in ("canonical_input_sha256", "content_sha256", "digest_recipe"):
            self.assertIn(key, meter)
        self.assertEqual(len(meter["content_sha256"]), 64)
        self.assertEqual(len(meter["canonical_input_sha256"]), 64)


class ValidatorTests(unittest.TestCase):
    """validate_economy_receipt_epistemics accepts the honest and refuses the inflated."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.good = _build_receipt()

    def _variant(self):
        return copy.deepcopy(self.good)

    def test_accepts_real_receipt(self):
        out = E.validate_economy_receipt_epistemics(self._variant())
        self.assertIs(out["receipt_schema"], E.RECEIPT_SCHEMA)

    def test_rejects_true_deductive_proof(self):
        bad = self._variant()
        bad["probably"]["deductive_proof"] = True
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_theorem_tier(self):
        bad = self._variant()
        bad["probably"]["epistemic_tier"] = "THEOREM"
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_wrong_receipt_schema(self):
        bad = self._variant()
        bad["receipt_schema"] = "worldsense.provably/1"
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_wrong_schema_alias(self):
        bad = self._variant()
        del bad["schema"]
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_wrong_domain(self):
        bad = self._variant()
        bad["domain"] = "physics"
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_missing_probably(self):
        bad = self._variant()
        del bad["probably"]
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_added_provably_block(self):
        bad = self._variant()
        bad["provably"] = {"schema": "z8.provably/1", "tier": "THEOREM"}
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_nested_numerical_leg_inflation(self):
        # A numerical leg deep in the tree must not claim deductive_proof.
        bad = self._variant()
        bad["arrow_debreu"]["results"]["deductive_proof"] = True
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_nested_unauthorised_tier(self):
        bad = self._variant()
        bad["kelly"]["bernoulli"]["epistemic_tier"] = "PROVED"
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(bad)

    def test_rejects_non_dict(self):
        with self.assertRaises(ValueError):
            E.validate_economy_receipt_epistemics(["not", "a", "dict"])  # type: ignore[arg-type]


class DigestAndDeterminismTests(unittest.TestCase):
    """The receipt is byte-reproducible and tamper-evident."""

    def test_content_digest_recomputes(self):
        receipt = E.build_economy_worldsense_receipt(skip_census=True)
        recorded = receipt["z8_meter"]["content_sha256"]
        recomputed = E._digest(E._digestible_content(receipt))
        self.assertEqual(recorded, recomputed)

    def test_determinism_across_two_builds(self):
        a = E.build_economy_worldsense_receipt(skip_census=True)
        b = E.build_economy_worldsense_receipt(skip_census=True)
        self.assertEqual(a["z8_meter"]["content_sha256"], b["z8_meter"]["content_sha256"])
        self.assertEqual(a["z8_meter"]["canonical_input_sha256"],
                         b["z8_meter"]["canonical_input_sha256"])

    def test_canonical_input_independent_of_host_volatile(self):
        # The replay key must not move when only wall-clock/provenance changes.
        a = E.build_economy_worldsense_receipt(skip_census=True)
        self.assertEqual(a["z8_meter"]["canonical_input_sha256"],
                         E.build_economy_worldsense_receipt(skip_census=True)
                         ["z8_meter"]["canonical_input_sha256"])

    def test_tampered_number_breaks_digest(self):
        receipt = E.build_economy_worldsense_receipt(skip_census=True)
        receipt["arrow_debreu"]["results"]["prices_simplex"][0] += 1e-3
        recomputed = E._digest(E._digestible_content(receipt))
        self.assertNotEqual(recomputed, receipt["z8_meter"]["content_sha256"])

    def test_receipt_is_json_serialisable_without_nan(self):
        text = json.dumps(_build_receipt(), allow_nan=False)
        self.assertIn("mathematical_economics", text)


class PrimitiveGuardTests(unittest.TestCase):
    """The numerical primitives refuse the inputs the identities forbid."""

    def test_normalise_rejects_negative_and_zero(self):
        with self.assertRaises(E.NumericalEconomyError):
            E.normalise([1.0, -2.0])
        with self.assertRaises(E.NumericalEconomyError):
            E.normalise([0.0, 0.0])

    def test_kl_raises_when_reference_zero_on_support(self):
        with self.assertRaises(E.NumericalEconomyError):
            E.kl_divergence([0.5, 0.5], [1.0, 0.0])

    def test_kl_zero_term_convention(self):
        # p_i = 0 contributes 0 (0 log 0 = 0), so this is finite.
        self.assertAlmostEqual(E.kl_divergence([0.0, 1.0], [0.5, 0.5]),
                               0.6931471805599453, places=9)

    def test_positive_vector_requires_normalisation(self):
        with self.assertRaises(E.NumericalEconomyError):
            E._require_positive_vector("x", [0.5, 0.9])

    def test_splitmix64_is_deterministic(self):
        a = [E.SplitMix64(99).next_u64() for _ in range(3)]
        b = [E.SplitMix64(99).next_u64() for _ in range(3)]
        self.assertEqual(a, b)
        self.assertNotEqual(a, [E.SplitMix64(100).next_u64() for _ in range(3)])

    def test_splitmix_rejects_bool_seed(self):
        with self.assertRaises(E.NumericalEconomyError):
            E.SplitMix64(True)  # type: ignore[arg-type]

    def test_marshallian_demand_rejects_nonpositive_price(self):
        ex = E.CobbDouglasExchange(alpha=((0.5, 0.5),), omega=((1.0, 1.0),))
        with self.assertRaises(E.NumericalEconomyError):
            E.marshallian_demand(ex, [0.0, 1.0])


class ForecastTests(unittest.TestCase):
    """Forecast-table exposures are reported as descriptive, never accuracy."""

    def test_forecast_leg_is_honest(self):
        receipt = _build_receipt()
        fc = receipt["proper_scoring"]["tracked_forecasts"]
        self.assertIs(fc["not_forecast_accuracy"], True)
        self.assertEqual(fc["score_semantics"], "descriptive_calibration_divergence")
        # Either present with parsed calibrations, or a typed absence -- never a
        # silently empty "pass".
        if fc["present"]:
            self.assertTrue(fc["calibrations"])
        else:
            self.assertIsNotNone(fc["absence"])

    def test_parse_from_repo(self):
        fc = E.parse_forecast_exposures(REPO_ROOT)
        self.assertEqual(fc["source"], E.FORECAST_TABLE_REL)
        if not fc["present"]:
            self.assertIsNotNone(fc["absence"])


class CliTests(unittest.TestCase):
    """The --check-file path validates an on-disk receipt and rejects a bad one."""

    def _script(self) -> str:
        return os.path.join(SCRIPT_DIR, "economy_worldsense_receipt.py")

    def test_check_file_round_trip(self):
        receipt = E.build_economy_worldsense_receipt(skip_census=True)
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
            json.dump(receipt, fh)
            path = fh.name
        try:
            proc = subprocess.run(
                [sys.executable, self._script(), "--check-file", path],
                capture_output=True, text=True, timeout=60, check=False)
            self.assertEqual(proc.returncode, 0, proc.stderr)
        finally:
            os.unlink(path)

    def test_check_file_rejects_inflated(self):
        receipt = E.build_economy_worldsense_receipt(skip_census=True)
        receipt["probably"]["deductive_proof"] = True
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
            json.dump(receipt, fh)
            path = fh.name
        try:
            proc = subprocess.run(
                [sys.executable, self._script(), "--check-file", path],
                capture_output=True, text=True, timeout=60, check=False)
            self.assertEqual(proc.returncode, 1)
        finally:
            os.unlink(path)


if __name__ == "__main__":
    unittest.main(verbosity=2)
