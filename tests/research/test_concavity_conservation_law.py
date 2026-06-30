"""Pytest wrapper for the Concavity Conservation Law empirical verification."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest


_TEST_MODULE_PATH = (
    Path(__file__).resolve().parents[2]
    / "docs" / "research" / "concavity_conservation_law_test.py"
)


def _load_module():
    if not _TEST_MODULE_PATH.exists():
        pytest.skip(f"missing {_TEST_MODULE_PATH}")
    spec = importlib.util.spec_from_file_location(
        "concavity_conservation_law_test", _TEST_MODULE_PATH
    )
    if spec is None or spec.loader is None:
        pytest.skip("could not load spec")
    module = importlib.util.module_from_spec(spec)
    sys.modules["concavity_conservation_law_test"] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def mod():
    return _load_module()


def test_cpmm_concavity_param_formula(mod) -> None:
    mod.test_cpmm_concavity_param_formula()


def test_cpmm_conservation_tradeoff(mod) -> None:
    mod.test_cpmm_conservation_tradeoff()


def test_stateful_gain_lipschitz_envelope_empirical(mod) -> None:
    mod.test_stateful_gain_lipschitz_envelope_empirical()


def test_concavity_bound_falsified_small_trades(mod) -> None:
    mod.test_concavity_bound_falsified_small_trades()


def test_concavity_bound_fails_large_trades(mod) -> None:
    mod.test_concavity_bound_fails_large_trades()


def test_actual_gain_decreases_with_depth(mod) -> None:
    mod.test_actual_gain_decreases_with_depth()


def test_min_out_cap_breaks_tradeoff(mod) -> None:
    mod.test_min_out_cap_breaks_tradeoff()


def test_donation_no_output_exact_optimizer(mod) -> None:
    mod.test_donation_no_output_exact_optimizer()


def test_fee_bearing_donation_no_output_exact_optimizer(mod) -> None:
    mod.test_fee_bearing_donation_no_output_exact_optimizer()


def test_donation_optimizer_not_filled_stateful_gain(mod) -> None:
    mod.test_donation_optimizer_not_filled_stateful_gain()


def test_tradeoff_frontier_characterization(mod) -> None:
    mod.test_tradeoff_frontier_characterization()


def test_pool_parameter_m_certificate_accepts_valid_corpus(mod) -> None:
    mod.test_pool_parameter_m_certificate_accepts_valid_corpus()


def test_pool_parameter_m_certificate_rejects_mutations(mod) -> None:
    mod.test_pool_parameter_m_certificate_rejects_mutations()


def test_endpoint_curvature_bound_is_not_exact(mod) -> None:
    mod.test_endpoint_curvature_bound_is_not_exact()


def test_symmetric_exact_curvature_minimizer_at_half(mod) -> None:
    mod.test_symmetric_exact_curvature_minimizer_at_half()


def test_stationary_curvature_m_certificate_accepts_constructive_asymmetric_corpus(mod) -> None:
    mod.test_stationary_curvature_m_certificate_accepts_constructive_asymmetric_corpus()


def test_stationary_curvature_m_certificate_rejects_mutations(mod) -> None:
    mod.test_stationary_curvature_m_certificate_rejects_mutations()


def test_exact_curvature_m_certificate_accepts_valid_corpus(mod) -> None:
    mod.test_exact_curvature_m_certificate_accepts_valid_corpus()


def test_exact_curvature_m_certificate_rejects_mutations(mod) -> None:
    mod.test_exact_curvature_m_certificate_rejects_mutations()


def test_exact_curvature_m_certificate_rejects_float_overflow_domain(mod) -> None:
    mod.test_exact_curvature_m_certificate_rejects_float_overflow_domain()


def test_interval_curvature_m_certificate_refines_endpoint_bound(mod) -> None:
    mod.test_interval_curvature_m_certificate_refines_endpoint_bound()


def test_interval_curvature_m_certificate_accepts_valid_corpus(mod) -> None:
    mod.test_interval_curvature_m_certificate_accepts_valid_corpus()


def test_interval_curvature_m_certificate_rejects_mutations(mod) -> None:
    mod.test_interval_curvature_m_certificate_rejects_mutations()


def test_best_interval_curvature_m_certificate_dominates_uniform_corpus(mod) -> None:
    mod.test_best_interval_curvature_m_certificate_dominates_uniform_corpus()


def test_refined_interval_curvature_m_certificate_monotone(mod) -> None:
    mod.test_refined_interval_curvature_m_certificate_monotone()


def test_optimal_midpoint_interval_curvature_m_certificate_audits_greedy(mod) -> None:
    mod.test_optimal_midpoint_interval_curvature_m_certificate_audits_greedy()


def test_exact_count(mod) -> None:
    mod.test_exact_count()
