"""Pytest wrapper for the Phase 3A-reformulated empirical verification.

Imports and runs the standalone test module so `pytest tests/research/`
picks up the hard-assertion verification of the Discrete Argmax Proximity
theorem (Lean PROVEN bounds + production-function bounds).

The standalone script lives at docs/research/discrete_argmax_proximity_test.py
to keep the runnable artifact in the research directory. This wrapper makes it
discoverable by pytest without duplicating the test logic.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest


_TEST_MODULE_PATH = (
    Path(__file__).resolve().parents[2]
    / "docs" / "research" / "discrete_argmax_proximity_test.py"
)


def _load_module():
    if not _TEST_MODULE_PATH.exists():
        pytest.skip(f"missing {_TEST_MODULE_PATH}")
    spec = importlib.util.spec_from_file_location(
        "discrete_argmax_proximity_test", _TEST_MODULE_PATH
    )
    if spec is None or spec.loader is None:
        pytest.skip("could not load spec for discrete_argmax_proximity_test")
    module = importlib.util.module_from_spec(spec)
    sys.modules["discrete_argmax_proximity_test"] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def mod():
    return _load_module()


def test_lean_model_floor_error_bound(mod) -> None:
    mod.test_lean_model_floor_error_bound()


def test_prod_model_floor_error_bound(mod) -> None:
    mod.test_prod_model_floor_error_bound()


def test_lean_model_argmax_proximity(mod) -> None:
    mod.test_lean_model_argmax_proximity()


def test_prod_model_argmax_proximity(mod) -> None:
    mod.test_prod_model_argmax_proximity()


def test_prod_model_window_sufficiency(mod) -> None:
    mod.test_prod_model_window_sufficiency()


def test_prod_argmax_distance_tight_one_sided_perturbation_bound(mod) -> None:
    mod.test_prod_argmax_distance_tight_one_sided_perturbation_bound()


def test_tight_argmax_certificate_accepts_valid_corpus(mod) -> None:
    mod.test_tight_argmax_certificate_accepts_valid_corpus()


def test_tight_argmax_certificate_rejects_mutations(mod) -> None:
    mod.test_tight_argmax_certificate_rejects_mutations()


def test_tight_argmax_certificate_rejects_float_overflow_domain(mod) -> None:
    mod.test_tight_argmax_certificate_rejects_float_overflow_domain()


def test_interval_m_backed_tight_argmax_certificate_composition(mod) -> None:
    mod.test_interval_m_backed_tight_argmax_certificate_composition()


def test_interval_m_backed_tight_argmax_certificate_rejects_bad_composition(mod) -> None:
    mod.test_interval_m_backed_tight_argmax_certificate_rejects_bad_composition()


def test_stationary_m_backed_tight_argmax_certificate_composition(mod) -> None:
    mod.test_stationary_m_backed_tight_argmax_certificate_composition()


def test_stationary_m_backed_tight_argmax_certificate_rejects_bad_composition(mod) -> None:
    mod.test_stationary_m_backed_tight_argmax_certificate_rejects_bad_composition()


def test_ternary_search_achieves_prod_bound(mod) -> None:
    mod.test_ternary_search_achieves_prod_bound()


def test_empirical_window_tighter(mod) -> None:
    mod.test_empirical_window_tighter()


def test_exact_count(mod) -> None:
    mod.test_exact_count()


def test_edge_case_L_zero(mod) -> None:
    mod.test_edge_case_L_zero()


def test_edge_case_small_m(mod) -> None:
    mod.test_edge_case_small_m()


def test_edge_case_bstar_at_boundary(mod) -> None:
    mod.test_edge_case_bstar_at_boundary()


def test_edge_case_D_le_2(mod) -> None:
    mod.test_edge_case_D_le_2()


def test_edge_case_all_fee_no_output(mod) -> None:
    mod.test_edge_case_all_fee_no_output()


def test_edge_case_tie_plateau(mod) -> None:
    mod.test_edge_case_tie_plateau()
