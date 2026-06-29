"""Pytest wrapper for the K-pool Discrete Argmax Proximity empirical verification.

Imports and runs the standalone test module so `pytest tests/research/`
picks up the hard-assertion verification of the k-pool generalization.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest


_TEST_MODULE_PATH = (
    Path(__file__).resolve().parents[2]
    / "docs" / "research" / "k_pool_discrete_argmax_proximity_test.py"
)


def _load_module():
    if not _TEST_MODULE_PATH.exists():
        pytest.skip(f"missing {_TEST_MODULE_PATH}")
    spec = importlib.util.spec_from_file_location(
        "k_pool_discrete_argmax_proximity_test", _TEST_MODULE_PATH
    )
    if spec is None or spec.loader is None:
        pytest.skip("could not load spec for k_pool_discrete_argmax_proximity_test")
    module = importlib.util.module_from_spec(spec)
    sys.modules["k_pool_discrete_argmax_proximity_test"] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def mod():
    return _load_module()


def test_kpool_floor_error_bound_lean(mod) -> None:
    mod.test_kpool_floor_error_bound_lean()


def test_kpool_floor_error_bound_prod(mod) -> None:
    mod.test_kpool_floor_error_bound_prod()


def test_kpool_argmax_proximity_lean(mod) -> None:
    mod.test_kpool_argmax_proximity_lean()


def test_kpool_argmax_proximity_prod(mod) -> None:
    mod.test_kpool_argmax_proximity_prod()


def test_kpool_balanced_corollary(mod) -> None:
    mod.test_kpool_balanced_corollary()


def test_floor_error_scales_linearly(mod) -> None:
    mod.test_floor_error_scales_linearly()


def test_k2_specialization_matches_2pool(mod) -> None:
    mod.test_k2_specialization_matches_2pool()


def test_exact_count(mod) -> None:
    mod.test_exact_count()


def test_kpool_exhaustive_small_domain_3pool(mod) -> None:
    mod.test_kpool_exhaustive_small_domain_3pool()


def test_kpool_exhaustive_small_domain_4pool(mod) -> None:
    mod.test_kpool_exhaustive_small_domain_4pool()
