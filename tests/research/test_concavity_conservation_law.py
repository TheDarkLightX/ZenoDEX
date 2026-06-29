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


def test_tradeoff_frontier_characterization(mod) -> None:
    mod.test_tradeoff_frontier_characterization()


def test_exact_count(mod) -> None:
    mod.test_exact_count()
