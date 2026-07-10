"""Focused evidence tests for recursive-STARK aggregate conservation."""

from __future__ import annotations

import json

import pytest

from docs.research import recursive_stark_conservation_smt as model


def _checks_by_name():
    return {check.name: check for check in model.run_checks()}


def _row_is_balanced(witness: dict[str, int | bool], asset: int, row: int) -> bool:
    prefix = f"asset_{asset}_row_{row}_"
    return witness[prefix + "debit"] + witness[prefix + "mint"] == (
        witness[prefix + "credit"] + witness[prefix + "burn"]
    )


def _column_sum(witness: dict[str, int | bool], asset: int, column: str) -> int:
    return sum(
        int(witness[f"asset_{asset}_row_{row}_{column}"])
        for row in range(model.ROW_COUNT)
    )


def _aggregate_is_balanced(witness: dict[str, int | bool], asset: int) -> bool:
    prefix = f"asset_{asset}_aggregate_"
    return witness[prefix + "debit"] + witness[prefix + "mint"] == (
        witness[prefix + "credit"] + witness[prefix + "burn"]
    )


def test_checked_rows_sums_and_bounds_prove_each_asset_conserved() -> None:
    checks = model.run_checks()
    assert [check.name for check in checks[:2]] == [
        "asset_0_aggregate_conservation",
        "asset_1_aggregate_conservation",
    ]
    assert all(check.verdict == "UNSAT_PROVED" for check in checks[:2])
    assert all(check.model is None for check in checks[:2])


def test_removed_row_equations_have_concrete_imbalance() -> None:
    check = _checks_by_name()["removed_row_equations_allow_aggregate_imbalance"]
    assert check.verdict == "SAT_COUNTEREXAMPLE"
    assert check.model is not None
    assert not _aggregate_is_balanced(check.model, 0)
    assert any(
        not _row_is_balanced(check.model, 0, row)
        for row in range(model.ROW_COUNT)
    )
    for column in model.EFFECT_COLUMNS:
        assert _column_sum(check.model, 0, column) < model.AGGREGATE_MODULUS


def test_removed_checked_sum_bindings_have_concrete_imbalance() -> None:
    check = _checks_by_name()[
        "removed_checked_sum_bindings_allow_aggregate_imbalance"
    ]
    assert check.verdict == "SAT_COUNTEREXAMPLE"
    assert check.model is not None
    assert all(
        _row_is_balanced(check.model, asset, row)
        for asset in range(model.ASSET_COUNT)
        for row in range(model.ROW_COUNT)
    )
    assert not _aggregate_is_balanced(check.model, 0)
    assert any(
        check.model[f"asset_0_aggregate_{column}"]
        != _column_sum(check.model, 0, column) % model.AGGREGATE_MODULUS
        for column in model.EFFECT_COLUMNS
    )


def test_removed_no_overflow_guards_have_concrete_runtime_imbalance() -> None:
    check = _checks_by_name()[
        "removed_no_overflow_guards_allow_runtime_imbalance"
    ]
    assert check.verdict == "SAT_COUNTEREXAMPLE"
    assert check.model is not None
    assert all(
        _row_is_balanced(check.model, asset, row)
        for asset in range(model.ASSET_COUNT)
        for row in range(model.ROW_COUNT)
    )
    assert any(
        _column_sum(check.model, 0, column) >= model.AGGREGATE_MODULUS
        for column in model.EFFECT_COLUMNS
    )
    assert all(
        check.model[f"asset_0_aggregate_{column}"]
        == _column_sum(check.model, 0, column) % model.AGGREGATE_MODULUS
        for column in model.EFFECT_COLUMNS
    )
    assert not _aggregate_is_balanced(check.model, 0)


def test_report_is_canonical_and_scopes_the_bounded_claim() -> None:
    first = model.build_report()
    second = model.build_report()
    rendered = model.render_report(first)
    assert rendered == model.render_report(second)
    assert json.loads(rendered) == first
    assert first["ok"] is True
    assert first["schema"] == "zenodex.recursive_stark_conservation_smt.v1"
    assert first["model"]["finite_bounds"] == {
        "aggregate_modulus": 4,
        "amount_domain": {"max": 3, "min": 0},
        "asset_count": 2,
        "child_rows_per_asset": 2,
    }
    assert "unbounded assets, child rows, or amount widths" in first["model"][
        "exclusions"
    ]


@pytest.mark.parametrize("verdict", ["UNKNOWN", "TIMEOUT", "ERROR"])
def test_solver_indeterminacy_is_fail_closed(verdict: str, monkeypatch) -> None:
    failed_check = {
        "expected_verdict": "UNSAT_PROVED",
        "name": "synthetic_solver_failure",
        "verdict": verdict,
    }
    assert model.checks_succeeded([failed_check]) is False
    monkeypatch.setattr(model, "build_report", lambda: {"checks": [failed_check]})
    assert model.main([]) == 1
