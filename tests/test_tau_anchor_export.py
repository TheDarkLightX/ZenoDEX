"""Native execution parity for bounded shared-anchor Tau controllers."""

from __future__ import annotations

import itertools
import os
import sys
from collections.abc import Callable, Mapping
from pathlib import Path

import pytest

from src.tau_composition.anchor import AnchorCompiler, AnchoredRepair, zero_anchor
from src.tau_composition.anchor_export import export_anchor_tau
from src.tau_composition.compiler import RepairCompiler
from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.replay import replay_controller
from src.tau_composition.resources import ExpressionBudgetError
from src.tau_composition.runtime import TauRuntime
from src.tau_composition.terms import join, meet, negate, variable, xor
from tools import benchmark_tau_composition as benchmark


@pytest.fixture
def native() -> TauRuntime:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if not binary:
        pytest.skip("explicit native Tau binary required")
    return TauRuntime(Path(binary), timeout_seconds=5)


def _rows(contract: Contract) -> tuple[dict[str, bool], ...]:
    names = contract.environment + contract.controls
    return tuple(
        dict(zip(names, bits, strict=True))
        for bits in itertools.product((False, True), repeat=len(names))
    )


def _triangular_contract(clause_count: int) -> Contract:
    names = tuple(f"x{index}" for index in range(clause_count + 2))
    variables = tuple(variable(name) for name in names)
    requirements = tuple(
        Requirement(
            f"triangle{index + 2}",
            meet(join(variables[index], variables[index + 1]), negate(variables[index + 2])),
        )
        for index in range(clause_count)
    )
    return Contract(f"triangular{clause_count}", (), names, requirements)


def _triangular_legal(values: Mapping[str, bool], clause_count: int) -> bool:
    return all(
        not ((values[f"x{index}"] or values[f"x{index + 1}"]) and not values[f"x{index + 2}"])
        for index in range(clause_count)
    )


def _assert_native_retraction(
    runtime: TauRuntime,
    repair: AnchoredRepair,
    rows: tuple[dict[str, bool], ...],
    legal: Callable[[Mapping[str, bool]], bool],
) -> None:
    contract = repair.contract
    before = tuple(dict(row) for row in rows)
    outputs = replay_controller(runtime, repair, rows)

    assert rows == before
    assert len(outputs) == len(rows)
    expected_image: dict[tuple[bool, ...], set[tuple[bool, ...]]] = {}
    actual_image: dict[tuple[bool, ...], set[tuple[bool, ...]]] = {}
    for original, output in zip(rows, outputs, strict=True):
        environment = tuple(original[name] for name in contract.environment)
        candidate = {name: original[name] for name in contract.environment}
        candidate.update(output)
        expected_image.setdefault(environment, set())
        actual_image.setdefault(environment, set())
        if legal(original):
            expected_image[environment].add(tuple(original[name] for name in contract.controls))
        assert set(output) == set(contract.controls)
        assert legal(candidate)
        assert repair.propose(candidate) == candidate
        if legal(original):
            assert candidate == original
        actual_image[environment].add(tuple(output[name] for name in contract.controls))
    assert actual_image == expected_image


@pytest.mark.parametrize("clause_count", (2, 3))
def test_native_common_zero_anchor_matches_exhaustive_triangular_oracle(
    native: TauRuntime, clause_count: int
) -> None:
    contract = _triangular_contract(clause_count)
    repair = AnchorCompiler(native).compile(contract, zero_anchor(contract))
    rows = _rows(contract)

    _assert_native_retraction(
        native, repair, rows, lambda values: _triangular_legal(values, clause_count)
    )
    source = export_anchor_tau(repair)
    assert "residual(" in source
    assert source.count(":= out file") == 0


def test_native_environment_dependent_anchor_preserves_each_environment_image(native: TauRuntime) -> None:
    mode, left, right = map(variable, ("mode", "left", "right"))
    contract = Contract("mode_anchor", ("mode",), ("left", "right"), (
        Requirement("left_matches_mode", xor(left, mode)),
        Requirement("right_matches_mode", xor(right, mode)),
    ))
    anchor = RepairMap((("left", mode), ("right", mode)))
    repair = AnchorCompiler(native).compile(contract, anchor)

    _assert_native_retraction(
        native,
        repair,
        _rows(contract),
        lambda values: values["left"] is values["mode"] and values["right"] is values["mode"],
    )


def test_native_repair_economy_witness_distinguishes_anchor_and_local_map(native: TauRuntime) -> None:
    contract = Contract("repair_economy", (), ("x", "y", "z"), (
        Requirement("x_must_be_zero", variable("x")),
    ))
    proposal = {"x": True, "y": True, "z": True}
    anchored = AnchorCompiler(native).compile(contract, zero_anchor(contract))
    local = RepairCompiler(native).native_repair(contract)

    assert anchored.propose(proposal) == {"x": False, "y": False, "z": False}
    assert local.apply(proposal) == {"x": False, "y": True, "z": True}


def test_benchmark_records_expression_budget_rejection_as_unknown(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    class BudgetRejectedCompiler:
        def __init__(self, _runtime: TauRuntime) -> None:
            pass

        def compile(self, _contract: Contract) -> object:
            raise ExpressionBudgetError("expression_node_bound")

    monkeypatch.setattr(benchmark, "RepairCompiler", BudgetRejectedCompiler)
    result = benchmark._source_size_measurement(
        Path(sys.executable), tmp_path, _triangular_contract(2), "native_composed"
    )

    assert result["status"] == "UNKNOWN"
    assert result["unknown_reason"] == "expression_budget"
    assert result["source_file"] is None
    assert (tmp_path / str(result["native_query_log"])).is_file()
