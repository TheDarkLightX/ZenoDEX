"""Independent factor-cover and native execution regressions."""

from __future__ import annotations

import itertools
import os
from pathlib import Path

import pytest

from src.tau_composition.codec import export_tau
from src.tau_composition.compiler import RepairCompiler
from src.tau_composition.examples import conditional_cycle, coupled_recovery
from src.tau_composition.models import Contract, Requirement, compose_maps
from src.tau_composition.replay import replay_controller
from src.tau_composition.runtime import TauQueryError, TauRuntime
from src.tau_composition.terms import join, meet, negate, variable


@pytest.fixture
def native() -> TauRuntime:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if not binary:
        pytest.skip("explicit native Tau binary required")
    return TauRuntime(Path(binary), timeout_seconds=5)


def _rows(contract: Contract) -> tuple[dict[str, bool], ...]:
    names = contract.environment + contract.controls
    return tuple(dict(zip(names, row, strict=True))
                 for row in itertools.product((False, True), repeat=len(names)))


def test_idempotent_factors_cover_opposite_order_failures(native: TauRuntime) -> None:
    contract = conditional_cycle()
    compiler = RepairCompiler(native)
    local = tuple(compiler.native_repair(Contract(
        "local", contract.environment, contract.controls, (requirement,),
    )) for requirement in contract.requirements)
    assert not compiler.preserves(local[0], contract.requirements[1].residual)
    assert not compiler.preserves(local[1], contract.requirements[0].residual)
    bad_ab = compose_maps(local, contract.controls).apply({"mode": False, "left": False, "right": False})
    bad_ba = compose_maps(tuple(reversed(local)), contract.controls).apply({"mode": True, "left": False, "right": False})
    assert bad_ab["left"] is True and bad_ba["left"] is True

    cover = compiler.compile_guarded_cover(contract, ((0, 1), (1, 0)))
    assert cover.merge_rounds == 0
    for row in _rows(contract):
        result = cover.propose(row)
        # Independently derived joint solution of the two equations.
        assert result == {"mode": row["mode"], "left": False, "right": True}
        assert cover.order_guards[0].evaluate(row) == row["mode"]
        assert cover.order_guards[1].evaluate(row) != row["mode"]
    # SBF is not restricted to the host's two-element Boolean domain.
    assert not native.valid("all p:sbf ((p = 0:sbf) || (p = 1:sbf))")
    assert native.valid("all p:sbf ((p | p') = 1:sbf)")


def test_missing_factor_is_rejected_without_mutating_inputs(native: TauRuntime) -> None:
    with pytest.raises(TauQueryError, match="incomplete_order_cover"):
        RepairCompiler(native).compile_guarded_cover(conditional_cycle(), ((0, 1),))


def test_zero_default_cannot_disguise_an_empty_order_cover(native: TauRuntime) -> None:
    x, y = variable("x"), variable("y")
    contract = Contract("empty_cover", (), ("x", "y"), (
        Requirement("A", join(meet(x, negate(y)), meet(x, y))),
        Requirement("B", join(meet(negate(x), y), meet(x, y))),
    ))
    # Independent algebra: conjunction requires (0,0). The native A then B
    # map gives (x|y,0), so no environment makes this order universally safe.
    # An implicit zero fallback happens to satisfy both rules, hiding no cover.
    with pytest.raises(TauQueryError, match="incomplete_order_cover"):
        RepairCompiler(native).compile_guarded_cover(contract, ((0, 1),))


@pytest.mark.parametrize("factory,use_cover", [(coupled_recovery, False), (conditional_cycle, True)])
def test_generated_controller_is_executed_by_native_tau(native: TauRuntime, factory, use_cover: bool) -> None:
    contract = factory()
    compiler = RepairCompiler(native)
    compiled = (compiler.compile_guarded_cover(contract, ((0, 1), (1, 0)))
                if use_cover else compiler.compile(contract))
    rows = _rows(contract)
    original_rows = tuple(dict(row) for row in rows)
    actual = replay_controller(native, compiled, rows)
    assert rows == original_rows
    assert len(actual) == len(rows)
    for row, output in zip(rows, actual, strict=True):
        if use_cover:
            assert output == {"left": False, "right": True}
        else:
            assert output["debit"] == output["credit"]
            assert not (row["paused"] and output["debit"])
    assert "repair0(" in export_tau(compiled)
    assert any(record.operation == "execute" for record in native.records)


def test_bad_or_truncated_order_is_never_a_cover(native: TauRuntime) -> None:
    compiler = RepairCompiler(native)
    for order in (((0,),), ((0, 0),), ((False, 1),)):
        with pytest.raises(ValueError, match="full_permutation"):
            compiler.compile_guarded_cover(conditional_cycle(), order)
