"""In-memory mutation evidence for retained buyback materialization invariants."""

from __future__ import annotations

import inspect

import pytest

from src.core import zdex_atomic_buyback_lane_coordinator_v2 as coordinator
from src.core import zdex_atomic_buyback_route_composition_v2 as route_composition
from src.core.global_settlement_types_v1 import GlobalEconomicEffectPlanV1
from tests.core import test_zdex_buyback_materialization_semantics_v2 as retained


def _clone(function, needle: str, replacement: str, *, count: int = 1, extras=None):
    source = inspect.getsource(function)
    if source.count(needle) != count:
        raise AssertionError(f"mutation needle count changed for {function.__name__}")
    namespace = dict(function.__globals__)
    if extras is not None:
        namespace.update(extras)
    compiled = compile(source.replace(needle, replacement), f"<mutant:{function.__name__}>", "exec")
    exec(compiled, namespace)
    return namespace[function.__name__]


def _kill(monkeypatch, *, symbol: str, function, needle: str, replacement: str, invariant, count: int = 1, extras=None) -> None:
    invariant()
    mutant = _clone(function, needle, replacement, count=count, extras=extras)
    monkeypatch.setattr(retained, symbol, mutant)
    with pytest.raises((AssertionError, pytest.fail.Exception)):
        invariant()


def _duplicate_occurrence_output(*args, **kwargs):
    plan = GlobalEconomicEffectPlanV1(*args, **kwargs)
    object.__setattr__(plan, "occurrence_consumptions", plan.occurrence_consumptions * 2)
    return plan


def test_fee_mirror_omission_is_killed_by_retained_invariant(monkeypatch) -> None:
    _kill(
        monkeypatch,
        symbol="_materialize_fee_allocations_v2",
        function=coordinator._materialize_fee_allocations_v2,
        needle="if row.kind is EconomicEffectKindV1.FEE_ALLOCATION:",
        replacement="if False:",
        invariant=retained.test_fee_materialization_keeps_full_effect_key_and_elides_zero__guards_partial_key_merge,
    )


def test_fee_materializer_principal_key_mutant_is_killed_by_retained_invariant(monkeypatch) -> None:
    _kill(
        monkeypatch,
        symbol="_materialize_fee_allocations_v2",
        function=coordinator._materialize_fee_allocations_v2,
        needle="addition.key",
        replacement="(addition.kind.value, addition.asset, addition.custody_domain)",
        invariant=retained.test_fee_materialization_keeps_full_effect_key_and_elides_zero__guards_partial_key_merge,
        count=2,
    )


def test_spot_wrong_kind_is_killed_by_retained_invariant(monkeypatch) -> None:
    _kill(
        monkeypatch,
        symbol="_materialize_spot_custody_v2",
        function=coordinator._materialize_spot_custody_v2,
        needle="EconomicEffectKindV1.CUSTODY,",
        replacement="EconomicEffectKindV1.ACCOUNT_MOVEMENT,",
        invariant=retained.test_spot_materialization_changes_only_kind__guards_account_movement_leak,
    )


def test_outbox_bypass_is_killed_by_retained_invariant(monkeypatch) -> None:
    _kill(
        monkeypatch,
        symbol="_compose_effects_v2",
        function=route_composition._compose_effects_v2,
        needle="if plan.external_outbox_enqueue:",
        replacement="if False:",
        invariant=retained.test_composition_rejects_invalid_occurrence_lane_and_outbox_controls__guards_control_placement,
    )


def test_duplicate_occurrence_output_is_killed_by_retained_invariant(monkeypatch) -> None:
    _kill(
        monkeypatch,
        symbol="_compose_effects_v2",
        function=route_composition._compose_effects_v2,
        needle="return GlobalEconomicEffectPlanV1(",
        replacement="return _duplicate_occurrence_output(",
        invariant=retained.test_composition_nets_permutations_with_complete_rows_and_route_controls__guards_partial_key_fold,
        extras={"_duplicate_occurrence_output": _duplicate_occurrence_output},
    )
