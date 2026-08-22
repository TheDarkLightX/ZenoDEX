from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.economic_effect_occurrence_v1 import (
    EconomicEffectOccurrenceV1,
    derive_route_effect_occurrences_v1,
)
from src.core.global_settlement_types_v1 import (
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _row(*, principal: str = "alice", delta_atoms: int = -7) -> EconomicEffectRowV1:
    return EconomicEffectRowV1(
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        principal,
        "USD",
        "accounts",
        delta_atoms,
    )


def _plan(occurrence_id: str) -> GlobalEconomicEffectPlanV1:
    return GlobalEconomicEffectPlanV1(
        rows=(
            _row(),
            _row(principal="bob", delta_atoms=7),
        ),
        asset_conservation=(
            AssetConservationRowV1("USD", 20, 20, 20, 20, 0, 0),
        ),
        fee_conservation=(),
        lane_writes=(),
        occurrence_consumptions=(occurrence_id,),
        external_outbox_enqueue=(),
    )


def test_effect_occurrence_identity_binds_route_occurrence_index_and_row() -> None:
    base = EconomicEffectOccurrenceV1.build(
        command_occurrence_id=_root(1),
        route_release_id=_root(2),
        effect_index=0,
        effect_row=_row(),
    )

    variants = (
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=_root(3),
            route_release_id=_root(2),
            effect_index=0,
            effect_row=_row(),
        ),
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=_root(1),
            route_release_id=_root(4),
            effect_index=0,
            effect_row=_row(),
        ),
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=_root(1),
            route_release_id=_root(2),
            effect_index=1,
            effect_row=_row(),
        ),
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=_root(1),
            route_release_id=_root(2),
            effect_index=0,
            effect_row=_row(delta_atoms=-8),
        ),
    )

    assert len({base.effect_occurrence_id, *(item.effect_occurrence_id for item in variants)}) == 5
    assert base.effect_occurrence_id == base.derived_effect_occurrence_id
    assert base.effect_occurrence_id == (
        "0xe21c9a9fef43e18576caa49441b3b865"
        "2005834d06b0fd515184b2365c1de36c"
    )


def test_effect_occurrence_rejects_forged_id_and_boolean_index() -> None:
    valid = EconomicEffectOccurrenceV1.build(
        command_occurrence_id=_root(1),
        route_release_id=_root(2),
        effect_index=0,
        effect_row=_row(),
    )

    with pytest.raises(ValueError, match="content-derived"):
        replace(valid, effect_occurrence_id=_root(99))
    with pytest.raises(TypeError, match="effect index"):
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=_root(1),
            route_release_id=_root(2),
            effect_index=True,  # type: ignore[arg-type]
            effect_row=_row(),
        )


def test_effect_occurrence_rejects_hostile_values_before_canonicalization() -> None:
    class HostileCanonicalValue:
        def to_canonical(self) -> object:
            raise AssertionError("hostile canonicalization must not run")

    class RootSubclass(str):
        pass

    with pytest.raises(TypeError, match="row must be exact typed data"):
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=_root(1),
            route_release_id=_root(2),
            effect_index=0,
            effect_row=HostileCanonicalValue(),  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="command occurrence id must be exact str"):
        EconomicEffectOccurrenceV1.build(
            command_occurrence_id=RootSubclass(_root(1)),
            route_release_id=_root(2),
            effect_index=0,
            effect_row=_row(),
        )


def test_route_effect_occurrences_are_ordered_and_disjoint_across_commands() -> None:
    first = derive_route_effect_occurrences_v1(
        command_occurrence_id=_root(1),
        route_release_id=_root(2),
        effect_plan=_plan(_root(1)),
    )
    second = derive_route_effect_occurrences_v1(
        command_occurrence_id=_root(3),
        route_release_id=_root(2),
        effect_plan=_plan(_root(3)),
    )

    assert tuple(item.effect_index for item in first) == (0, 1)
    assert len({item.effect_occurrence_id for item in (*first, *second)}) == 4
    assert first[0].effect_row == second[0].effect_row


def test_route_effect_occurrence_derivation_requires_exact_consumed_occurrence() -> None:
    with pytest.raises(ValueError, match="consumed occurrence"):
        derive_route_effect_occurrences_v1(
            command_occurrence_id=_root(1),
            route_release_id=_root(2),
            effect_plan=_plan(_root(99)),
        )
