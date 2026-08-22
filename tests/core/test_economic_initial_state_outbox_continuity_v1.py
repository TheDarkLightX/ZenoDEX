from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_abi_v1 import (
    ALL_LANE_IDS_V1,
    MAX_INITIAL_STATE_OUTBOX_ROWS_V1,
    ZERO_ROOT_V1,
    EconomicInitialStateKindV1,
    GlobalEconomicStateV1,
    LaneStateRootV1,
    OutboxStateV1,
    OutboxStatusV1,
    derive_economic_initial_state_outbox_continuity_root_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _state() -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="outbox-continuity-test",
        deployment_root=_root(1),
        writer_epoch=7,
        height=41,
        profile_root=_root(2),
        lane_roots=tuple(
            LaneStateRootV1(lane_id, _root(100 + index), False, ZERO_ROOT_V1)
            for index, lane_id in enumerate(ALL_LANE_IDS_V1)
        ),
    )


def _outbox_row(
    index: int,
    *,
    status: OutboxStatusV1 = OutboxStatusV1.PENDING,
) -> OutboxStateV1:
    return OutboxStateV1(
        effect_id=_root(10_000 + index),
        destination_id="bridge:test",
        payload_hash=_root(20_000 + index),
        commit_id=_root(30_000 + index),
        status=status,
    )


def test_genesis_requires_an_empty_outbox() -> None:
    # Arrange
    empty = _state()
    nonempty = replace(empty, outbox=(_outbox_row(1),))

    # Act / Assert
    assert derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1.GENESIS,
        empty,
        None,
    ).startswith("0x")
    with pytest.raises(ValueError, match="genesis outbox must be empty"):
        derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1.GENESIS,
            nonempty,
            None,
        )


def test_migration_requires_exact_outbox_preservation() -> None:
    # Arrange
    predecessor = replace(
        _state(),
        outbox=(
            _outbox_row(1),
            _outbox_row(2, status=OutboxStatusV1.ACKNOWLEDGED),
        ),
    )
    exact_target = replace(predecessor, writer_epoch=8, height=42, profile_root=_root(3))
    deleted = replace(exact_target, outbox=exact_target.outbox[:1])
    added = replace(exact_target, outbox=(*exact_target.outbox, _outbox_row(3)))
    first_row_mutations = (
        replace(exact_target.outbox[0], effect_id=_root(9_999)),
        replace(exact_target.outbox[0], destination_id="bridge:evil"),
        replace(exact_target.outbox[0], payload_hash=_root(99_001)),
        replace(exact_target.outbox[0], commit_id=_root(99_002)),
        replace(exact_target.outbox[0], status=OutboxStatusV1.ACKNOWLEDGED),
    )
    rewritten_targets = tuple(
        replace(exact_target, outbox=(changed, exact_target.outbox[1]))
        for changed in first_row_mutations
    )
    reordered = replace(exact_target)
    object.__setattr__(reordered, "outbox", tuple(reversed(exact_target.outbox)))

    # Act / Assert
    assert derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        exact_target,
        predecessor,
    ).startswith("0x")
    for changed_target in (deleted, added, *rewritten_targets):
        with pytest.raises(
            ValueError,
            match="preserve the exact predecessor outbox",
        ):
            derive_economic_initial_state_outbox_continuity_root_v1(
                EconomicInitialStateKindV1.MIGRATION,
                changed_target,
                predecessor,
            )
    with pytest.raises(ValueError, match="canonically ordered"):
        derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1.MIGRATION,
            reordered,
            predecessor,
        )


def test_outbox_row_bound_accepts_maximum_and_preflights_maximum_plus_one() -> None:
    # Arrange
    rows = tuple(_outbox_row(index) for index in range(MAX_INITIAL_STATE_OUTBOX_ROWS_V1))
    predecessor = replace(_state(), outbox=rows)
    target = replace(predecessor, writer_epoch=8, height=42, profile_root=_root(3))
    oversized = _state()
    object.__setattr__(oversized, "outbox", (*rows, rows[0]))

    # Act / Assert
    assert derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        target,
        predecessor,
    ).startswith("0x")
    with pytest.raises(ValueError, match="initial state outbox exceeds"):
        derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1.GENESIS,
            oversized,
            None,
        )
