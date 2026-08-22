from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_abi_v1 import (
    ALL_LANE_IDS_V1,
    ZERO_ROOT_V1,
    EconomicInitialStateKindV1,
    GlobalEconomicStateV1,
    LaneStateRootV1,
    ReplayStateV1,
    derive_economic_initial_state_replay_continuity_root_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _state() -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="replay-continuity-test",
        deployment_root=_root(1),
        writer_epoch=7,
        height=41,
        profile_root=_root(2),
        lane_roots=tuple(
            LaneStateRootV1(lane_id, _root(100 + index), False, ZERO_ROOT_V1)
            for index, lane_id in enumerate(ALL_LANE_IDS_V1)
        ),
    )


def _replay_row(index: int) -> ReplayStateV1:
    return ReplayStateV1(f"replay-{index:04}", _root(10_000 + index))


def test_genesis_requires_an_empty_replay_table() -> None:
    # Arrange
    empty = _state()
    nonempty = replace(empty, replay_state=(_replay_row(1),))

    # Act / Assert
    assert derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1.GENESIS,
        empty,
        None,
    ).startswith("0x")
    with pytest.raises(ValueError, match="genesis replay state must be empty"):
        derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1.GENESIS,
            nonempty,
            None,
        )


def test_kind_requires_exact_predecessor_shape() -> None:
    # Arrange
    state = _state()

    # Act / Assert
    with pytest.raises(ValueError, match="must not include a predecessor"):
        derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1.GENESIS,
            state,
            state,
        )
    with pytest.raises(ValueError, match="requires a predecessor"):
        derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1.MIGRATION,
            state,
            None,
        )


def test_migration_requires_exact_replay_table_preservation() -> None:
    # Arrange
    rows = (_replay_row(1), _replay_row(2))
    predecessor = replace(_state(), replay_state=rows)
    exact_target = replace(predecessor, writer_epoch=8, height=42, profile_root=_root(3))
    first = rows[0]
    changed_targets = (
        replace(exact_target, replay_state=rows[1:]),
        replace(exact_target, replay_state=(*rows, _replay_row(3))),
        replace(
            exact_target,
            replay_state=(
                ReplayStateV1("replay-0000", first.occurrence_id),
                rows[1],
            ),
        ),
        replace(
            exact_target,
            replay_state=(replace(first, occurrence_id=_root(99_001)), rows[1]),
        ),
    )
    reordered = replace(exact_target)
    object.__setattr__(reordered, "replay_state", tuple(reversed(rows)))

    # Act / Assert
    assert derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        exact_target,
        predecessor,
    ).startswith("0x")
    for changed_target in changed_targets:
        with pytest.raises(
            ValueError,
            match="preserve the exact predecessor replay state",
        ):
            derive_economic_initial_state_replay_continuity_root_v1(
                EconomicInitialStateKindV1.MIGRATION,
                changed_target,
                predecessor,
            )
    with pytest.raises(ValueError, match="canonically ordered"):
        derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1.MIGRATION,
            reordered,
            predecessor,
        )


def test_zero_and_one_row_migrations_preserve_exactly() -> None:
    # Arrange
    empty_predecessor = _state()
    empty_target = replace(
        empty_predecessor,
        writer_epoch=8,
        height=42,
        profile_root=_root(3),
    )
    one_row_predecessor = replace(
        empty_predecessor,
        replay_state=(_replay_row(1),),
    )
    one_row_target = replace(
        one_row_predecessor,
        writer_epoch=8,
        height=42,
        profile_root=_root(3),
    )

    # Act
    empty_root = derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        empty_target,
        empty_predecessor,
    )
    one_row_root = derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        one_row_target,
        one_row_predecessor,
    )

    # Assert
    assert empty_root.startswith("0x")
    assert one_row_root.startswith("0x")
    assert one_row_root != empty_root
