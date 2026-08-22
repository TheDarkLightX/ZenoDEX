from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_abi_v1 import (
    ALL_LANE_IDS_V1,
    MAX_INITIAL_STATE_ATOM_ROWS_V1,
    ZERO_ROOT_V1,
    EconomicInitialStateKindV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    derive_economic_initial_state_terminal_continuity_root_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _state() -> GlobalEconomicStateV1:
    return GlobalEconomicStateV1(
        chain_id="terminal-continuity-test",
        deployment_root=_root(1),
        writer_epoch=7,
        height=41,
        profile_root=_root(2),
        lane_roots=tuple(
            LaneStateRootV1(lane_id, _root(100 + index), False, ZERO_ROOT_V1)
            for index, lane_id in enumerate(ALL_LANE_IDS_V1)
        ),
    )


def _obligation(
    index: int,
    *,
    status: TerminalObligationStatusV1 = TerminalObligationStatusV1.OPEN,
) -> TerminalObligationV1:
    return TerminalObligationV1(
        obligation_id=f"obligation-{index:04}",
        lane_id=LaneIdV1.ZUSD_MONETARY,
        claimant=f"claimant-{index:04}",
        asset="zUSD",
        amount_atoms=index + 1,
        status=status,
    )


def test_genesis_commits_nonempty_classified_terminal_obligations() -> None:
    # Arrange
    state = replace(
        _state(),
        terminal_obligations=(
            _obligation(1, status=TerminalObligationStatusV1.OPEN),
            _obligation(2, status=TerminalObligationStatusV1.DRAINED),
            _obligation(3, status=TerminalObligationStatusV1.TOMBSTONED),
        ),
    )

    # Act
    root = derive_economic_initial_state_terminal_continuity_root_v1(
        EconomicInitialStateKindV1.GENESIS,
        state,
        None,
    )

    # Assert
    assert root.startswith("0x")


def test_kind_requires_exact_predecessor_shape() -> None:
    # Arrange
    state = _state()

    # Act / Assert
    with pytest.raises(ValueError, match="must not include a predecessor"):
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1.GENESIS,
            state,
            state,
        )
    with pytest.raises(ValueError, match="requires a predecessor"):
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1.MIGRATION,
            state,
            None,
        )


def test_migration_requires_exact_terminal_obligation_preservation() -> None:
    # Arrange
    rows = (
        _obligation(1, status=TerminalObligationStatusV1.OPEN),
        _obligation(2, status=TerminalObligationStatusV1.DRAINED),
    )
    predecessor = replace(_state(), terminal_obligations=rows)
    exact_target = replace(predecessor, writer_epoch=8, height=42, profile_root=_root(3))
    first = exact_target.terminal_obligations[0]
    mutations = (
        replace(first, obligation_id="obligation-0000"),
        replace(first, lane_id=LaneIdV1.PERPS_MARKET),
        replace(first, claimant="other-claimant"),
        replace(first, asset="ZDEX"),
        replace(first, amount_atoms=first.amount_atoms + 1),
        replace(first, status=TerminalObligationStatusV1.TOMBSTONED),
    )
    changed_targets = (
        replace(exact_target, terminal_obligations=rows[1:]),
        replace(exact_target, terminal_obligations=(*rows, _obligation(3))),
        *(replace(exact_target, terminal_obligations=(row, rows[1])) for row in mutations),
    )
    reordered = replace(exact_target)
    object.__setattr__(reordered, "terminal_obligations", tuple(reversed(rows)))

    # Act / Assert
    assert derive_economic_initial_state_terminal_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        exact_target,
        predecessor,
    ).startswith("0x")
    for changed_target in changed_targets:
        with pytest.raises(
            ValueError,
            match="preserve the exact predecessor terminal obligations",
        ):
            derive_economic_initial_state_terminal_continuity_root_v1(
                EconomicInitialStateKindV1.MIGRATION,
                changed_target,
                predecessor,
            )
    with pytest.raises(ValueError, match="canonically ordered"):
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1.MIGRATION,
            reordered,
            predecessor,
        )


def test_terminal_row_bound_accepts_maximum_and_preflights_maximum_plus_one() -> None:
    # Arrange
    rows = tuple(_obligation(index) for index in range(MAX_INITIAL_STATE_ATOM_ROWS_V1))
    predecessor = replace(_state(), terminal_obligations=rows)
    target = replace(predecessor, writer_epoch=8, height=42, profile_root=_root(3))
    oversized = _state()
    oversized_rows = tuple(
        _obligation(index) for index in range(MAX_INITIAL_STATE_ATOM_ROWS_V1 + 1)
    )
    object.__setattr__(oversized, "terminal_obligations", oversized_rows)
    object.__setattr__(oversized.terminal_obligations[0], "claimant", "invalid unicode ☃")

    # Act / Assert
    assert derive_economic_initial_state_terminal_continuity_root_v1(
        EconomicInitialStateKindV1.MIGRATION,
        target,
        predecessor,
    ).startswith("0x")
    with pytest.raises(ValueError, match="explicit value rows exceed"):
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1.GENESIS,
            oversized,
            None,
        )
