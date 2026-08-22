"""Deterministic outbox preservation for genesis and migration admission."""

from __future__ import annotations

from typing import Final

from .economic_initial_state_atom_coverage_v1 import EconomicInitialStateKindV1
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
    GlobalEconomicStateV1,
    OutboxStateV1,
    hash_global_v1,
)

MAX_INITIAL_STATE_OUTBOX_ROWS_V1: Final = 4_096


def validate_economic_initial_state_outbox_row_count_v1(
    state: GlobalEconomicStateV1,
) -> int:
    if type(state) is not GlobalEconomicStateV1:
        raise TypeError("initial state outbox continuity state type is not closed")
    if type(state.outbox) is not tuple:
        raise TypeError("initial state outbox must be an exact tuple")
    if len(state.outbox) > MAX_INITIAL_STATE_OUTBOX_ROWS_V1:
        raise ValueError("initial state outbox exceeds the continuity row bound")
    return len(state.outbox)


def derive_economic_initial_state_outbox_continuity_root_v1(
    kind: EconomicInitialStateKindV1,
    target_state: GlobalEconomicStateV1,
    predecessor_state: GlobalEconomicStateV1 | None,
) -> str:
    """Commit exact outbox tables after enforcing migration preservation."""

    if type(kind) is not EconomicInitialStateKindV1:
        raise TypeError("initial state outbox continuity kind is not closed")
    if type(target_state) is not GlobalEconomicStateV1:
        raise TypeError("initial state outbox continuity target type is not closed")
    if predecessor_state is not None and type(
        predecessor_state
    ) is not GlobalEconomicStateV1:
        raise TypeError("initial state outbox continuity predecessor type is not closed")

    validate_economic_initial_state_outbox_row_count_v1(target_state)
    if predecessor_state is not None:
        validate_economic_initial_state_outbox_row_count_v1(predecessor_state)
    target = _snapshot_state_v1(target_state)
    if kind is EconomicInitialStateKindV1.GENESIS:
        if predecessor_state is not None:
            raise ValueError("genesis outbox continuity must not include a predecessor")
        if target.outbox:
            raise ValueError("genesis outbox must be empty")
        source_state_root = ZERO_ROOT_V1
        source_rows: tuple[OutboxStateV1, ...] = ()
    else:
        if predecessor_state is None:
            raise ValueError("migration outbox continuity requires a predecessor")
        predecessor = _snapshot_state_v1(predecessor_state)
        if target.outbox != predecessor.outbox:
            raise ValueError("migration must preserve the exact predecessor outbox")
        source_state_root = predecessor.state_root
        source_rows = predecessor.outbox

    return hash_global_v1(
        "economic-initial-state-outbox-continuity-v1",
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "kind": kind,
            "source_state_root": source_state_root,
            "target_state_root": target.state_root,
            "source_outbox": source_rows,
            "target_outbox": target.outbox,
        },
    )


__all__ = [
    "MAX_INITIAL_STATE_OUTBOX_ROWS_V1",
    "derive_economic_initial_state_outbox_continuity_root_v1",
    "validate_economic_initial_state_outbox_row_count_v1",
]
