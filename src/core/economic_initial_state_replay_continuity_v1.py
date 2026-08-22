"""Deterministic replay-row preservation for genesis and migration admission."""

from __future__ import annotations

from .economic_initial_state_atom_coverage_v1 import EconomicInitialStateKindV1
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
    GlobalEconomicStateV1,
    ReplayStateV1,
    hash_global_v1,
)


def derive_economic_initial_state_replay_continuity_root_v1(
    kind: EconomicInitialStateKindV1,
    target_state: GlobalEconomicStateV1,
    predecessor_state: GlobalEconomicStateV1 | None,
) -> str:
    """Commit exact replay tables after enforcing isolated-migration equality."""

    if type(kind) is not EconomicInitialStateKindV1:
        raise TypeError("initial state replay continuity kind is not closed")
    if type(target_state) is not GlobalEconomicStateV1:
        raise TypeError("initial state replay continuity target type is not closed")
    if predecessor_state is not None and type(
        predecessor_state
    ) is not GlobalEconomicStateV1:
        raise TypeError("initial state replay continuity predecessor type is not closed")

    target = _snapshot_state_v1(target_state)
    if kind is EconomicInitialStateKindV1.GENESIS:
        if predecessor_state is not None:
            raise ValueError("genesis replay continuity must not include a predecessor")
        if target.replay_state:
            raise ValueError("genesis replay state must be empty")
        source_state_root = ZERO_ROOT_V1
        source_rows: tuple[ReplayStateV1, ...] = ()
    else:
        if predecessor_state is None:
            raise ValueError("migration replay continuity requires a predecessor")
        predecessor = _snapshot_state_v1(predecessor_state)
        source_state_root = predecessor.state_root
        source_rows = predecessor.replay_state
        if target.replay_state != source_rows:
            raise ValueError(
                "migration replay continuity must preserve the exact predecessor "
                "replay state"
            )

    return hash_global_v1(
        "economic-initial-state-replay-continuity-v1",
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "kind": kind,
            "source_state_root": source_state_root,
            "target_state_root": target.state_root,
            "source_replay_state": source_rows,
            "target_replay_state": target.replay_state,
        },
    )


__all__ = ["derive_economic_initial_state_replay_continuity_root_v1"]
