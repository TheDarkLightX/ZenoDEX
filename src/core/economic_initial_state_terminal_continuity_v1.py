"""Deterministic terminal-obligation preservation for initial-state admission."""

from __future__ import annotations

from .economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateKindV1,
    validate_economic_initial_state_explicit_row_count_v1,
)
from .global_economic_refinement_snapshot_v1 import _snapshot_state_v1
from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
    GlobalEconomicStateV1,
    TerminalObligationV1,
    hash_global_v1,
)


def derive_economic_initial_state_terminal_continuity_root_v1(
    kind: EconomicInitialStateKindV1,
    target_state: GlobalEconomicStateV1,
    predecessor_state: GlobalEconomicStateV1 | None,
) -> str:
    """Commit complete terminal tables under a conservative migration rule.

    Genesis may declare obligations already classified by the initial-state
    atom manifest. Migration preserves every predecessor obligation byte for
    byte; draining, tombstoning, creation, or rewrite requires an ordinary
    proved transition outside the isolated migration block.
    """

    if type(kind) is not EconomicInitialStateKindV1:
        raise TypeError("initial state terminal continuity kind is not closed")
    if type(target_state) is not GlobalEconomicStateV1:
        raise TypeError("initial state terminal continuity target type is not closed")
    if predecessor_state is not None and type(
        predecessor_state
    ) is not GlobalEconomicStateV1:
        raise TypeError("initial state terminal continuity predecessor type is not closed")

    validate_economic_initial_state_explicit_row_count_v1(target_state)
    if predecessor_state is not None:
        validate_economic_initial_state_explicit_row_count_v1(predecessor_state)
    target = _snapshot_state_v1(target_state)
    if kind is EconomicInitialStateKindV1.GENESIS:
        if predecessor_state is not None:
            raise ValueError("genesis terminal continuity must not include a predecessor")
        source_state_root = ZERO_ROOT_V1
        source_rows: tuple[TerminalObligationV1, ...] = ()
    else:
        if predecessor_state is None:
            raise ValueError("migration terminal continuity requires a predecessor")
        predecessor = _snapshot_state_v1(predecessor_state)
        if target.terminal_obligations != predecessor.terminal_obligations:
            raise ValueError(
                "migration must preserve the exact predecessor terminal obligations"
            )
        source_state_root = predecessor.state_root
        source_rows = predecessor.terminal_obligations

    return hash_global_v1(
        "economic-initial-state-terminal-continuity-v1",
        {
            "schema": GLOBAL_SETTLEMENT_ABI_V1,
            "kind": kind,
            "source_state_root": source_state_root,
            "target_state_root": target.state_root,
            "source_terminal_obligations": source_rows,
            "target_terminal_obligations": target.terminal_obligations,
        },
    )


__all__ = ["derive_economic_initial_state_terminal_continuity_root_v1"]
