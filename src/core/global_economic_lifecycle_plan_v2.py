"""Canonical terminal and Oracle lifecycle-plan derivation for ABI V2."""

from __future__ import annotations

from .global_economic_state_ownership_v2 import (
    MAX_GLOBAL_ORACLE_ROWS_V2,
    MAX_GLOBAL_TERMINAL_ROWS_V2,
    snapshot_global_lifecycle_rows_v2,
)
from .global_settlement_types_v2 import (
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    OracleOccurrenceDeltaV2,
    OracleOccurrenceStateV2,
    TerminalObligationDeltaV2,
    TerminalObligationV2,
    _require_ordered_objects_v2,
)


def derive_global_terminal_obligation_plan_v2(
    pre_obligations: tuple[TerminalObligationV2, ...],
    post_obligations: tuple[TerminalObligationV2, ...],
) -> GlobalTerminalObligationPlanV2:
    """Derive the unique nondeleting terminal-registry delta."""

    pre_rows = snapshot_global_lifecycle_rows_v2(
        pre_obligations,
        TerminalObligationV2,
        "pre terminal obligations",
        MAX_GLOBAL_TERMINAL_ROWS_V2,
    )
    post_rows = snapshot_global_lifecycle_rows_v2(
        post_obligations,
        TerminalObligationV2,
        "post terminal obligations",
        MAX_GLOBAL_TERMINAL_ROWS_V2,
    )
    for name, rows in (
        ("pre terminal obligations", pre_rows),
        ("post terminal obligations", post_rows),
    ):
        _require_ordered_objects_v2(
            rows,
            name=name,
            expected_type=TerminalObligationV2,
            key="obligation_id",
        )
    before = {row.obligation_id: row for row in pre_rows}
    after = {row.obligation_id: row for row in post_rows}
    if set(before) - set(after):
        raise ValueError("terminal obligation records cannot be deleted in ABI V2")
    return GlobalTerminalObligationPlanV2(
        tuple(
            TerminalObligationDeltaV2(obligation_id, before.get(obligation_id), row)
            for obligation_id, row in sorted(after.items())
            if before.get(obligation_id) != row
        )
    )


def derive_global_oracle_occurrence_plan_v2(
    pre_occurrences: tuple[OracleOccurrenceStateV2, ...],
    post_occurrences: tuple[OracleOccurrenceStateV2, ...],
) -> GlobalOracleOccurrencePlanV2:
    """Derive the unique nondeleting Oracle-registry delta."""

    pre_rows = snapshot_global_lifecycle_rows_v2(
        pre_occurrences,
        OracleOccurrenceStateV2,
        "pre Oracle occurrences",
        MAX_GLOBAL_ORACLE_ROWS_V2,
    )
    post_rows = snapshot_global_lifecycle_rows_v2(
        post_occurrences,
        OracleOccurrenceStateV2,
        "post Oracle occurrences",
        MAX_GLOBAL_ORACLE_ROWS_V2,
    )
    for name, rows in (
        ("pre Oracle occurrences", pre_rows),
        ("post Oracle occurrences", post_rows),
    ):
        _require_ordered_objects_v2(
            rows,
            name=name,
            expected_type=OracleOccurrenceStateV2,
            key="oracle_id",
        )
    before = {row.oracle_id: row for row in pre_rows}
    after = {row.oracle_id: row for row in post_rows}
    if set(before) - set(after):
        raise ValueError("Oracle occurrence records cannot be deleted in ABI V2")
    return GlobalOracleOccurrencePlanV2(
        tuple(
            OracleOccurrenceDeltaV2(oracle_id, before.get(oracle_id), row)
            for oracle_id, row in sorted(after.items())
            if before.get(oracle_id) != row
        )
    )


__all__ = [
    "derive_global_terminal_obligation_plan_v2",
    "derive_global_oracle_occurrence_plan_v2",
]
