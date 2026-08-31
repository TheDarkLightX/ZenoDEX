"""Shared finite-resource limits for rootable GlobalSettlementABI V2 asset state.

The constants are construction-time limits for the research-only V2 value
graph.  They grant no verifier, settlement, release, or production authority.
"""

from __future__ import annotations

from typing import Final

from .global_settlement_effect_plan_v2 import (
    MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2,
)

MAX_ASSETS_PER_ASSET_STATE_V2: Final = 256
MAX_BALANCE_ROWS_PER_ASSET_STATE_V2: Final = 4_096
MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2: Final = 1_048_576
MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2: Final = 64
MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2: Final = 64

# Compatibility spellings preserve established import surfaces while routing
# every rootable asset-state consumer through the same finite contract.
MAX_ROOTABLE_ASSET_STATE_ASSETS_V2: Final = MAX_ASSETS_PER_ASSET_STATE_V2
MAX_ROOTABLE_ASSET_STATE_BALANCE_ROWS_V2: Final = MAX_BALANCE_ROWS_PER_ASSET_STATE_V2
MAX_ECONOMIC_COMMAND_OCCURRENCE_OBJECT_IDS_V2: Final = MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2
MAX_GLOBAL_ECONOMIC_REFINEMENT_CONSUMED_OCCURRENCES_V2: Final = (
    MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2
)
MAX_GLOBAL_SETTLEMENT_ASSETS_V2: Final = MAX_ASSETS_PER_ASSET_STATE_V2
MAX_GLOBAL_SETTLEMENT_BALANCE_ROWS_V2: Final = MAX_BALANCE_ROWS_PER_ASSET_STATE_V2
MAX_GLOBAL_SETTLEMENT_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2: Final = (
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2
)
MAX_OCCURRENCE_CONSUMED_OBJECT_IDS_V2: Final = MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2
MAX_REFINEMENT_CONSUMED_OCCURRENCES_V2: Final = MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2

if (
    MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2 != MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2
    or MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2 != MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2
):
    raise RuntimeError("V2 occurrence ceilings must remain equal")


def require_raw_tuple_ceiling_v2(
    values: object,
    *,
    name: str,
    ceiling: int,
) -> tuple[object, ...]:
    """Check an exact raw tuple count before snapshotting or item validation."""

    if type(values) is not tuple:
        raise TypeError(f"{name} must be a tuple")
    if len(values) > ceiling:
        raise ValueError(f"{name} exceeds its {ceiling}-item ceiling")
    return values


def require_rootable_asset_state_bytes_v2(
    canonical_bytes: bytes,
    *,
    name: str,
) -> None:
    """Reject a structurally valid rootable asset state above the byte ceiling."""

    if type(canonical_bytes) is not bytes:
        raise TypeError(f"{name} canonical bytes must be exact bytes")
    if len(canonical_bytes) > MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2:
        raise ValueError(
            f"{name} exceeds its {MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2}-byte ceiling"
        )


__all__ = [
    "MAX_ASSETS_PER_ASSET_STATE_V2",
    "MAX_BALANCE_ROWS_PER_ASSET_STATE_V2",
    "MAX_ROOTABLE_ASSET_STATE_ASSETS_V2",
    "MAX_ROOTABLE_ASSET_STATE_BALANCE_ROWS_V2",
    "MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2",
    "MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2",
    "MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2",
    "MAX_ECONOMIC_COMMAND_OCCURRENCE_OBJECT_IDS_V2",
    "MAX_OCCURRENCE_CONSUMPTIONS_PER_PLAN_V2",
    "MAX_GLOBAL_ECONOMIC_REFINEMENT_CONSUMED_OCCURRENCES_V2",
    "MAX_GLOBAL_SETTLEMENT_ASSETS_V2",
    "MAX_GLOBAL_SETTLEMENT_BALANCE_ROWS_V2",
    "MAX_GLOBAL_SETTLEMENT_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2",
    "MAX_OCCURRENCE_CONSUMED_OBJECT_IDS_V2",
    "MAX_REFINEMENT_CONSUMED_OCCURRENCES_V2",
    "require_raw_tuple_ceiling_v2",
    "require_rootable_asset_state_bytes_v2",
]
