"""Closed canonical bytes for the V2 complete custody-lane state.

This boundary turns untrusted canonical JSON into the existing immutable custody
state. It establishes no command admission, accepted witness, receipt, store,
or publication authority.
"""

from __future__ import annotations

from .asset_lane_custody_state_v2 import (
    ASSET_LANE_CUSTODY_SCHEMA_V2,
    MAX_ASSET_LANE_CUSTODY_ROWS_V2,
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from .asset_origin_registry_codec_v2 import _decode_state_object_v2
from .global_settlement_abi_v2_codec import (
    MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2,
    GlobalSettlementCodecErrorV2,
    _construct_v2,
    _decode_amount_object_v2,
    _decode_asset_transfer_state_object_v2,
    _decode_managed_asset_lifecycle_policy_object_v2,
    _expect_fields_v2,
    _expect_object_list_v2,
    _expect_object_v2,
    _load_canonical_object_v2,
)
from .global_settlement_resource_limits_v2 import MAX_ASSETS_PER_ASSET_STATE_V2
from .global_settlement_types_v2 import canonical_global_bytes_v2

_CUSTODY_STATE_FIELDS_V2 = frozenset(
    {"schema", "transfer_state", "origin_registry", "managed_policies", "custody"}
)


def _require_raw_list_ceiling_v2(value: object, *, name: str, ceiling: int) -> None:
    """Reject an oversized decoded JSON array before a component builds its tuple."""

    if type(value) is list and len(value) > ceiling:
        raise GlobalSettlementCodecErrorV2(f"{name} exceeds the {ceiling}-item ceiling")


def _load_custody_object_v2(raw: bytes) -> dict[str, object]:
    """Convert parser depth and integer-limit failures into the codec rejection type."""

    try:
        return _load_canonical_object_v2(raw)
    except GlobalSettlementCodecErrorV2:
        raise
    except (RecursionError, TypeError, ValueError) as exc:
        raise GlobalSettlementCodecErrorV2("encoded custody state is invalid JSON") from exc


def _decode_asset_lane_custody_state_object_v2(
    value: dict[str, object],
) -> AssetLaneCustodyStateV2:
    _expect_fields_v2(value, _CUSTODY_STATE_FIELDS_V2, name="custody lane state")
    if value["schema"] != ASSET_LANE_CUSTODY_SCHEMA_V2:
        raise GlobalSettlementCodecErrorV2("custody lane state schema is not V2")
    transfer_value = _expect_object_v2(value["transfer_state"], name="custody lane transfer state")
    _require_raw_list_ceiling_v2(
        transfer_value.get("policies"),
        name="custody lane transfer policies",
        ceiling=MAX_ASSETS_PER_ASSET_STATE_V2,
    )
    _require_raw_list_ceiling_v2(
        transfer_value.get("balances"),
        name="custody lane transfer balances",
        ceiling=MAX_ASSET_LANE_CUSTODY_ROWS_V2,
    )
    _require_raw_list_ceiling_v2(
        transfer_value.get("supplies"),
        name="custody lane transfer supplies",
        ceiling=MAX_ASSETS_PER_ASSET_STATE_V2,
    )
    transfer_state = _decode_asset_transfer_state_object_v2(transfer_value)
    origin_value = _expect_object_v2(value["origin_registry"], name="custody lane origin registry")
    _require_raw_list_ceiling_v2(
        origin_value.get("assets"),
        name="custody lane origin assets",
        ceiling=MAX_ASSETS_PER_ASSET_STATE_V2,
    )
    origin_registry = _decode_state_object_v2(origin_value)
    raw_managed_policies = value["managed_policies"]
    _require_raw_list_ceiling_v2(
        raw_managed_policies,
        name="custody lane managed policies",
        ceiling=MAX_ASSETS_PER_ASSET_STATE_V2,
    )
    managed_policies = _expect_object_list_v2(
        raw_managed_policies,
        name="custody lane managed policies",
    )
    raw_custody = value["custody"]
    _require_raw_list_ceiling_v2(
        raw_custody,
        name="custody lane rows",
        ceiling=MAX_ASSET_LANE_CUSTODY_ROWS_V2,
    )
    custody = _expect_object_list_v2(raw_custody, name="custody lane rows")
    return _construct_v2(
        lambda: AssetLaneCustodyStateV2(
            transfer_state,
            origin_registry,
            tuple(
                _decode_managed_asset_lifecycle_policy_object_v2(row) for row in managed_policies
            ),
            tuple(_decode_amount_object_v2(row) for row in custody),
        )
    )


def decode_asset_lane_custody_state_v2(raw: bytes) -> AssetLaneCustodyStateV2:
    """Decode exact canonical V2 custody-state bytes into an owned immutable state."""

    return _decode_asset_lane_custody_state_object_v2(_load_custody_object_v2(raw))


def encode_asset_lane_custody_state_v2(value: AssetLaneCustodyStateV2) -> bytes:
    """Snapshot and canonical-encode an exact, valid V2 custody state."""

    if type(value) is not AssetLaneCustodyStateV2:
        raise GlobalSettlementCodecErrorV2("custody lane state must be exact V2")
    try:
        raw = canonical_global_bytes_v2(snapshot_asset_lane_custody_state_v2(value))
    except (AttributeError, RecursionError, TypeError, ValueError) as exc:
        raise GlobalSettlementCodecErrorV2("custody lane state is not valid V2") from exc
    if len(raw) > MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2:
        raise GlobalSettlementCodecErrorV2("encoded custody state exceeds the codec byte bound")
    return raw


__all__ = [
    "decode_asset_lane_custody_state_v2",
    "encode_asset_lane_custody_state_v2",
]
