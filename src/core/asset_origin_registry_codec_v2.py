"""Strict canonical JSON boundary for the V2 asset-origin registry.

The decoder treats bytes as untrusted and admits only the exact closed field
sets used by the owned registry values. It grants no runtime, settlement,
migration, release, or production authority.
"""

from __future__ import annotations

from .asset_origin_registry_types_v2 import (
    ASSET_ORIGIN_REGISTRY_SCHEMA_V2,
    MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2,
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistrationCommandV2,
    AssetOriginRegistrationContextV2,
    AssetOriginRegistrationPolicyV2,
    AssetOriginRegistryStateV2,
)
from .asset_transfer_types_v2 import AssetClassV2
from .global_settlement_abi_v2_codec import (
    GlobalSettlementCodecErrorV2,
    _construct_v2,
    _decode_occurrence_object_v2,
    _expect_boolean_v2,
    _expect_fields_v2,
    _expect_nonnegative_integer_v2,
    _expect_object_list_v2,
    _expect_object_v2,
    _expect_text_v2,
    _load_canonical_object_v2,
)
from .global_settlement_types_v2 import canonical_global_bytes_v2

_RECORD_FIELDS_V2 = frozenset(
    {
        "asset",
        "origin_kind",
        "origin_root",
        "transfer_policy_root",
        "issue_policy_root",
        "decimals",
        "asset_class",
    }
)
_POLICY_FIELDS_V2 = frozenset(
    {
        "authority_subject",
        "authority_grant_root",
        "allow_native",
        "allow_tau_originated",
    }
)
_STATE_FIELDS_V2 = frozenset({"schema", "module_release_id", "policy", "assets"})
_CONTEXT_FIELDS_V2 = frozenset(
    {"writer_epoch", "module_release_id", "global_pre_state_root", "occurrence"}
)
_COMMAND_FIELDS_V2 = frozenset(
    {
        "command_kind",
        "asset",
        "origin_kind",
        "origin_root",
        "transfer_policy_root",
        "issue_policy_root",
        "decimals",
        "asset_class",
    }
)


def _decode_origin_kind_v2(value: object, *, name: str) -> AssetOriginKindV2:
    text = _expect_text_v2(value, name=name)
    try:
        return AssetOriginKindV2(text)
    except ValueError as exc:
        raise GlobalSettlementCodecErrorV2(f"{name} is unknown") from exc


def _decode_asset_class_v2(value: object, *, name: str) -> AssetClassV2:
    text = _expect_text_v2(value, name=name)
    try:
        return AssetClassV2(text)
    except ValueError as exc:
        raise GlobalSettlementCodecErrorV2(f"{name} is unknown") from exc


def _decode_record_object_v2(value: dict[str, object]) -> AssetOriginRecordV2:
    _expect_fields_v2(value, _RECORD_FIELDS_V2, name="asset origin record")
    return _construct_v2(
        lambda: AssetOriginRecordV2(
            asset=_expect_text_v2(value["asset"], name="asset origin record asset"),
            origin_kind=_decode_origin_kind_v2(
                value["origin_kind"],
                name="asset origin record kind",
            ),
            origin_root=_expect_text_v2(
                value["origin_root"],
                name="asset origin record root",
            ),
            transfer_policy_root=_expect_text_v2(
                value["transfer_policy_root"],
                name="asset origin record transfer policy root",
            ),
            issue_policy_root=_expect_text_v2(
                value["issue_policy_root"],
                name="asset origin record issue policy root",
            ),
            decimals=_expect_nonnegative_integer_v2(
                value["decimals"],
                name="asset origin record decimals",
            ),
            asset_class=_decode_asset_class_v2(
                value["asset_class"],
                name="asset origin record class",
            ),
        )
    )


def _decode_policy_object_v2(
    value: dict[str, object],
) -> AssetOriginRegistrationPolicyV2:
    _expect_fields_v2(value, _POLICY_FIELDS_V2, name="asset origin policy")
    return _construct_v2(
        lambda: AssetOriginRegistrationPolicyV2(
            authority_subject=_expect_text_v2(
                value["authority_subject"],
                name="asset origin policy authority subject",
            ),
            authority_grant_root=_expect_text_v2(
                value["authority_grant_root"],
                name="asset origin policy grant root",
            ),
            allow_native=_expect_boolean_v2(
                value["allow_native"],
                name="asset origin policy allow native",
            ),
            allow_tau_originated=_expect_boolean_v2(
                value["allow_tau_originated"],
                name="asset origin policy allow Tau originated",
            ),
        )
    )


def _decode_state_object_v2(value: dict[str, object]) -> AssetOriginRegistryStateV2:
    _expect_fields_v2(value, _STATE_FIELDS_V2, name="asset origin registry state")
    if value["schema"] != ASSET_ORIGIN_REGISTRY_SCHEMA_V2:
        raise GlobalSettlementCodecErrorV2("asset origin registry schema is not V2")
    policy = _decode_policy_object_v2(
        _expect_object_v2(value["policy"], name="asset origin policy")
    )
    raw_rows = value["assets"]
    if type(raw_rows) is list and len(raw_rows) > MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2:
        raise GlobalSettlementCodecErrorV2(
            "asset origin records exceed the "
            f"{MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2}-item ceiling"
        )
    rows = _expect_object_list_v2(raw_rows, name="asset origin records")
    return _construct_v2(
        lambda: AssetOriginRegistryStateV2(
            module_release_id=_expect_text_v2(
                value["module_release_id"],
                name="asset origin registry module release",
            ),
            policy=policy,
            assets=tuple(_decode_record_object_v2(row) for row in rows),
        )
    )


def _decode_context_object_v2(
    value: dict[str, object],
) -> AssetOriginRegistrationContextV2:
    _expect_fields_v2(value, _CONTEXT_FIELDS_V2, name="asset origin context")
    occurrence_value = value["occurrence"]
    occurrence = (
        None
        if occurrence_value is None
        else _decode_occurrence_object_v2(
            _expect_object_v2(occurrence_value, name="asset origin occurrence")
        )
    )
    return _construct_v2(
        lambda: AssetOriginRegistrationContextV2(
            writer_epoch=_expect_nonnegative_integer_v2(
                value["writer_epoch"],
                name="asset origin context writer epoch",
            ),
            module_release_id=_expect_text_v2(
                value["module_release_id"],
                name="asset origin context module release",
            ),
            global_pre_state_root=_expect_text_v2(
                value["global_pre_state_root"],
                name="asset origin context global pre-state root",
            ),
            occurrence=occurrence,
        )
    )


def _decode_command_object_v2(
    value: dict[str, object],
) -> AssetOriginRegistrationCommandV2:
    _expect_fields_v2(value, _COMMAND_FIELDS_V2, name="asset origin command")
    return _construct_v2(
        lambda: AssetOriginRegistrationCommandV2(
            command_kind=_expect_text_v2(
                value["command_kind"],
                name="asset origin command kind",
            ),
            asset=_expect_text_v2(value["asset"], name="asset origin command asset"),
            origin_kind=_decode_origin_kind_v2(
                value["origin_kind"],
                name="asset origin command origin kind",
            ),
            origin_root=_expect_text_v2(
                value["origin_root"],
                name="asset origin command root",
            ),
            transfer_policy_root=_expect_text_v2(
                value["transfer_policy_root"],
                name="asset origin command transfer policy root",
            ),
            issue_policy_root=_expect_text_v2(
                value["issue_policy_root"],
                name="asset origin command issue policy root",
            ),
            decimals=_expect_nonnegative_integer_v2(
                value["decimals"],
                name="asset origin command decimals",
            ),
            asset_class=_decode_asset_class_v2(
                value["asset_class"],
                name="asset origin command class",
            ),
        )
    )


def decode_asset_origin_registration_command_v2(
    raw: bytes,
) -> AssetOriginRegistrationCommandV2:
    return _decode_command_object_v2(_load_canonical_object_v2(raw))


def decode_asset_origin_registration_context_v2(
    raw: bytes,
) -> AssetOriginRegistrationContextV2:
    return _decode_context_object_v2(_load_canonical_object_v2(raw))


def decode_asset_origin_registry_state_v2(raw: bytes) -> AssetOriginRegistryStateV2:
    return _decode_state_object_v2(_load_canonical_object_v2(raw))


def encode_asset_origin_registration_command_v2(
    value: AssetOriginRegistrationCommandV2,
) -> bytes:
    if type(value) is not AssetOriginRegistrationCommandV2:
        raise GlobalSettlementCodecErrorV2("asset origin command must be exact V2")
    return canonical_global_bytes_v2(value)


def encode_asset_origin_registration_context_v2(
    value: AssetOriginRegistrationContextV2,
) -> bytes:
    if type(value) is not AssetOriginRegistrationContextV2:
        raise GlobalSettlementCodecErrorV2("asset origin context must be exact V2")
    return canonical_global_bytes_v2(value)


def encode_asset_origin_registry_state_v2(value: AssetOriginRegistryStateV2) -> bytes:
    if type(value) is not AssetOriginRegistryStateV2:
        raise GlobalSettlementCodecErrorV2("asset origin registry state must be exact V2")
    return canonical_global_bytes_v2(value)


__all__ = [
    "decode_asset_origin_registration_command_v2",
    "decode_asset_origin_registration_context_v2",
    "decode_asset_origin_registry_state_v2",
    "encode_asset_origin_registration_command_v2",
    "encode_asset_origin_registration_context_v2",
    "encode_asset_origin_registry_state_v2",
]
