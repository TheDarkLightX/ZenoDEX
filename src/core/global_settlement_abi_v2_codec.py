"""Closed canonical decoder for the initial GlobalSettlementABI V2 leaf.

The codec accepts only exact canonical JSON bytes and exact field sets.  It is
an untrusted decode edge: decoded mappings are converted immediately into the
owned V2 value graph used by the functional core.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from typing import Final, TypeVar

from .asset_transfer_types_v2 import (
    ASSET_TRANSFER_MODULE_SCHEMA_V2,
    AssetClassV2,
    AssetTransferCommandV2,
    AssetTransferContextV2,
    AssetTransferPolicyV2,
    AssetTransferStateV2,
)
from .global_economic_proof_v2 import EconomicCommandOccurrenceV2
from .global_settlement_types_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)

MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2: Final = 1_048_576


class GlobalSettlementCodecErrorV2(ValueError):
    """One deterministic malformed or noncanonical V2 decode failure."""


_T = TypeVar("_T")


def _construct_v2(builder: Callable[[], _T]) -> _T:
    try:
        return builder()
    except GlobalSettlementCodecErrorV2:
        raise
    except (TypeError, ValueError) as exc:
        raise GlobalSettlementCodecErrorV2(str(exc)) from exc


def _object_from_pairs_v2(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise GlobalSettlementCodecErrorV2(f"duplicate field: {key}")
        result[key] = value
    return result


def _reject_float_v2(_value: str) -> object:
    raise GlobalSettlementCodecErrorV2("floating-point values are unsupported")


def _reject_constant_v2(value: str) -> object:
    raise GlobalSettlementCodecErrorV2(f"non-finite JSON value is unsupported: {value}")


def _load_canonical_object_v2(raw: bytes) -> dict[str, object]:
    if type(raw) is not bytes:
        raise GlobalSettlementCodecErrorV2("encoded V2 value must be exact bytes")
    if not raw:
        raise GlobalSettlementCodecErrorV2("encoded V2 value must not be empty")
    if len(raw) > MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2:
        raise GlobalSettlementCodecErrorV2("encoded V2 value exceeds the codec byte bound")
    try:
        text = raw.decode("utf-8")
        value = json.loads(
            text,
            object_pairs_hook=_object_from_pairs_v2,
            parse_float=_reject_float_v2,
            parse_constant=_reject_constant_v2,
        )
    except GlobalSettlementCodecErrorV2:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise GlobalSettlementCodecErrorV2("encoded V2 value is invalid JSON") from exc
    if type(value) is not dict:
        raise GlobalSettlementCodecErrorV2("encoded V2 value must be an object")
    if canonical_global_bytes_v2(value) != raw:
        raise GlobalSettlementCodecErrorV2("encoded V2 value is not canonical")
    return value


def _expect_object_v2(value: object, *, name: str) -> dict[str, object]:
    if type(value) is not dict:
        raise GlobalSettlementCodecErrorV2(f"{name} must be an object")
    return value


def _expect_fields_v2(
    value: dict[str, object],
    expected: frozenset[str],
    *,
    name: str,
) -> None:
    actual = frozenset(value)
    if actual != expected:
        missing = sorted(expected - actual)
        unknown = sorted(actual - expected)
        raise GlobalSettlementCodecErrorV2(
            f"{name} field set mismatch; missing={missing}; unknown={unknown}"
        )


def _expect_text_v2(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise GlobalSettlementCodecErrorV2(f"{name} must be exact text")
    return value


def _expect_optional_text_v2(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _expect_text_v2(value, name=name)


def _expect_nonnegative_integer_v2(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise GlobalSettlementCodecErrorV2(f"{name} must be a non-negative integer")
    return value


def _expect_boolean_v2(value: object, *, name: str) -> bool:
    if type(value) is not bool:
        raise GlobalSettlementCodecErrorV2(f"{name} must be bool")
    return value


def _expect_object_list_v2(value: object, *, name: str) -> tuple[dict[str, object], ...]:
    if type(value) is not list:
        raise GlobalSettlementCodecErrorV2(f"{name} must be an array")
    return tuple(
        _expect_object_v2(item, name=f"{name}[{index}]") for index, item in enumerate(value)
    )


def _expect_text_list_v2(value: object, *, name: str) -> tuple[str, ...]:
    if type(value) is not list:
        raise GlobalSettlementCodecErrorV2(f"{name} must be an array")
    return tuple(_expect_text_v2(item, name=f"{name}[{index}]") for index, item in enumerate(value))


_COMMAND_FIELDS_V2 = frozenset(
    {
        "command_kind",
        "asset",
        "sender",
        "recipient",
        "amount_atoms",
        "max_fee_atoms",
        "asset_origin_root",
    }
)


def _decode_asset_transfer_command_object_v2(
    value: dict[str, object],
) -> AssetTransferCommandV2:
    _expect_fields_v2(value, _COMMAND_FIELDS_V2, name="asset transfer command")
    return _construct_v2(
        lambda: AssetTransferCommandV2(
            command_kind=_expect_text_v2(
                value["command_kind"],
                name="asset transfer command kind",
            ),
            asset=_expect_text_v2(value["asset"], name="asset transfer command asset"),
            sender=_expect_text_v2(
                value["sender"],
                name="asset transfer command sender",
            ),
            recipient=_expect_text_v2(
                value["recipient"],
                name="asset transfer command recipient",
            ),
            amount_atoms=_expect_nonnegative_integer_v2(
                value["amount_atoms"],
                name="asset transfer command amount",
            ),
            max_fee_atoms=_expect_nonnegative_integer_v2(
                value["max_fee_atoms"],
                name="asset transfer command max fee",
            ),
            asset_origin_root=_expect_optional_text_v2(
                value["asset_origin_root"],
                name="asset transfer command origin root",
            ),
        )
    )


_OCCURRENCE_FIELDS_V2 = frozenset(
    {
        "schema",
        "chain_id",
        "deployment_root",
        "height",
        "tx_index",
        "op_index",
        "command_kind",
        "command_body_hash",
        "route_release_id",
        "subject_id",
        "grant_root",
        "nonce",
        "profile_root",
        "pre_state_root",
        "consumed_object_ids",
    }
)


def _decode_occurrence_object_v2(
    value: dict[str, object],
) -> EconomicCommandOccurrenceV2:
    _expect_fields_v2(value, _OCCURRENCE_FIELDS_V2, name="occurrence")
    if value["schema"] != GLOBAL_SETTLEMENT_ABI_V2:
        raise GlobalSettlementCodecErrorV2("occurrence schema is not V2")
    return _construct_v2(
        lambda: EconomicCommandOccurrenceV2(
            chain_id=_expect_text_v2(value["chain_id"], name="occurrence chain id"),
            deployment_root=_expect_text_v2(
                value["deployment_root"],
                name="occurrence deployment root",
            ),
            height=_expect_nonnegative_integer_v2(
                value["height"],
                name="occurrence height",
            ),
            tx_index=_expect_nonnegative_integer_v2(
                value["tx_index"],
                name="occurrence tx index",
            ),
            op_index=_expect_nonnegative_integer_v2(
                value["op_index"],
                name="occurrence op index",
            ),
            command_kind=_expect_text_v2(
                value["command_kind"],
                name="occurrence command kind",
            ),
            command_body_hash=_expect_text_v2(
                value["command_body_hash"],
                name="occurrence command body hash",
            ),
            route_release_id=_expect_text_v2(
                value["route_release_id"],
                name="occurrence route release id",
            ),
            subject_id=_expect_text_v2(
                value["subject_id"],
                name="occurrence subject id",
            ),
            grant_root=_expect_text_v2(
                value["grant_root"],
                name="occurrence grant root",
            ),
            nonce=_expect_nonnegative_integer_v2(
                value["nonce"],
                name="occurrence nonce",
            ),
            profile_root=_expect_text_v2(
                value["profile_root"],
                name="occurrence profile root",
            ),
            pre_state_root=_expect_text_v2(
                value["pre_state_root"],
                name="occurrence pre-state root",
            ),
            consumed_object_ids=_expect_text_list_v2(
                value["consumed_object_ids"],
                name="occurrence consumed object ids",
            ),
        )
    )


_CONTEXT_FIELDS_V2 = frozenset(
    {
        "writer_epoch",
        "module_release_id",
        "global_pre_state_root",
        "occurrence",
    }
)


def _decode_asset_transfer_context_object_v2(
    value: dict[str, object],
) -> AssetTransferContextV2:
    _expect_fields_v2(value, _CONTEXT_FIELDS_V2, name="asset transfer context")
    occurrence_value = value["occurrence"]
    occurrence = (
        None
        if occurrence_value is None
        else _decode_occurrence_object_v2(_expect_object_v2(occurrence_value, name="occurrence"))
    )
    return _construct_v2(
        lambda: AssetTransferContextV2(
            writer_epoch=_expect_nonnegative_integer_v2(
                value["writer_epoch"],
                name="asset transfer context writer epoch",
            ),
            module_release_id=_expect_text_v2(
                value["module_release_id"],
                name="asset transfer context module release",
            ),
            global_pre_state_root=_expect_text_v2(
                value["global_pre_state_root"],
                name="asset transfer context global pre-state root",
            ),
            occurrence=occurrence,
        )
    )


_POLICY_FIELDS_V2 = frozenset(
    {
        "asset",
        "fee_owner",
        "transfer_fee_atoms",
        "enabled",
        "asset_class",
        "asset_origin_root",
        "atom_decimals",
    }
)


def _decode_policy_object_v2(value: dict[str, object]) -> AssetTransferPolicyV2:
    _expect_fields_v2(value, _POLICY_FIELDS_V2, name="asset transfer policy")

    def build() -> AssetTransferPolicyV2:
        asset_class_text = _expect_text_v2(
            value["asset_class"],
            name="asset transfer policy class",
        )
        try:
            asset_class = AssetClassV2(asset_class_text)
        except ValueError as exc:
            raise GlobalSettlementCodecErrorV2("asset transfer policy class is unknown") from exc
        return AssetTransferPolicyV2(
            asset=_expect_text_v2(value["asset"], name="asset transfer policy asset"),
            fee_owner=_expect_text_v2(
                value["fee_owner"],
                name="asset transfer policy fee owner",
            ),
            transfer_fee_atoms=_expect_nonnegative_integer_v2(
                value["transfer_fee_atoms"],
                name="asset transfer policy fee atoms",
            ),
            enabled=_expect_boolean_v2(
                value["enabled"],
                name="asset transfer policy enabled",
            ),
            asset_class=asset_class,
            asset_origin_root=_expect_optional_text_v2(
                value["asset_origin_root"],
                name="asset transfer policy origin root",
            ),
            atom_decimals=_expect_nonnegative_integer_v2(
                value["atom_decimals"],
                name="asset transfer policy atom decimals",
            ),
        )

    return _construct_v2(build)


_AMOUNT_FIELDS_V2 = frozenset({"owner", "asset", "custody_domain", "amount_atoms"})


def _decode_amount_object_v2(value: dict[str, object]) -> EconomicAmountV2:
    _expect_fields_v2(value, _AMOUNT_FIELDS_V2, name="economic amount")
    return _construct_v2(
        lambda: EconomicAmountV2(
            owner=_expect_text_v2(value["owner"], name="economic amount owner"),
            asset=_expect_text_v2(value["asset"], name="economic amount asset"),
            custody_domain=_expect_text_v2(
                value["custody_domain"],
                name="economic amount custody domain",
            ),
            amount_atoms=_expect_nonnegative_integer_v2(
                value["amount_atoms"],
                name="economic amount atoms",
            ),
        )
    )


_SUPPLY_FIELDS_V2 = frozenset({"asset", "amount_atoms"})


def _decode_supply_object_v2(value: dict[str, object]) -> AssetSupplyV2:
    _expect_fields_v2(value, _SUPPLY_FIELDS_V2, name="asset supply")
    return _construct_v2(
        lambda: AssetSupplyV2(
            asset=_expect_text_v2(value["asset"], name="asset supply asset"),
            amount_atoms=_expect_nonnegative_integer_v2(
                value["amount_atoms"],
                name="asset supply atoms",
            ),
        )
    )


_STATE_FIELDS_V2 = frozenset({"schema", "module_release_id", "policies", "balances", "supplies"})


def _decode_asset_transfer_state_object_v2(
    value: dict[str, object],
) -> AssetTransferStateV2:
    _expect_fields_v2(value, _STATE_FIELDS_V2, name="asset transfer state")
    if value["schema"] != ASSET_TRANSFER_MODULE_SCHEMA_V2:
        raise GlobalSettlementCodecErrorV2("asset transfer state schema is not V2")
    policy_values = _expect_object_list_v2(
        value["policies"],
        name="asset transfer policies",
    )
    balance_values = _expect_object_list_v2(
        value["balances"],
        name="asset transfer balances",
    )
    supply_values = _expect_object_list_v2(
        value["supplies"],
        name="asset transfer supplies",
    )
    return _construct_v2(
        lambda: AssetTransferStateV2(
            module_release_id=_expect_text_v2(
                value["module_release_id"],
                name="asset transfer module release id",
            ),
            policies=tuple(_decode_policy_object_v2(row) for row in policy_values),
            balances=tuple(_decode_amount_object_v2(row) for row in balance_values),
            supplies=tuple(_decode_supply_object_v2(row) for row in supply_values),
        )
    )


def decode_asset_transfer_command_v2(raw: bytes) -> AssetTransferCommandV2:
    return _decode_asset_transfer_command_object_v2(_load_canonical_object_v2(raw))


def decode_asset_transfer_context_v2(raw: bytes) -> AssetTransferContextV2:
    return _decode_asset_transfer_context_object_v2(_load_canonical_object_v2(raw))


def decode_asset_transfer_state_v2(raw: bytes) -> AssetTransferStateV2:
    return _decode_asset_transfer_state_object_v2(_load_canonical_object_v2(raw))


def encode_asset_transfer_command_v2(value: AssetTransferCommandV2) -> bytes:
    if type(value) is not AssetTransferCommandV2:
        raise GlobalSettlementCodecErrorV2("asset transfer command must be exact V2")
    return canonical_global_bytes_v2(value)


def encode_asset_transfer_context_v2(value: AssetTransferContextV2) -> bytes:
    if type(value) is not AssetTransferContextV2:
        raise GlobalSettlementCodecErrorV2("asset transfer context must be exact V2")
    return canonical_global_bytes_v2(value)


def encode_asset_transfer_state_v2(value: AssetTransferStateV2) -> bytes:
    if type(value) is not AssetTransferStateV2:
        raise GlobalSettlementCodecErrorV2("asset transfer state must be exact V2")
    return canonical_global_bytes_v2(value)


__all__ = [
    "MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2",
    "GlobalSettlementCodecErrorV2",
    "decode_asset_transfer_command_v2",
    "decode_asset_transfer_context_v2",
    "decode_asset_transfer_state_v2",
    "encode_asset_transfer_command_v2",
    "encode_asset_transfer_context_v2",
    "encode_asset_transfer_state_v2",
]
