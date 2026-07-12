"""Strict reconstruction of canonical persisted SettlementEffectPlanV1 bytes."""

from __future__ import annotations

import json
from collections.abc import Callable, Mapping
from typing import Any, NoReturn, TypeVar, cast

from src.core.zrpf_settlement_effect_plan import (
    SETTLEMENT_EFFECT_PLAN_SCHEMA_V1,
    AssetEffectKindV1,
    AssetEffectV1,
    AuthorizationConsumptionV1,
    CarryEffectKindV1,
    CarryEffectV1,
    LedgerCellWriteV1,
    MessageEffectKindV1,
    MessageEffectV1,
    ProposedSettlementEffectPlanV1,
    RewardEffectV1,
    SettlementEffectPlanV1,
    SettlementEffectPlanValidationError,
    build_settlement_effect_plan_v1,
)

_PLAN_KEYS = frozenset(
    {
        "schema",
        "application_id",
        "chain_or_domain_id",
        "epoch_id",
        "source_root_journal_hash",
        "public_policy_hash",
        "pre_state_root",
        "post_state_root",
        "economic_action_ids",
        "economic_action_ids_root",
        "ledger_cell_writes",
        "ledger_cell_writes_root",
        "asset_effects",
        "asset_effects_root",
        "authorization_consumptions",
        "authorization_consumptions_root",
        "authorization_nullifiers_root",
        "authorization_grant_spend_nullifiers_root",
        "message_effects",
        "message_effects_root",
        "carry_effects",
        "carry_effects_root",
        "reward_effects",
        "reward_effects_root",
    }
)

_CELL_KEYS = frozenset({"economic_action_id", "cell_key", "pre_value_hash", "post_value_hash"})
_ASSET_KEYS = frozenset(
    {
        "effect_id",
        "kind",
        "economic_action_id",
        "asset_id",
        "debit_atoms",
        "credit_atoms",
        "authorized_mint_atoms",
        "authorized_burn_atoms",
        "authority_scope_id",
        "authorization_nullifier",
    }
)
_AUTHORIZATION_KEYS = frozenset(
    {
        "application_id",
        "chain_or_domain_id",
        "economic_action_id",
        "authorization_subject_id",
        "authorization_grant_id",
        "authorization_scope_id",
        "authorization_nonce",
        "action_pre_state_root",
        "authorization_nullifier",
        "authorization_grant_spend_nullifier",
    }
)
_MESSAGE_KEYS = frozenset(
    {
        "message_id",
        "economic_action_id",
        "asset_effect_id",
        "source_domain_id",
        "destination_domain_id",
        "asset_id",
        "amount_atoms",
        "kind",
    }
)
_CARRY_KEYS = frozenset(
    {"carry_id", "economic_action_id", "message_id", "asset_id", "amount_atoms", "kind"}
)
_REWARD_KEYS = frozenset(
    {
        "reward_id",
        "economic_action_id",
        "asset_effect_id",
        "recipient_cell_key",
        "asset_id",
        "amount_atoms",
        "authority_scope_id",
        "authorization_nullifier",
    }
)

_MAX_PERSISTED_PLAN_BYTES_V1 = 128 * 1024 * 1024
_MAX_JSON_NESTING_V1 = 64


def _decode_canonical_settlement_plan_v1(raw: bytes) -> SettlementEffectPlanV1:
    """Reconstruct the typed plan and require byte-exact canonical encoding."""

    decoded = _decode_json_object(raw)
    try:
        plan = _reconstruct_plan(decoded)
    except (KeyError, TypeError, ValueError, SettlementEffectPlanValidationError) as exc:
        raise ValueError("stored settlement plan fails typed V1 validation") from exc
    try:
        canonical = plan.canonical_bytes()
    except (TypeError, ValueError, RecursionError) as exc:
        raise ValueError("stored settlement plan canonicalization failed") from exc
    if canonical != raw:
        raise ValueError("stored settlement plan bytes are noncanonical or self-inconsistent")
    return plan


def _decode_json_object(raw: bytes) -> Mapping[str, Any]:
    if type(raw) is not bytes or not raw or len(raw) > _MAX_PERSISTED_PLAN_BYTES_V1:
        raise ValueError("stored settlement plan byte length is out of bounds")
    _require_bounded_json_nesting(raw)
    try:
        decoded = json.loads(
            raw,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
            parse_float=_reject_json_float,
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        TypeError,
        ValueError,
        RecursionError,
    ) as exc:
        raise ValueError("stored settlement plan is invalid bounded JSON") from exc
    if type(decoded) is not dict:
        raise ValueError("stored settlement plan must be a JSON object")
    result = cast(dict[str, Any], decoded)
    _require_exact_keys(result, _PLAN_KEYS, "plan")
    return result


def _require_bounded_json_nesting(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            in_string, escaped = _scan_json_string_byte(byte, escaped)
            continue
        if byte == ord('"'):
            in_string = True
            continue
        depth = _scan_json_structure_byte(byte, depth)


def _scan_json_string_byte(byte: int, escaped: bool) -> tuple[bool, bool]:
    if escaped:
        return True, False
    if byte == ord("\\"):
        return True, True
    return byte != ord('"'), False


def _scan_json_structure_byte(byte: int, depth: int) -> int:
    if byte in (ord("{"), ord("[")):
        result = depth + 1
        if result > _MAX_JSON_NESTING_V1:
            raise ValueError("stored settlement plan JSON nesting exceeds V1 bound")
        return result
    if byte in (ord("}"), ord("]")):
        result = depth - 1
        if result < 0:
            raise ValueError("stored settlement plan JSON nesting is unbalanced")
        return result
    return depth


def _reconstruct_plan(value: Mapping[str, Any]) -> SettlementEffectPlanV1:
    if _require_str(value, "schema") != SETTLEMENT_EFFECT_PLAN_SCHEMA_V1:
        raise ValueError("stored settlement plan schema mismatch")
    proposal = ProposedSettlementEffectPlanV1(
        application_id=_require_str(value, "application_id"),
        chain_or_domain_id=_require_str(value, "chain_or_domain_id"),
        epoch_id=_require_int(value, "epoch_id"),
        source_root_journal_hash=_require_str(value, "source_root_journal_hash"),
        public_policy_hash=_require_str(value, "public_policy_hash"),
        pre_state_root=_require_str(value, "pre_state_root"),
        post_state_root=_require_str(value, "post_state_root"),
        economic_action_ids=tuple(_require_string_list(value, "economic_action_ids")),
        ledger_cell_writes=_decode_records(value, "ledger_cell_writes", _decode_cell),
        asset_effects=_decode_records(value, "asset_effects", _decode_asset),
        authorization_consumptions=_decode_records(
            value,
            "authorization_consumptions",
            _decode_authorization,
        ),
        message_effects=_decode_records(value, "message_effects", _decode_message),
        carry_effects=_decode_records(value, "carry_effects", _decode_carry),
        reward_effects=_decode_records(value, "reward_effects", _decode_reward),
    )
    return build_settlement_effect_plan_v1(proposal)


def _decode_cell(value: Mapping[str, Any]) -> LedgerCellWriteV1:
    _require_exact_keys(value, _CELL_KEYS, "cell write")
    return LedgerCellWriteV1(
        economic_action_id=_require_str(value, "economic_action_id"),
        cell_key=_require_str(value, "cell_key"),
        pre_value_hash=_require_str(value, "pre_value_hash"),
        post_value_hash=_require_str(value, "post_value_hash"),
    )


def _decode_asset(value: Mapping[str, Any]) -> AssetEffectV1:
    _require_exact_keys(value, _ASSET_KEYS, "asset effect")
    result = AssetEffectV1(
        kind=_enum_value(value, "kind", AssetEffectKindV1),
        economic_action_id=_require_str(value, "economic_action_id"),
        asset_id=_require_str(value, "asset_id"),
        debit_atoms=_require_int(value, "debit_atoms"),
        credit_atoms=_require_int(value, "credit_atoms"),
        authorized_mint_atoms=_require_int(value, "authorized_mint_atoms"),
        authorized_burn_atoms=_require_int(value, "authorized_burn_atoms"),
        authority_scope_id=_require_str(value, "authority_scope_id"),
        authorization_nullifier=_require_str(value, "authorization_nullifier"),
    )
    _require_derived_identifier(value, "effect_id", result.effect_id)
    return result


def _decode_authorization(value: Mapping[str, Any]) -> AuthorizationConsumptionV1:
    _require_exact_keys(value, _AUTHORIZATION_KEYS, "authorization consumption")
    result = AuthorizationConsumptionV1(
        application_id=_require_str(value, "application_id"),
        chain_or_domain_id=_require_str(value, "chain_or_domain_id"),
        economic_action_id=_require_str(value, "economic_action_id"),
        authorization_subject_id=_require_str(value, "authorization_subject_id"),
        authorization_grant_id=_require_str(value, "authorization_grant_id"),
        authorization_scope_id=_require_str(value, "authorization_scope_id"),
        authorization_nonce=_require_int(value, "authorization_nonce"),
        action_pre_state_root=_require_str(value, "action_pre_state_root"),
        authorization_nullifier=_require_str(value, "authorization_nullifier"),
    )
    _require_derived_identifier(
        value,
        "authorization_grant_spend_nullifier",
        result.authorization_grant_spend_nullifier,
    )
    return result


def _decode_message(value: Mapping[str, Any]) -> MessageEffectV1:
    _require_exact_keys(value, _MESSAGE_KEYS, "message effect")
    result = MessageEffectV1(
        economic_action_id=_require_str(value, "economic_action_id"),
        asset_effect_id=_require_str(value, "asset_effect_id"),
        source_domain_id=_require_str(value, "source_domain_id"),
        destination_domain_id=_require_str(value, "destination_domain_id"),
        asset_id=_require_str(value, "asset_id"),
        amount_atoms=_require_int(value, "amount_atoms"),
        kind=_enum_value(value, "kind", MessageEffectKindV1),
    )
    _require_derived_identifier(value, "message_id", result.message_id)
    return result


def _decode_carry(value: Mapping[str, Any]) -> CarryEffectV1:
    _require_exact_keys(value, _CARRY_KEYS, "carry effect")
    result = CarryEffectV1(
        economic_action_id=_require_str(value, "economic_action_id"),
        message_id=_require_str(value, "message_id"),
        asset_id=_require_str(value, "asset_id"),
        amount_atoms=_require_int(value, "amount_atoms"),
        kind=_enum_value(value, "kind", CarryEffectKindV1),
    )
    _require_derived_identifier(value, "carry_id", result.carry_id)
    return result


def _decode_reward(value: Mapping[str, Any]) -> RewardEffectV1:
    _require_exact_keys(value, _REWARD_KEYS, "reward effect")
    result = RewardEffectV1(
        economic_action_id=_require_str(value, "economic_action_id"),
        asset_effect_id=_require_str(value, "asset_effect_id"),
        recipient_cell_key=_require_str(value, "recipient_cell_key"),
        asset_id=_require_str(value, "asset_id"),
        amount_atoms=_require_int(value, "amount_atoms"),
        authority_scope_id=_require_str(value, "authority_scope_id"),
        authorization_nullifier=_require_str(value, "authorization_nullifier"),
    )
    _require_derived_identifier(value, "reward_id", result.reward_id)
    return result


_RecordT = TypeVar(
    "_RecordT",
    LedgerCellWriteV1,
    AssetEffectV1,
    AuthorizationConsumptionV1,
    MessageEffectV1,
    CarryEffectV1,
    RewardEffectV1,
)


def _decode_records(
    value: Mapping[str, Any],
    key: str,
    decode: Callable[[Mapping[str, Any]], _RecordT],
) -> tuple[_RecordT, ...]:
    records = _require_list(value, key)
    result = []
    for index, record in enumerate(records):
        if type(record) is not dict:
            raise ValueError(f"stored {key}[{index}] must be an object")
        result.append(decode(cast(dict[str, Any], record)))
    return tuple(result)


def _require_string_list(value: Mapping[str, Any], key: str) -> list[str]:
    result = _require_list(value, key)
    if any(type(item) is not str for item in result):
        raise ValueError(f"stored {key} must contain only strings")
    return result


def _require_list(value: Mapping[str, Any], key: str) -> list[Any]:
    result = value[key]
    if type(result) is not list:
        raise ValueError(f"stored {key} must be a list")
    return result


def _require_str(value: Mapping[str, Any], key: str) -> str:
    result = value[key]
    if type(result) is not str:
        raise ValueError(f"stored {key} must be a string")
    return result


def _require_int(value: Mapping[str, Any], key: str) -> int:
    result = value[key]
    if type(result) is not int:
        raise ValueError(f"stored {key} must be an integer")
    return result


_EnumT = TypeVar("_EnumT", AssetEffectKindV1, MessageEffectKindV1, CarryEffectKindV1)


def _enum_value(value: Mapping[str, Any], key: str, enum_type: type[_EnumT]) -> _EnumT:
    return enum_type(_require_str(value, key))


def _require_derived_identifier(value: Mapping[str, Any], key: str, expected: str) -> None:
    if _require_str(value, key) != expected:
        raise ValueError(f"stored derived identifier mismatch: {key}")


def _require_exact_keys(value: Mapping[str, Any], expected: frozenset[str], name: str) -> None:
    if frozenset(value) != expected:
        raise ValueError(f"stored settlement {name} key set mismatch")


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> Mapping[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate settlement plan key: {key}")
        result[key] = value
    return result


def _reject_json_constant(_value: str) -> NoReturn:
    raise ValueError("stored settlement plan cannot contain non-finite numbers")


def _reject_json_float(_value: str) -> NoReturn:
    raise ValueError("stored settlement plan cannot contain floating-point numbers")
