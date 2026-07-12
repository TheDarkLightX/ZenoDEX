"""Shared bounds, enums, and primitive validators for ZRPF effect plans."""

from __future__ import annotations

from enum import Enum
from typing import Any, NoReturn

HASH_BYTES = 32
MAX_U64 = (1 << 64) - 1
MAX_U128 = (1 << 128) - 1
MAX_SETTLEMENT_EFFECT_PLAN_ROWS_V1 = 8_192
SETTLEMENT_EFFECT_PLAN_SCHEMA_V1 = "zenodex/zrpf_settlement_effect_plan/v1"
ZERO_HASH_V1 = "0x" + "00" * HASH_BYTES


class SettlementEffectPlanRejectCodeV1(str, Enum):
    """Stable fail-closed validation codes for the V1 pure constructor."""

    INVALID_PROPOSAL = "zrpf.effect_plan.invalid_proposal"
    INVALID_HASH = "zrpf.effect_plan.invalid_hash"
    INVALID_INTEGER = "zrpf.effect_plan.invalid_integer"
    INVALID_ENUM = "zrpf.effect_plan.invalid_enum"
    INVALID_COLLECTION = "zrpf.effect_plan.invalid_collection"
    COLLECTION_CAPACITY_EXCEEDED = "zrpf.effect_plan.collection_capacity_exceeded"
    ZERO_EFFECT = "zrpf.effect_plan.zero_effect"
    NON_CHANGING_CELL_WRITE = "zrpf.effect_plan.non_changing_cell_write"
    NON_CHANGING_STATE_ROOT = "zrpf.effect_plan.non_changing_state_root"
    COMBINED_MINT_AND_BURN = "zrpf.effect_plan.combined_mint_and_burn"
    INVALID_SUPPLY_EFFECT_SHAPE = "zrpf.effect_plan.invalid_supply_effect_shape"
    UNEXPECTED_AUTHORITY_MATERIAL = "zrpf.effect_plan.unexpected_authority_material"
    MISSING_AUTHORITY_MATERIAL = "zrpf.effect_plan.missing_authority_material"
    DUPLICATE_ECONOMIC_ACTION = "zrpf.effect_plan.duplicate_economic_action"
    DUPLICATE_CELL_WRITE = "zrpf.effect_plan.duplicate_cell_write"
    DUPLICATE_ASSET_EFFECT = "zrpf.effect_plan.duplicate_asset_effect"
    DUPLICATE_AUTHORIZATION_NULLIFIER = "zrpf.effect_plan.duplicate_authorization_nullifier"
    DUPLICATE_AUTHORIZATION_GRANT_SPEND = "zrpf.effect_plan.duplicate_authorization_grant_spend"
    DUPLICATE_MESSAGE = "zrpf.effect_plan.duplicate_message"
    DUPLICATE_CARRY = "zrpf.effect_plan.duplicate_carry"
    DUPLICATE_REWARD = "zrpf.effect_plan.duplicate_reward"
    DERIVED_ID_MISMATCH = "zrpf.effect_plan.derived_id_mismatch"
    UNKNOWN_ECONOMIC_ACTION = "zrpf.effect_plan.unknown_economic_action"
    ACTION_WITHOUT_CELL_WRITE = "zrpf.effect_plan.action_without_cell_write"
    ACTION_WITHOUT_ASSET_EFFECT = "zrpf.effect_plan.action_without_asset_effect"
    AUTHORIZATION_NULLIFIER_MISMATCH = "zrpf.effect_plan.authorization_nullifier_mismatch"
    AUTHORIZATION_SCOPE_MISMATCH = "zrpf.effect_plan.authorization_scope_mismatch"
    AUTHORIZATION_PRE_STATE_MISMATCH = "zrpf.effect_plan.authorization_pre_state_mismatch"
    AUTHORIZATION_CONSUMPTION_REUSED = "zrpf.effect_plan.authorization_consumption_reused"
    MISSING_AUTHORIZATION_CONSUMPTION = "zrpf.effect_plan.missing_authorization_consumption"
    DETACHED_AUTHORIZATION_CONSUMPTION = "zrpf.effect_plan.detached_authorization_consumption"
    ASSET_CONSERVATION_VIOLATION = "zrpf.effect_plan.asset_conservation_violation"
    ARITHMETIC_OVERFLOW = "zrpf.effect_plan.arithmetic_overflow"
    MESSAGE_CARRY_MISMATCH = "zrpf.effect_plan.message_carry_mismatch"
    REWARD_EFFECT_MISMATCH = "zrpf.effect_plan.reward_effect_mismatch"


class SettlementEffectPlanValidationError(ValueError):
    """Typed V1 validation failure with a stable machine-readable code."""

    def __init__(self, code: SettlementEffectPlanRejectCodeV1, detail: str) -> None:
        super().__init__(f"{code.value}: {detail}")
        self.code = code
        self.detail = detail


class AssetEffectKindV1(str, Enum):
    ORDINARY_TRANSFER = "ordinary_transfer"
    AUTHORIZED_MINT = "authorized_mint"
    AUTHORIZED_BURN = "authorized_burn"
    AUTHORIZED_REWARD = "authorized_reward"


class MessageEffectKindV1(str, Enum):
    OUTBOX_ENQUEUE = "outbox_enqueue"
    INBOX_CONSUME = "inbox_consume"


class CarryEffectKindV1(str, Enum):
    LOCK = "lock"
    RELEASE = "release"


def _require_collection(values: object, *, name: str, allow_empty: bool) -> tuple[Any, ...]:
    if type(values) is not tuple:
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_COLLECTION,
            f"{name} must be a tuple",
        )
    if not allow_empty and not values:
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_COLLECTION,
            f"{name} must be nonempty",
        )
    if len(values) > MAX_SETTLEMENT_EFFECT_PLAN_ROWS_V1:
        _reject(
            SettlementEffectPlanRejectCodeV1.COLLECTION_CAPACITY_EXCEEDED,
            f"{name} exceeds {MAX_SETTLEMENT_EFFECT_PLAN_ROWS_V1} rows",
        )
    return values


def _require_hash(value: object, *, name: str, allow_zero: bool) -> str:
    if type(value) is not str or len(value) != 66 or not value.startswith("0x"):
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_HASH,
            f"{name} must be canonical 0x-prefixed 32-byte hex",
        )
    bare = value[2:]
    if any(character not in "0123456789abcdef" for character in bare):
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_HASH,
            f"{name} must use canonical lowercase hex",
        )
    if not allow_zero and value == ZERO_HASH_V1:
        _reject(SettlementEffectPlanRejectCodeV1.INVALID_HASH, f"{name} must be nonzero")
    return value


def _require_nonzero_hash(value: object, *, name: str) -> str:
    return _require_hash(value, name=name, allow_zero=False)


def _hash_bytes(value: object, *, name: str) -> bytes:
    return bytes.fromhex(_require_nonzero_hash(value, name=name)[2:])


def _require_uint(value: object, *, name: str, maximum: int) -> int:
    if type(value) is not int:
        _reject(SettlementEffectPlanRejectCodeV1.INVALID_INTEGER, f"{name} must be an int")
    if value < 0 or value > maximum:
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_INTEGER,
            f"{name} must be in 0..{maximum}",
        )
    return value


def _require_positive_uint(value: object, *, name: str, maximum: int) -> int:
    checked = _require_uint(value, name=name, maximum=maximum)
    if checked == 0:
        _reject(SettlementEffectPlanRejectCodeV1.ZERO_EFFECT, f"{name} must be positive")
    return checked


def _require_enum(value: object, enum_type: type[Enum], *, name: str) -> None:
    if type(value) is not enum_type:
        _reject(
            SettlementEffectPlanRejectCodeV1.INVALID_ENUM,
            f"{name} must be exactly {enum_type.__name__}",
        )


def _reject(code: SettlementEffectPlanRejectCodeV1, detail: str) -> NoReturn:
    raise SettlementEffectPlanValidationError(code, detail)
