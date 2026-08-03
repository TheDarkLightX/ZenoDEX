"""Immutable current-liability state for zUSD borrowing fees.

The zUSD debt kernel records cumulative protocol revenue.  A cumulative counter
does not identify the amount that remains unissued.  This module owns that
current amount as an exact claim:

    accrued_cumulative_e8 = outstanding_e8 + realized_cumulative_e8

The transitions are deterministic candidates.  They do not authenticate a fee
policy, credit a ledger account, distribute fees, or publish state.  A mounted
global composition must perform those operations atomically before a settlement
candidate can acquire authority.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, Mapping, TypeAlias, cast

from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)

ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1: Final = "zenodex/zusd/protocol-fee-claim/v1"
ZUSD_PROTOCOL_FEE_CLAIM_TRANSITION_SCHEMA_V1: Final = (
    "zenodex/zusd/protocol-fee-claim-transition/v1"
)

_U256_MAX: Final = (1 << 256) - 1
_STATE_CONSTRUCTION_TOKEN_V1 = object()
_TRANSITION_CONSTRUCTION_TOKEN_V1 = object()
_KINDS_V1: Final = frozenset({"accrue", "settle"})


class ZUSDProtocolFeeClaimRejectCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_IDENTITY = "invalid_identity"
    NEGATIVE_VALUE = "negative_value"
    VALUE_EXCEEDS_U256 = "value_exceeds_u256"
    INVALID_STATE = "invalid_state"
    ZERO_SETTLEMENT = "zero_settlement"
    AMOUNT_EXCEEDS_OUTSTANDING = "amount_exceeds_outstanding"
    EXTERNAL_INSTANCE_MISMATCH = "external_instance_mismatch"
    INVALID_TRANSITION = "invalid_transition"


@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeClaimRejectV1:
    code: ZUSDProtocolFeeClaimRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDProtocolFeeClaimRejectCodeV1:
            raise TypeError("protocol fee claim reject code must be exact")
        if type(self.path) is not tuple or not self.path:
            raise TypeError("protocol fee claim reject path must be a nonempty tuple")
        if any(type(part) is not str or not part for part in self.path):
            raise TypeError("protocol fee claim reject path parts must be nonempty strings")


def _canonical_asset_id_v1(value: object) -> str:
    if type(value) is not str:
        raise TypeError("asset_id must be an exact string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name="asset_id")


def _canonical_custody_pubkey_v1(value: object) -> str:
    if type(value) is not str:
        raise TypeError("custody_pubkey must be an exact string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name="custody_pubkey")


def _require_u256_v1(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact int")
    exact = value
    if exact < 0:
        raise ArithmeticError(f"{name} must be nonnegative")
    if exact > _U256_MAX:
        raise OverflowError(f"{name} exceeds U256")
    return exact


def _state_body_v1(state: "ZUSDProtocolFeeClaimV1") -> dict[str, object]:
    return {
        "schema": ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
        "version": 1,
        "asset_id": state.asset_id,
        "custody_pubkey": state.custody_pubkey,
        "outstanding_e8": state.outstanding_e8,
        "accrued_cumulative_e8": state.accrued_cumulative_e8,
    }


@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeClaimV1:
    """Verifier-created current claim state in E8 base units."""

    asset_id: str
    custody_pubkey: str
    outstanding_e8: int
    accrued_cumulative_e8: int
    _construction_token: InitVar[object] = None

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _STATE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("protocol fee claim states require controlled derivation")
        canonical_asset = _canonical_asset_id_v1(self.asset_id)
        canonical_custody = _canonical_custody_pubkey_v1(self.custody_pubkey)
        if self.asset_id != canonical_asset or self.custody_pubkey != canonical_custody:
            raise ValueError("protocol fee claim identity must be canonical")
        _require_u256_v1("outstanding_e8", self.outstanding_e8)
        _require_u256_v1("accrued_cumulative_e8", self.accrued_cumulative_e8)
        if self.outstanding_e8 > self.accrued_cumulative_e8:
            raise ValueError("outstanding claim exceeds cumulative accrual")

    @property
    def realized_cumulative_e8(self) -> int:
        return self.accrued_cumulative_e8 - self.outstanding_e8

    @property
    def state_root(self) -> str:
        preimage = domain_sep_bytes("zusd/protocol-fee-claim", version=1) + canonical_json_bytes(
            _state_body_v1(self)
        )
        return cast(str, sha256_hex(preimage))

    def to_obj(self) -> dict[str, object]:
        return {
            **_state_body_v1(self),
            "realized_cumulative_e8": self.realized_cumulative_e8,
            "state_root": self.state_root,
        }


def _construct_state_v1(
    *,
    asset_id: str,
    custody_pubkey: str,
    outstanding_e8: int,
    accrued_cumulative_e8: int,
) -> ZUSDProtocolFeeClaimV1:
    return ZUSDProtocolFeeClaimV1(
        asset_id=asset_id,
        custody_pubkey=custody_pubkey,
        outstanding_e8=outstanding_e8,
        accrued_cumulative_e8=accrued_cumulative_e8,
        _construction_token=_STATE_CONSTRUCTION_TOKEN_V1,
    )


def empty_zusd_protocol_fee_claim_v1(
    *, asset_id: object, custody_pubkey: object
) -> ZUSDProtocolFeeClaimV1:
    """Construct the unique empty claim for one exact asset and custody owner."""

    return _construct_state_v1(
        asset_id=_canonical_asset_id_v1(asset_id),
        custody_pubkey=_canonical_custody_pubkey_v1(custody_pubkey),
        outstanding_e8=0,
        accrued_cumulative_e8=0,
    )


def decode_zusd_protocol_fee_claim_v1(obj: object) -> ZUSDProtocolFeeClaimV1:
    """Strictly decode a canonical claim-state object without trusting derived fields."""

    if not isinstance(obj, Mapping):
        raise TypeError("protocol_fee_claim must be an object")
    allowed = {
        "schema",
        "version",
        "asset_id",
        "custody_pubkey",
        "outstanding_e8",
        "accrued_cumulative_e8",
    }
    extra = sorted(set(obj.keys()) - allowed)
    if extra:
        raise ValueError(f"protocol_fee_claim unknown fields: {extra}")
    if obj.get("schema") != ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1:
        raise ValueError("unsupported protocol fee claim schema")
    if type(obj.get("version")) is not int or obj.get("version") != 1:
        raise ValueError("unsupported protocol fee claim version")
    asset_id = _canonical_asset_id_v1(obj.get("asset_id"))
    custody_pubkey = _canonical_custody_pubkey_v1(obj.get("custody_pubkey"))
    outstanding_e8 = _require_u256_v1("outstanding_e8", obj.get("outstanding_e8"))
    accrued_cumulative_e8 = _require_u256_v1(
        "accrued_cumulative_e8", obj.get("accrued_cumulative_e8")
    )
    return _construct_state_v1(
        asset_id=asset_id,
        custody_pubkey=custody_pubkey,
        outstanding_e8=outstanding_e8,
        accrued_cumulative_e8=accrued_cumulative_e8,
    )


def _transition_body_v1(
    transition: "ZUSDProtocolFeeClaimTransitionV1",
) -> dict[str, object]:
    return {
        "schema": ZUSD_PROTOCOL_FEE_CLAIM_TRANSITION_SCHEMA_V1,
        "version": 1,
        "kind": transition.kind,
        "amount_e8": transition.amount_e8,
        "pre_state_root": transition.pre_state.state_root,
        "post_state_root": transition.post_state.state_root,
    }


@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeClaimTransitionV1:
    """Controlled deterministic candidate for one claim-state transition."""

    kind: str
    amount_e8: int
    pre_state: ZUSDProtocolFeeClaimV1
    post_state: ZUSDProtocolFeeClaimV1
    _construction_token: InitVar[object] = None

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _TRANSITION_CONSTRUCTION_TOKEN_V1:
            raise TypeError("protocol fee claim transitions require controlled derivation")
        if type(self.kind) is not str or self.kind not in _KINDS_V1:
            raise TypeError("protocol fee claim transition kind is invalid")
        _require_u256_v1("amount_e8", self.amount_e8)
        if type(self.pre_state) is not ZUSDProtocolFeeClaimV1:
            raise TypeError("pre_state must be an exact protocol fee claim")
        if type(self.post_state) is not ZUSDProtocolFeeClaimV1:
            raise TypeError("post_state must be an exact protocol fee claim")
        if (
            self.pre_state.asset_id,
            self.pre_state.custody_pubkey,
        ) != (
            self.post_state.asset_id,
            self.post_state.custody_pubkey,
        ):
            raise ValueError("protocol fee claim identity changed")
        if self.kind == "accrue":
            if self.post_state.outstanding_e8 != self.pre_state.outstanding_e8 + self.amount_e8:
                raise ValueError("invalid protocol fee claim accrual")
            if (
                self.post_state.accrued_cumulative_e8
                != self.pre_state.accrued_cumulative_e8 + self.amount_e8
            ):
                raise ValueError("invalid cumulative protocol fee accrual")
        else:
            if self.amount_e8 > self.pre_state.outstanding_e8:
                raise ValueError("protocol fee settlement exceeds outstanding claim")
            if self.post_state.outstanding_e8 != self.pre_state.outstanding_e8 - self.amount_e8:
                raise ValueError("invalid protocol fee claim settlement")
            if self.post_state.accrued_cumulative_e8 != self.pre_state.accrued_cumulative_e8:
                raise ValueError("settlement changed cumulative protocol fee accrual")

    @property
    def transition_root(self) -> str:
        preimage = domain_sep_bytes(
            "zusd/protocol-fee-claim-transition", version=1
        ) + canonical_json_bytes(_transition_body_v1(self))
        return cast(str, sha256_hex(preimage))

    def to_obj(self) -> dict[str, object]:
        return {**_transition_body_v1(self), "transition_root": self.transition_root}


ZUSDProtocolFeeClaimResultV1: TypeAlias = (
    ZUSDProtocolFeeClaimTransitionV1 | ZUSDProtocolFeeClaimRejectV1
)


def _reject_v1(code: ZUSDProtocolFeeClaimRejectCodeV1, *path: str) -> ZUSDProtocolFeeClaimRejectV1:
    return ZUSDProtocolFeeClaimRejectV1(code=code, path=tuple(path))


def _derive_transition_v1(
    *,
    kind: str,
    expected_asset_id: object,
    expected_custody_pubkey: object,
    expected_pre_state: object,
    amount_e8: object,
) -> ZUSDProtocolFeeClaimResultV1:
    try:
        asset_id = _canonical_asset_id_v1(expected_asset_id)
        custody_pubkey = _canonical_custody_pubkey_v1(expected_custody_pubkey)
    except (TypeError, ValueError):
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.INVALID_IDENTITY, "identity")
    if type(expected_pre_state) is not ZUSDProtocolFeeClaimV1:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.WRONG_EXACT_TYPE, "pre_state")
    pre_state = expected_pre_state
    if (pre_state.asset_id, pre_state.custody_pubkey) != (asset_id, custody_pubkey):
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH, "identity")
    try:
        amount = _require_u256_v1("amount_e8", amount_e8)
    except TypeError:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.WRONG_EXACT_TYPE, "amount_e8")
    except OverflowError:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.VALUE_EXCEEDS_U256, "amount_e8")
    except ArithmeticError:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.NEGATIVE_VALUE, "amount_e8")

    if kind == "accrue":
        if (
            pre_state.outstanding_e8 > _U256_MAX - amount
            or pre_state.accrued_cumulative_e8 > _U256_MAX - amount
        ):
            return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.VALUE_EXCEEDS_U256, "post_state")
        post_state = _construct_state_v1(
            asset_id=asset_id,
            custody_pubkey=custody_pubkey,
            outstanding_e8=pre_state.outstanding_e8 + amount,
            accrued_cumulative_e8=pre_state.accrued_cumulative_e8 + amount,
        )
    else:
        if amount == 0:
            return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.ZERO_SETTLEMENT, "amount_e8")
        if amount > pre_state.outstanding_e8:
            return _reject_v1(
                ZUSDProtocolFeeClaimRejectCodeV1.AMOUNT_EXCEEDS_OUTSTANDING, "amount_e8"
            )
        post_state = _construct_state_v1(
            asset_id=asset_id,
            custody_pubkey=custody_pubkey,
            outstanding_e8=pre_state.outstanding_e8 - amount,
            accrued_cumulative_e8=pre_state.accrued_cumulative_e8,
        )
    return ZUSDProtocolFeeClaimTransitionV1(
        kind=kind,
        amount_e8=amount,
        pre_state=pre_state,
        post_state=post_state,
        _construction_token=_TRANSITION_CONSTRUCTION_TOKEN_V1,
    )


def accrue_zusd_protocol_fee_claim_v1(
    *,
    expected_asset_id: object,
    expected_custody_pubkey: object,
    expected_pre_state: object,
    amount_e8: object,
) -> ZUSDProtocolFeeClaimResultV1:
    """Accrue an exact fee amount into the current outstanding claim."""

    return _derive_transition_v1(
        kind="accrue",
        expected_asset_id=expected_asset_id,
        expected_custody_pubkey=expected_custody_pubkey,
        expected_pre_state=expected_pre_state,
        amount_e8=amount_e8,
    )


def settle_zusd_protocol_fee_claim_v1(
    *,
    expected_asset_id: object,
    expected_custody_pubkey: object,
    expected_pre_state: object,
    amount_e8: object,
) -> ZUSDProtocolFeeClaimResultV1:
    """Stage claim reduction; global composition must credit the exact ledger amount."""

    return _derive_transition_v1(
        kind="settle",
        expected_asset_id=expected_asset_id,
        expected_custody_pubkey=expected_custody_pubkey,
        expected_pre_state=expected_pre_state,
        amount_e8=amount_e8,
    )


def verify_zusd_protocol_fee_claim_transition_v1(
    *,
    expected_kind: object,
    expected_asset_id: object,
    expected_custody_pubkey: object,
    expected_pre_state: object,
    expected_amount_e8: object,
    transition: object,
) -> ZUSDProtocolFeeClaimResultV1:
    """Rebuild one transition from externally supplied exact source values."""

    if type(transition) is not ZUSDProtocolFeeClaimTransitionV1:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.INVALID_TRANSITION, "transition")
    if type(expected_kind) is not str or expected_kind not in _KINDS_V1:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.WRONG_EXACT_TYPE, "kind")
    if type(expected_pre_state) is not ZUSDProtocolFeeClaimV1:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.WRONG_EXACT_TYPE, "pre_state")
    try:
        expected_identity = (
            _canonical_asset_id_v1(expected_asset_id),
            _canonical_custody_pubkey_v1(expected_custody_pubkey),
        )
    except (TypeError, ValueError):
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.INVALID_IDENTITY, "identity")
    if expected_identity != (
        transition.pre_state.asset_id,
        transition.pre_state.custody_pubkey,
    ):
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH, "identity")
    expected_fields = (
        expected_kind,
        expected_pre_state,
        expected_amount_e8,
    )
    actual_fields = (transition.kind, transition.pre_state, transition.amount_e8)
    if expected_fields != actual_fields or any(
        type(expected) is not type(actual)
        for expected, actual in zip(expected_fields, actual_fields, strict=True)
    ):
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH, "instance")
    rebuilt = _derive_transition_v1(
        kind=expected_kind,
        expected_asset_id=expected_asset_id,
        expected_custody_pubkey=expected_custody_pubkey,
        expected_pre_state=expected_pre_state,
        amount_e8=expected_amount_e8,
    )
    if type(rebuilt) is not ZUSDProtocolFeeClaimTransitionV1 or rebuilt != transition:
        return _reject_v1(ZUSDProtocolFeeClaimRejectCodeV1.INVALID_TRANSITION, "transition")
    return transition


__all__ = [
    "ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1",
    "ZUSD_PROTOCOL_FEE_CLAIM_TRANSITION_SCHEMA_V1",
    "ZUSDProtocolFeeClaimRejectCodeV1",
    "ZUSDProtocolFeeClaimRejectV1",
    "ZUSDProtocolFeeClaimResultV1",
    "ZUSDProtocolFeeClaimTransitionV1",
    "ZUSDProtocolFeeClaimV1",
    "accrue_zusd_protocol_fee_claim_v1",
    "decode_zusd_protocol_fee_claim_v1",
    "empty_zusd_protocol_fee_claim_v1",
    "settle_zusd_protocol_fee_claim_v1",
    "verify_zusd_protocol_fee_claim_transition_v1",
]
