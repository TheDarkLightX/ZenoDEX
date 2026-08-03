"""V2 transition certificate for zUSD debt, ledger supply, and current claim.

The exact transition-local conservation relation is:

    debt_delta = ledger_supply_delta + outstanding_claim_delta

Unlike the historical V1 certificate, this relation remains correct when a
current protocol-fee claim is later settled into ledger supply.  It does not
authenticate custody, prove the global supply inventory complete, or authorize
publication.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)
from .zusd_protocol_fee_claim import (
    ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
    ZUSDProtocolFeeClaimV1,
    decode_zusd_protocol_fee_claim_v1,
)

ZUSD_SUPPLY_CLAIM_DELTA_SCHEMA_V2: Final = "zenodex/zusd/supply-claim-delta-certificate/v2"
_U256_MAX: Final = (1 << 256) - 1
_CONSTRUCTION_TOKEN_V2 = object()

_MINT_ACTIONS_V2: Final = frozenset({"mint_zusd"})
_BURN_ACTIONS_V2: Final = frozenset({"repay_zusd", "redeem_zusd", "liquidate"})
_SETTLEMENT_ACTIONS_V2: Final = frozenset({"settle_protocol_fee_claim"})
_STUTTER_ACTIONS_V2: Final = frozenset(
    {
        "advance_epoch",
        "bootstrap_oracle",
        "oracle_report",
        "oracle_commit",
        "deposit_collateral",
        "withdraw_collateral",
        "deposit_sp",
        "withdraw_sp",
        "claim_sp_collateral",
    }
)
_ACTIONS_V2: Final = (
    _MINT_ACTIONS_V2 | _BURN_ACTIONS_V2 | _SETTLEMENT_ACTIONS_V2 | _STUTTER_ACTIONS_V2
)


class ZUSDSupplyClaimDeltaRejectCodeV2(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    UNSUPPORTED_ACTION = "unsupported_action"
    NEGATIVE_VALUE = "negative_value"
    VALUE_EXCEEDS_U256 = "value_exceeds_u256"
    INVALID_CLAIM_IDENTITY = "invalid_claim_identity"
    INVALID_CLAIM_STATE = "invalid_claim_state"
    INVALID_CLAIM_ROOT = "invalid_claim_root"
    DELTA_IDENTITY_MISMATCH = "delta_identity_mismatch"
    ACTION_DELTA_INVALID = "action_delta_invalid"
    INVALID_CERTIFICATE = "invalid_certificate"
    EXTERNAL_INSTANCE_MISMATCH = "external_instance_mismatch"


@dataclass(frozen=True, slots=True)
class ZUSDSupplyClaimDeltaRejectV2:
    code: ZUSDSupplyClaimDeltaRejectCodeV2
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDSupplyClaimDeltaRejectCodeV2:
            raise TypeError("zUSD supply-claim reject code must be exact")
        if type(self.path) is not tuple or not self.path:
            raise TypeError("zUSD supply-claim reject path must be a nonempty tuple")
        if any(type(part) is not str or not part for part in self.path):
            raise TypeError("zUSD supply-claim reject path parts must be nonempty strings")


def _require_action_v2(action: object) -> str:
    if type(action) is not str:
        raise TypeError("action must be an exact string")
    if action not in _ACTIONS_V2:
        raise ValueError("unsupported zUSD supply-claim action")
    return action


def _require_u256_v2(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact int")
    exact = value
    if exact < 0:
        raise ArithmeticError(f"{name} must be nonnegative")
    if exact > _U256_MAX:
        raise OverflowError(f"{name} exceeds U256")
    return exact


def _require_claim_asset_v2(value: object) -> str:
    if type(value) is not str:
        raise TypeError("claim_asset_id must be an exact string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name="claim_asset_id")
    if value != canonical:
        raise ValueError("claim_asset_id must be canonical")
    return canonical


def _require_claim_custody_v2(value: object) -> str:
    if type(value) is not str:
        raise TypeError("claim_custody_pubkey must be an exact string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name="claim_custody_pubkey")
    if value != canonical:
        raise ValueError("claim_custody_pubkey must be canonical")
    return canonical


def _require_claim_root_v2(name: str, value: object) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be an exact string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical")
    return canonical


def _require_claim_state_v2(name: str, value: object) -> ZUSDProtocolFeeClaimV1:
    if type(value) is not ZUSDProtocolFeeClaimV1:
        raise TypeError(f"{name} must be an exact ZUSDProtocolFeeClaimV1")
    try:
        rebuilt = decode_zusd_protocol_fee_claim_v1(
            {
                "schema": ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
                "version": 1,
                "asset_id": value.asset_id,
                "custody_pubkey": value.custody_pubkey,
                "outstanding_e8": value.outstanding_e8,
                "accrued_cumulative_e8": value.accrued_cumulative_e8,
            }
        )
    except (ArithmeticError, OverflowError, TypeError, ValueError) as exc:
        raise ValueError(f"{name} is not a valid claim state") from exc
    if rebuilt != value or rebuilt.state_root != value.state_root:
        raise ValueError(f"{name} does not reconstruct exactly")
    return value


def _claim_transition_matches_action_v2(
    action: str,
    pre_claim: ZUSDProtocolFeeClaimV1,
    post_claim: ZUSDProtocolFeeClaimV1,
) -> bool:
    if (pre_claim.asset_id, pre_claim.custody_pubkey) != (
        post_claim.asset_id,
        post_claim.custody_pubkey,
    ):
        return False
    if action in _MINT_ACTIONS_V2:
        if post_claim.outstanding_e8 < pre_claim.outstanding_e8:
            return False
        claim_delta = post_claim.outstanding_e8 - pre_claim.outstanding_e8
        return post_claim.accrued_cumulative_e8 == pre_claim.accrued_cumulative_e8 + claim_delta
    if action in _SETTLEMENT_ACTIONS_V2:
        return (
            post_claim.outstanding_e8 < pre_claim.outstanding_e8
            and post_claim.accrued_cumulative_e8 == pre_claim.accrued_cumulative_e8
        )
    return post_claim == pre_claim


def _body_v2(certificate: "ZUSDSupplyClaimDeltaCertificateV2") -> dict[str, object]:
    return {
        "schema": ZUSD_SUPPLY_CLAIM_DELTA_SCHEMA_V2,
        "version": 2,
        "action": certificate.action,
        "claim_asset_id": certificate.claim_asset_id,
        "claim_custody_pubkey": certificate.claim_custody_pubkey,
        "claim_pre_root": certificate.claim_pre_root,
        "claim_post_root": certificate.claim_post_root,
        "debt_pre_e8": certificate.debt_pre_e8,
        "debt_post_e8": certificate.debt_post_e8,
        "ledger_supply_pre_e8": certificate.ledger_supply_pre_e8,
        "ledger_supply_post_e8": certificate.ledger_supply_post_e8,
        "outstanding_claim_pre_e8": certificate.outstanding_claim_pre_e8,
        "outstanding_claim_post_e8": certificate.outstanding_claim_post_e8,
    }


def _validate_delta_laws_v2(certificate: "ZUSDSupplyClaimDeltaCertificateV2") -> None:
    debt_delta = certificate.debt_delta_e8
    supply_delta = certificate.ledger_supply_delta_e8
    claim_delta = certificate.outstanding_claim_delta_e8
    if debt_delta != supply_delta + claim_delta:
        raise ArithmeticError(ZUSDSupplyClaimDeltaRejectCodeV2.DELTA_IDENTITY_MISMATCH.value)
    if certificate.action in _MINT_ACTIONS_V2:
        if debt_delta <= 0 or supply_delta <= 0 or claim_delta < 0:
            raise ArithmeticError(ZUSDSupplyClaimDeltaRejectCodeV2.ACTION_DELTA_INVALID.value)
        return
    if certificate.action in _BURN_ACTIONS_V2:
        if debt_delta >= 0 or supply_delta >= 0 or claim_delta != 0:
            raise ArithmeticError(ZUSDSupplyClaimDeltaRejectCodeV2.ACTION_DELTA_INVALID.value)
        return
    if certificate.action in _SETTLEMENT_ACTIONS_V2:
        if debt_delta != 0 or supply_delta <= 0 or claim_delta >= 0:
            raise ArithmeticError(ZUSDSupplyClaimDeltaRejectCodeV2.ACTION_DELTA_INVALID.value)
        return
    if debt_delta != 0 or supply_delta != 0 or claim_delta != 0:
        raise ArithmeticError(ZUSDSupplyClaimDeltaRejectCodeV2.ACTION_DELTA_INVALID.value)


@dataclass(frozen=True, slots=True)
class ZUSDSupplyClaimDeltaCertificateV2:
    """Verifier-created certificate for one externally supplied transition."""

    action: str
    claim_asset_id: str
    claim_custody_pubkey: str
    claim_pre_root: str
    claim_post_root: str
    debt_pre_e8: int
    debt_post_e8: int
    ledger_supply_pre_e8: int
    ledger_supply_post_e8: int
    outstanding_claim_pre_e8: int
    outstanding_claim_post_e8: int
    _construction_token: InitVar[object] = None

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _CONSTRUCTION_TOKEN_V2:
            raise TypeError("zUSD supply-claim certificates require controlled derivation")
        _require_action_v2(self.action)
        _require_claim_asset_v2(self.claim_asset_id)
        _require_claim_custody_v2(self.claim_custody_pubkey)
        _require_claim_root_v2("claim_pre_root", self.claim_pre_root)
        _require_claim_root_v2("claim_post_root", self.claim_post_root)
        for name in (
            "debt_pre_e8",
            "debt_post_e8",
            "ledger_supply_pre_e8",
            "ledger_supply_post_e8",
            "outstanding_claim_pre_e8",
            "outstanding_claim_post_e8",
        ):
            _require_u256_v2(name, object.__getattribute__(self, name))
        _validate_delta_laws_v2(self)

    @property
    def debt_delta_e8(self) -> int:
        return self.debt_post_e8 - self.debt_pre_e8

    @property
    def ledger_supply_delta_e8(self) -> int:
        return self.ledger_supply_post_e8 - self.ledger_supply_pre_e8

    @property
    def outstanding_claim_delta_e8(self) -> int:
        return self.outstanding_claim_post_e8 - self.outstanding_claim_pre_e8

    @property
    def certificate_root(self) -> str:
        preimage = domain_sep_bytes(
            "zusd/supply-claim-delta-certificate", version=2
        ) + canonical_json_bytes(_body_v2(self))
        return cast(str, sha256_hex(preimage))

    def to_obj(self) -> dict[str, object]:
        return {
            **_body_v2(self),
            "debt_delta_e8": self.debt_delta_e8,
            "ledger_supply_delta_e8": self.ledger_supply_delta_e8,
            "outstanding_claim_delta_e8": self.outstanding_claim_delta_e8,
            "certificate_root": self.certificate_root,
        }


ZUSDSupplyClaimDeltaResultV2: TypeAlias = (
    ZUSDSupplyClaimDeltaCertificateV2 | ZUSDSupplyClaimDeltaRejectV2
)


def _reject_v2(code: ZUSDSupplyClaimDeltaRejectCodeV2, *path: str) -> ZUSDSupplyClaimDeltaRejectV2:
    return ZUSDSupplyClaimDeltaRejectV2(code=code, path=tuple(path))


def derive_zusd_supply_claim_delta_certificate_v2(
    *,
    action: object,
    pre_claim: object,
    post_claim: object,
    debt_pre_e8: object,
    debt_post_e8: object,
    ledger_supply_pre_e8: object,
    ledger_supply_post_e8: object,
) -> ZUSDSupplyClaimDeltaResultV2:
    """Derive a V2 certificate from exact source values or return a typed reject."""

    try:
        exact_action = _require_action_v2(action)
    except TypeError:
        return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.WRONG_EXACT_TYPE, "action")
    except ValueError:
        return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.UNSUPPORTED_ACTION, "action")

    try:
        exact_pre_claim = _require_claim_state_v2("pre_claim", pre_claim)
        exact_post_claim = _require_claim_state_v2("post_claim", post_claim)
    except TypeError:
        return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.WRONG_EXACT_TYPE, "claim")
    except ValueError:
        return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.INVALID_CLAIM_STATE, "claim")
    if (exact_pre_claim.asset_id, exact_pre_claim.custody_pubkey) != (
        exact_post_claim.asset_id,
        exact_post_claim.custody_pubkey,
    ):
        return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.INVALID_CLAIM_IDENTITY, "claim_identity")
    if not _claim_transition_matches_action_v2(
        exact_action,
        exact_pre_claim,
        exact_post_claim,
    ):
        return _reject_v2(
            ZUSDSupplyClaimDeltaRejectCodeV2.ACTION_DELTA_INVALID,
            "claim_transition",
        )

    names_and_values = (
        ("debt_pre_e8", debt_pre_e8),
        ("debt_post_e8", debt_post_e8),
        ("ledger_supply_pre_e8", ledger_supply_pre_e8),
        ("ledger_supply_post_e8", ledger_supply_post_e8),
        ("outstanding_claim_pre_e8", exact_pre_claim.outstanding_e8),
        ("outstanding_claim_post_e8", exact_post_claim.outstanding_e8),
    )
    checked: dict[str, int] = {}
    for name, value in names_and_values:
        try:
            checked[name] = _require_u256_v2(name, value)
        except TypeError:
            return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.WRONG_EXACT_TYPE, name)
        except OverflowError:
            return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.VALUE_EXCEEDS_U256, name)
        except ArithmeticError:
            return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.NEGATIVE_VALUE, name)

    try:
        return ZUSDSupplyClaimDeltaCertificateV2(
            action=exact_action,
            claim_asset_id=exact_pre_claim.asset_id,
            claim_custody_pubkey=exact_pre_claim.custody_pubkey,
            claim_pre_root=exact_pre_claim.state_root,
            claim_post_root=exact_post_claim.state_root,
            **checked,
            _construction_token=_CONSTRUCTION_TOKEN_V2,
        )
    except ArithmeticError as exc:
        try:
            code = ZUSDSupplyClaimDeltaRejectCodeV2(str(exc))
        except ValueError:
            code = ZUSDSupplyClaimDeltaRejectCodeV2.INVALID_CERTIFICATE
        return _reject_v2(code, "delta")


def verify_zusd_supply_claim_delta_certificate_v2(
    *,
    expected_action: object,
    expected_pre_claim: object,
    expected_post_claim: object,
    expected_debt_pre_e8: object,
    expected_debt_post_e8: object,
    expected_ledger_supply_pre_e8: object,
    expected_ledger_supply_post_e8: object,
    certificate: object,
) -> ZUSDSupplyClaimDeltaResultV2:
    """Verify one V2 certificate against the exact external transition instance."""

    if type(certificate) is not ZUSDSupplyClaimDeltaCertificateV2:
        return _reject_v2(ZUSDSupplyClaimDeltaRejectCodeV2.INVALID_CERTIFICATE, "certificate")
    rebuilt = derive_zusd_supply_claim_delta_certificate_v2(
        action=expected_action,
        pre_claim=expected_pre_claim,
        post_claim=expected_post_claim,
        debt_pre_e8=expected_debt_pre_e8,
        debt_post_e8=expected_debt_post_e8,
        ledger_supply_pre_e8=expected_ledger_supply_pre_e8,
        ledger_supply_post_e8=expected_ledger_supply_post_e8,
    )
    if type(rebuilt) is not ZUSDSupplyClaimDeltaCertificateV2:
        return _reject_v2(
            ZUSDSupplyClaimDeltaRejectCodeV2.EXTERNAL_INSTANCE_MISMATCH,
            "instance",
        )
    if rebuilt != certificate:
        return _reject_v2(
            ZUSDSupplyClaimDeltaRejectCodeV2.EXTERNAL_INSTANCE_MISMATCH,
            "instance",
        )
    return certificate


__all__ = [
    "ZUSD_SUPPLY_CLAIM_DELTA_SCHEMA_V2",
    "ZUSDSupplyClaimDeltaCertificateV2",
    "ZUSDSupplyClaimDeltaRejectCodeV2",
    "ZUSDSupplyClaimDeltaRejectV2",
    "ZUSDSupplyClaimDeltaResultV2",
    "derive_zusd_supply_claim_delta_certificate_v2",
    "verify_zusd_supply_claim_delta_certificate_v2",
]
