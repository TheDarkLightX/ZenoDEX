"""Exact transition-local zUSD debt, supply, and fee-accrual certificates.

The monetary kernel records borrowing fees as debt and cumulative protocol fee
accrual while the Tau balance table receives only the minted principal.  This
module closes that one-transition accounting relation:

    debt_delta = ledger_supply_delta + protocol_fee_accrual_delta

The certificate deliberately does not assert a whole-system supply invariant.
Other mounted custody domains, fee distribution, and outstanding-claim
settlement require separate certificates and a composition theorem.

The current live bridge accepts only the zero-fee subset until an exact
outstanding-claim and claim-realization lifecycle is mounted.  The fee-bearing
certificate remains the checked target relation for that later refinement.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

ZUSD_SUPPLY_DELTA_SCHEMA_V1: Final = "zenodex/zusd/supply-delta-certificate/v1"
_U256_MAX: Final = (1 << 256) - 1

_CONSTRUCTION_TOKEN_V1 = object()

_MINT_ACTIONS_V1: Final = frozenset({"mint_zusd"})
_BURN_ACTIONS_V1: Final = frozenset({"repay_zusd", "redeem_zusd", "liquidate"})
_STUTTER_ACTIONS_V1: Final = frozenset(
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
_ACTIONS_V1: Final = _MINT_ACTIONS_V1 | _BURN_ACTIONS_V1 | _STUTTER_ACTIONS_V1


class ZUSDSupplyDeltaRejectCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    UNSUPPORTED_ACTION = "unsupported_action"
    NEGATIVE_VALUE = "negative_value"
    VALUE_EXCEEDS_U256 = "value_exceeds_u256"
    FEE_ACCRUAL_DECREASED = "fee_accrual_decreased"
    DELTA_IDENTITY_MISMATCH = "delta_identity_mismatch"
    ACTION_DELTA_INVALID = "action_delta_invalid"
    INVALID_CERTIFICATE = "invalid_certificate"
    EXTERNAL_INSTANCE_MISMATCH = "external_instance_mismatch"


@dataclass(frozen=True, slots=True)
class ZUSDSupplyDeltaRejectV1:
    code: ZUSDSupplyDeltaRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDSupplyDeltaRejectCodeV1:
            raise TypeError("zUSD supply-delta reject code must be exact")
        if type(self.path) is not tuple or not self.path:
            raise TypeError("zUSD supply-delta reject path must be a nonempty tuple")
        if any(type(part) is not str or not part for part in self.path):
            raise TypeError("zUSD supply-delta reject path parts must be nonempty strings")


def _require_action_v1(action: object) -> str:
    if type(action) is not str:
        raise TypeError("action must be an exact string")
    if action not in _ACTIONS_V1:
        raise ValueError("unsupported zUSD supply-delta action")
    return action


def _require_u256_v1(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact int")
    exact = value
    if exact < 0:
        raise ArithmeticError(f"{name} must be nonnegative")
    if exact > _U256_MAX:
        raise OverflowError(f"{name} exceeds U256")
    return exact


def _body_v1(certificate: "ZUSDSupplyDeltaCertificateV1") -> dict[str, object]:
    return {
        "schema": ZUSD_SUPPLY_DELTA_SCHEMA_V1,
        "version": 1,
        "action": certificate.action,
        "debt_pre_e8": certificate.debt_pre_e8,
        "debt_post_e8": certificate.debt_post_e8,
        "ledger_supply_pre_e8": certificate.ledger_supply_pre_e8,
        "ledger_supply_post_e8": certificate.ledger_supply_post_e8,
        "protocol_fee_accrual_pre_e8": certificate.protocol_fee_accrual_pre_e8,
        "protocol_fee_accrual_post_e8": certificate.protocol_fee_accrual_post_e8,
    }


def _certificate_root_v1(certificate: "ZUSDSupplyDeltaCertificateV1") -> str:
    preimage = domain_sep_bytes("zusd/supply-delta-certificate", version=1) + canonical_json_bytes(
        _body_v1(certificate)
    )
    return cast(str, sha256_hex(preimage))


def _validate_delta_laws_v1(certificate: "ZUSDSupplyDeltaCertificateV1") -> None:
    debt_delta = certificate.debt_delta_e8
    supply_delta = certificate.ledger_supply_delta_e8
    fee_delta = certificate.protocol_fee_accrual_delta_e8
    if fee_delta < 0:
        raise ArithmeticError(ZUSDSupplyDeltaRejectCodeV1.FEE_ACCRUAL_DECREASED.value)
    if debt_delta != supply_delta + fee_delta:
        raise ArithmeticError(ZUSDSupplyDeltaRejectCodeV1.DELTA_IDENTITY_MISMATCH.value)
    if certificate.action in _MINT_ACTIONS_V1:
        if debt_delta <= 0 or supply_delta <= 0:
            raise ArithmeticError(ZUSDSupplyDeltaRejectCodeV1.ACTION_DELTA_INVALID.value)
        return
    if certificate.action in _BURN_ACTIONS_V1:
        if debt_delta >= 0 or supply_delta >= 0 or fee_delta != 0:
            raise ArithmeticError(ZUSDSupplyDeltaRejectCodeV1.ACTION_DELTA_INVALID.value)
        return
    if debt_delta != 0 or supply_delta != 0 or fee_delta != 0:
        raise ArithmeticError(ZUSDSupplyDeltaRejectCodeV1.ACTION_DELTA_INVALID.value)


@dataclass(frozen=True, slots=True)
class ZUSDSupplyDeltaCertificateV1:
    """Verifier-created certificate for one externally supplied transition."""

    action: str
    debt_pre_e8: int
    debt_post_e8: int
    ledger_supply_pre_e8: int
    ledger_supply_post_e8: int
    protocol_fee_accrual_pre_e8: int
    protocol_fee_accrual_post_e8: int
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _CONSTRUCTION_TOKEN_V1:
            raise TypeError("zUSD supply-delta certificates require controlled derivation")
        _require_action_v1(self.action)
        for name in (
            "debt_pre_e8",
            "debt_post_e8",
            "ledger_supply_pre_e8",
            "ledger_supply_post_e8",
            "protocol_fee_accrual_pre_e8",
            "protocol_fee_accrual_post_e8",
        ):
            _require_u256_v1(name, object.__getattribute__(self, name))
        _validate_delta_laws_v1(self)

    @property
    def debt_delta_e8(self) -> int:
        return self.debt_post_e8 - self.debt_pre_e8

    @property
    def ledger_supply_delta_e8(self) -> int:
        return self.ledger_supply_post_e8 - self.ledger_supply_pre_e8

    @property
    def protocol_fee_accrual_delta_e8(self) -> int:
        return self.protocol_fee_accrual_post_e8 - self.protocol_fee_accrual_pre_e8

    @property
    def certificate_root(self) -> str:
        return _certificate_root_v1(self)

    def to_obj(self) -> dict[str, object]:
        return {
            **_body_v1(self),
            "debt_delta_e8": self.debt_delta_e8,
            "ledger_supply_delta_e8": self.ledger_supply_delta_e8,
            "protocol_fee_accrual_delta_e8": self.protocol_fee_accrual_delta_e8,
            "certificate_root": self.certificate_root,
        }


ZUSDSupplyDeltaResultV1: TypeAlias = ZUSDSupplyDeltaCertificateV1 | ZUSDSupplyDeltaRejectV1


def _reject_v1(code: ZUSDSupplyDeltaRejectCodeV1, *path: str) -> ZUSDSupplyDeltaRejectV1:
    return ZUSDSupplyDeltaRejectV1(code=code, path=tuple(path))


def derive_zusd_supply_delta_certificate_v1(
    *,
    action: object,
    debt_pre_e8: object,
    debt_post_e8: object,
    ledger_supply_pre_e8: object,
    ledger_supply_post_e8: object,
    protocol_fee_accrual_pre_e8: object,
    protocol_fee_accrual_post_e8: object,
) -> ZUSDSupplyDeltaResultV1:
    """Derive a certificate from exact source values or return a typed reject."""

    try:
        exact_action = _require_action_v1(action)
    except TypeError:
        return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.WRONG_EXACT_TYPE, "action")
    except ValueError:
        return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.UNSUPPORTED_ACTION, "action")

    names_and_values = (
        ("debt_pre_e8", debt_pre_e8),
        ("debt_post_e8", debt_post_e8),
        ("ledger_supply_pre_e8", ledger_supply_pre_e8),
        ("ledger_supply_post_e8", ledger_supply_post_e8),
        ("protocol_fee_accrual_pre_e8", protocol_fee_accrual_pre_e8),
        ("protocol_fee_accrual_post_e8", protocol_fee_accrual_post_e8),
    )
    checked: dict[str, int] = {}
    for name, value in names_and_values:
        try:
            checked[name] = _require_u256_v1(name, value)
        except TypeError:
            return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.WRONG_EXACT_TYPE, name)
        except OverflowError:
            return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.VALUE_EXCEEDS_U256, name)
        except ArithmeticError:
            return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.NEGATIVE_VALUE, name)

    try:
        return ZUSDSupplyDeltaCertificateV1(
            action=exact_action,
            **checked,
            _construction_token=_CONSTRUCTION_TOKEN_V1,
        )
    except ArithmeticError as exc:
        try:
            code = ZUSDSupplyDeltaRejectCodeV1(str(exc))
        except ValueError:
            code = ZUSDSupplyDeltaRejectCodeV1.INVALID_CERTIFICATE
        return _reject_v1(code, "delta")


def verify_zusd_supply_delta_certificate_v1(
    *,
    expected_action: object,
    expected_debt_pre_e8: object,
    expected_debt_post_e8: object,
    expected_ledger_supply_pre_e8: object,
    expected_ledger_supply_post_e8: object,
    expected_protocol_fee_accrual_pre_e8: object,
    expected_protocol_fee_accrual_post_e8: object,
    certificate: object,
) -> ZUSDSupplyDeltaResultV1:
    """Verify one certificate against the exact externally supplied transition."""

    if type(certificate) is not ZUSDSupplyDeltaCertificateV1:
        return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.INVALID_CERTIFICATE, "certificate")
    exact_certificate = certificate
    expected_fields = (
        expected_action,
        expected_debt_pre_e8,
        expected_debt_post_e8,
        expected_ledger_supply_pre_e8,
        expected_ledger_supply_post_e8,
        expected_protocol_fee_accrual_pre_e8,
        expected_protocol_fee_accrual_post_e8,
    )
    actual_fields = (
        exact_certificate.action,
        exact_certificate.debt_pre_e8,
        exact_certificate.debt_post_e8,
        exact_certificate.ledger_supply_pre_e8,
        exact_certificate.ledger_supply_post_e8,
        exact_certificate.protocol_fee_accrual_pre_e8,
        exact_certificate.protocol_fee_accrual_post_e8,
    )
    if expected_fields != actual_fields or any(
        type(expected) is not type(actual)
        for expected, actual in zip(expected_fields, actual_fields, strict=True)
    ):
        return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH, "instance")

    rebuilt = derive_zusd_supply_delta_certificate_v1(
        action=expected_action,
        debt_pre_e8=expected_debt_pre_e8,
        debt_post_e8=expected_debt_post_e8,
        ledger_supply_pre_e8=expected_ledger_supply_pre_e8,
        ledger_supply_post_e8=expected_ledger_supply_post_e8,
        protocol_fee_accrual_pre_e8=expected_protocol_fee_accrual_pre_e8,
        protocol_fee_accrual_post_e8=expected_protocol_fee_accrual_post_e8,
    )
    if type(rebuilt) is not ZUSDSupplyDeltaCertificateV1 or rebuilt != exact_certificate:
        return _reject_v1(ZUSDSupplyDeltaRejectCodeV1.INVALID_CERTIFICATE, "certificate")
    return exact_certificate


__all__ = [
    "ZUSD_SUPPLY_DELTA_SCHEMA_V1",
    "ZUSDSupplyDeltaCertificateV1",
    "ZUSDSupplyDeltaRejectCodeV1",
    "ZUSDSupplyDeltaRejectV1",
    "ZUSDSupplyDeltaResultV1",
    "derive_zusd_supply_delta_certificate_v1",
    "verify_zusd_supply_delta_certificate_v1",
]
