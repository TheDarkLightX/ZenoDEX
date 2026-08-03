"""Internal exact-source validation for zUSD fee-claim realization V1."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final, cast

from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.state_snapshot_values import CommittedBalanceTableV1
from ..state.state_transitions import (
    BalanceDeltaV1,
    BalancePatchApplyOkV1,
    BalancePatchRejectV1,
    CanonicalBalancePatchV1,
    apply_balance_deltas_v1,
    validate_committed_balance_state_v1,
)
from .zusd_protocol_fee_claim import (
    ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
    ZUSDProtocolFeeClaimV1,
    decode_zusd_protocol_fee_claim_v1,
)
from .zusd_protocol_fee_claim_realization_values import (
    ZUSD_LEDGER_UNIT_E8_V1,
    ZUSDProtocolFeeClaimRealizationRejectCodeV1,
    ZUSDProtocolFeeClaimRealizationRejectV1,
    ZUSDProtocolFeeClaimRealizationSourceV1,
    _reject_v1,
)

U256_MAX_V1: Final = (1 << 256) - 1
_MAX_LEDGER_UNITS: Final = U256_MAX_V1 // ZUSD_LEDGER_UNIT_E8_V1


def _canonical_asset_id_v1(value: object) -> str:
    if type(value) is not str:
        raise TypeError("asset_id must be an exact string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name="asset_id")
    if value != canonical:
        raise ValueError("asset_id must be canonical")
    return cast(str, canonical)


def _canonical_custody_pubkey_v1(value: object) -> str:
    if type(value) is not str:
        raise TypeError("custody_pubkey must be an exact string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name="custody_pubkey")
    if value != canonical:
        raise ValueError("custody_pubkey must be canonical")
    return cast(str, canonical)


def _require_u256_v1(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact int")
    if value < 0:
        raise ArithmeticError(f"{name} must be nonnegative")
    if value > U256_MAX_V1:
        raise OverflowError(f"{name} exceeds U256")
    return value


def _validated_claim_v1(
    value: object,
) -> ZUSDProtocolFeeClaimV1 | ZUSDProtocolFeeClaimRealizationRejectV1:
    if type(value) is not ZUSDProtocolFeeClaimV1:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE,
            "pre_claim",
        )
    claim = cast(ZUSDProtocolFeeClaimV1, value)
    try:
        rebuilt = decode_zusd_protocol_fee_claim_v1(
            {
                "schema": ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
                "version": 1,
                "asset_id": claim.asset_id,
                "custody_pubkey": claim.custody_pubkey,
                "outstanding_e8": claim.outstanding_e8,
                "accrued_cumulative_e8": claim.accrued_cumulative_e8,
            }
        )
    except (ArithmeticError, OverflowError, TypeError, ValueError):
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_CLAIM_STATE,
            "pre_claim",
        )
    if rebuilt != claim or rebuilt.state_root != claim.state_root:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_CLAIM_STATE,
            "pre_claim",
        )
    return claim


def _validated_balances_v1(
    value: object,
) -> CommittedBalanceTableV1 | ZUSDProtocolFeeClaimRealizationRejectV1:
    if type(value) is not CommittedBalanceTableV1:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE,
            "pre_balances",
        )
    balances = cast(CommittedBalanceTableV1, value)
    if validate_committed_balance_state_v1(balances) is not None:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_PRESTATE,
            "pre_balances",
        )
    return balances


def ledger_supply_e8_v1(
    balances: CommittedBalanceTableV1,
    asset_id: str,
) -> int | ZUSDProtocolFeeClaimRealizationRejectV1:
    total_units = 0
    for (_pubkey, asset), amount in balances.entries:
        if asset != asset_id:
            continue
        if amount > _MAX_LEDGER_UNITS - total_units:
            return _reject_v1(
                ZUSDProtocolFeeClaimRealizationRejectCodeV1.LEDGER_SUPPLY_OVERFLOW,
                "ledger_supply",
            )
        total_units += amount
    return total_units * ZUSD_LEDGER_UNIT_E8_V1


def _validated_amount_v1(
    value: object,
    *,
    outstanding_e8: int,
) -> int | ZUSDProtocolFeeClaimRealizationRejectV1:
    try:
        amount_e8 = _require_u256_v1("amount_e8", value)
    except TypeError:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE,
            "amount_e8",
        )
    except OverflowError:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.VALUE_EXCEEDS_U256,
            "amount_e8",
        )
    except ArithmeticError:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.NEGATIVE_VALUE,
            "amount_e8",
        )
    if amount_e8 == 0:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.ZERO_AMOUNT,
            "amount_e8",
        )
    if amount_e8 % ZUSD_LEDGER_UNIT_E8_V1 != 0:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.NON_WHOLE_AMOUNT,
            "amount_e8",
        )
    if amount_e8 > outstanding_e8:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.AMOUNT_EXCEEDS_OUTSTANDING,
            "amount_e8",
        )
    return amount_e8


def _validated_debt_v1(
    value: object,
) -> int | ZUSDProtocolFeeClaimRealizationRejectV1:
    try:
        return _require_u256_v1("debt_e8", value)
    except TypeError:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE,
            "debt_e8",
        )
    except OverflowError:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.VALUE_EXCEEDS_U256,
            "debt_e8",
        )
    except ArithmeticError:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.NEGATIVE_VALUE,
            "debt_e8",
        )


@dataclass(frozen=True, slots=True)
class ValidatedRealizationSourceV1:
    asset_id: str
    custody_pubkey: str
    claim: ZUSDProtocolFeeClaimV1
    balances: CommittedBalanceTableV1
    debt_e8: int
    amount_e8: int


def validate_realization_source_v1(
    value: object,
) -> ValidatedRealizationSourceV1 | ZUSDProtocolFeeClaimRealizationRejectV1:
    if type(value) is not ZUSDProtocolFeeClaimRealizationSourceV1:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.WRONG_EXACT_TYPE,
            "source",
        )
    source = value
    try:
        asset_id = _canonical_asset_id_v1(source.asset_id)
        custody_pubkey = _canonical_custody_pubkey_v1(source.custody_pubkey)
    except (TypeError, ValueError):
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_IDENTITY,
            "identity",
        )
    claim = _validated_claim_v1(source.pre_claim)
    if type(claim) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return claim
    if (claim.asset_id, claim.custody_pubkey) != (asset_id, custody_pubkey):
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
            "identity",
        )
    balances = _validated_balances_v1(source.pre_balances)
    if type(balances) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return balances
    debt_e8 = _validated_debt_v1(source.debt_e8)
    if type(debt_e8) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return debt_e8
    amount_e8 = _validated_amount_v1(source.amount_e8, outstanding_e8=claim.outstanding_e8)
    if type(amount_e8) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return amount_e8
    return ValidatedRealizationSourceV1(
        asset_id,
        custody_pubkey,
        claim,
        balances,
        debt_e8,
        amount_e8,
    )


def apply_escrow_credit_v1(
    pre_balances: CommittedBalanceTableV1,
    *,
    custody_pubkey: str,
    asset_id: str,
    amount_units: int,
) -> (
    tuple[CommittedBalanceTableV1, CanonicalBalancePatchV1]
    | ZUSDProtocolFeeClaimRealizationRejectV1
):
    try:
        delta = BalanceDeltaV1((custody_pubkey, asset_id), amount_units)
    except (TypeError, ValueError):
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.BALANCE_TRANSITION,
            "balance_delta",
        )
    applied = apply_balance_deltas_v1(pre_balances, (delta,))
    if type(applied) is BalancePatchRejectV1:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.BALANCE_TRANSITION,
            "balance_patch",
            applied.code.value,
        )
    exact = cast(BalancePatchApplyOkV1, applied)
    if type(exact.patch) is not CanonicalBalancePatchV1:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.BALANCE_TRANSITION,
            "balance_patch",
        )
    return exact.state, exact.patch


__all__ = (
    "U256_MAX_V1",
    "ValidatedRealizationSourceV1",
    "apply_escrow_credit_v1",
    "ledger_supply_e8_v1",
    "validate_realization_source_v1",
)
