"""Exact unmounted realization of a zUSD fee claim into protocol custody.

One realization candidate owns the complete local transition:

* the exact pre-claim and its deterministic settlement;
* the exact committed pre-balance table and canonical escrow credit patch;
* the protocol-fee credit consumed by the later fee-distribution machine; and
* the V2 debt/supply/current-claim conservation certificate.

The current ledger transport stores whole zUSD units while the monetary kernel
uses E8.  This machine therefore realizes only positive multiples of one whole
zUSD and leaves any smaller residue in the outstanding claim.

This module does not authenticate a fee policy, establish datastore currentness,
publish state, distribute custody, or mount a value-moving entrypoint.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import TypeAlias, cast, final

from ..state.state_snapshot_values import CommittedBalanceTableV1
from ..state.state_transitions import (
    BalancePatchApplyOkV1,
    CanonicalBalancePatchV1,
    apply_canonical_balance_patch_v1,
    validate_committed_balance_state_v1,
)
from ._zusd_protocol_fee_claim_realization_validation import (
    U256_MAX_V1,
    ValidatedRealizationSourceV1,
    apply_escrow_credit_v1,
    ledger_supply_e8_v1,
    validate_realization_source_v1,
)
from .fcis_fee_custody_values import ProtocolFeeCreditV2
from .zusd_protocol_fee_claim import (
    ZUSDProtocolFeeClaimTransitionV1,
    settle_zusd_protocol_fee_claim_v1,
    verify_zusd_protocol_fee_claim_transition_v1,
)
from .zusd_protocol_fee_claim_realization_values import (
    ZUSD_LEDGER_UNIT_E8_V1,
    ZUSD_PROTOCOL_FEE_CLAIM_REALIZATION_SCHEMA_V1,
    ZUSDProtocolFeeClaimRealizationRejectCodeV1,
    ZUSDProtocolFeeClaimRealizationRejectV1,
    ZUSDProtocolFeeClaimRealizationSourceV1,
    _reject_v1,
)
from .zusd_supply_claim_delta_certificate import (
    ZUSDSupplyClaimDeltaCertificateV2,
    ZUSDSupplyClaimDeltaRejectV2,
    derive_zusd_supply_claim_delta_certificate_v2,
    verify_zusd_supply_claim_delta_certificate_v2,
)

_CONSTRUCTION_TOKEN_V1 = object()


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeClaimRealizationV1:
    """Controlled local candidate for claim reduction plus escrow issuance."""

    claim_transition: ZUSDProtocolFeeClaimTransitionV1
    pre_balances: CommittedBalanceTableV1
    post_balances: CommittedBalanceTableV1
    balance_patch: CanonicalBalancePatchV1
    protocol_fee_credit: ProtocolFeeCreditV2
    supply_claim_certificate: ZUSDSupplyClaimDeltaCertificateV2
    _construction_token: InitVar[object] = None

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _CONSTRUCTION_TOKEN_V1:
            raise TypeError("fee-claim realizations require controlled derivation")
        if type(self.claim_transition) is not ZUSDProtocolFeeClaimTransitionV1:
            raise TypeError("claim_transition must be exact")
        if type(self.pre_balances) is not CommittedBalanceTableV1:
            raise TypeError("pre_balances must be exact")
        if type(self.post_balances) is not CommittedBalanceTableV1:
            raise TypeError("post_balances must be exact")
        if type(self.balance_patch) is not CanonicalBalancePatchV1:
            raise TypeError("balance_patch must be exact")
        if type(self.protocol_fee_credit) is not ProtocolFeeCreditV2:
            raise TypeError("protocol_fee_credit must be exact")
        if type(self.supply_claim_certificate) is not ZUSDSupplyClaimDeltaCertificateV2:
            raise TypeError("supply_claim_certificate must be exact")
        _require_realization_consistency_v1(self)

    @property
    def amount_e8(self) -> int:
        return cast(int, self.claim_transition.amount_e8)

    @property
    def amount_units(self) -> int:
        return self.amount_e8 // ZUSD_LEDGER_UNIT_E8_V1


def _require_realization_consistency_v1(
    realization: ZUSDProtocolFeeClaimRealizationV1,
) -> None:
    transition = realization.claim_transition
    if transition.kind != "settle" or transition.amount_e8 <= 0:
        raise ValueError("realization requires a positive claim settlement")
    if transition.amount_e8 % ZUSD_LEDGER_UNIT_E8_V1 != 0:
        raise ValueError("realization amount must be whole-zUSD E8")
    if validate_committed_balance_state_v1(realization.pre_balances) is not None:
        raise ValueError("realization pre-balances are invalid")
    if validate_committed_balance_state_v1(realization.post_balances) is not None:
        raise ValueError("realization post-balances are invalid")

    applied = apply_canonical_balance_patch_v1(
        realization.pre_balances,
        realization.balance_patch,
    )
    if type(applied) is not BalancePatchApplyOkV1 or applied.state != realization.post_balances:
        raise ValueError("realization balance patch does not reconstruct post-balances")

    asset_id = transition.pre_state.asset_id
    custody_pubkey = transition.pre_state.custody_pubkey
    expected_units = transition.amount_e8 // ZUSD_LEDGER_UNIT_E8_V1
    if realization.protocol_fee_credit != ProtocolFeeCreditV2(
        custody_pubkey,
        asset_id,
        expected_units,
    ):
        raise ValueError("realization protocol-fee credit is crossed")

    claim_verified = verify_zusd_protocol_fee_claim_transition_v1(
        expected_kind="settle",
        expected_asset_id=asset_id,
        expected_custody_pubkey=custody_pubkey,
        expected_pre_state=transition.pre_state,
        expected_amount_e8=transition.amount_e8,
        transition=transition,
    )
    if claim_verified is not transition:
        raise ValueError("realization claim transition does not replay")

    _require_certificate_consistency_v1(realization, transition, asset_id)


def _require_certificate_consistency_v1(
    realization: ZUSDProtocolFeeClaimRealizationV1,
    transition: ZUSDProtocolFeeClaimTransitionV1,
    asset_id: str,
) -> None:
    """Recompute both absolute identities and the transition certificate."""

    pre_supply = ledger_supply_e8_v1(realization.pre_balances, asset_id)
    post_supply = ledger_supply_e8_v1(realization.post_balances, asset_id)
    if type(pre_supply) is not int or type(post_supply) is not int:
        raise ValueError("realization ledger supply is outside U256")
    certificate = realization.supply_claim_certificate
    if pre_supply + transition.pre_state.outstanding_e8 != certificate.debt_pre_e8:
        raise ValueError("realization pre-state violates debt/supply/claim identity")
    if post_supply + transition.post_state.outstanding_e8 != certificate.debt_post_e8:
        raise ValueError("realization post-state violates debt/supply/claim identity")
    certificate_verified = verify_zusd_supply_claim_delta_certificate_v2(
        expected_action="settle_protocol_fee_claim",
        expected_pre_claim=transition.pre_state,
        expected_post_claim=transition.post_state,
        expected_debt_pre_e8=certificate.debt_pre_e8,
        expected_debt_post_e8=certificate.debt_pre_e8,
        expected_ledger_supply_pre_e8=pre_supply,
        expected_ledger_supply_post_e8=post_supply,
        certificate=certificate,
    )
    if certificate_verified is not certificate:
        raise ValueError("realization supply-claim certificate does not replay")


ZUSDProtocolFeeClaimRealizationResultV1: TypeAlias = (
    ZUSDProtocolFeeClaimRealizationV1 | ZUSDProtocolFeeClaimRealizationRejectV1
)


def _derive_delta_certificate_v1(
    source: ValidatedRealizationSourceV1,
    claim_transition: ZUSDProtocolFeeClaimTransitionV1,
    pre_supply_e8: int,
    post_supply_e8: int,
) -> ZUSDSupplyClaimDeltaCertificateV2 | ZUSDProtocolFeeClaimRealizationRejectV1:
    certificate = derive_zusd_supply_claim_delta_certificate_v2(
        action="settle_protocol_fee_claim",
        pre_claim=source.claim,
        post_claim=claim_transition.post_state,
        debt_pre_e8=source.debt_e8,
        debt_post_e8=source.debt_e8,
        ledger_supply_pre_e8=pre_supply_e8,
        ledger_supply_post_e8=post_supply_e8,
    )
    if type(certificate) is ZUSDSupplyClaimDeltaRejectV2:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.DELTA_CERTIFICATE,
            "supply_claim_certificate",
            certificate.code.value,
        )
    if type(certificate) is not ZUSDSupplyClaimDeltaCertificateV2:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.DELTA_CERTIFICATE,
            "supply_claim_certificate",
        )
    return certificate


def _pre_supply_with_capacity_v1(
    source: ValidatedRealizationSourceV1,
) -> int | ZUSDProtocolFeeClaimRealizationRejectV1:
    pre_supply = ledger_supply_e8_v1(source.balances, source.asset_id)
    if type(pre_supply) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return pre_supply
    if pre_supply > U256_MAX_V1 - source.amount_e8:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.LEDGER_SUPPLY_OVERFLOW,
            "ledger_supply",
        )
    if pre_supply + source.claim.outstanding_e8 != source.debt_e8:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_PRESTATE,
            "economic_identity",
        )
    return pre_supply


def derive_zusd_protocol_fee_claim_realization_v1(
    source: object,
) -> ZUSDProtocolFeeClaimRealizationResultV1:
    """Derive one exact unmounted claim-to-escrow realization candidate."""

    validated = validate_realization_source_v1(source)
    if type(validated) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return validated

    pre_supply = _pre_supply_with_capacity_v1(validated)
    if type(pre_supply) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return pre_supply

    claim_transition = settle_zusd_protocol_fee_claim_v1(
        expected_asset_id=validated.asset_id,
        expected_custody_pubkey=validated.custody_pubkey,
        expected_pre_state=validated.claim,
        amount_e8=validated.amount_e8,
    )
    if type(claim_transition) is not ZUSDProtocolFeeClaimTransitionV1:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.CLAIM_TRANSITION,
            "claim_transition",
        )

    amount_units = validated.amount_e8 // ZUSD_LEDGER_UNIT_E8_V1
    balance_transition = apply_escrow_credit_v1(
        validated.balances,
        custody_pubkey=validated.custody_pubkey,
        asset_id=validated.asset_id,
        amount_units=amount_units,
    )
    if type(balance_transition) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return balance_transition
    post_balances, balance_patch = balance_transition
    post_supply = ledger_supply_e8_v1(post_balances, validated.asset_id)
    if type(post_supply) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return post_supply

    certificate = _derive_delta_certificate_v1(
        validated,
        claim_transition,
        pre_supply,
        post_supply,
    )
    if type(certificate) is ZUSDProtocolFeeClaimRealizationRejectV1:
        return certificate
    return ZUSDProtocolFeeClaimRealizationV1(
        claim_transition=claim_transition,
        pre_balances=validated.balances,
        post_balances=post_balances,
        balance_patch=balance_patch,
        protocol_fee_credit=ProtocolFeeCreditV2(
            validated.custody_pubkey,
            validated.asset_id,
            amount_units,
        ),
        supply_claim_certificate=certificate,
        _construction_token=_CONSTRUCTION_TOKEN_V1,
    )


def verify_zusd_protocol_fee_claim_realization_v1(
    source: object,
    realization: object,
) -> ZUSDProtocolFeeClaimRealizationResultV1:
    """Rebuild a candidate from the externally supplied exact transition instance."""

    if type(realization) is not ZUSDProtocolFeeClaimRealizationV1:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.INVALID_REALIZATION,
            "realization",
        )
    rebuilt = derive_zusd_protocol_fee_claim_realization_v1(source)
    if type(rebuilt) is not ZUSDProtocolFeeClaimRealizationV1 or rebuilt != realization:
        return _reject_v1(
            ZUSDProtocolFeeClaimRealizationRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH,
            "instance",
        )
    return realization


__all__ = (
    "ZUSD_LEDGER_UNIT_E8_V1",
    "ZUSD_PROTOCOL_FEE_CLAIM_REALIZATION_SCHEMA_V1",
    "ZUSDProtocolFeeClaimRealizationRejectCodeV1",
    "ZUSDProtocolFeeClaimRealizationRejectV1",
    "ZUSDProtocolFeeClaimRealizationResultV1",
    "ZUSDProtocolFeeClaimRealizationSourceV1",
    "ZUSDProtocolFeeClaimRealizationV1",
    "derive_zusd_protocol_fee_claim_realization_v1",
    "verify_zusd_protocol_fee_claim_realization_v1",
)
