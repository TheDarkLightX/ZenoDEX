from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.zusd_protocol_fee_claim import (
    ZUSDProtocolFeeClaimTransitionV1,
    ZUSDProtocolFeeClaimV1,
    accrue_zusd_protocol_fee_claim_v1,
    empty_zusd_protocol_fee_claim_v1,
    settle_zusd_protocol_fee_claim_v1,
)
from src.core.zusd_supply_claim_delta_certificate import (
    ZUSDSupplyClaimDeltaCertificateV2,
    ZUSDSupplyClaimDeltaRejectCodeV2,
    ZUSDSupplyClaimDeltaRejectV2,
    derive_zusd_supply_claim_delta_certificate_v2,
    verify_zusd_supply_claim_delta_certificate_v2,
)

ASSET = "0x" + "aa" * 32
ESCROW = "0x" + "bb" * 48


def _claim_states() -> tuple[
    ZUSDProtocolFeeClaimV1,
    ZUSDProtocolFeeClaimV1,
    ZUSDProtocolFeeClaimV1,
]:
    empty = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    accrued = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=1,
    )
    assert type(accrued) is ZUSDProtocolFeeClaimTransitionV1
    settled = settle_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=accrued.post_state,
        amount_e8=1,
    )
    assert type(settled) is ZUSDProtocolFeeClaimTransitionV1
    return empty, accrued.post_state, settled.post_state


def _mint_certificate() -> ZUSDSupplyClaimDeltaCertificateV2:
    empty, accrued, _settled = _claim_states()
    result = derive_zusd_supply_claim_delta_certificate_v2(
        action="mint_zusd",
        pre_claim=empty,
        post_claim=accrued,
        debt_pre_e8=0,
        debt_post_e8=101,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=100,
    )
    assert type(result) is ZUSDSupplyClaimDeltaCertificateV2
    return result


def test_supply_claim_delta_certificate_covers_mint_settlement_and_burn() -> None:
    _empty, accrued, settled_claim = _claim_states()
    mint = _mint_certificate()
    settlement = derive_zusd_supply_claim_delta_certificate_v2(
        action="settle_protocol_fee_claim",
        pre_claim=accrued,
        post_claim=settled_claim,
        debt_pre_e8=101,
        debt_post_e8=101,
        ledger_supply_pre_e8=100,
        ledger_supply_post_e8=101,
    )
    burn = derive_zusd_supply_claim_delta_certificate_v2(
        action="repay_zusd",
        pre_claim=settled_claim,
        post_claim=settled_claim,
        debt_pre_e8=101,
        debt_post_e8=1,
        ledger_supply_pre_e8=101,
        ledger_supply_post_e8=1,
    )

    assert mint.debt_delta_e8 == mint.ledger_supply_delta_e8 + mint.outstanding_claim_delta_e8
    assert type(settlement) is ZUSDSupplyClaimDeltaCertificateV2
    assert settlement.outstanding_claim_delta_e8 == -1
    assert type(burn) is ZUSDSupplyClaimDeltaCertificateV2
    assert burn.outstanding_claim_delta_e8 == 0


def test_supply_claim_delta_certificate_rejects_omitted_or_invented_claim() -> None:
    empty, accrued, _settled = _claim_states()
    omitted = derive_zusd_supply_claim_delta_certificate_v2(
        action="mint_zusd",
        pre_claim=empty,
        post_claim=empty,
        debt_pre_e8=0,
        debt_post_e8=101,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=100,
    )
    invented = derive_zusd_supply_claim_delta_certificate_v2(
        action="repay_zusd",
        pre_claim=empty,
        post_claim=accrued,
        debt_pre_e8=101,
        debt_post_e8=1,
        ledger_supply_pre_e8=101,
        ledger_supply_post_e8=0,
    )

    assert omitted == ZUSDSupplyClaimDeltaRejectV2(
        code=ZUSDSupplyClaimDeltaRejectCodeV2.DELTA_IDENTITY_MISMATCH,
        path=("delta",),
    )
    assert type(invented) is ZUSDSupplyClaimDeltaRejectV2
    assert invented.code is ZUSDSupplyClaimDeltaRejectCodeV2.ACTION_DELTA_INVALID


def test_supply_claim_delta_certificate_derives_exact_paired_claim_lineage() -> None:
    empty, accrued, _settled = _claim_states()
    crossed_action = derive_zusd_supply_claim_delta_certificate_v2(
        action="advance_epoch",
        pre_claim=empty,
        post_claim=accrued,
        debt_pre_e8=0,
        debt_post_e8=0,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=0,
    )
    assert crossed_action == ZUSDSupplyClaimDeltaRejectV2(
        code=ZUSDSupplyClaimDeltaRejectCodeV2.ACTION_DELTA_INVALID,
        path=("claim_transition",),
    )

    hostile = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    object.__setattr__(hostile, "outstanding_e8", 1)
    invalid_state = derive_zusd_supply_claim_delta_certificate_v2(
        action="mint_zusd",
        pre_claim=hostile,
        post_claim=accrued,
        debt_pre_e8=0,
        debt_post_e8=101,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=100,
    )
    assert invalid_state == ZUSDSupplyClaimDeltaRejectV2(
        code=ZUSDSupplyClaimDeltaRejectCodeV2.INVALID_CLAIM_STATE,
        path=("claim",),
    )


def test_supply_claim_delta_certificate_is_externally_grounded() -> None:
    empty, accrued, _settled = _claim_states()
    certificate = _mint_certificate()
    verified = verify_zusd_supply_claim_delta_certificate_v2(
        expected_action="mint_zusd",
        expected_pre_claim=empty,
        expected_post_claim=accrued,
        expected_debt_pre_e8=0,
        expected_debt_post_e8=101,
        expected_ledger_supply_pre_e8=0,
        expected_ledger_supply_post_e8=100,
        certificate=certificate,
    )
    assert verified is certificate

    foreign_empty = empty_zusd_protocol_fee_claim_v1(
        asset_id=ASSET,
        custody_pubkey="0x" + "cc" * 48,
    )
    foreign_accrued_result = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=foreign_empty.custody_pubkey,
        expected_pre_state=foreign_empty,
        amount_e8=1,
    )
    assert type(foreign_accrued_result) is ZUSDProtocolFeeClaimTransitionV1
    crossed = verify_zusd_supply_claim_delta_certificate_v2(
        expected_action="mint_zusd",
        expected_pre_claim=foreign_empty,
        expected_post_claim=foreign_accrued_result.post_state,
        expected_debt_pre_e8=0,
        expected_debt_post_e8=101,
        expected_ledger_supply_pre_e8=0,
        expected_ledger_supply_post_e8=100,
        certificate=certificate,
    )
    assert type(crossed) is ZUSDSupplyClaimDeltaRejectV2
    assert crossed.code is ZUSDSupplyClaimDeltaRejectCodeV2.EXTERNAL_INSTANCE_MISMATCH

    with pytest.raises(TypeError, match="controlled derivation"):
        replace(certificate, debt_post_e8=102)


def test_supply_claim_delta_certificate_rejects_bool_alias() -> None:
    empty, accrued, _settled = _claim_states()
    result = derive_zusd_supply_claim_delta_certificate_v2(
        action="mint_zusd",
        pre_claim=empty,
        post_claim=accrued,
        debt_pre_e8=False,
        debt_post_e8=101,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=100,
    )
    assert result == ZUSDSupplyClaimDeltaRejectV2(
        code=ZUSDSupplyClaimDeltaRejectCodeV2.WRONG_EXACT_TYPE,
        path=("debt_pre_e8",),
    )
