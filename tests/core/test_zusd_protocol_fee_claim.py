from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.zusd_protocol_fee_claim import (
    ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
    ZUSDProtocolFeeClaimRejectCodeV1,
    ZUSDProtocolFeeClaimRejectV1,
    ZUSDProtocolFeeClaimTransitionV1,
    ZUSDProtocolFeeClaimV1,
    accrue_zusd_protocol_fee_claim_v1,
    decode_zusd_protocol_fee_claim_v1,
    empty_zusd_protocol_fee_claim_v1,
    settle_zusd_protocol_fee_claim_v1,
    verify_zusd_protocol_fee_claim_transition_v1,
)

ASSET = "0x" + "aa" * 32
ESCROW = "0x" + "bb" * 48
FOREIGN_ESCROW = "0x" + "cc" * 48


def test_fee_claim_accrual_and_settlement_preserve_exact_current_liability() -> None:
    empty = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    accrued = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=125_000_000,
    )

    assert type(accrued) is ZUSDProtocolFeeClaimTransitionV1
    assert accrued.post_state.outstanding_e8 == 125_000_000
    assert accrued.post_state.accrued_cumulative_e8 == 125_000_000
    assert accrued.post_state.realized_cumulative_e8 == 0

    settled = settle_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=accrued.post_state,
        amount_e8=100_000_000,
    )

    assert type(settled) is ZUSDProtocolFeeClaimTransitionV1
    assert settled.post_state.outstanding_e8 == 25_000_000
    assert settled.post_state.accrued_cumulative_e8 == 125_000_000
    assert settled.post_state.realized_cumulative_e8 == 100_000_000
    assert (
        settled.amount_e8 + settled.post_state.outstanding_e8 == accrued.post_state.outstanding_e8
    )


def test_fee_claim_rejects_bool_alias_overflow_and_over_settlement() -> None:
    empty = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)

    bool_alias = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=True,
    )
    overflow = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=1 << 256,
    )
    over_settlement = settle_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=1,
    )
    zero_settlement = settle_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=0,
    )

    assert bool_alias == ZUSDProtocolFeeClaimRejectV1(
        code=ZUSDProtocolFeeClaimRejectCodeV1.WRONG_EXACT_TYPE,
        path=("amount_e8",),
    )
    assert overflow == ZUSDProtocolFeeClaimRejectV1(
        code=ZUSDProtocolFeeClaimRejectCodeV1.VALUE_EXCEEDS_U256,
        path=("amount_e8",),
    )
    assert over_settlement == ZUSDProtocolFeeClaimRejectV1(
        code=ZUSDProtocolFeeClaimRejectCodeV1.AMOUNT_EXCEEDS_OUTSTANDING,
        path=("amount_e8",),
    )
    assert zero_settlement == ZUSDProtocolFeeClaimRejectV1(
        code=ZUSDProtocolFeeClaimRejectCodeV1.ZERO_SETTLEMENT,
        path=("amount_e8",),
    )


def test_fee_claim_verifier_rejects_crossed_identity_and_mutated_transition() -> None:
    empty = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    transition = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=7,
    )
    assert type(transition) is ZUSDProtocolFeeClaimTransitionV1

    crossed = verify_zusd_protocol_fee_claim_transition_v1(
        expected_kind="accrue",
        expected_asset_id=ASSET,
        expected_custody_pubkey=FOREIGN_ESCROW,
        expected_pre_state=empty,
        expected_amount_e8=7,
        transition=transition,
    )
    assert type(crossed) is ZUSDProtocolFeeClaimRejectV1
    assert crossed.code is ZUSDProtocolFeeClaimRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH

    with pytest.raises(TypeError, match="controlled derivation"):
        replace(transition, amount_e8=8)


def test_fee_claim_root_is_canonical_and_stable() -> None:
    empty = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    transition = accrue_zusd_protocol_fee_claim_v1(
        expected_asset_id=ASSET,
        expected_custody_pubkey=ESCROW,
        expected_pre_state=empty,
        amount_e8=7,
    )
    assert type(transition) is ZUSDProtocolFeeClaimTransitionV1

    assert empty.state_root == "0x45323060ce67b409a8d537dc3f8f615ca2d5bf4e672a6f1d24b14cd747522b8d"
    assert (
        transition.transition_root
        == "0x0f3f4cbfc7449d57ea502852c4f2430604a398bd675bcbd5ee91749718ca90dd"
    )


def test_fee_claim_decoder_rejects_surplus_fields_bool_version_and_direct_construction() -> None:
    source = {
        "schema": ZUSD_PROTOCOL_FEE_CLAIM_SCHEMA_V1,
        "version": 1,
        "asset_id": ASSET,
        "custody_pubkey": ESCROW,
        "outstanding_e8": 0,
        "accrued_cumulative_e8": 0,
    }
    decoded = decode_zusd_protocol_fee_claim_v1(source)
    assert decoded == empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)

    with pytest.raises(ValueError, match="unknown fields"):
        decode_zusd_protocol_fee_claim_v1({**source, "state_root": decoded.state_root})
    with pytest.raises(ValueError, match="version"):
        decode_zusd_protocol_fee_claim_v1({**source, "version": True})
    with pytest.raises(TypeError, match="controlled derivation"):
        ZUSDProtocolFeeClaimV1(
            asset_id=ASSET,
            custody_pubkey=ESCROW,
            outstanding_e8=0,
            accrued_cumulative_e8=0,
        )


def test_fee_claim_bounded_transition_family_preserves_partition_and_identity() -> None:
    empty = empty_zusd_protocol_fee_claim_v1(asset_id=ASSET, custody_pubkey=ESCROW)
    for accrued_e8 in range(6):
        accrued = accrue_zusd_protocol_fee_claim_v1(
            expected_asset_id=ASSET,
            expected_custody_pubkey=ESCROW,
            expected_pre_state=empty,
            amount_e8=accrued_e8,
        )
        assert type(accrued) is ZUSDProtocolFeeClaimTransitionV1
        for settled_e8 in range(1, accrued_e8 + 1):
            settled = settle_zusd_protocol_fee_claim_v1(
                expected_asset_id=ASSET,
                expected_custody_pubkey=ESCROW,
                expected_pre_state=accrued.post_state,
                amount_e8=settled_e8,
            )
            assert type(settled) is ZUSDProtocolFeeClaimTransitionV1
            post = settled.post_state
            assert post.outstanding_e8 + post.realized_cumulative_e8 == post.accrued_cumulative_e8
            assert post.asset_id == ASSET
            assert post.custody_pubkey == ESCROW
