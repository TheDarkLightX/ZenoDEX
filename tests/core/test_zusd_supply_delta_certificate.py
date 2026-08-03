from __future__ import annotations

from src.core.zusd_supply_delta_certificate import (
    ZUSDSupplyDeltaCertificateV1,
    ZUSDSupplyDeltaRejectCodeV1,
    ZUSDSupplyDeltaRejectV1,
    derive_zusd_supply_delta_certificate_v1,
    verify_zusd_supply_delta_certificate_v1,
)


def test_fee_bearing_mint_derives_exact_debt_supply_accrual_identity() -> None:
    result = derive_zusd_supply_delta_certificate_v1(
        action="mint_zusd",
        debt_pre_e8=0,
        debt_post_e8=101,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=100,
        protocol_fee_accrual_pre_e8=0,
        protocol_fee_accrual_post_e8=1,
    )

    assert isinstance(result, ZUSDSupplyDeltaCertificateV1)
    assert result.debt_delta_e8 == 101
    assert result.ledger_supply_delta_e8 == 100
    assert result.protocol_fee_accrual_delta_e8 == 1
    assert result.to_obj()["certificate_root"] == result.certificate_root
    assert result.certificate_root == (
        "0x88af66e8ef0d4b7dc3ff355acc2effd3b012c6d45494691fde304783153a2bc3"
    )


def test_supply_delta_rejects_missing_fee_accrual() -> None:
    result = derive_zusd_supply_delta_certificate_v1(
        action="mint_zusd",
        debt_pre_e8=0,
        debt_post_e8=101,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=100,
        protocol_fee_accrual_pre_e8=0,
        protocol_fee_accrual_post_e8=0,
    )

    assert isinstance(result, ZUSDSupplyDeltaRejectV1)
    assert result.code is ZUSDSupplyDeltaRejectCodeV1.DELTA_IDENTITY_MISMATCH


def test_supply_delta_rejects_bool_alias_and_decreasing_cumulative_accrual() -> None:
    bool_alias = derive_zusd_supply_delta_certificate_v1(
        action="mint_zusd",
        debt_pre_e8=False,
        debt_post_e8=1,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=1,
        protocol_fee_accrual_pre_e8=0,
        protocol_fee_accrual_post_e8=0,
    )
    decreasing = derive_zusd_supply_delta_certificate_v1(
        action="repay_zusd",
        debt_pre_e8=10,
        debt_post_e8=9,
        ledger_supply_pre_e8=10,
        ledger_supply_post_e8=9,
        protocol_fee_accrual_pre_e8=2,
        protocol_fee_accrual_post_e8=1,
    )

    assert isinstance(bool_alias, ZUSDSupplyDeltaRejectV1)
    assert bool_alias.code is ZUSDSupplyDeltaRejectCodeV1.WRONG_EXACT_TYPE
    assert isinstance(decreasing, ZUSDSupplyDeltaRejectV1)
    assert decreasing.code is ZUSDSupplyDeltaRejectCodeV1.FEE_ACCRUAL_DECREASED


def test_supply_delta_verifier_is_bound_to_external_transition() -> None:
    result = derive_zusd_supply_delta_certificate_v1(
        action="mint_zusd",
        debt_pre_e8=0,
        debt_post_e8=101,
        ledger_supply_pre_e8=0,
        ledger_supply_post_e8=100,
        protocol_fee_accrual_pre_e8=0,
        protocol_fee_accrual_post_e8=1,
    )
    assert isinstance(result, ZUSDSupplyDeltaCertificateV1)

    accepted = verify_zusd_supply_delta_certificate_v1(
        expected_action="mint_zusd",
        expected_debt_pre_e8=0,
        expected_debt_post_e8=101,
        expected_ledger_supply_pre_e8=0,
        expected_ledger_supply_post_e8=100,
        expected_protocol_fee_accrual_pre_e8=0,
        expected_protocol_fee_accrual_post_e8=1,
        certificate=result,
    )
    crossed = verify_zusd_supply_delta_certificate_v1(
        expected_action="mint_zusd",
        expected_debt_pre_e8=0,
        expected_debt_post_e8=102,
        expected_ledger_supply_pre_e8=0,
        expected_ledger_supply_post_e8=100,
        expected_protocol_fee_accrual_pre_e8=0,
        expected_protocol_fee_accrual_post_e8=1,
        certificate=result,
    )

    assert accepted is result
    assert isinstance(crossed, ZUSDSupplyDeltaRejectV1)
    assert crossed.code is ZUSDSupplyDeltaRejectCodeV1.EXTERNAL_INSTANCE_MISMATCH
