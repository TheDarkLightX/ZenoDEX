from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.zusd_monetary_policy_binding import (
    ZUSD_MONETARY_POLICY_FIELDS,
    ZUSDMonetaryPolicyBinding,
    ZUSDPolicyBindingCode,
    ZUSDPolicyBindingDecision,
    evaluate_zusd_policy_binding,
)

ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
STAKE_ASSET = "0x" + "33" * 32
ORACLE = "0x" + "44" * 48
CLOCK_HASH = "0x" + "55" * 32
PROTOCOL_RECIPIENT = "0x" + "66" * 48
NATIVE_ASSET = "0x" + "00" * 32


def _binding() -> ZUSDMonetaryPolicyBinding:
    return ZUSDMonetaryPolicyBinding(
        chain_id="tau-local",
        canonical_zusd_asset=ASSET_A,
        clock_policy_hash=CLOCK_HASH,
        oracle_pubkey=None,
        protocol_fee_recipient_pubkey=None,
        liquidation_gas_comp_fixed_collateral_e8=7,
        liquidation_gas_comp_bps=20,
        borrow_fee_floor_bps=10,
        borrow_fee_max_bps=100,
        host_protocol_fee_share_bps=30,
        fee_stake_asset_id=None,
        staking_activation_delay_epochs=2,
    )


@pytest.mark.parametrize(
    ("field_name", "replacement"),
    (
        ("chain_id", "tau-other"),
        ("canonical_zusd_asset", ASSET_B),
        ("clock_policy_hash", "0x" + "77" * 32),
        ("oracle_pubkey", ORACLE),
        ("protocol_fee_recipient_pubkey", PROTOCOL_RECIPIENT),
        ("liquidation_gas_comp_fixed_collateral_e8", 8),
        ("liquidation_gas_comp_bps", 21),
        ("borrow_fee_floor_bps", 11),
        ("borrow_fee_max_bps", 101),
        ("host_protocol_fee_share_bps", 31),
        ("fee_stake_asset_id", STAKE_ASSET),
        ("staking_activation_delay_epochs", 3),
    ),
)
def test_policy_binding_identifies_each_mismatch_in_canonical_order(
    field_name: str,
    replacement: object,
) -> None:
    committed = _binding()
    configured = replace(committed, **{field_name: replacement})

    decision = evaluate_zusd_policy_binding(
        committed=committed,
        configured=configured,
    )

    assert decision.code is ZUSDPolicyBindingCode.MISMATCH
    assert decision.matched is False
    assert decision.mismatch_fields == (field_name,)


def test_policy_binding_reports_multiple_mismatches_in_schema_order() -> None:
    committed = _binding()
    configured = replace(
        committed,
        chain_id="tau-other",
        clock_policy_hash="0x" + "77" * 32,
        oracle_pubkey=ORACLE,
        protocol_fee_recipient_pubkey=PROTOCOL_RECIPIENT,
        fee_stake_asset_id=STAKE_ASSET,
    )

    decision = evaluate_zusd_policy_binding(
        committed=committed,
        configured=configured,
    )

    assert decision.mismatch_fields == (
        "chain_id",
        "clock_policy_hash",
        "oracle_pubkey",
        "protocol_fee_recipient_pubkey",
        "fee_stake_asset_id",
    )
    assert (
        tuple(field for field in ZUSD_MONETARY_POLICY_FIELDS if field in decision.mismatch_fields)
        == decision.mismatch_fields
    )


def test_matching_policy_binding_has_the_only_valid_matched_shape() -> None:
    binding = _binding()

    decision = evaluate_zusd_policy_binding(
        committed=binding,
        configured=binding,
    )

    assert decision == ZUSDPolicyBindingDecision(
        code=ZUSDPolicyBindingCode.MATCHED,
        mismatch_fields=(),
    )
    assert decision.matched is True


@pytest.mark.parametrize(
    ("code", "mismatch_fields", "error_type"),
    (
        (ZUSDPolicyBindingCode.MATCHED, ("chain_id",), ValueError),
        (ZUSDPolicyBindingCode.MISMATCH, (), ValueError),
        (ZUSDPolicyBindingCode.MISMATCH, ("unknown",), ValueError),
        (ZUSDPolicyBindingCode.MISMATCH, ("chain_id", "chain_id"), ValueError),
        (
            ZUSDPolicyBindingCode.MISMATCH,
            ("oracle_pubkey", "chain_id"),
            ValueError,
        ),
        (0, (), TypeError),
        (ZUSDPolicyBindingCode.MATCHED, [], TypeError),
    ),
)
def test_policy_decision_rejects_unrepresentable_shapes(
    code: object,
    mismatch_fields: object,
    error_type: type[Exception],
) -> None:
    with pytest.raises(error_type):
        ZUSDPolicyBindingDecision(  # type: ignore[arg-type]
            code=code,
            mismatch_fields=mismatch_fields,
        )


@pytest.mark.parametrize(
    ("changes", "message"),
    (
        ({"chain_id": " tau-local"}, "surrounding whitespace"),
        ({"chain_id": "tau\nlocal"}, "control or format"),
        ({"chain_id": "tau-e\u0301"}, "NFC-normalized"),
        ({"chain_id": "x" * 129}, "at most 128 UTF-8 bytes"),
        ({"canonical_zusd_asset": NATIVE_ASSET}, "must be non-native"),
        ({"clock_policy_hash": NATIVE_ASSET}, "must be non-zero"),
        (
            {"protocol_fee_recipient_pubkey": "0x" + "66" * 47},
            "must be canonical",
        ),
        ({"fee_stake_asset_id": NATIVE_ASSET}, "must be non-native"),
        ({"fee_stake_asset_id": ASSET_A}, "must differ"),
        ({"borrow_fee_floor_bps": 101}, "bounds are inverted"),
        (
            {"liquidation_gas_comp_fixed_collateral_e8": 10**30 + 1},
            "must be in",
        ),
        ({"staking_activation_delay_epochs": 10**30 + 1}, "must be in"),
        ({"staking_activation_delay_epochs": 0}, "must be in"),
    ),
)
def test_policy_binding_rejects_ambiguous_or_unsafe_identity_shapes(
    changes: dict[str, object],
    message: str,
) -> None:
    with pytest.raises(ValueError, match=message):
        replace(_binding(), **changes)


@pytest.mark.parametrize(
    ("field_name", "value"),
    (
        ("liquidation_gas_comp_fixed_collateral_e8", True),
        ("liquidation_gas_comp_bps", "20"),
        ("borrow_fee_floor_bps", False),
        ("borrow_fee_max_bps", 1.5),
        ("host_protocol_fee_share_bps", "30"),
        ("staking_activation_delay_epochs", True),
    ),
)
def test_policy_binding_rejects_numeric_coercion(
    field_name: str,
    value: object,
) -> None:
    with pytest.raises(TypeError):
        replace(_binding(), **{field_name: value})
