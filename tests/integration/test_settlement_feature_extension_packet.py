from __future__ import annotations

from src.integration.settlement_feature_extension_packet import (
    SettlementFeatureExtensionInputs,
    build_settlement_feature_extension_packet,
    verify_settlement_feature_extension_packet_payload,
)


def _inputs() -> SettlementFeatureExtensionInputs:
    return SettlementFeatureExtensionInputs(
        trade_amount=100,
        fee_charged=1,
        buyback_amount=1,
        burned_amount=1,
        supply_before=1_000,
        supply_after=999,
        supply_floor=500,
        unit_scale=1,
        rebate_rate_bps=500,
        rebate_amount=1,
        rebate_cap=1,
        lock_days=60,
        stake_amount=50,
        tier1_days=30,
        tier2_days=90,
        weight_t1=1,
        weight_t2=2,
        weight_t3=3,
        weight_claimed=2,
        weighted_stake=100,
    )


def test_settlement_feature_extension_packet_round_trips() -> None:
    inputs = _inputs()
    packet = build_settlement_feature_extension_packet(inputs)
    assert packet.packet_ok is True
    assert packet.feature_extension_ok is True

    ok, err = verify_settlement_feature_extension_packet_payload(
        inputs_payload=inputs.to_dict(),
        packet_payload=packet.to_dict(),
    )
    assert ok is True
    assert err is None


def test_settlement_feature_extension_packet_rejects_tampering() -> None:
    inputs = _inputs()
    packet = build_settlement_feature_extension_packet(inputs)
    bad = dict(packet.to_dict())
    bad["rebate_ok"] = False

    ok, err = verify_settlement_feature_extension_packet_payload(
        inputs_payload=inputs.to_dict(),
        packet_payload=bad,
    )
    assert ok is False
    assert err == "settlement feature extension packet mismatch"
