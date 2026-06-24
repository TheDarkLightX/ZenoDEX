from __future__ import annotations

import pytest

import src.integration.settlement_feature_extension_packet as feature_packet
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


@pytest.mark.parametrize(
    "flag_name",
    (
        "buyback_floor_ok",
        "buyback_floor_fixedpoint_ok",
        "rebate_ok",
        "lock_weight_ok",
        "feature_extension_ok",
        "packet_ok",
    ),
)
def test_settlement_feature_extension_packet_rejects_int_bool_flags(flag_name: str) -> None:
    inputs = _inputs()
    packet = build_settlement_feature_extension_packet(inputs)
    payload = packet.to_dict()
    payload[flag_name] = int(payload[flag_name])

    ok, err = verify_settlement_feature_extension_packet_payload(
        inputs_payload=inputs.to_dict(),
        packet_payload=payload,
    )

    assert ok is False
    assert err == f"{flag_name} must be bool"


def test_settlement_feature_extension_packet_rejects_expected_input_parse_error() -> None:
    payload = _inputs().to_dict()
    del payload["trade_amount"]
    packet = build_settlement_feature_extension_packet(_inputs())

    ok, err = verify_settlement_feature_extension_packet_payload(
        inputs_payload=payload,
        packet_payload=packet.to_dict(),
    )

    assert ok is False
    assert err == "missing feature extension input field: trade_amount"


def test_settlement_feature_extension_packet_caps_malformed_input_error() -> None:
    payload = _inputs().to_dict()
    payload["trade_amount"] = "9" * 1_000 + "x"
    packet = build_settlement_feature_extension_packet(_inputs())

    ok, err = verify_settlement_feature_extension_packet_payload(
        inputs_payload=payload,
        packet_payload=packet.to_dict(),
    )

    assert ok is False
    assert err is not None
    assert len(err) <= 200
    assert "9" * 201 not in err


def test_settlement_feature_extension_packet_surfaces_unexpected_input_parse_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    packet = build_settlement_feature_extension_packet(_inputs())

    def fail_from_dict(
        cls: type[feature_packet.SettlementFeatureExtensionInputs],
        payload: object,
    ) -> feature_packet.SettlementFeatureExtensionInputs:
        raise RuntimeError("unexpected feature input parse fault")

    monkeypatch.setattr(
        feature_packet.SettlementFeatureExtensionInputs,
        "from_dict",
        classmethod(fail_from_dict),
    )

    with pytest.raises(RuntimeError, match="unexpected feature input parse fault"):
        verify_settlement_feature_extension_packet_payload(
            inputs_payload=_inputs().to_dict(),
            packet_payload=packet.to_dict(),
        )


def test_settlement_feature_extension_packet_rejects_expected_builder_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    packet = build_settlement_feature_extension_packet(_inputs())

    def reject_builder(
        inputs: feature_packet.SettlementFeatureExtensionInputs,
    ) -> feature_packet.SettlementFeatureExtensionPacket:
        raise ValueError("expected feature builder reject")

    monkeypatch.setattr(feature_packet, "build_settlement_feature_extension_packet", reject_builder)

    ok, err = verify_settlement_feature_extension_packet_payload(
        inputs_payload=_inputs().to_dict(),
        packet_payload=packet.to_dict(),
    )

    assert ok is False
    assert err == "expected feature builder reject"


def test_settlement_feature_extension_packet_surfaces_unexpected_builder_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    packet = build_settlement_feature_extension_packet(_inputs())

    def fail_builder(
        inputs: feature_packet.SettlementFeatureExtensionInputs,
    ) -> feature_packet.SettlementFeatureExtensionPacket:
        raise RuntimeError("unexpected feature builder fault")

    monkeypatch.setattr(feature_packet, "build_settlement_feature_extension_packet", fail_builder)

    with pytest.raises(RuntimeError, match="unexpected feature builder fault"):
        verify_settlement_feature_extension_packet_payload(
            inputs_payload=_inputs().to_dict(),
            packet_payload=packet.to_dict(),
        )
