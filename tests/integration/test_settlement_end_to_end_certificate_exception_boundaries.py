from __future__ import annotations

import pytest

import src.integration.settlement_end_to_end_certificate_packet as packet_mod


def test_price_packet_verifier_returns_false_for_malformed_price_packet(monkeypatch) -> None:
    def _raise_value_error(_payload: object) -> object:
        raise ValueError("bad price packet")

    monkeypatch.setattr(packet_mod.SettlementSpotPricePacket, "from_dict", _raise_value_error)

    ok, err = packet_mod.verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
        settlement=object(),  # type: ignore[arg-type]
        proof_flags=object(),  # type: ignore[arg-type]
        price_history=(1, 1, 1),
        feature_extension_inputs_payload={},
        price_packet_payload={},
        packet_payload={},
    )

    assert ok is False
    assert err == "bad price packet"


def test_price_packet_verifier_does_not_swallow_programming_errors(monkeypatch) -> None:
    def _raise_runtime_error(_payload: object) -> object:
        raise RuntimeError("unexpected bug")

    monkeypatch.setattr(packet_mod.SettlementSpotPricePacket, "from_dict", _raise_runtime_error)

    with pytest.raises(RuntimeError, match="unexpected bug"):
        packet_mod.verify_settlement_end_to_end_certificate_packet_payload_from_price_packet(
            settlement=object(),  # type: ignore[arg-type]
            proof_flags=object(),  # type: ignore[arg-type]
            price_history=(1, 1, 1),
            feature_extension_inputs_payload={},
            price_packet_payload={},
            packet_payload={},
        )
