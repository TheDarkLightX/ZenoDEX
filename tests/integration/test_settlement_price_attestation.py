from __future__ import annotations

import importlib.util

import pytest

from tests.integration._attestation_policy_helper import make_attestation_policy, make_attestation_registry_snapshot

from src.integration.settlement_price_attestation import (
    build_settlement_spot_price_attestation,
    verify_settlement_spot_price_attestation,
    verify_settlement_spot_price_attestation_payload,
)
from src.integration.settlement_price_provenance import (
    SettlementSpotPricePacket,
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)


pytestmark = pytest.mark.skipif(importlib.util.find_spec("py_ecc") is None, reason="py_ecc is not available")


def _packet() -> SettlementSpotPricePacket:
    return build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="0x" + "01" * 32, price=100, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset="0x" + "02" * 32, price=120, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )


def test_settlement_spot_price_attestation_round_trips() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=make_attestation_policy(attestation),
    )
    assert ok is True
    assert err is None

    ok2, err2 = verify_settlement_spot_price_attestation_payload(
        payload=attestation.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=make_attestation_policy(attestation),
    )
    assert ok2 is True
    assert err2 is None


def test_settlement_spot_price_attestation_rejects_stale_consumer_epoch() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=107,
        max_attestation_age_epochs=5,
        attestation_policy=make_attestation_policy(attestation),
    )
    assert ok is False
    assert err == "settlement spot price attestation is stale"


def test_settlement_spot_price_attestation_rejects_source_allowlist_violation() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=102,
        max_attestation_age_epochs=5,
        attestation_policy=make_attestation_policy(attestation, allowed_sources=("oracle:a",)),
    )
    assert ok is False
    assert err is not None
    assert err.startswith("source_id not allowlisted by attestation policy: oracle:b")
    assert "violating_source=oracle:b" in err


def test_settlement_spot_price_attestation_rejects_missing_policy() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=102,
        max_attestation_age_epochs=5,
        attestation_policy=None,
    )
    assert ok is False
    assert err is not None
    assert err.startswith("settlement spot price attestation requires attestation_policy")
    assert "consumer_now_epoch=102" in err


def test_settlement_spot_price_attestation_rejects_tampering() -> None:
    packet = _packet()
    built = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )
    attestation = built.to_dict()
    attestation["packet_hash"] = "0x" + "00" * 32

    ok, err = verify_settlement_spot_price_attestation_payload(
        payload=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=make_attestation_policy(built),
    )
    assert ok is False
    assert err == "packet_hash mismatch"


def test_settlement_spot_price_attestation_accepts_registry_snapshot_without_policy() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=None,
        attestation_registry_snapshot=make_attestation_registry_snapshot(attestation),
    )
    assert ok is True
    assert err is None


def test_settlement_spot_price_attestation_rejects_policy_snapshot_binding_drift() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=make_attestation_policy(attestation, policy_epoch=1),
        attestation_registry_snapshot=make_attestation_registry_snapshot(attestation, policy_epoch=2),
    )
    assert ok is False
    assert err is not None
    assert err.startswith("attestation policy_epoch does not match registry snapshot policy")
