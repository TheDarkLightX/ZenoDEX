from __future__ import annotations

import importlib.util

import pytest

from tests.integration._attestation_policy_helper import make_attestation_policy, make_attestation_registry_snapshot

from src.integration.settlement_price_attestation import (
    SettlementSpotPriceAttestationBundle,
    build_settlement_spot_price_attestation_bundle,
    build_settlement_spot_price_attestation,
    verify_settlement_spot_price_attestation_bundle,
    verify_settlement_spot_price_attestation_bundle_payload,
    verify_settlement_spot_price_attestation,
    verify_settlement_spot_price_attestation_payload,
)
from src.integration.settlement_signer_registry import InMemorySettlementSignerRegistrySnapshotLoader
from src.integration.settlement_price_provenance import (
    SettlementSpotPricePacket,
    SettlementSpotPriceEntry,
    build_settlement_spot_price_packet,
)


pytestmark = pytest.mark.skipif(importlib.util.find_spec("py_ecc") is None, reason="py_ecc is not available")


def _packet() -> SettlementSpotPricePacket:
    return _packet_with_prices(price_a=100, price_b=120)


def _packet_with_prices(*, price_a: int, price_b: int) -> SettlementSpotPricePacket:
    return build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(asset="0x" + "01" * 32, price=price_a, observed_epoch=95, age_epochs=5, source_id="oracle:a"),
            SettlementSpotPriceEntry(asset="0x" + "02" * 32, price=price_b, observed_epoch=97, age_epochs=3, source_id="oracle:b"),
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


def test_settlement_spot_price_attestation_accepts_snapshot_loader() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(
        packet=packet,
        signer_privkey=7,
    )
    policy = make_attestation_policy(attestation)
    snapshot = make_attestation_registry_snapshot(attestation)
    loader = InMemorySettlementSignerRegistrySnapshotLoader(
        {
            (
                int(policy.chain_id),
                policy.registry_contract,
                policy.policy_id,
                int(policy.policy_epoch),
            ): snapshot
        }
    )

    ok, err = verify_settlement_spot_price_attestation(
        attestation=attestation,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=policy,
        attestation_registry_snapshot=None,
        attestation_registry_snapshot_loader=loader,
    )
    assert ok is True
    assert err is None


def test_settlement_spot_price_attestation_bundle_accepts_multi_signer_quorum() -> None:
    packet = _packet()
    attestation_a = build_settlement_spot_price_attestation(packet=packet, signer_privkey=7)
    attestation_b = build_settlement_spot_price_attestation(packet=packet, signer_privkey=8)
    bundle = build_settlement_spot_price_attestation_bundle(
        attestations=(attestation_a, attestation_b),
    )
    policy = make_attestation_policy(
        attestation_a,
        min_distinct_signers=2,
        additional_allowed_signers={attestation_b.signer_pubkey: ("oracle:a", "oracle:b")},
    )

    ok, err = verify_settlement_spot_price_attestation_bundle(
        bundle=bundle,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=policy,
    )
    assert ok is True
    assert err is None

    ok2, err2 = verify_settlement_spot_price_attestation_bundle_payload(
        payload=bundle.to_dict(),
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=policy,
    )
    assert ok2 is True
    assert err2 is None


def test_settlement_spot_price_attestation_bundle_accepts_bounded_disagreement_with_lower_median_consensus() -> None:
    attestation_a = build_settlement_spot_price_attestation(packet=_packet_with_prices(price_a=100, price_b=120), signer_privkey=7)
    attestation_b = build_settlement_spot_price_attestation(packet=_packet_with_prices(price_a=101, price_b=121), signer_privkey=8)
    bundle = build_settlement_spot_price_attestation_bundle(attestations=(attestation_a, attestation_b))
    policy = make_attestation_policy(
        attestation_a,
        min_distinct_signers=2,
        max_bundle_price_spread_bps=100,
        additional_allowed_signers={attestation_b.signer_pubkey: ("oracle:a", "oracle:b")},
    )

    assert [entry.price for entry in bundle.packet.entries] == [100, 120]

    ok, err = verify_settlement_spot_price_attestation_bundle(
        bundle=bundle,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=policy,
    )
    assert ok is True
    assert err is None


def test_settlement_spot_price_attestation_bundle_rejects_price_spread_above_policy_bound() -> None:
    attestation_a = build_settlement_spot_price_attestation(packet=_packet_with_prices(price_a=100, price_b=120), signer_privkey=7)
    attestation_b = build_settlement_spot_price_attestation(packet=_packet_with_prices(price_a=120, price_b=150), signer_privkey=8)
    bundle = build_settlement_spot_price_attestation_bundle(attestations=(attestation_a, attestation_b))
    policy = make_attestation_policy(
        attestation_a,
        min_distinct_signers=2,
        max_bundle_price_spread_bps=500,
        additional_allowed_signers={attestation_b.signer_pubkey: ("oracle:a", "oracle:b")},
    )

    ok, err = verify_settlement_spot_price_attestation_bundle(
        bundle=bundle,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=policy,
    )
    assert ok is False
    assert err is not None
    assert err.startswith("bundle price disagreement exceeds attestation policy bound")
    assert "allowed_max_bundle_price_spread_bps=500" in err
    assert "observed_max_bundle_price_spread_bps=2500" in err


def test_settlement_spot_price_attestation_bundle_rejects_signer_quorum_not_met() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(packet=packet, signer_privkey=7)
    bundle = build_settlement_spot_price_attestation_bundle(attestations=(attestation,))
    policy = make_attestation_policy(attestation, min_distinct_signers=2)

    ok, err = verify_settlement_spot_price_attestation_bundle(
        bundle=bundle,
        consumer_now_epoch=103,
        max_attestation_age_epochs=5,
        attestation_policy=policy,
    )
    assert ok is False
    assert err is not None
    assert err.startswith("attestation policy signer quorum not met")


def test_settlement_spot_price_attestation_bundle_rejects_duplicate_signers() -> None:
    packet = _packet()
    attestation = build_settlement_spot_price_attestation(packet=packet, signer_privkey=7)

    with pytest.raises(ValueError, match="bundle attestation signer_pubkey values must be distinct"):
        SettlementSpotPriceAttestationBundle(
            packet=packet,
            packet_hash=attestation.packet_hash,
            signed_at_epoch=attestation.signed_at_epoch,
            attestations=(attestation, attestation),
        )
