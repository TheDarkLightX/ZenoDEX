from __future__ import annotations

import pytest

from src.integration import (
    perp_engine,
    settlement_price_attestation,
    tau_net_client,
)
from src.integration import (
    perps_wallet_social_recovery_v1 as social_recovery,
)
from src.integration.settlement_price_attestation import SettlementSpotPriceAttestation
from src.integration.settlement_price_provenance import (
    SettlementSpotPriceEntry,
    SettlementSpotPricePacket,
    build_settlement_spot_price_packet,
)
from src.state.nonces import NonceTable

PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48
PUBKEY_C = "0x" + "33" * 48


def _price_packet() -> SettlementSpotPricePacket:
    return build_settlement_spot_price_packet(
        entries=(
            SettlementSpotPriceEntry(
                asset="0x" + "01" * 32,
                price=100,
                observed_epoch=95,
                age_epochs=5,
                source_id="oracle:a",
            ),
        ),
        now_epoch=100,
        max_staleness_epochs=10,
    )


def test_tau_net_bls_guard_rejects_partial_dependency_state(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(tau_net_client, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(tau_net_client, "G2Basic", None)

    with pytest.raises(tau_net_client.TauNetRpcError, match="py_ecc\\.bls is required"):
        tau_net_client.bls_pubkey_hex_from_privkey(1)
    with pytest.raises(tau_net_client.TauNetRpcError, match="py_ecc\\.bls is required"):
        tau_net_client.sign_tau_transaction_payload(
            {
                "sender_pubkey": PUBKEY_A[2:],
                "sequence_number": 1,
                "expiration_time": 2,
                "operations": {},
                "fee_limit": 0,
            },
            privkey=1,
        )
    with pytest.raises(tau_net_client.TauNetRpcError, match="py_ecc\\.bls is required"):
        tau_net_client.sign_dex_intent_for_engine({}, privkey=1, chain_id="tau-local")
    with pytest.raises(tau_net_client.TauNetRpcError, match="py_ecc\\.bls is required"):
        tau_net_client.sign_perp_op_for_engine(
            {},
            privkey=1,
            chain_id="tau-local",
            signer_pubkey=PUBKEY_A[2:],
            nonce=1,
        )
    assert tau_net_client.verify_tau_transaction_payload_signature({"sender_pubkey": "", "signature": ""}) is False


def test_settlement_attestation_bls_guard_rejects_partial_dependency_state(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    packet = _price_packet()
    monkeypatch.setattr(settlement_price_attestation, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(settlement_price_attestation, "G2Basic", None)

    with pytest.raises(ValueError, match="py_ecc\\.bls is required"):
        settlement_price_attestation.build_settlement_spot_price_attestation(
            packet=packet,
            signer_privkey=7,
        )

    settlement_price_attestation._PRICE_ATTESTATION_VERIFY_CACHE.clear()
    attestation = SettlementSpotPriceAttestation(
        packet=packet,
        signer_pubkey=PUBKEY_A,
        signed_at_epoch=packet.now_epoch,
        packet_hash=settlement_price_attestation._packet_hash_hex(packet),
        signature="0x" + "11" * 96,
    )
    with pytest.raises(ValueError, match="py_ecc\\.bls is required"):
        settlement_price_attestation.verify_settlement_spot_price_attestation(
            attestation=attestation,
            consumer_now_epoch=packet.now_epoch,
            max_attestation_age_epochs=5,
        )


def test_social_recovery_bls_guard_blocks_partial_dependency_state(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(social_recovery, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(social_recovery, "G2Basic", None)

    with pytest.raises(RuntimeError, match="py_ecc\\.bls is required"):
        social_recovery.aggregate_guardian_bls_signatures_v1([])

    coordinator = social_recovery.SocialRecoveryCoordinatorV1(
        chain_id="tau-local",
        authority_id="perps-authority-1",
    )
    coordinator.register_guardian(guardian_id="guardian-a", public_key=PUBKEY_A)
    coordinator.register_guardian(guardian_id="guardian-b", public_key=PUBKEY_B)
    coordinator.register_guardian(guardian_id="guardian-c", public_key=PUBKEY_C)
    coordinator.set_recovery_policy(
        policy_id="recovery-policy-1",
        subject_key_id="perps-wallet-a",
        threshold=2,
    )

    assert coordinator.production_security_claim is False


def test_perp_engine_signature_guard_rejects_partial_dependency_state(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(perp_engine, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(perp_engine, "G2Basic", None)

    err = perp_engine._verify_perp_op_signature(
        config=perp_engine.PerpEngineConfig(chain_id="tau-local"),
        signer_pubkey=PUBKEY_A,
        nonce=1,
        signature="0x" + "11" * 96,
        op={"deadline": 10},
        nonces=NonceTable(),
        block_timestamp=1,
    )

    assert err == "BLS verification not available (install py-ecc)"
