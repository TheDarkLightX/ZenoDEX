"""Tests for production social recovery with live BLS guardian quorum signing.

Copyright (c) DarkLightX/Dana Edwards. All rights reserved.
"""

from __future__ import annotations

import pytest

from src.integration.perps_wallet_social_recovery_v1 import (
    PAYLOAD_KIND_DEVICE_APPROVAL,
    PAYLOAD_KIND_RECOVERY,
    PAYLOAD_KIND_ROTATION,
    PROPOSAL_STATUS_EXECUTED,
    SocialRecoveryCoordinatorV1,
)
from src.integration.zeno_key_manager import generate_tau_testnet_compatible_private_key_hex
from src.integration.zeno_ledger_signature import bls_public_key_hex_from_private_key_v0

try:
    from py_ecc.bls import G2Basic  # noqa: F401

    _BLS_AVAILABLE = True
except Exception:
    _BLS_AVAILABLE = False

pytestmark = pytest.mark.skipif(not _BLS_AVAILABLE, reason="py_ecc.bls not available")


def _make_guardian_keys(count: int) -> list[tuple[str, str, str]]:
    """Generate (guardian_id, private_key_hex, public_key) tuples for N guardians."""
    out: list[tuple[str, str, str]] = []
    for i in range(count):
        gid = f"guardian-{chr(ord('a') + i)}"
        sk = generate_tau_testnet_compatible_private_key_hex()
        pk = bls_public_key_hex_from_private_key_v0(sk)
        out.append((gid, sk, pk))
    return out


def _make_coordinator_with_guardians(
    n: int = 3, threshold: int = 2, *, fixture_mode: bool = False,
) -> tuple[SocialRecoveryCoordinatorV1, list[tuple[str, str, str]], dict]:
    """Create a coordinator with N registered guardians and a 2-of-N policy."""
    coord = SocialRecoveryCoordinatorV1(
        chain_id="tau-local", authority_id="perps-authority-1",
        fixture_mode=fixture_mode,
    )
    guardians = _make_guardian_keys(n)
    for gid, _sk, pk in guardians:
        coord.register_guardian(guardian_id=gid, public_key=pk, weight=1)
    policy = coord.set_recovery_policy(
        policy_id="recovery-policy-1", subject_key_id="perps-wallet-a",
        threshold=threshold, delay_epochs=0,
    )
    return coord, guardians, policy


# -- Guardian key registration ------------------------------------------------

def test_guardian_key_registration_stores_bls_public_key() -> None:
    coord = SocialRecoveryCoordinatorV1(
        chain_id="tau-local", authority_id="perps-authority-1",
    )
    sk = generate_tau_testnet_compatible_private_key_hex()
    pk = bls_public_key_hex_from_private_key_v0(sk)
    reg = coord.register_guardian(guardian_id="guardian-a", public_key=pk, weight=1)
    assert reg["guardian_id"] == "guardian-a"
    assert reg["public_key"] == pk
    assert reg["weight"] == 1
    assert reg["status"] == "active"
    assert "registration_hash" in reg
    status = coord.coordinator_status()
    assert status["guardian_count"] == 1
    assert status["active_guardian_count"] == 1


# -- Recovery proposal submission and quorum collection -----------------------

def test_recovery_proposal_submission_and_quorum_collection() -> None:
    coord, guardians, _ = _make_coordinator_with_guardians(3, 2)
    _gid_a, sk_a, _ = guardians[0]
    _gid_b, sk_b, _ = guardians[1]
    new_sk = generate_tau_testnet_compatible_private_key_hex()
    new_pk = bls_public_key_hex_from_private_key_v0(new_sk)
    proposal = coord.submit_recovery_proposal(
        proposal_id="rec-1", subject_key_id="perps-wallet-a",
        replacement_key_id="perps-wallet-b", replacement_public_key=new_pk,
        requested_at_epoch=10, policy_id="recovery-policy-1",
    )
    assert "proposal_hash" in proposal
    env_a = coord.guardian_sign_proposal(
        guardian_id="guardian-a", guardian_private_key_hex=sk_a, proposal=proposal,
    )
    env_b = coord.guardian_sign_proposal(
        guardian_id="guardian-b", guardian_private_key_hex=sk_b, proposal=proposal,
    )
    report = coord.verify_quorum(
        proposal=proposal, envelopes=[env_a, env_b],
        payload_kind=PAYLOAD_KIND_RECOVERY,
    )
    assert report["quorum_met"] is True
    assert report["accepted_weight"] == 2
    assert report["threshold"] == 2
    assert len(report["accepted_signatures"]) == 2
    assert report["aggregate_verified"] is True
    assert report["aggregate_signature"] is not None


# -- Recovery execution with sufficient quorum --------------------------------

def test_recovery_execution_with_sufficient_quorum() -> None:
    coord, guardians, _ = _make_coordinator_with_guardians(3, 2)
    _gid_a, sk_a, _ = guardians[0]
    _gid_b, sk_b, _ = guardians[1]
    new_pk = bls_public_key_hex_from_private_key_v0(
        generate_tau_testnet_compatible_private_key_hex()
    )
    proposal = coord.submit_recovery_proposal(
        proposal_id="rec-exec-1", subject_key_id="perps-wallet-a",
        replacement_key_id="perps-wallet-b", replacement_public_key=new_pk,
        requested_at_epoch=10, policy_id="recovery-policy-1",
    )
    env_a = coord.guardian_sign_proposal(
        guardian_id="guardian-a", guardian_private_key_hex=sk_a, proposal=proposal,
    )
    env_b = coord.guardian_sign_proposal(
        guardian_id="guardian-b", guardian_private_key_hex=sk_b, proposal=proposal,
    )
    result = coord.execute_recovery(
        proposal=proposal, envelopes=[env_a, env_b], current_epoch=10,
    )
    assert result["executed"] is True
    assert result["production_security_claim"] is True
    assert result["quorum_report"]["quorum_met"] is True
    assert result["quorum_report"]["aggregate_verified"] is True


# -- Recovery rejection with insufficient quorum ------------------------------

def test_recovery_rejection_with_insufficient_quorum() -> None:
    coord, guardians, _ = _make_coordinator_with_guardians(3, 2)
    _gid_a, sk_a, _ = guardians[0]
    new_pk = bls_public_key_hex_from_private_key_v0(
        generate_tau_testnet_compatible_private_key_hex()
    )
    proposal = coord.submit_recovery_proposal(
        proposal_id="rec-reject-1", subject_key_id="perps-wallet-a",
        replacement_key_id="perps-wallet-b", replacement_public_key=new_pk,
        requested_at_epoch=10, policy_id="recovery-policy-1",
    )
    env_a = coord.guardian_sign_proposal(
        guardian_id="guardian-a", guardian_private_key_hex=sk_a, proposal=proposal,
    )
    report = coord.verify_quorum(
        proposal=proposal, envelopes=[env_a], payload_kind=PAYLOAD_KIND_RECOVERY,
    )
    assert report["quorum_met"] is False
    assert report["accepted_weight"] == 0
    result = coord.execute_recovery(
        proposal=proposal, envelopes=[env_a], current_epoch=10,
    )
    assert result["executed"] is False
    assert "quorum threshold not met" in result["errors"]


# -- Key rotation ceremony ----------------------------------------------------

def test_key_rotation_ceremony() -> None:
    coord, guardians, _ = _make_coordinator_with_guardians(3, 2)
    _gid_a, sk_a, _ = guardians[0]
    _gid_b, sk_b, _ = guardians[1]
    new_pk = bls_public_key_hex_from_private_key_v0(
        generate_tau_testnet_compatible_private_key_hex()
    )
    proposal = coord.submit_rotation_proposal(
        proposal_id="rot-1", rotated_key_id="perps-wallet-a",
        replacement_key_id="perps-wallet-c", replacement_public_key=new_pk,
        requested_at_epoch=10, broadcast_at_epoch=13,
        policy_id="recovery-policy-1",
    )
    env_a = coord.guardian_sign_proposal(
        guardian_id="guardian-a", guardian_private_key_hex=sk_a,
        proposal=proposal, payload_kind=PAYLOAD_KIND_ROTATION,
    )
    env_b = coord.guardian_sign_proposal(
        guardian_id="guardian-b", guardian_private_key_hex=sk_b,
        proposal=proposal, payload_kind=PAYLOAD_KIND_ROTATION,
    )
    result = coord.execute_rotation(
        proposal=proposal, envelopes=[env_a, env_b], current_epoch=13,
    )
    assert result["executed"] is True
    assert result["quorum_report"]["quorum_met"] is True
    assert result["quorum_report"]["aggregate_verified"] is True


# -- Device approval flow -----------------------------------------------------

def test_device_approval_flow() -> None:
    coord, guardians, _ = _make_coordinator_with_guardians(3, 2)
    _gid_a, sk_a, _ = guardians[0]
    _gid_b, sk_b, _ = guardians[1]
    proposal = coord.submit_device_approval_proposal(
        proposal_id="dev-1", key_id="perps-wallet-a",
        device_descriptor={"device_label": "Hardware Wallet A", "backend_kind": "hardware_wallet"},
        requested_at_epoch=10, policy_id="recovery-policy-1",
    )
    env_a = coord.guardian_sign_proposal(
        guardian_id="guardian-a", guardian_private_key_hex=sk_a,
        proposal=proposal, payload_kind=PAYLOAD_KIND_DEVICE_APPROVAL,
    )
    env_b = coord.guardian_sign_proposal(
        guardian_id="guardian-b", guardian_private_key_hex=sk_b,
        proposal=proposal, payload_kind=PAYLOAD_KIND_DEVICE_APPROVAL,
    )
    result = coord.execute_device_approval(
        proposal=proposal, envelopes=[env_a, env_b], current_epoch=10,
    )
    assert result["executed"] is True
    assert result["quorum_report"]["quorum_met"] is True
    assert result["quorum_report"]["aggregate_verified"] is True


# -- Production security claim validation -------------------------------------

def test_production_security_claim_true_for_live_mode() -> None:
    coord, _, _ = _make_coordinator_with_guardians(3, 2, fixture_mode=False)
    assert coord.production_security_claim is True
    status = coord.coordinator_status()
    assert status["production_security_claim"] is True
    assert status["fixture_mode"] is False


# -- Fixture fallback for local-testnet ---------------------------------------

def test_fixture_fallback_for_local_testnet() -> None:
    coord, guardians, _ = _make_coordinator_with_guardians(3, 2, fixture_mode=True)
    assert coord.production_security_claim is False
    assert coord.fixture_mode is True
    _gid_a, sk_a, _ = guardians[0]
    _gid_b, sk_b, _ = guardians[1]
    new_pk = bls_public_key_hex_from_private_key_v0(
        generate_tau_testnet_compatible_private_key_hex()
    )
    proposal = coord.submit_recovery_proposal(
        proposal_id="rec-fixture-1", subject_key_id="perps-wallet-a",
        replacement_key_id="perps-wallet-b", replacement_public_key=new_pk,
        requested_at_epoch=10, policy_id="recovery-policy-1",
    )
    env_a = coord.guardian_sign_proposal(
        guardian_id="guardian-a", guardian_private_key_hex=sk_a, proposal=proposal,
    )
    env_b = coord.guardian_sign_proposal(
        guardian_id="guardian-b", guardian_private_key_hex=sk_b, proposal=proposal,
    )
    result = coord.execute_recovery(
        proposal=proposal, envelopes=[env_a, env_b], current_epoch=10,
    )
    assert result["executed"] is True
    assert result["production_security_claim"] is False
    assert result["quorum_report"]["production_security_claim"] is False
    assert result["quorum_report"]["fixture_mode"] is True
    assert result["quorum_report"]["aggregate_verified"] is True
