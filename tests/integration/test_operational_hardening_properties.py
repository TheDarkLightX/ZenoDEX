from __future__ import annotations

import importlib.util

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.integration.zeno_key_manager import (
    KeyRef,
    KeyUsePolicy,
    RecoveryGuardian,
    SignRequestContext,
    SocialRecoveryPolicy,
)
from src.integration.zeno_key_manager_v0 import (
    BACKEND_TAU_BLS_IMPORT,
    KeyBackendDescriptor,
    SignAdmissionRequest,
    evaluate_sign_admission_v0,
)
from src.integration.zeno_key_recovery_v0 import evaluate_recovery_rotation_v0
from tools.check_upba_policy_profiles import validate_upba_policy_profile_v1
from tools.zeno_ledger_network_scenario import BlockEnvelope, ChaosNetworkModel
from tools.zenoctl import build_node_status_snapshot, derive_node_hash_v0

PUBKEY_A = "0x" + "11" * 48
PUBKEY_B = "0x" + "22" * 48
ROOT_A = "0x" + "aa" * 32


def _sign_request(payload: dict[str, object], *, seen_nonces: tuple[int, ...] = ()) -> SignAdmissionRequest:
    key_ref = KeyRef(key_id="k", public_key=PUBKEY_A)
    return SignAdmissionRequest(
        key_ref=key_ref,
        backend=KeyBackendDescriptor(
            key_id="k",
            backend_kind=BACKEND_TAU_BLS_IMPORT,
            backend_id="tau-wallet",
            policy_hash=ROOT_A,
        ),
        policy=KeyUsePolicy(
            allowed_payload_kinds=("checkpoint",),
            allowed_chain_ids=("tau-testnet-1",),
        ),
        context=SignRequestContext(
            payload_kind="checkpoint",
            chain_id="tau-testnet-1",
            purpose="sign",
            current_epoch=1,
        ),
        payload=payload,
        seen_nonces=seen_nonces,
    )


@settings(max_examples=50)
@given(nonce=st.integers(min_value=0, max_value=10_000))
def test_sign_admission_reused_nonce_is_always_rejected(nonce: int) -> None:
    receipt = evaluate_sign_admission_v0(
        _sign_request(
            {"domain": "zenodex.ledger.checkpoint.v0", "chain_id": "tau-testnet-1", "nonce": nonce},
            seen_nonces=(nonce,),
        )
    )

    assert receipt["ok"] is False
    assert "payload_nonce_reused" in receipt["errors"]


@settings(max_examples=50)
@given(chain_id=st.text(min_size=0, max_size=16).filter(lambda value: value != "tau-testnet-1"))
def test_sign_admission_payload_chain_mismatch_is_always_rejected(chain_id: str) -> None:
    receipt = evaluate_sign_admission_v0(
        _sign_request({"domain": "zenodex.ledger.checkpoint.v0", "chain_id": chain_id, "nonce": 1})
    )

    assert receipt["ok"] is False
    assert "payload_chain_id_mismatch" in receipt["errors"]


@settings(max_examples=25)
@given(secret_field=st.sampled_from(["private_key", "private_key_hex", "privkey", "seed", "mnemonic"]))
def test_sign_admission_secret_fields_are_never_accepted(secret_field: str) -> None:
    with pytest.raises(ValueError, match="private key material"):
        _sign_request(
            {
                "domain": "zenodex.ledger.checkpoint.v0",
                "chain_id": "tau-testnet-1",
                "nonce": 1,
                secret_field: "secret",
            }
        )


@settings(max_examples=50)
@given(
    requested_at=st.integers(min_value=0, max_value=20),
    delay=st.integers(min_value=0, max_value=8),
    extra=st.integers(min_value=0, max_value=8),
)
def test_recovery_threshold_delay_is_monotone_after_unlock(requested_at: int, delay: int, extra: int) -> None:
    policy = SocialRecoveryPolicy(
        policy_id="recover",
        subject_key_id="old",
        threshold=2,
        delay_epochs=delay,
        guardians=(
            RecoveryGuardian(guardian_id="g1", public_key=PUBKEY_A),
            RecoveryGuardian(guardian_id="g2", public_key=PUBKEY_B),
        ),
    )
    new_key = KeyRef(key_id="new", public_key=PUBKEY_B, replaces_key_id="old")
    ready_epoch = requested_at + delay + extra

    ready = evaluate_recovery_rotation_v0(
        policy=policy,
        approvals=("g1", "g2"),
        requested_at_epoch=requested_at,
        current_epoch=ready_epoch,
        new_key_ref=new_key,
        recovery_nonce="r",
    )

    assert ready["ok"] is True
    if delay > 0:
        early = evaluate_recovery_rotation_v0(
            policy=policy,
            approvals=("g1", "g2"),
            requested_at_epoch=requested_at,
            current_epoch=requested_at + delay - 1,
            new_key_ref=new_key,
            recovery_nonce="r",
        )
        assert early["ok"] is False
        assert "recovery_policy_not_satisfied" in early["errors"]


@settings(max_examples=25)
@given(kind=st.sampled_from(["bad_auth", "oversized", "wrong_proposer", "wrong_previous"]))
def test_invalid_chaos_block_never_advances_height(kind: str) -> None:
    model = ChaosNetworkModel()
    model.add_node("node-a")
    block = model.make_block(node_id="node-a")
    updates: dict[str, object] = {}
    if kind == "bad_auth":
        updates["auth_token"] = "bad"
    elif kind == "oversized":
        updates["tx_count"] = model.max_tx_count + 1
    elif kind == "wrong_proposer":
        updates["proposer_id"] = "validator-c"
    elif kind == "wrong_previous":
        updates["previous_hash"] = "0x" + "99" * 32
    bad = BlockEnvelope(**{**block.__dict__, **updates})

    result = model.submit_block(node_id="node-a", envelope=bad)

    assert result["ok"] is False
    assert model.node("node-a").height == 0


@settings(max_examples=50)
@given(
    peer_count=st.integers(min_value=0, max_value=20),
    gossip_rejections=st.integers(min_value=0, max_value=20),
    slashing_evidence=st.integers(min_value=0, max_value=20),
    proof_mismatches=st.integers(min_value=0, max_value=20),
    key_rejections=st.integers(min_value=0, max_value=20),
)
def test_operator_readiness_score_is_bounded(
    peer_count: int,
    gossip_rejections: int,
    slashing_evidence: int,
    proof_mismatches: int,
    key_rejections: int,
) -> None:
    snapshot = build_node_status_snapshot(
        ledger_height=1,
        peer_count=peer_count,
        gossip_rejections=gossip_rejections,
        slashing_evidence=slashing_evidence,
        proof_metadata_mismatches=proof_mismatches,
        key_admission_rejections=key_rejections,
        network_id="n",
        chain_id="c",
        node_id="node-a",
        deployment_profile="public-testnet",
        proof_profile="spot_v1_single_pool_success",
        upba_policy="balanced",
    )

    assert 0 <= snapshot["operator_readiness_score"] <= 100
    if proof_mismatches > 0:
        assert snapshot["operator_readiness_score"] <= 60


@settings(max_examples=50)
@given(
    network_id=st.text(alphabet="abcdefghijklmnopqrstuvwxyz0123456789-_", min_size=1, max_size=24),
    chain_id=st.text(alphabet="abcdefghijklmnopqrstuvwxyz0123456789-_", min_size=1, max_size=24),
    node_identity=st.text(alphabet="abcdefghijklmnopqrstuvwxyz0123456789-_:.", min_size=1, max_size=48),
)
def test_node_hash_is_stable_chain_bound_and_hash_shaped(
    network_id: str,
    chain_id: str,
    node_identity: str,
) -> None:
    first = derive_node_hash_v0(
        network_id=network_id,
        chain_id=chain_id,
        node_identity=node_identity,
    )
    second = derive_node_hash_v0(
        network_id=network_id,
        chain_id=chain_id,
        node_identity=node_identity,
    )

    assert first == second
    assert first.startswith("0x")
    assert len(first) == 66
    assert first != node_identity


@settings(max_examples=25)
@given(omit_requires_certificate=st.booleans())
def test_upba_energy_omission_policy_is_fail_closed(omit_requires_certificate: bool) -> None:
    profile = {
        "schema": "zenodex/upba_policy_profile/v1",
        "profile_id": "balanced",
        "max_relative_loss_ppm": 25,
        "max_absolute_loss_atoms": 10000,
        "fill_quantum_atoms": 100,
        "candidate_evaluation_count": 10000,
        "max_trade_fraction_ppm": 100000,
        "proof_required": True,
        "energy_scorer_allowed": True,
        "energy_may_omit_candidates": True,
        "energy_omit_requires_certificate": omit_requires_certificate,
        "fallback_required": True,
        "user_warning_required": False,
    }

    report = validate_upba_policy_profile_v1(profile)

    assert report["ok"] is False
    assert "default ZenoEnergy policy must be order-only" in report["errors"]
