from __future__ import annotations

import pytest

from src.integration.production_key_management_v0 import (
    DEFAULT_ACTION_POLICIES_V0,
    build_admission_receipt_v0,
    build_key_descriptor_v0,
    build_privileged_action_packet_v0,
    build_signature_envelope_v0,
)
from src.integration.zeno_ledger_v0 import ZERO_ROOT_V0, build_proof_metadata_v0, hash_v0
from src.integration.zeno_ledger_verifier_registry_v0 import (
    VERIFIER_STATUS_REVOKED_V0,
    clone_verifier_registry_with_new_id_v0,
    make_verifier_registry_entry_v0,
    make_verifier_registry_v0,
    validate_proof_metadata_against_verifier_registry_v0,
    validate_verifier_registry_v0,
)


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _metadata(*, proof_kind: str = "risc0_zkvm_v0", height: int = 7) -> dict[str, object]:
    return build_proof_metadata_v0(
        chain_id="zeno-ledger-devnet-0",
        height=height,
        proof_kind=proof_kind,
        program_id="risc0:zenodex-spot-transition-v1",
        verifier_id="risc0:receipt-verifier-v1",
        proof_commitment=_root("proof-commitment"),
        public_input_hash=_root("public-input"),
        journal_hash=_root("journal"),
        pre_state_root=_root("pre-state"),
        post_state_root=_root("post-state"),
        tx_root=_root("tx"),
        evidence_root=_root("evidence"),
        body_root=_root("body"),
        conflict_schedule_hash=_root("schedule"),
        feature_suite_hash=_root("feature-suite"),
        dependency_lock_hash=_root("dependency-lock"),
        toolchain_lock_hash=_root("toolchain-lock"),
    )


def _pkm_receipt(action: str = "verifier_registry_update") -> dict[str, object]:
    policy = DEFAULT_ACTION_POLICIES_V0[action]
    packet = build_privileged_action_packet_v0(
        environment="production",
        action=action,
        target_kind="zeno_ledger_verifier_registry",
        target_hash=_root(f"{action}-target"),
        policy_hash=str(policy["policy_hash"]),
        nonce=1,
        epoch=10,
        not_before_epoch=5,
        expires_at_epoch=20,
        payload_hash=_root(f"{action}-payload"),
    )
    keys = [
        build_key_descriptor_v0(
            key_id=f"{action}-key-{index}",
            public_key=f"{action}-pub-{index}",
            role=str(policy["role"]),
            environment="production",
            status="active",
            storage_class="hardware",
            custodian_id=f"{action}-custodian-{index}",
            valid_from_epoch=0,
            valid_until_epoch=100,
        )
        for index in range(int(policy["threshold"]))
    ]
    envelopes = [
        build_signature_envelope_v0(
            key_id=str(key["key_id"]),
            public_key=str(key["public_key"]),
            packet_hash=str(packet["packet_hash"]),
            signature_scheme="external-verifier-v0",
            signature=f"fixture:{key['key_id']}:{packet['packet_hash']}",
        )
        for key in keys
    ]
    return build_admission_receipt_v0(
        packet,
        policy,
        keys,
        envelopes,
        transparency_log_hash=_root(f"{action}-transparency"),
        signature_verifier=lambda p, d, e: e["signature"] == f"fixture:{d['key_id']}:{p['packet_hash']}",
    )


def test_verifier_registry_admits_matching_metadata() -> None:
    metadata = _metadata()
    entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
        valid_from_height=0,
        valid_until_height=10,
    )
    registry = make_verifier_registry_v0(entries=[entry])

    validate_verifier_registry_v0(registry)
    validate_proof_metadata_against_verifier_registry_v0(
        proof_metadata=metadata,
        registry=registry,
    )


def test_verifier_registry_rejects_unlisted_and_revoked_verifier() -> None:
    metadata = _metadata()
    wrong_entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id="risc0:other-verifier",
    )
    wrong_registry = make_verifier_registry_v0(entries=[wrong_entry])
    with pytest.raises(ValueError, match="not admitted"):
        validate_proof_metadata_against_verifier_registry_v0(
            proof_metadata=metadata,
            registry=wrong_registry,
        )

    revoked_entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
        status=VERIFIER_STATUS_REVOKED_V0,
    )
    revoked_registry = make_verifier_registry_v0(entries=[revoked_entry])
    with pytest.raises(ValueError, match="not active"):
        validate_proof_metadata_against_verifier_registry_v0(
            proof_metadata=metadata,
            registry=revoked_registry,
        )


def test_verifier_registry_rejects_height_outside_window() -> None:
    metadata = _metadata(height=7)
    entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
        valid_from_height=8,
    )
    registry = make_verifier_registry_v0(entries=[entry])

    with pytest.raises(ValueError, match="precedes"):
        validate_proof_metadata_against_verifier_registry_v0(
            proof_metadata=metadata,
            registry=registry,
        )


def test_tee_registry_entry_requires_measurement() -> None:
    with pytest.raises(ValueError, match="requires tee_measurement_hash"):
        make_verifier_registry_entry_v0(
            proof_kind="tee_attestation_v0",
            program_id="tee:route-premium-v1:tee-policy-v1",
            verifier_id="tee:nitro-advisory-verifier-v1",
            tee_measurement_hash=ZERO_ROOT_V0,
        )


def test_verifier_registry_hash_rejects_tampering() -> None:
    metadata = _metadata()
    entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
    )
    registry = make_verifier_registry_v0(entries=[entry])
    tampered = clone_verifier_registry_with_new_id_v0(registry)
    tampered["registry_id"] = _root("bad-registry")

    with pytest.raises(ValueError, match="registry_id mismatch"):
        validate_verifier_registry_v0(tampered)


def test_production_strict_verifier_registry_requires_key_admission() -> None:
    metadata = _metadata()
    entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
    )
    registry = make_verifier_registry_v0(entries=[entry])

    with pytest.raises(ValueError, match="admission receipt is required"):
        validate_verifier_registry_v0(registry, require_production_key_admission=True)

    with pytest.raises(ValueError, match="cannot be validated without full signed admission evidence"):
        validate_verifier_registry_v0(
            registry,
            require_production_key_admission=True,
            production_key_admission_receipt=_pkm_receipt(),
        )


def test_production_strict_verifier_registry_rejects_wrong_key_admission() -> None:
    metadata = _metadata()
    entry = make_verifier_registry_entry_v0(
        proof_kind=str(metadata["proof_kind"]),
        program_id=str(metadata["program_id"]),
        verifier_id=str(metadata["verifier_id"]),
    )
    registry = make_verifier_registry_v0(entries=[entry])

    with pytest.raises(ValueError, match="cannot be validated without full signed admission evidence"):
        validate_verifier_registry_v0(
            registry,
            require_production_key_admission=True,
            production_key_admission_receipt=_pkm_receipt("public_network_config_update"),
        )
