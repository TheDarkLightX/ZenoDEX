"""Exact retained finality-checker invocation mechanics for Spot V7 V6."""

from __future__ import annotations

import hashlib
import sqlite3

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
)
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v5 import (
    _SpotV7DormantAuthorityPacketV5,
)
from src.integration._zrpf_spot_v7_checkpoint_finality_checker_codec import (
    _CheckpointFinalityCheckerBindingV1,
    _CheckpointFinalityCheckerInputV1,
    _CheckpointFinalityCheckerPolicyV1,
    _encode_checker_request_v1,
    _expected_response_v1,
    _parse_checker_response_v1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementRejectReasonV1,
    _hash_bytes,
)
from src.integration.zrpf_spot_v7_checkpoint_finality_checker_adapter import (
    _CheckpointFinalityCheckerInvocationArtifactsV1,
    _CheckpointFinalityCheckerInvocationEvidenceV1,
    _prefixed_hash_bytes,
    _revalidate_invocation_artifacts_v1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AuthenticatedCheckpointFinalityProjectionV3,
)

_INVOCATION_TABLE_V6 = "spot_v7_checkpoint_finality_invocation_v6"


def _finality_invocation_v6_reject_reason_locked(
    connection: sqlite3.Connection,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    artifacts = _invocation_artifacts_for_packet_v6(packet)
    operational = packet.operational
    duplicate = connection.execute(
        f"""
        SELECT 1 FROM {_INVOCATION_TABLE_V6}
        WHERE finality_certificate_root = ?
           OR exact_finality_certificate_sha256 = ?
           OR request_sha256 = ?
           OR response_sha256 = ?
        """,
        (
            _hash_bytes(
                operational.finality.certificate_root,
                name="V6 finality certificate root",
            ),
            hashlib.sha256(operational.exact_finality_certificate_bytes).digest(),
            bytes.fromhex(artifacts.evidence.request_sha256),
            bytes.fromhex(artifacts.evidence.response_sha256),
        ),
    ).fetchone()
    if duplicate is not None:
        return SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN
    return None


def _persist_finality_invocation_v6(
    connection: sqlite3.Connection,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> None:
    operational = packet.operational
    artifacts = _invocation_artifacts_for_packet_v6(packet)
    evidence = artifacts.evidence
    connection.execute(
        f"""
        INSERT INTO {_INVOCATION_TABLE_V6} (
            settlement_commitment, finality_certificate_root,
            exact_finality_certificate_sha256, authority_manifest_sha256,
            checker_executable_sha256, request_sha256, response_sha256,
            exact_authority_manifest, exact_request, exact_response,
            manifest_pinned_cross_check_executed,
            release_governed_checker_identity_verified,
            hostile_same_interpreter_resistance_established,
            proof_receipt_authority, runtime_authority, release_authority,
            settlement_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 0, 0, 0, 0, 0, 0, 0)
        """,
        (
            _hash_bytes(
                _derive_capability_commitment(operational.candidate),
                name="V6 settlement commitment",
            ),
            _hash_bytes(
                operational.finality.certificate_root,
                name="V6 finality certificate root",
            ),
            hashlib.sha256(operational.exact_finality_certificate_bytes).digest(),
            bytes.fromhex(evidence.authority_manifest_sha256),
            bytes.fromhex(evidence.executable_sha256),
            bytes.fromhex(evidence.request_sha256),
            bytes.fromhex(evidence.response_sha256),
            artifacts.exact_authority_manifest_bytes,
            artifacts.exact_request_bytes,
            artifacts.exact_response_bytes,
        ),
    )


def _stored_finality_invocation_matches_v6(
    connection: sqlite3.Connection,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> bool:
    commitment = _hash_bytes(
        _derive_capability_commitment(packet.operational.candidate),
        name="V6 stored settlement commitment",
    )
    row = connection.execute(
        f"SELECT * FROM {_INVOCATION_TABLE_V6} WHERE settlement_commitment = ?",
        (commitment,),
    ).fetchone()
    if row is None:
        return False
    try:
        _validate_finality_invocation_row_v6(row, packet)
    except (TypeError, ValueError):
        return False
    return True


def _validate_finality_invocation_row_v6(
    row: sqlite3.Row,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> None:
    stored = _stored_invocation_artifacts_v6(row)
    expected = _invocation_artifacts_for_packet_v6(packet)
    operational = packet.operational
    expected_blobs = {
        "settlement_commitment": _hash_bytes(
            _derive_capability_commitment(operational.candidate),
            name="V6 stored settlement commitment",
        ),
        "finality_certificate_root": _hash_bytes(
            operational.finality.certificate_root,
            name="V6 stored finality certificate root",
        ),
        "exact_finality_certificate_sha256": hashlib.sha256(
            operational.exact_finality_certificate_bytes
        ).digest(),
        "authority_manifest_sha256": bytes.fromhex(expected.evidence.authority_manifest_sha256),
        "checker_executable_sha256": bytes.fromhex(expected.evidence.executable_sha256),
        "request_sha256": bytes.fromhex(expected.evidence.request_sha256),
        "response_sha256": bytes.fromhex(expected.evidence.response_sha256),
        "exact_authority_manifest": expected.exact_authority_manifest_bytes,
        "exact_request": expected.exact_request_bytes,
        "exact_response": expected.exact_response_bytes,
    }
    for field, expected_value in expected_blobs.items():
        if bytes(row[field]) != expected_value:
            raise ValueError(f"Spot V7 V6 finality invocation mismatch: {field}")
    if stored != expected:
        raise ValueError("Spot V7 V6 stored invocation differs from the exact packet")
    if int(row["manifest_pinned_cross_check_executed"]) != 1:
        raise ValueError("Spot V7 V6 checker-execution evidence mismatch")
    false_fields = (
        "release_governed_checker_identity_verified",
        "hostile_same_interpreter_resistance_established",
        "proof_receipt_authority",
        "runtime_authority",
        "release_authority",
        "settlement_authority",
        "production_authority",
    )
    if any(int(row[field]) != 0 for field in false_fields):
        raise ValueError("Spot V7 V6 finality-invocation nonclaim mismatch")


def _stored_invocation_artifacts_v6(
    row: sqlite3.Row,
) -> _CheckpointFinalityCheckerInvocationArtifactsV1:
    evidence = _CheckpointFinalityCheckerInvocationEvidenceV1(
        authority_manifest_sha256=bytes(row["authority_manifest_sha256"]).hex(),
        executable_sha256=bytes(row["checker_executable_sha256"]).hex(),
        request_sha256=bytes(row["request_sha256"]).hex(),
        response_sha256=bytes(row["response_sha256"]).hex(),
    )
    return _CheckpointFinalityCheckerInvocationArtifactsV1(
        exact_authority_manifest_bytes=bytes(row["exact_authority_manifest"]),
        exact_request_bytes=bytes(row["exact_request"]),
        exact_response_bytes=bytes(row["exact_response"]),
        evidence=evidence,
    )


def _invocation_artifacts_for_packet_v6(
    packet: _SpotV7DormantAuthorityPacketV5,
) -> _CheckpointFinalityCheckerInvocationArtifactsV1:
    if type(packet) is not _SpotV7DormantAuthorityPacketV5:
        raise TypeError("Spot V7 V6 requires the exact dormant authority packet V5")
    operational = packet.operational
    artifacts = operational.checkpoint_finality_checker_invocation
    if type(artifacts) is not _CheckpointFinalityCheckerInvocationArtifactsV1:
        raise TypeError("Spot V7 V6 packet retained the wrong invocation-artifact type")
    _revalidate_invocation_artifacts_v1(artifacts)
    checker_input = _checker_input_from_packet_v6(packet)
    expected_request = _encode_checker_request_v1(checker_input)
    if artifacts.exact_request_bytes != expected_request:
        raise ValueError("Spot V7 V6 checker request differs from exact finality")
    expected_response = _expected_response_v1(expected_request, checker_input)
    _parse_checker_response_v1(artifacts.exact_response_bytes, expected_response)
    return artifacts


def _checker_input_from_packet_v6(
    packet: _SpotV7DormantAuthorityPacketV5,
) -> _CheckpointFinalityCheckerInputV1:
    operational = packet.operational
    store_policy = operational.policy._base_store_policy_for_finality_v3()
    finality = operational.finality
    policy_root = _prefixed_hash_bytes(
        store_policy.checkpoint_finality_policy_root,
        "checkpoint-finality policy root",
    )
    if policy_root != _prefixed_hash_bytes(finality.policy_root, "finality policy root"):
        raise ValueError("Spot V7 V6 finality policy differs from governed policy")
    return _CheckpointFinalityCheckerInputV1(
        policy=_checker_policy_v6(store_policy),
        binding=_checker_binding_v6(store_policy, finality, policy_root),
        exact_certificate_bytes=operational.exact_finality_certificate_bytes,
    )


def _checker_policy_v6(
    store_policy: _TestOnlySpotV7OperationalPolicyV1,
) -> _CheckpointFinalityCheckerPolicyV1:
    return _CheckpointFinalityCheckerPolicyV1(
        application_id=_prefixed_hash_bytes(store_policy.application_id, "application ID"),
        chain_or_domain_id=_prefixed_hash_bytes(store_policy.chain_or_domain_id, "domain ID"),
        finality_network_id=_prefixed_hash_bytes(
            store_policy.finality_network_id,
            "finality network ID",
        ),
        finality_protocol_id=_prefixed_hash_bytes(
            store_policy.finality_protocol_id,
            "finality protocol ID",
        ),
        external_finality_policy_hash=_prefixed_hash_bytes(
            store_policy.external_finality_policy_hash,
            "external finality policy hash",
        ),
        finality_verifier_set_root=_prefixed_hash_bytes(
            store_policy.finality_verifier_set_root,
            "finality verifier set root",
        ),
        genesis_application_checkpoint_sequence=(
            store_policy.genesis_application_checkpoint_sequence
        ),
        genesis_application_checkpoint_hash=_prefixed_hash_bytes(
            store_policy.genesis_application_checkpoint_hash,
            "genesis checkpoint hash",
        ),
    )


def _checker_binding_v6(
    store_policy: _TestOnlySpotV7OperationalPolicyV1,
    finality: _AuthenticatedCheckpointFinalityProjectionV3,
    policy_root: bytes,
) -> _CheckpointFinalityCheckerBindingV1:
    return _CheckpointFinalityCheckerBindingV1(
        application_id=_prefixed_hash_bytes(finality.application_id, "application ID"),
        chain_or_domain_id=_prefixed_hash_bytes(finality.chain_or_domain_id, "domain ID"),
        epoch_id=finality.epoch_id,
        proof_journal_hash=_prefixed_hash_bytes(
            finality.proof_journal_hash,
            "proof journal hash",
        ),
        post_state_root=_prefixed_hash_bytes(finality.post_state_root, "post-state root"),
        application_checkpoint_sequence=finality.next_application_checkpoint_sequence,
        application_checkpoint_hash=_prefixed_hash_bytes(
            finality.next_application_checkpoint_hash,
            "next checkpoint hash",
        ),
        parent_application_checkpoint_hash=_prefixed_hash_bytes(
            finality.prior_application_checkpoint_hash,
            "prior checkpoint hash",
        ),
        finality_network_id=_prefixed_hash_bytes(
            store_policy.finality_network_id,
            "finality network ID",
        ),
        finality_protocol_id=_prefixed_hash_bytes(
            store_policy.finality_protocol_id,
            "finality protocol ID",
        ),
        external_finality_policy_hash=_prefixed_hash_bytes(
            store_policy.external_finality_policy_hash,
            "external finality policy hash",
        ),
        finality_verifier_set_root=_prefixed_hash_bytes(
            store_policy.finality_verifier_set_root,
            "finality verifier set root",
        ),
        finality_evidence_root=_prefixed_hash_bytes(
            finality.finality_evidence_root,
            "finality evidence root",
        ),
        finality_policy_root=policy_root,
        certificate_root=_prefixed_hash_bytes(
            finality.certificate_root,
            "finality certificate root",
        ),
    )


__all__ = ()
