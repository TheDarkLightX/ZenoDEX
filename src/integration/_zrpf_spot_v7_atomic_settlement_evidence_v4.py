"""Exact DA and finality evidence replay for Spot V7 schema V4."""

from __future__ import annotations

import hashlib
import sqlite3
from collections.abc import Mapping
from typing import Any, cast

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _derive_test_only_full_blob_artifacts_v1,
    _encode_checkpoint_finality_certificate_v2,
    _finality_certificate_root_v2,
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _decode_exact_json_object,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    _ZERO_ROOT,
    SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2,
    SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3,
    ZenoLedgerCheckpointFinalityCursorV1,
    _snapshot_inputs,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_finality_protocol_id_v3,
)
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    hash_v0,
)
from src.integration.zrpf_sampled_retrievability_v1.hashing import (
    derive_exact_full_blob_target_v1,
)
from src.integration.zrpf_sampled_retrievability_v1.model import BeaconCommitmentV1
from src.integration.zrpf_sampled_retrievability_v1.verifier import (
    verify_exact_evidence_v1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import _hex_hash
from src.integration.zrpf_spot_v7_lagged_checkpoint_beacon import (
    derive_lagged_checkpoint_beacon_commitment_v1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _authenticate_checkpoint_quorum_core,
    _require_checkpoint_transition_binding,
    _require_registry_and_external_policy_binding,
    _require_scheduled_header_admission,
    _validate_checkpoint_structure,
    _validate_header_app_hash,
)

_FINALITY_EVIDENCE_V2_FIELDS = frozenset(
    {
        "application_binding",
        "checkpoint",
        "envelopes",
        "header",
        "live_quorum_admission",
        "prior_application_checkpoint",
        "proposer_authorship_admission",
        "proposer_envelope",
        "registry",
        "replay_bound_observation",
        "scheduled_header_admission",
        "schema",
        "validator_set",
    }
)
_FINALITY_EVIDENCE_V3_FIELDS = frozenset(
    {
        "application_binding",
        "checkpoint",
        "claims",
        "envelopes",
        "header",
        "live_quorum_admission",
        "prior_application_checkpoint",
        "proposer_authorship_admission",
        "proposer_envelope",
        "registry",
        "scheduled_header_admission",
        "schema",
        "settlement_replay_observation",
        "validator_set",
    }
)
_SOURCE_APPLICATION_BINDING_FIELDS = frozenset(
    {
        "application_id",
        "chain_or_domain_id",
        "epoch_id",
        "post_state_root",
        "proof_journal_hash",
    }
)
_CHECKPOINT_CURSOR_FIELDS = frozenset({"checkpoint_hash", "sequence"})
_FINALITY_V3_CLAIMS = {
    "application_domain_to_ledger_chain_binding_established": False,
    "candidate_effect_and_state_bindings_checked": True,
    "canonical_conflicting_checkpoint_selection_established": False,
    "cryptographic_checkpoint_quorum_supported": True,
    "durable_settlement_replay_material_persisted": False,
    "durable_settlement_replay_reverified": False,
    "exact_header_derived_from_sealed_replay": True,
    "exact_replay_material_authenticated": True,
    "exact_settlement_envelope_replay_bound": True,
    "hostile_same_interpreter_resistance_established": False,
    "production_authority": False,
    "proof_receipt_authentication_established": False,
    "public_data_retrievability_established": False,
    "release_authority": False,
    "replay_material_commitment_bound": True,
    "settlement_authority": False,
}
_SOURCE_REPLAY_OBSERVATION_FIELDS = frozenset(
    {
        "body_committed_proof_journal_hash",
        "body_root",
        "body_sha256",
        "chain_id",
        "committed_proof_receipt_count",
        "committed_proof_receipts_root",
        "config_digest",
        "config_document_root",
        "evidence_root",
        "header_hash",
        "height",
        "ingress_root",
        "observation_evidence_root",
        "parent_header_hash",
        "post_state_root",
        "pre_snapshot_sha256",
        "pre_state_root",
        "prior_header_hash",
        "replayed_receipt_count",
        "replayed_receipts_root",
        "replayed_rejection_count",
        "replayed_rejections_root",
        "transaction_root",
    }
)


def _validate_da_row(
    policy: _GovernedSpotV7OperationalPolicyV3,
    *,
    candidate_epoch: int,
    settlement_row: sqlite3.Row,
    row: sqlite3.Row,
) -> None:
    base_policy = policy._base_store_policy_for_full_blob_v2()
    sampled_policy = policy._sampled_policy_for_governed_da_v2()
    beacon_policy = policy._beacon_policy_for_governed_da_v2()
    checked_epoch = int.from_bytes(bytes(row["checked_epoch_be"]), "big")
    policy._require_active_at_epoch_for_governed_da_v2(checked_epoch)
    retention = int.from_bytes(bytes(row["retention_through_epoch_be"]), "big")
    exact_blob = bytes(row["exact_full_blob"])
    exact_certificate = bytes(row["exact_full_blob_certificate"])
    full = _derive_test_only_full_blob_artifacts_v1(
        policy=base_policy,
        epoch_id=candidate_epoch,
        checked_epoch=checked_epoch,
        retention_through_epoch=retention,
        exact_blob_bytes=exact_blob,
        exact_certificate_bytes=exact_certificate,
    )
    target = derive_exact_full_blob_target_v1(
        application_id=base_policy.application_id,
        chain_or_domain_id=base_policy.chain_or_domain_id,
        epoch_id=candidate_epoch,
        data_schema_id=base_policy.data_schema_id,
        exact_blob_bytes=exact_blob,
        retention_through_epoch=retention,
        storage_policy_hash=base_policy.storage_policy_hash,
    )
    beacon = BeaconCommitmentV1.validated(
        source_id=sampled_policy.beacon_source_id,
        policy_hash=sampled_policy.beacon_policy_hash,
        beacon_epoch=checked_epoch,
        commitment=_hex_hash(bytes(row["beacon_commitment"])),
    )
    sampled = verify_exact_evidence_v1(
        bytes(row["exact_sampled_evidence"]),
        expected_policy=sampled_policy,
        expected_target=target,
        expected_beacon=beacon,
        checked_epoch=checked_epoch,
    )._projection_for_spot_v7_da_prerequisite_v1()
    provider_root = hash_v0(
        "zrpf_spot_v7_sampled_provider_set_v1",
        list(sampled.accepted_provider_ids),
    )
    expected = (
        (_hex_hash(bytes(row["certificate_root"])), full.certificate_root),
        (_hex_hash(bytes(row["data_root"])), full.data_root),
        (_hex_hash(bytes(row["chunk_root"])), full.chunk_root),
        (_hex_hash(bytes(row["full_blob_policy_root"])), full.policy_root),
        (_hex_hash(bytes(row["sampled_policy_root"])), sampled.policy_root),
        (
            _hex_hash(bytes(row["exact_blob_sha256"])),
            "0x" + hashlib.sha256(exact_blob).hexdigest(),
        ),
        (bytes(row["sampled_evidence_sha256"]).hex(), sampled.evidence_sha256),
        (_hex_hash(bytes(row["accepted_provider_set_root"])), provider_root),
        (
            _hex_hash(bytes(settlement_row["data_availability_certificate_root"])),
            full.certificate_root,
        ),
        (_hex_hash(bytes(settlement_row["data_root"])), full.data_root),
        (_hex_hash(bytes(row["source_network_id"])), beacon_policy.source_network_id),
        (_hex_hash(bytes(row["source_protocol_id"])), beacon_policy.source_protocol_id),
        (
            _hex_hash(bytes(row["source_finality_policy_root"])),
            policy._projection_for_governed_da_v2().beacon_source_finality_policy_root,
        ),
    )
    if any(left != right for left, right in expected):
        raise ValueError("Spot V7 V4 DA row binding mismatch")
    if int.from_bytes(bytes(row["source_epoch_lag_be"]), "big") != (beacon_policy.source_epoch_lag):
        raise ValueError("Spot V7 V4 DA source lag mismatch")
    expected_beacon_commitment = derive_lagged_checkpoint_beacon_commitment_v1(
        beacon_policy=beacon_policy,
        checked_epoch=checked_epoch,
        source_checkpoint_sequence=int.from_bytes(
            bytes(row["source_checkpoint_sequence_be"]), "big"
        ),
        source_checkpoint_hash=_hex_hash(bytes(row["source_checkpoint_hash"])),
    )
    if _hex_hash(bytes(row["beacon_commitment"])) != expected_beacon_commitment:
        raise ValueError("Spot V7 V4 DA beacon commitment mismatch")
    _validate_source_finality_evidence(policy, row, checked_epoch=checked_epoch)
    _require_binary_flags(
        row,
        true_fields=(
            "exact_content_verified",
            "sampled_policy_governance_verified",
            "governed_beacon_provenance_verified",
        ),
        false_fields=(
            "public_future_availability_verified",
            "settlement_authority",
            "production_authority",
        ),
    )


def _validate_source_finality_evidence(
    policy: _GovernedSpotV7OperationalPolicyV3,
    row: sqlite3.Row,
    *,
    checked_epoch: int,
) -> None:
    evidence = bytes(row["exact_source_finality_evidence"])
    document = _verify_quorum_evidence(
        evidence,
        verification_policy=policy._base_store_policy_for_governed_beacon_v1(),
        expected_schema=SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2,
        expected_protocol=derive_zeno_ledger_finality_protocol_id_v2(),
        expected_fields=_FINALITY_EVIDENCE_V2_FIELDS,
    )
    binding = _exact_mapping(document, "application_binding")
    prior = _exact_mapping(document, "prior_application_checkpoint")
    checkpoint = _exact_mapping(document, "checkpoint")
    header = _exact_mapping(document, "header")
    replay = _exact_mapping(document, "replay_bound_observation")
    _require_exact_keys(binding, _SOURCE_APPLICATION_BINDING_FIELDS, "source binding")
    _require_exact_keys(prior, _CHECKPOINT_CURSOR_FIELDS, "source prior cursor")
    _require_exact_keys(replay, _SOURCE_REPLAY_OBSERVATION_FIELDS, "source replay observation")
    source_sequence = int.from_bytes(bytes(row["source_checkpoint_sequence_be"]), "big")
    source_hash = _hex_hash(bytes(row["source_checkpoint_hash"]))
    source_policy = policy._base_store_policy_for_governed_beacon_v1()
    prior_sequence = _exact_int(prior, "sequence")
    prior_hash = _exact_str(prior, "checkpoint_hash")
    expected_parent = (
        None
        if prior_sequence == source_policy.genesis_application_checkpoint_sequence
        else prior_hash
    )
    projection = policy._projection_for_governed_da_v2()
    expected_binding = {
        "application_id": projection.application_id,
        "chain_or_domain_id": projection.chain_or_domain_id,
        "epoch_id": source_sequence,
        "post_state_root": header.get("post_state_root"),
        "proof_journal_hash": header.get("proof_journal_hash"),
    }
    replay_header_bindings = (
        (replay.get("chain_id"), header.get("chain_id")),
        (replay.get("height"), header.get("height")),
        (replay.get("header_hash"), source_hash),
        (replay.get("body_root"), header.get("body_root")),
        (replay.get("config_digest"), header.get("config_digest")),
        (replay.get("evidence_root"), header.get("evidence_root")),
        (replay.get("ingress_root"), header.get("ingress_root")),
        (replay.get("transaction_root"), header.get("tx_root")),
        (replay.get("pre_state_root"), header.get("pre_state_root")),
        (replay.get("post_state_root"), header.get("post_state_root")),
        (replay.get("prior_header_hash"), header.get("prev_header_hash")),
        (replay.get("parent_header_hash"), expected_parent),
        (
            replay.get("body_committed_proof_journal_hash"),
            header.get("proof_journal_hash"),
        ),
    )
    if (
        not _exact_document_equal(binding, expected_binding)
        or source_sequence + policy._beacon_policy_for_governed_da_v2().source_epoch_lag
        != checked_epoch
        or checkpoint.get("header_hash") != source_hash
        or prior_sequence + 1 != source_sequence
        or prior_sequence < source_policy.genesis_application_checkpoint_sequence
        or (
            prior_sequence == source_policy.genesis_application_checkpoint_sequence
            and prior_hash != source_policy.genesis_application_checkpoint_hash
        )
        or prior_hash != header.get("prev_header_hash")
        or header.get("height") != source_sequence
        or canonical_header_hash_v0(header) != source_hash
        or not all(_exact_value_equal(left, right) for left, right in replay_header_bindings)
    ):
        raise ValueError("Spot V7 V4 source finality scope mismatch")
    expected_policy_root = source_policy.checkpoint_finality_policy_root
    if _hex_hash(bytes(row["source_finality_policy_root"])) != expected_policy_root:
        raise ValueError("Spot V7 V4 source finality policy root mismatch")
    _validate_certificate_from_evidence(
        source_policy,
        binding=binding,
        prior=prior,
        checkpoint=checkpoint,
        evidence=evidence,
        expected_policy_root=expected_policy_root,
        expected_certificate_root=_hex_hash(bytes(row["source_finality_certificate_root"])),
        exact_certificate=bytes(row["exact_source_finality_certificate"]),
    )
    if _hex_hash(hashlib.sha256(evidence).digest()) != _hex_hash(
        bytes(row["source_finality_evidence_root"])
    ):
        raise ValueError("Spot V7 V4 source finality evidence root mismatch")


def _validate_finality_row(
    policy: _GovernedSpotV7OperationalPolicyV3,
    *,
    candidate: Any,
    settlement_row: sqlite3.Row,
    replay_projection: Mapping[str, Any],
    row: sqlite3.Row,
    prior_sequence: int,
    prior_hash: str,
) -> tuple[int, str]:
    policy._require_active_at_epoch_for_finality_v3(candidate.epoch_id)
    evidence = bytes(row["exact_finality_evidence"])
    settlement_policy = policy._base_store_policy_for_finality_v3()
    document = _verify_quorum_evidence(
        evidence,
        verification_policy=settlement_policy,
        expected_schema=SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3,
        expected_protocol=derive_zeno_ledger_finality_protocol_id_v3(),
        expected_fields=_FINALITY_EVIDENCE_V3_FIELDS,
    )
    binding = _exact_mapping(document, "application_binding")
    prior = _exact_mapping(document, "prior_application_checkpoint")
    checkpoint = _exact_mapping(document, "checkpoint")
    header = _exact_mapping(document, "header")
    next_sequence = int.from_bytes(bytes(row["next_checkpoint_sequence_be"]), "big")
    next_hash = _hex_hash(bytes(row["next_checkpoint_hash"]))
    expected_binding = {
        "application_id": candidate.application_id,
        "chain_or_domain_id": candidate.chain_or_domain_id,
        "epoch_id": candidate.epoch_id,
        "verified_program_id": candidate.verified_program_id,
        "verified_profile_id": candidate.verified_profile_id,
        "verified_program_manifest_root": candidate.verified_program_manifest_root,
        "candidate_settlement_commitment": _derive_capability_commitment(candidate),
        "settlement_effect_plan_commitment": candidate.settlement_effect_plan_commitment,
        "pre_state_root": candidate.pre_state_root,
        "post_state_root": candidate.post_state_root,
        "economic_action_id": candidate.economic_action_id,
        "authorization_nullifier": candidate.authorization_nullifier,
        "authorization_grant_spend_nullifier": (candidate.authorization_grant_spend_nullifier),
        "cell_transitions_root": candidate.cell_transitions_root,
        "proof_journal_hash": ("0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()),
    }
    if not _exact_document_equal(binding, expected_binding):
        raise ValueError("Spot V7 V4 finality application binding mismatch")
    if not _exact_document_equal(
        prior,
        {"sequence": prior_sequence, "checkpoint_hash": prior_hash},
    ):
        raise ValueError("Spot V7 V4 finality prior cursor mismatch")
    try:
        _require_checkpoint_transition_binding(
            candidate=candidate,
            cursor=ZenoLedgerCheckpointFinalityCursorV1(
                sequence=prior_sequence,
                checkpoint_hash=prior_hash,
            ),
            header=header,
            checkpoint=checkpoint,
            policy=settlement_policy,
        )
    except ValueError as exc:
        raise ValueError("Spot V7 V4 finality transition mismatch") from exc
    if (
        int.from_bytes(bytes(row["prior_checkpoint_sequence_be"]), "big") != prior_sequence
        or _hex_hash(bytes(row["prior_checkpoint_hash"])) != prior_hash
    ):
        raise ValueError("Spot V7 V4 stored finality prior cursor mismatch")
    expected_parent_hash = (
        None
        if (
            prior_sequence == settlement_policy.genesis_application_checkpoint_sequence
            and prior_hash == _ZERO_ROOT
        )
        else prior_hash
    )
    if (
        next_sequence != prior_sequence + 1
        or next_hash != replay_projection["header_hash"]
        or checkpoint.get("header_hash") != next_hash
        or replay_projection.get("parent_header_hash") != expected_parent_hash
        or _hex_hash(bytes(settlement_row["journal_sha256"])) != binding["proof_journal_hash"]
    ):
        raise ValueError("Spot V7 V4 finality successor mismatch")
    if not _exact_document_equal(
        document.get("settlement_replay_observation"),
        dict(replay_projection),
    ):
        raise ValueError("Spot V7 V4 finality replay projection mismatch")
    _require_exact_claims(document.get("claims"))
    expected_policy_root = settlement_policy.checkpoint_finality_policy_root
    if _hex_hash(bytes(row["policy_root"])) != expected_policy_root:
        raise ValueError("Spot V7 V4 finality policy root mismatch")
    _validate_certificate_from_evidence(
        settlement_policy,
        binding=binding,
        prior=prior,
        checkpoint=checkpoint,
        evidence=evidence,
        expected_policy_root=expected_policy_root,
        expected_certificate_root=_hex_hash(bytes(row["certificate_root"])),
        exact_certificate=bytes(row["exact_certificate"]),
    )
    if (
        _hex_hash(hashlib.sha256(evidence).digest())
        != _hex_hash(bytes(row["finality_evidence_root"]))
        or _hex_hash(bytes(row["proof_journal_hash"])) != binding["proof_journal_hash"]
        or _hex_hash(bytes(row["post_state_root"])) != binding["post_state_root"]
    ):
        raise ValueError("Spot V7 V4 finality row root mismatch")
    _require_binary_flags(
        row,
        true_fields=("cryptographic_checkpoint_quorum_authenticated",),
        false_fields=(
            "proof_receipt_authentication_established",
            "settlement_authority",
            "production_authority",
        ),
    )
    return next_sequence, next_hash


def _verify_quorum_evidence(
    exact_evidence: bytes,
    *,
    verification_policy: _TestOnlySpotV7OperationalPolicyV1,
    expected_schema: str,
    expected_protocol: str,
    expected_fields: frozenset[str],
) -> dict[str, Any]:
    document = _decode_exact_json_object(exact_evidence, name="V4 exact finality evidence")
    _require_exact_keys(document, expected_fields, "finality evidence")
    if document.get("schema") != expected_schema:
        raise ValueError("Spot V7 V4 finality evidence schema mismatch")
    proposer = _exact_mapping(document, "proposer_envelope")
    envelopes = document.get("envelopes")
    if type(envelopes) is not list:
        raise ValueError("Spot V7 V4 finality envelopes must be an exact array")
    snapshot = _snapshot_inputs(
        header=document.get("header"),
        checkpoint=document.get("checkpoint"),
        validator_set=document.get("validator_set"),
        proposer_id=proposer.get("signer_id"),
        proposer_key_id=proposer.get("key_id"),
        proposer_envelope=proposer,
        registry=document.get("registry"),
        envelopes=tuple(envelopes),
    )
    _validate_checkpoint_structure(snapshot)
    _validate_header_app_hash(snapshot.header)
    scheduled = _require_scheduled_header_admission(snapshot)
    _require_registry_and_external_policy_binding(
        header=snapshot.header,
        registry=snapshot.registry,
        policy=verification_policy,
        expected_finality_protocol_id=expected_protocol,
    )
    quorum = _authenticate_checkpoint_quorum_core(
        snapshot=snapshot,
        scheduled_header_admission=scheduled,
    )
    if not all(
        _exact_document_equal(observed, expected)
        for observed, expected in (
            (
                document.get("scheduled_header_admission"),
                quorum.scheduled_header_admission,
            ),
            (
                document.get("proposer_authorship_admission"),
                quorum.proposer_authorship_admission,
            ),
            (document.get("live_quorum_admission"), quorum.live_quorum_admission),
        )
    ):
        raise ValueError("Spot V7 V4 finality admission transcript mismatch")
    return document


def _validate_certificate_from_evidence(
    policy: Any,
    *,
    binding: Mapping[str, Any],
    prior: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    evidence: bytes,
    expected_policy_root: str,
    expected_certificate_root: str,
    exact_certificate: bytes,
) -> None:
    evidence_root = "0x" + hashlib.sha256(evidence).hexdigest()
    sequence = _exact_int(prior, "sequence") + 1
    certificate_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=_exact_int(binding, "epoch_id"),
        proof_journal_hash=_exact_str(binding, "proof_journal_hash"),
        post_state_root=_exact_str(binding, "post_state_root"),
        sequence=sequence,
        checkpoint_hash=_exact_str(checkpoint, "header_hash"),
        parent_hash=_exact_str(prior, "checkpoint_hash"),
        evidence_root=evidence_root,
        policy_root=expected_policy_root,
    )
    if certificate_root != expected_certificate_root:
        raise ValueError("Spot V7 V4 finality certificate root mismatch")
    expected = _encode_checkpoint_finality_certificate_v2(
        policy=policy,
        epoch_id=_exact_int(binding, "epoch_id"),
        proof_journal_hash=_exact_str(binding, "proof_journal_hash"),
        post_state_root=_exact_str(binding, "post_state_root"),
        sequence=sequence,
        checkpoint_hash=_exact_str(checkpoint, "header_hash"),
        parent_hash=_exact_str(prior, "checkpoint_hash"),
        evidence_root=evidence_root,
        policy_root=expected_policy_root,
        certificate_root=certificate_root,
    )
    if exact_certificate != expected:
        raise ValueError("Spot V7 V4 finality certificate bytes mismatch")


def _require_binary_flags(
    row: sqlite3.Row,
    *,
    true_fields: tuple[str, ...],
    false_fields: tuple[str, ...],
) -> None:
    if any(int(row[field]) != 1 for field in true_fields) or any(
        int(row[field]) != 0 for field in false_fields
    ):
        raise ValueError("Spot V7 V4 scoped claim flag mismatch")


def _exact_mapping(document: Mapping[str, Any], field: str) -> dict[str, Any]:
    value = document.get(field)
    if type(value) is not dict:
        raise ValueError(f"Spot V7 V4 {field} must be an exact object")
    return value


def _require_exact_keys(
    document: Mapping[str, Any],
    expected: frozenset[str],
    name: str,
) -> None:
    if frozenset(document) != expected:
        raise ValueError(f"Spot V7 V4 {name} fields mismatch")


def _require_exact_claims(value: object) -> None:
    if type(value) is not dict:
        raise ValueError("Spot V7 V4 finality claims must be an exact object")
    claims = cast(dict[str, object], value)
    _require_exact_keys(claims, frozenset(_FINALITY_V3_CLAIMS), "finality claims")
    for field, expected in _FINALITY_V3_CLAIMS.items():
        observed = claims[field]
        if type(observed) is not bool or observed is not expected:
            raise ValueError("Spot V7 V4 finality claim boundary mismatch")


def _exact_document_equal(observed: object, expected: Mapping[str, Any]) -> bool:
    if type(observed) is not dict:
        return False
    try:
        return canonical_json_bytes_v0(observed) == canonical_json_bytes_v0(dict(expected))
    except (TypeError, ValueError, RecursionError):
        return False


def _exact_value_equal(left: object, right: object) -> bool:
    return type(left) is type(right) and left == right


def _exact_str(document: Mapping[str, Any], field: str) -> str:
    value = document.get(field)
    if type(value) is not str:
        raise ValueError(f"Spot V7 V4 {field} must be an exact string")
    return value


def _exact_int(document: Mapping[str, Any], field: str) -> int:
    value = document.get(field)
    if type(value) is not int:
        raise ValueError(f"Spot V7 V4 {field} must be an exact integer")
    return value


__all__ = ()
