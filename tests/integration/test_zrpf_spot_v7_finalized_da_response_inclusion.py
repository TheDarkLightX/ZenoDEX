"""CBC tests for finalized sampled-response digest inclusion V1."""

from __future__ import annotations

import copy
import hashlib
import pickle
from typing import Any, Callable

import pytest

import tests.integration.test_zrpf_spot_v7_governed_da_prerequisite_v2 as da_test
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
)
from src.integration.zrpf_sampled_retrievability_v1 import (
    SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1,
    build_sampled_response_ledger_inclusion_record_v1,
    parse_sampled_response_ledger_inclusion_record_v1,
)
from src.integration.zrpf_sampled_retrievability_v1.ledger_inclusion import (
    SAMPLED_RESPONSE_LEDGER_RESPONSE_SET_ROOT_DOMAIN_V1,
)
from src.integration.zrpf_sampled_retrievability_v1.verifier import (
    _AuthenticatedSampledRetrievabilityEvidenceV1,
)
from src.integration.zrpf_spot_v7_finalized_da_response_inclusion import (
    SpotV7FinalizedDaResponseInclusionErrorV1,
    _AuthenticatedFinalizedSampledResponseInclusionV1,
    bind_finalized_sampled_response_inclusion_v1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    _AuthenticatedCheckpointFinalityProjectionV3,
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)


def _root(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("ascii")).hexdigest()


def _body(record: dict[str, object], *, height: int, chain_id: str) -> dict[str, Any]:
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": chain_id,
                "height": height,
                "cutoff_time_ms": 1_784_000_000_000,
                "cutoff_sequence": height,
                "sequencer_id": "sequencer-0",
                "policy_id": "sampled-response-inclusion-v1",
                "policy_digest": _root("inclusion-policy"),
            },
            "ingress_receipts": [],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [],
        "settlement_envelopes": [],
        "evidence": {
            "upba_certificates": [],
            "price_grid_tables": [],
            "uniform_batch_hypergraph_roots": [],
            "oracle_packets": [record],
            "proof_receipts": [],
            "rejection_receipts": [],
        },
    }


def _header(
    body: dict[str, Any],
    *,
    post_state_root: str,
    proof_journal_hash: str,
    data_root: str,
) -> dict[str, Any]:
    evidence_root = compute_evidence_root_v0(body["evidence"])
    config_digest = _root("config")
    versions = _root("module-versions")
    return build_header_v0(
        chain_id=body["chain_id"],
        height=body["height"],
        time_ms=1_784_000_000_001,
        prev_header_hash=_root("prior-checkpoint"),
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=_root("pre-state"),
        post_state_root=post_state_root,
        app_hash=compute_app_hash_v0(
            {
                "chain_id": body["chain_id"],
                "height": body["height"],
                "post_state_root": post_state_root,
                "evidence_root": evidence_root,
                "config_digest": config_digest,
                "module_versions_digest": versions,
            }
        ),
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=data_root,
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=versions,
        signature_set_root=ZERO_ROOT_V0,
    )


def _finality(
    *,
    sampled: _AuthenticatedSampledRetrievabilityEvidenceV1,
    body: dict[str, Any],
    application_id: str | None = None,
) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
    sampled_projection = sampled._projection
    app_id = application_id or sampled_projection.application_id
    journal = _root("proof-journal")
    post_state = _root("post-state")
    header = _header(
        body,
        post_state_root=post_state,
        proof_journal_hash=journal,
        data_root=sampled_projection.data_root,
    )
    header_hash = canonical_header_hash_v0(header)
    prior_sequence = body["height"] - 1
    prior_hash = header["prev_header_hash"]
    evidence = {
        "schema": "zenodex/zrpf/spot_v7/zeno_ledger_checkpoint_finality_evidence/v3",
        "application_binding": {
            "application_id": app_id,
            "chain_or_domain_id": sampled_projection.chain_or_domain_id,
            "epoch_id": body["height"],
            "post_state_root": post_state,
            "proof_journal_hash": journal,
        },
        "prior_application_checkpoint": {
            "sequence": prior_sequence,
            "checkpoint_hash": prior_hash,
        },
        "settlement_replay_observation": {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "header_hash": header_hash,
            "body_root": canonical_body_root_v0(body),
        },
        "header": header,
        "checkpoint": build_checkpoint_v0(header),
    }
    evidence_bytes = canonical_json_bytes_v0(evidence)
    evidence_root = "0x" + hashlib.sha256(evidence_bytes).hexdigest()
    projection = _AuthenticatedCheckpointFinalityProjectionV3(
        application_id=app_id,
        chain_or_domain_id=sampled_projection.chain_or_domain_id,
        epoch_id=body["height"],
        proof_journal_hash=journal,
        post_state_root=post_state,
        policy_root=_root("finality-policy"),
        certificate_root=_root("finality-certificate"),
        finality_evidence_root=evidence_root,
        prior_application_checkpoint_sequence=prior_sequence,
        prior_application_checkpoint_hash=prior_hash,
        next_application_checkpoint_sequence=body["height"],
        next_application_checkpoint_hash=header_hash,
    )
    return _AuthenticatedExactCheckpointFinalityTransitionV3(
        projection,
        exact_certificate_bytes=b"bounded-test-finality-certificate-v3",
        exact_finality_evidence_bytes=evidence_bytes,
        seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )


def _fixture(
    mutate_record: Callable[[dict[str, object]], None] | None = None,
) -> tuple[
    _AuthenticatedSampledRetrievabilityEvidenceV1,
    dict[str, Any],
    _AuthenticatedExactCheckpointFinalityTransitionV3,
]:
    policy, _beacon, sampled, _governed_sample, _full_blob = da_test._valid()
    inclusion_height = sampled.checked_epoch + 1
    record = build_sampled_response_ledger_inclusion_record_v1(
        sampled.exact_evidence_bytes,
        zeno_ledger_chain_id=policy._projection.zeno_ledger_chain_id,
        inclusion_height=inclusion_height,
    )
    if mutate_record is not None:
        mutate_record(record)
    body = _body(
        record,
        height=inclusion_height,
        chain_id=policy._projection.zeno_ledger_chain_id,
    )
    return sampled, body, _finality(sampled=sampled, body=body)


def test_finalized_inclusion_binds_exact_digest_and_keeps_authority_false() -> None:
    sampled, body, finality = _fixture()

    capability = bind_finalized_sampled_response_inclusion_v1(
        sampled_response=sampled,
        checkpoint_finality=finality,
        exact_body_bytes=canonical_json_bytes_v0(body),
    )

    assert type(capability) is _AuthenticatedFinalizedSampledResponseInclusionV1
    projection = capability._projection_for_da_store_v5()
    assert projection.sampled_evidence_sha256 == (
        "0x" + hashlib.sha256(sampled.exact_evidence_bytes).hexdigest()
    )
    assert projection.inclusion_height == sampled.checked_epoch + 1
    assert projection.finalized_body_root == canonical_body_root_v0(body)
    assert capability.finalized_sampled_evidence_digest_included_by_deadline is True
    assert capability.exact_response_and_signature_envelope_digests_committed is True
    assert capability.sampled_evidence_bytes_published_in_ledger_body is False
    assert capability.provider_response_generation_time_verified is False
    assert capability.response_timing_provenance_verified is False
    assert capability.provider_independence_verified is False
    assert capability.continuous_availability_verified is False
    assert capability.public_future_availability_verified is False
    assert capability.hostile_same_interpreter_resistance_established is False
    assert capability.release_authority is False
    assert capability.settlement_authority is False
    assert capability.production_authority is False


def test_position_distinct_response_commitments_reject_field_swap() -> None:
    def mutate(record: dict[str, object]) -> None:
        responses = record["response_records"]
        assert isinstance(responses, list)
        first = responses[0]
        assert isinstance(first, dict)
        first["response_sha256"], first["signature_envelope_sha256"] = (
            first["signature_envelope_sha256"],
            first["response_sha256"],
        )

    sampled, body, finality = _fixture(mutate)

    with pytest.raises(SpotV7FinalizedDaResponseInclusionErrorV1) as captured:
        bind_finalized_sampled_response_inclusion_v1(
            sampled_response=sampled,
            checkpoint_finality=finality,
            exact_body_bytes=canonical_json_bytes_v0(body),
        )

    assert captured.value.code == "INCLUSION_RECORD_MISMATCH"


def test_record_parser_rejects_unknown_fields_and_noncanonical_response_order() -> None:
    sampled, body, _finality_value = _fixture()
    record = copy.deepcopy(body["evidence"]["oracle_packets"][0])
    record["unexpected"] = False
    with pytest.raises(ValueError, match="fields mismatch"):
        parse_sampled_response_ledger_inclusion_record_v1(record)

    record = copy.deepcopy(body["evidence"]["oracle_packets"][0])
    record["response_records"].reverse()
    record["accepted_provider_ids"].reverse()
    with pytest.raises(ValueError, match="canonical and distinct"):
        parse_sampled_response_ledger_inclusion_record_v1(record)


@pytest.mark.parametrize("delta", (-1, 1))
def test_finalized_inclusion_rejects_record_height_different_from_body(delta: int) -> None:
    def mutate(record: dict[str, object]) -> None:
        current = record["inclusion_height"]
        assert type(current) is int
        record["inclusion_height"] = current + delta

    sampled, body, finality = _fixture(mutate)
    with pytest.raises(SpotV7FinalizedDaResponseInclusionErrorV1):
        bind_finalized_sampled_response_inclusion_v1(
            sampled_response=sampled,
            checkpoint_finality=finality,
            exact_body_bytes=canonical_json_bytes_v0(body),
        )


def test_builder_rejects_inclusion_after_response_deadline() -> None:
    policy, _beacon, sampled, _governed_sample, _full_blob = da_test._valid()
    deadline = sampled.checked_epoch + sampled._projection.response_window_epochs

    with pytest.raises(ValueError, match="outside the response window"):
        build_sampled_response_ledger_inclusion_record_v1(
            sampled.exact_evidence_bytes,
            zeno_ledger_chain_id=policy._projection.zeno_ledger_chain_id,
            inclusion_height=deadline + 1,
        )


def test_finalized_inclusion_rejects_record_that_extends_the_signed_deadline() -> None:
    sampled, body, _finality_value = _fixture()
    changed = copy.deepcopy(body)
    record = changed["evidence"]["oracle_packets"][0]
    responses = record["response_records"]
    assert isinstance(responses, list)
    forged_deadline = sampled.checked_epoch + sampled._projection.response_window_epochs + 1
    changed["height"] = forged_deadline
    changed["ingress"]["batch_cutoff"]["height"] = forged_deadline
    changed["ingress"]["batch_cutoff"]["cutoff_sequence"] = forged_deadline
    record["inclusion_height"] = forged_deadline
    record["response_deadline_epoch"] = forged_deadline
    for response in responses:
        assert isinstance(response, dict)
        response["response_deadline_epoch"] = forged_deadline
    record["response_records_root"] = hash_v0(
        SAMPLED_RESPONSE_LEDGER_RESPONSE_SET_ROOT_DOMAIN_V1,
        {"responses": responses},
    )
    finality = _finality(sampled=sampled, body=changed)

    with pytest.raises(SpotV7FinalizedDaResponseInclusionErrorV1) as captured:
        bind_finalized_sampled_response_inclusion_v1(
            sampled_response=sampled,
            checkpoint_finality=finality,
            exact_body_bytes=canonical_json_bytes_v0(changed),
        )

    assert captured.value.code == "INCLUSION_AFTER_DEADLINE"


def test_finalized_inclusion_rejects_application_substitution() -> None:
    sampled, body, _finality_value = _fixture()
    wrong_finality = _finality(
        sampled=sampled,
        body=body,
        application_id=_root("different-application"),
    )

    with pytest.raises(SpotV7FinalizedDaResponseInclusionErrorV1) as captured:
        bind_finalized_sampled_response_inclusion_v1(
            sampled_response=sampled,
            checkpoint_finality=wrong_finality,
            exact_body_bytes=canonical_json_bytes_v0(body),
        )

    assert captured.value.code == "SAMPLED_EVIDENCE_BINDING_MISMATCH"


def test_duplicate_or_missing_inclusion_record_rejects() -> None:
    sampled, body, _finality_value = _fixture()
    record = copy.deepcopy(body["evidence"]["oracle_packets"][0])
    for packets in ([], [record, copy.deepcopy(record)]):
        changed = copy.deepcopy(body)
        changed["evidence"]["oracle_packets"] = packets
        finality = _finality(sampled=sampled, body=changed)
        with pytest.raises(SpotV7FinalizedDaResponseInclusionErrorV1) as captured:
            bind_finalized_sampled_response_inclusion_v1(
                sampled_response=sampled,
                checkpoint_finality=finality,
                exact_body_bytes=canonical_json_bytes_v0(changed),
            )
        assert captured.value.code == "INCLUSION_RECORD_MISMATCH"


def test_raw_values_and_capability_transfer_attempts_reject() -> None:
    sampled, body, finality = _fixture()
    body_bytes = canonical_json_bytes_v0(body)
    with pytest.raises(TypeError, match="exact authenticated sampled"):
        bind_finalized_sampled_response_inclusion_v1(
            sampled_response={"verified": True},
            checkpoint_finality=finality,
            exact_body_bytes=body_bytes,
        )
    with pytest.raises(TypeError, match="exact authenticated finality"):
        bind_finalized_sampled_response_inclusion_v1(
            sampled_response=sampled,
            checkpoint_finality={"finalized": True},
            exact_body_bytes=body_bytes,
        )

    capability = bind_finalized_sampled_response_inclusion_v1(
        sampled_response=sampled,
        checkpoint_finality=finality,
        exact_body_bytes=body_bytes,
    )
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(capability)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(capability)
    with pytest.raises(TypeError, match="cannot be mutated"):
        capability._projection = capability._projection


def test_exact_sampled_evidence_bytes_are_not_embedded_in_body() -> None:
    sampled, body, _finality_value = _fixture()
    body_bytes = canonical_json_bytes_v0(body)

    assert sampled.exact_evidence_bytes not in body_bytes
    record = body["evidence"]["oracle_packets"][0]
    assert record["schema"] == SAMPLED_RESPONSE_LEDGER_INCLUSION_RECORD_SCHEMA_V1
    assert record["sampled_evidence_sha256"] == (
        "0x" + hashlib.sha256(sampled.exact_evidence_bytes).hexdigest()
    )
