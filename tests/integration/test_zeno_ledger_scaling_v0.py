from __future__ import annotations

import pytest

from src.integration.zeno_ledger_scaling_v0 import (
    EXECUTION_JOURNAL_SCHEMA_V0,
    PROOF_METADATA_SCHEMA_V0,
    TRANSITION_RECEIPT_SCHEMA_V0,
    build_proof_metadata_v0,
    build_execution_journal_from_header_v0,
    build_execution_journal_v0,
    build_transition_receipt_v0,
    execution_journal_hash_v0,
    proof_metadata_hash_v0,
    transition_receipt_hash_v0,
    validate_execution_journal_v0,
    validate_header_transition_receipt_binding_v0,
    validate_proof_metadata_journal_binding_v0,
    validate_proof_metadata_v0,
    validate_transition_receipt_v0,
)
from src.integration.zeno_ledger_v0 import build_header_v0, compute_app_hash_v0, hash_v0
from tools.zeno_ledger_make_transition_receipt import build_transition_receipt_report_v0


ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("scaling_test_root", {"label": label})


def _header(*, proof_journal_hash: str = ZERO_ROOT, post_state_root: str | None = None) -> dict[str, object]:
    actual_post_state_root = post_state_root or _root("post")
    evidence_root = _root("evidence")
    config_digest = _root("config")
    module_versions_digest = _root("modules")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": "zeno-ledger-devnet-0",
            "height": 7,
            "post_state_root": actual_post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    return build_header_v0(
        chain_id="zeno-ledger-devnet-0",
        height=7,
        time_ms=1_778_730_000_000,
        prev_header_hash=_root("prev"),
        sequencer_set_hash=_root("sequencer"),
        ingress_root=_root("ingress"),
        tx_root=_root("tx"),
        pre_state_root=_root("pre"),
        post_state_root=actual_post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=_root("body"),
        data_availability_root=_root("da"),
        proof_journal_hash=proof_journal_hash,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )


def _journal() -> dict[str, object]:
    return build_execution_journal_v0(
        chain_id="zeno-ledger-devnet-0",
        height=7,
        program_id="zenodex.scaling.replay.v0",
        proof_policy_id="public-testnet-replay-v0",
        pre_state_root=_root("pre"),
        ordered_body_root=_root("body"),
        post_state_root=_root("post"),
        app_hash=_root("app"),
        data_availability_root=_root("da"),
        conflict_schedule_hash=_root("schedule"),
        feature_suite_hash=_root("features"),
        token_registry_hash=_root("tokens"),
        rejection_receipt_root=_root("reject"),
    )


def test_execution_journal_hash_is_mutation_sensitive() -> None:
    journal = _journal()
    assert journal["schema"] == EXECUTION_JOURNAL_SCHEMA_V0
    validate_execution_journal_v0(journal)
    base_hash = execution_journal_hash_v0(journal)

    mutated = dict(journal)
    mutated["post_state_root"] = _root("post-mutated")
    assert execution_journal_hash_v0(mutated) != base_hash

    schedule_mutated = dict(journal)
    schedule_mutated["conflict_schedule_hash"] = _root("schedule-mutated")
    assert execution_journal_hash_v0(schedule_mutated) != base_hash


def test_execution_journal_rejects_uppercase_roots_and_bool_height() -> None:
    journal = _journal()
    bad_root = dict(journal)
    bad_root["pre_state_root"] = "0x" + "AA" * 32
    with pytest.raises(ValueError, match="canonical lowercase"):
        validate_execution_journal_v0(bad_root)

    bad_height = dict(journal)
    bad_height["height"] = True
    with pytest.raises(ValueError, match="height"):
        validate_execution_journal_v0(bad_height)

    bad_schedule = dict(journal)
    bad_schedule["conflict_schedule_hash"] = "0x" + "BB" * 32
    with pytest.raises(ValueError, match="canonical lowercase"):
        validate_execution_journal_v0(bad_schedule)


def test_transition_receipt_binds_journal_and_rejects_tampering() -> None:
    journal = _journal()
    receipt = build_transition_receipt_v0(
        execution_journal=journal,
        verifier_kind="deterministic_replay_v0",
        verifier_version="zeno-ledger-replay-0",
        proof_commitment=_root("proof"),
        receipt_metadata_hash=_root("metadata"),
    )
    assert receipt["schema"] == TRANSITION_RECEIPT_SCHEMA_V0
    validate_transition_receipt_v0(receipt)
    assert transition_receipt_hash_v0(receipt) == receipt["receipt_hash"]

    tampered = dict(receipt)
    tampered["execution_journal_hash"] = _root("wrong-journal")
    with pytest.raises(ValueError, match="execution_journal_hash mismatch"):
        validate_transition_receipt_v0(tampered)

    tampered_hash = dict(receipt)
    tampered_hash["receipt_hash"] = _root("wrong-receipt")
    with pytest.raises(ValueError, match="receipt_hash mismatch"):
        validate_transition_receipt_v0(tampered_hash)


def test_transition_receipt_rejects_unknown_verifier_kind() -> None:
    with pytest.raises(ValueError, match="verifier_kind is not allowed"):
        build_transition_receipt_v0(
            execution_journal=_journal(),
            verifier_kind="unknown_prover",
            verifier_version="v0",
            proof_commitment=_root("proof"),
        )


def test_proof_backends_reject_empty_proof_fields() -> None:
    journal = _journal()
    with pytest.raises(ValueError, match="proof_commitment must be nonzero"):
        build_transition_receipt_v0(
            execution_journal=journal,
            verifier_kind="risc0_zkvm_v0",
            verifier_version="risc0-zkvm-0",
            proof_commitment=ZERO_ROOT,
            receipt_metadata_hash=_root("metadata"),
        )
    with pytest.raises(ValueError, match="receipt_metadata_hash must be nonzero"):
        build_transition_receipt_v0(
            execution_journal=journal,
            verifier_kind="sp1_zkvm_v0",
            verifier_version="sp1-zkvm-0",
            proof_commitment=_root("proof"),
            receipt_metadata_hash=ZERO_ROOT,
        )


def test_zk_and_tee_receipts_bind_the_same_schedule_hash() -> None:
    journal = _journal()
    for verifier_kind in ("risc0_zkvm_v0", "sp1_zkvm_v0", "tee_attestation_v0"):
        receipt = build_transition_receipt_v0(
            execution_journal=journal,
            verifier_kind=verifier_kind,
            verifier_version="backend-0",
            proof_commitment=_root(f"proof-{verifier_kind}"),
            receipt_metadata_hash=_root(f"metadata-{verifier_kind}"),
        )
        validate_transition_receipt_v0(receipt)
        assert receipt["execution_journal"]["conflict_schedule_hash"] == _root("schedule")
        assert receipt["execution_journal_hash"] == execution_journal_hash_v0(journal)


def test_proof_metadata_binds_backend_code_and_public_input() -> None:
    journal = _journal()
    metadata = build_proof_metadata_v0(
        verifier_kind="risc0_zkvm_v0",
        verifier_version="risc0-zkvm-0",
        program_id=str(journal["program_id"]),
        code_commitment=_root("risc0-image"),
        public_input_hash=execution_journal_hash_v0(journal),
        backend_claim_hash=_root("risc0-claim"),
    )
    assert metadata["schema"] == PROOF_METADATA_SCHEMA_V0
    validate_proof_metadata_v0(metadata)
    validate_proof_metadata_journal_binding_v0(metadata=metadata, execution_journal=journal)
    receipt = build_transition_receipt_v0(
        execution_journal=journal,
        verifier_kind="risc0_zkvm_v0",
        verifier_version="risc0-zkvm-0",
        proof_commitment=_root("risc0-receipt"),
        receipt_metadata_hash=proof_metadata_hash_v0(metadata),
    )
    assert receipt["receipt_metadata_hash"] == proof_metadata_hash_v0(metadata)


def test_tee_metadata_requires_nonzero_measurement() -> None:
    journal = _journal()
    with pytest.raises(ValueError, match="TEE measurement"):
        build_proof_metadata_v0(
            verifier_kind="tee_attestation_v0",
            verifier_version="tee-0",
            program_id=str(journal["program_id"]),
            code_commitment=_root("tee-code"),
            public_input_hash=execution_journal_hash_v0(journal),
        )

    metadata = build_proof_metadata_v0(
        verifier_kind="tee_attestation_v0",
        verifier_version="tee-0",
        program_id=str(journal["program_id"]),
        code_commitment=_root("tee-code"),
        public_input_hash=execution_journal_hash_v0(journal),
        backend_claim_hash=_root("tee-claim"),
        tee_measurement_hash=_root("tee-measurement"),
    )
    validate_proof_metadata_journal_binding_v0(metadata=metadata, execution_journal=journal)


def test_header_transition_receipt_binding_accepts_matching_header() -> None:
    header_without_proof = _header()
    journal = build_execution_journal_from_header_v0(
        header=header_without_proof,
        program_id="zenodex.scaling.replay.v0",
        proof_policy_id="public-testnet-replay-v0",
        feature_suite_hash=_root("features"),
        token_registry_hash=_root("tokens"),
        conflict_schedule_hash=_root("schedule"),
        rejection_receipt_root=_root("reject"),
    )
    journal_hash = execution_journal_hash_v0(journal)
    header = _header(proof_journal_hash=journal_hash)
    rebound_journal = build_execution_journal_from_header_v0(
        header=header,
        program_id="zenodex.scaling.replay.v0",
        proof_policy_id="public-testnet-replay-v0",
        feature_suite_hash=_root("features"),
        token_registry_hash=_root("tokens"),
        conflict_schedule_hash=_root("schedule"),
        rejection_receipt_root=_root("reject"),
    )
    receipt = build_transition_receipt_v0(
        execution_journal=rebound_journal,
        verifier_kind="deterministic_replay_v0",
        verifier_version="zeno-ledger-replay-0",
        proof_commitment=_root("proof"),
    )
    validate_header_transition_receipt_binding_v0(header, receipt)


def test_header_transition_receipt_binding_rejects_mismatched_header() -> None:
    header_without_proof = _header()
    journal = build_execution_journal_from_header_v0(
        header=header_without_proof,
        program_id="zenodex.scaling.replay.v0",
        proof_policy_id="public-testnet-replay-v0",
        feature_suite_hash=_root("features"),
        token_registry_hash=_root("tokens"),
        conflict_schedule_hash=_root("schedule"),
    )
    receipt = build_transition_receipt_v0(
        execution_journal=journal,
        verifier_kind="deterministic_replay_v0",
        verifier_version="zeno-ledger-replay-0",
        proof_commitment=_root("proof"),
    )
    mismatched_header = _header(proof_journal_hash=receipt["execution_journal_hash"])
    mismatched_header["post_state_root"] = _root("different-post")
    with pytest.raises(ValueError, match="binding mismatch"):
        validate_header_transition_receipt_binding_v0(mismatched_header, receipt)


def test_transition_receipt_report_marks_unbound_legacy_header() -> None:
    journal = build_execution_journal_from_header_v0(
        header=_header(),
        program_id="zenodex.scaling.replay.v0",
        proof_policy_id="public-testnet-replay-v0",
        feature_suite_hash=_root("features"),
        token_registry_hash=_root("tokens"),
        conflict_schedule_hash=_root("schedule"),
        rejection_receipt_root=_root("reject"),
    )
    proof_metadata = build_proof_metadata_v0(
        verifier_kind="deterministic_replay_v0",
        verifier_version="zeno-ledger-replay-0",
        program_id="zenodex.scaling.replay.v0",
        code_commitment=_root("replay-code"),
        public_input_hash=execution_journal_hash_v0(journal),
        backend_claim_hash=_root("replay-claim"),
    )
    report = build_transition_receipt_report_v0(
        header=_header(),
        program_id="zenodex.scaling.replay.v0",
        proof_policy_id="public-testnet-replay-v0",
        feature_suite_hash=_root("features"),
        token_registry_hash=_root("tokens"),
        conflict_schedule_hash=_root("schedule"),
        rejection_receipt_root=_root("reject"),
        verifier_kind="deterministic_replay_v0",
        verifier_version="zeno-ledger-replay-0",
        proof_commitment=_root("proof"),
        receipt_metadata_hash=_root("metadata"),
        proof_metadata=proof_metadata,
    )
    assert report["ok"] is True
    assert report["header_binding"]["ok"] is False
    assert report["header_binding"]["header_proof_journal_hash"] == ZERO_ROOT
    assert report["header_binding"]["required_proof_journal_hash"] == report["execution_journal_hash"]
    assert report["execution_journal"]["conflict_schedule_hash"] == _root("schedule")
    assert report["proof_metadata_hash"] == proof_metadata_hash_v0(proof_metadata)
    assert report["transition_receipt"]["receipt_metadata_hash"] == proof_metadata_hash_v0(proof_metadata)
