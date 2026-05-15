from __future__ import annotations

import pytest

from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    EMPTY_MERKLE_ROOT_V0,
    FORCED_INCLUSION_DECISION_SCHEMA_V0,
    FORCED_INCLUSION_REQUEST_SCHEMA_V0,
    HEADER_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    PROOF_METADATA_SCHEMA_V0,
    build_checkpoint_v0,
    build_header_v0,
    build_proof_metadata_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    expected_header_roots_from_body_v0,
    hash_v0,
    merkle_root_v0,
    proof_metadata_hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_body_v0,
    validate_header_body_roots_v0,
    validate_header_v0,
    validate_proof_metadata_header_binding_v0,
    validate_proof_metadata_v0,
)


ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _batch_cutoff(*, height: int = 1, policy_digest: str | None = None) -> dict[str, object]:
    return {
        "schema": BATCH_CUTOFF_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "height": height,
        "cutoff_time_ms": 1_778_730_000_000,
        "cutoff_sequence": 12345,
        "sequencer_id": "sequencer-dev-0",
        "policy_id": "public_cutoff_v0",
        "policy_digest": policy_digest or _root("policy"),
    }


def _ingress_receipt(*, tx_hash: str | None = None, status: str = "included") -> dict[str, object]:
    return {
        "schema": INGRESS_RECEIPT_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "tx_hash": tx_hash or _root("tx-0"),
        "received_time_ms": 1_778_729_999_000,
        "received_sequence": 12344,
        "sequencer_id": "sequencer-dev-0",
        "status": status,
        "height": 1,
        "index": 0,
        "reject_code": None,
        "receipt_hash": _root("ingress-receipt"),
    }


def _forced_request() -> dict[str, object]:
    return {
        "schema": FORCED_INCLUSION_REQUEST_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "tx_hash": _root("forced-tx"),
        "tx_body_hash": _root("forced-body"),
        "submitter_id": "0xsubmitter",
        "first_seen_time_ms": 1_778_729_999_000,
        "first_seen_sequence": 12344,
        "deadline_height": 5,
        "request_hash": _root("forced-request"),
    }


def _forced_decision() -> dict[str, object]:
    return {
        "schema": FORCED_INCLUSION_DECISION_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "height": 5,
        "request_hash": _root("forced-request"),
        "decision": "included",
        "tx_hash": _root("forced-tx"),
        "index": 2,
        "reject_code": None,
    }


def _ingress(*, receipt_status: str = "included") -> dict[str, object]:
    return {
        "batch_cutoff": _batch_cutoff(),
        "ingress_receipts": [_ingress_receipt(status=receipt_status)],
        "forced_inclusion_requests": [_forced_request()],
        "forced_inclusion_decisions": [_forced_decision()],
    }


def _evidence() -> dict[str, object]:
    return {
        "upba_certificates": [{"cert_id": "upba-1", "root": _root("upba")}],
        "price_grid_tables": [{"table_root": _root("table")}],
        "uniform_batch_hypergraph_roots": [_root("hypergraph")],
        "oracle_packets": [{"oracle_packet_root": _root("oracle")}],
        "proof_receipts": [{"proof_receipt_root": _root("proof")}],
        "rejection_receipts": [{"receipt_root": _root("reject")}],
    }


def _body(*, txs: list[object] | None = None, ingress: dict[str, object] | None = None) -> dict[str, object]:
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "height": 1,
        "ingress": ingress or _ingress(),
        "transactions": [{"sender": "alice", "nonce": 1}] if txs is None else txs,
        "settlement_envelopes": [],
        "evidence": _evidence(),
    }


def _header(
    *,
    body: dict[str, object] | None = None,
    ingress_root: str | None = None,
    tx_root: str | None = None,
    proof_journal_hash: str = ZERO_ROOT,
) -> dict[str, object]:
    actual_body = _body() if body is None else body
    actual_ingress_root = ingress_root or compute_ingress_root_v0(actual_body["ingress"])  # type: ignore[arg-type]
    actual_tx_root = tx_root or compute_tx_root_v0(actual_body["transactions"])  # type: ignore[arg-type]
    evidence_root = compute_evidence_root_v0(actual_body["evidence"])  # type: ignore[arg-type]
    app_hash = compute_app_hash_v0(
        {
            "chain_id": "zeno-ledger-devnet-0",
            "height": 1,
            "post_state_root": _root("post-state"),
            "evidence_root": evidence_root,
            "config_digest": _root("config"),
            "module_versions_digest": _root("modules"),
        }
    )
    return build_header_v0(
        chain_id="zeno-ledger-devnet-0",
        height=1,
        time_ms=1_778_730_000_000,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=actual_ingress_root,
        tx_root=actual_tx_root,
        pre_state_root=_root("pre-state"),
        post_state_root=_root("post-state"),
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(actual_body),
        data_availability_root=_root("da"),
        proof_journal_hash=proof_journal_hash,
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _proof_metadata(*, header: dict[str, object], proof_kind: str = "risc0_zkvm_v0") -> dict[str, object]:
    return build_proof_metadata_v0(
        chain_id=str(header["chain_id"]),
        height=int(header["height"]),
        proof_kind=proof_kind,
        program_id="risc0:zenodex-spot-transition-v1",
        verifier_id="risc0:receipt-verifier-v1",
        proof_commitment=_root("proof-commitment"),
        public_input_hash=_root("public-input"),
        journal_hash=_root("journal"),
        pre_state_root=str(header["pre_state_root"]),
        post_state_root=str(header["post_state_root"]),
        tx_root=str(header["tx_root"]),
        evidence_root=str(header["evidence_root"]),
        body_root=str(header["body_root"]),
        conflict_schedule_hash=_root("sequential-schedule"),
        feature_suite_hash=_root("feature-suite"),
        dependency_lock_hash=_root("dependency-lock"),
    )


def test_empty_merkle_root_is_stable() -> None:
    assert merkle_root_v0("empty_test", []) == EMPTY_MERKLE_ROOT_V0
    assert merkle_root_v0("empty_test", []) == merkle_root_v0("other_empty_test", [])


def test_canonical_json_key_order_does_not_affect_body_root() -> None:
    body = _body()
    reordered = {
        "evidence": body["evidence"],
        "settlement_envelopes": body["settlement_envelopes"],
        "transactions": body["transactions"],
        "ingress": body["ingress"],
        "height": body["height"],
        "chain_id": body["chain_id"],
        "schema": body["schema"],
    }
    assert canonical_body_root_v0(body) == canonical_body_root_v0(reordered)


def test_transaction_order_changes_tx_root() -> None:
    tx_a = {"sender": "alice", "nonce": 1}
    tx_b = {"sender": "bob", "nonce": 1}
    assert compute_tx_root_v0([tx_a, tx_b]) != compute_tx_root_v0([tx_b, tx_a])


def test_body_ingress_evidence_and_header_mutations_change_roots() -> None:
    body = _body()
    base_body_root = canonical_body_root_v0(body)
    base_ingress_root = compute_ingress_root_v0(body["ingress"])  # type: ignore[arg-type]
    base_evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    base_header_hash = canonical_header_hash_v0(_header())

    mutated_body = _body(txs=[{"sender": "alice", "nonce": 2}])
    assert canonical_body_root_v0(mutated_body) != base_body_root

    mutated_ingress = _ingress(receipt_status="deferred_after_cutoff")
    assert compute_ingress_root_v0(mutated_ingress) != base_ingress_root

    mutated_evidence = _evidence()
    mutated_evidence["oracle_packets"] = [{"oracle_packet_root": _root("oracle-2")}]
    assert compute_evidence_root_v0(mutated_evidence) != base_evidence_root

    assert canonical_header_hash_v0(_header(tx_root=_root("different-tx-root"))) != base_header_hash


def test_header_body_root_verifier_accepts_matching_body() -> None:
    body = _body()
    header = _header(body=body)
    expected = expected_header_roots_from_body_v0(body)
    assert expected["body_root"] == header["body_root"]
    assert expected["tx_root"] == header["tx_root"]
    assert expected["ingress_root"] == header["ingress_root"]
    assert expected["evidence_root"] == header["evidence_root"]
    validate_header_body_roots_v0(header, body)


def test_header_body_root_verifier_rejects_tampered_body() -> None:
    body = _body()
    header = _header(body=body)
    tampered = _body(txs=[{"sender": "mallory", "nonce": 1}])
    with pytest.raises(ValueError, match="body_root mismatch|tx_root mismatch"):
        validate_header_body_roots_v0(header, tampered)


def test_header_body_root_verifier_rejects_bad_app_hash() -> None:
    body = _body()
    header = _header(body=body)
    bad_header = dict(header)
    bad_header["app_hash"] = _root("bad-app-hash")
    with pytest.raises(ValueError, match="app_hash mismatch"):
        validate_header_body_roots_v0(bad_header, body)


def test_ingress_changes_header_hash_without_changing_app_hash() -> None:
    evidence_root = compute_evidence_root_v0(_evidence())
    app_fields = {
        "chain_id": "zeno-ledger-devnet-0",
        "height": 1,
        "post_state_root": _root("post-state"),
        "evidence_root": evidence_root,
        "config_digest": _root("config"),
        "module_versions_digest": _root("modules"),
    }
    app_hash = compute_app_hash_v0(app_fields)
    changed_ingress_root = compute_ingress_root_v0(_ingress(receipt_status="deferred_after_cutoff"))

    header_a = _header()
    header_b = _header(ingress_root=changed_ingress_root)

    assert header_a["app_hash"] == app_hash
    assert header_b["app_hash"] == app_hash
    assert header_a["post_state_root"] == header_b["post_state_root"]
    assert canonical_header_hash_v0(header_a) != canonical_header_hash_v0(header_b)


def test_validate_body_rejects_missing_batch_cutoff() -> None:
    body = _body()
    ingress = dict(body["ingress"])  # type: ignore[arg-type]
    ingress.pop("batch_cutoff")
    body["ingress"] = ingress
    with pytest.raises(ValueError, match="ingress keys mismatch"):
        validate_body_v0(body)


def test_validate_body_rejects_unknown_ingress_status() -> None:
    body = _body(ingress=_ingress(receipt_status="unexpected"))
    with pytest.raises(ValueError, match="status is not allowed"):
        validate_body_v0(body)


def test_validate_header_rejects_bool_height_and_uppercase_root() -> None:
    header = _header()
    bad_height = dict(header)
    bad_height["height"] = True
    with pytest.raises(ValueError, match="height"):
        validate_header_v0(bad_height)

    bad_root = dict(header)
    bad_root["tx_root"] = "0x" + "AA" * 32
    with pytest.raises(ValueError, match="canonical lowercase"):
        validate_header_v0(bad_root)


def test_canonical_hash_rejects_float_payloads() -> None:
    body = _body(txs=[{"sender": "alice", "price": 1.25}])
    with pytest.raises(TypeError, match="floats are not allowed"):
        canonical_body_root_v0(body)


def test_build_checkpoint_binds_header_hash_and_roots() -> None:
    header = _header()
    checkpoint = build_checkpoint_v0(header)
    assert checkpoint["schema"] == "zenodex/zeno_ledger/checkpoint/v0"
    assert checkpoint["header_hash"] == canonical_header_hash_v0(header)
    assert checkpoint["ingress_root"] == header["ingress_root"]
    assert checkpoint["app_hash"] == header["app_hash"]
    assert checkpoint["signature_set"] == []
    validate_checkpoint_header_binding_v0(checkpoint, header)


def test_checkpoint_header_binding_rejects_tampering() -> None:
    header = _header()
    checkpoint = build_checkpoint_v0(header)
    tampered = dict(checkpoint)
    tampered["app_hash"] = _root("bad-app")
    with pytest.raises(ValueError, match="checkpoint/header binding mismatch"):
        validate_checkpoint_header_binding_v0(tampered, header)


def test_body_rejects_unknown_top_level_key() -> None:
    body = _body()
    body["unexpected"] = "value"
    with pytest.raises(ValueError, match="body keys mismatch"):
        validate_body_v0(body)


def test_header_schema_is_explicit() -> None:
    header = _header()
    assert header["schema"] == HEADER_SCHEMA_V0
    validate_header_v0(header)


def test_proof_metadata_hash_binds_header_roots() -> None:
    header_without_proof = _header()
    metadata = _proof_metadata(header=header_without_proof)
    assert metadata["schema"] == PROOF_METADATA_SCHEMA_V0
    header = _header(proof_journal_hash=proof_metadata_hash_v0(metadata))

    validate_proof_metadata_header_binding_v0(metadata, header)


def test_proof_metadata_header_binding_rejects_tampered_root() -> None:
    header_without_proof = _header()
    metadata = _proof_metadata(header=header_without_proof)
    metadata_hash = proof_metadata_hash_v0(metadata)
    header = _header(proof_journal_hash=metadata_hash)
    tampered = dict(metadata)
    tampered["post_state_root"] = _root("different-post")
    with pytest.raises(ValueError, match="post_state_root mismatch"):
        validate_proof_metadata_header_binding_v0(tampered, header)


def test_proof_metadata_rejects_missing_commitment_and_wrong_kind() -> None:
    header = _header()
    metadata = _proof_metadata(header=header)
    no_commitment = dict(metadata)
    no_commitment["proof_commitment"] = ZERO_ROOT
    with pytest.raises(ValueError, match="proof_commitment must be non-zero"):
        validate_proof_metadata_v0(no_commitment)

    bad_kind = dict(metadata)
    bad_kind["proof_kind"] = "unknown_proof"
    with pytest.raises(ValueError, match="proof_kind is not allowed"):
        validate_proof_metadata_v0(bad_kind)


def test_proof_metadata_rejects_placeholder_binding_roots() -> None:
    header = _header()
    metadata = _proof_metadata(header=header)
    for key in (
        "public_input_hash",
        "journal_hash",
        "pre_state_root",
        "post_state_root",
        "tx_root",
        "evidence_root",
        "body_root",
        "conflict_schedule_hash",
        "feature_suite_hash",
        "dependency_lock_hash",
    ):
        bad = dict(metadata)
        bad[key] = ZERO_ROOT
        with pytest.raises(ValueError, match=rf"proof_metadata.{key} must be non-zero"):
            validate_proof_metadata_v0(bad)


def test_proof_metadata_enforces_tee_and_recursive_specific_roots() -> None:
    header = _header()
    metadata = _proof_metadata(header=header)

    zk_with_tee_measurement = dict(metadata)
    zk_with_tee_measurement["tee_measurement_hash"] = _root("tee-measurement")
    with pytest.raises(ValueError, match="tee_measurement_hash must be zero"):
        validate_proof_metadata_v0(zk_with_tee_measurement)

    tee_missing_measurement = dict(metadata)
    tee_missing_measurement["proof_kind"] = "tee_attestation_v0"
    tee_missing_measurement["program_id"] = "tee:confidential-advisory-v1"
    tee_missing_measurement["verifier_id"] = "tee:attestation-verifier-v1"
    with pytest.raises(ValueError, match="tee_measurement_hash must be non-zero"):
        validate_proof_metadata_v0(tee_missing_measurement)

    recursive_missing_children = dict(metadata)
    recursive_missing_children["proof_kind"] = "recursive_epoch_v0"
    recursive_missing_children["program_id"] = "recursive:epoch-aggregator-v1"
    recursive_missing_children["verifier_id"] = "recursive:receipt-verifier-v1"
    with pytest.raises(ValueError, match="child_receipts_root must be non-zero"):
        validate_proof_metadata_v0(recursive_missing_children)
