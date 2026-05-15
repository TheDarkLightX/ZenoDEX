from __future__ import annotations

import pytest

from src.integration.zeno_ledger_scaling_v0 import (
    EXECUTION_JOURNAL_SCHEMA_V0,
    TRANSITION_RECEIPT_SCHEMA_V0,
    build_execution_journal_from_header_v0,
    build_execution_journal_v0,
    build_transition_receipt_v0,
    execution_journal_hash_v0,
    transition_receipt_hash_v0,
    validate_execution_journal_v0,
    validate_header_transition_receipt_binding_v0,
    validate_transition_receipt_v0,
)
from src.integration.zeno_ledger_v0 import build_header_v0, compute_app_hash_v0, hash_v0


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


def test_header_transition_receipt_binding_accepts_matching_header() -> None:
    header_without_proof = _header()
    journal = build_execution_journal_from_header_v0(
        header=header_without_proof,
        program_id="zenodex.scaling.replay.v0",
        proof_policy_id="public-testnet-replay-v0",
        feature_suite_hash=_root("features"),
        token_registry_hash=_root("tokens"),
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

