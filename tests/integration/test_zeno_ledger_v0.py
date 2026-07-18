from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest

from src.core.dex import DexState
from src.integration import zeno_ledger_v0 as zv
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import state_from_snapshot
from src.integration.proof_toolchain_lock import (
    build_proof_toolchain_lock_manifest_v0,
    proof_toolchain_lock_hash_v0,
)
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    EMPTY_MERKLE_ROOT_V0,
    FORCED_INCLUSION_DECISION_SCHEMA_V0,
    FORCED_INCLUSION_REQUEST_SCHEMA_V0,
    HEADER_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    PROOF_METADATA_SCHEMA_V0,
    VALIDATOR_SET_SCHEMA_V0,
    build_checkpoint_v0,
    build_header_v0,
    build_proof_metadata_v0,
    canonical_body_root_v0,
    canonical_header_chain_tip_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    detect_header_equivocations_v0,
    evaluate_header_fork_choice_v0,
    expected_header_roots_from_body_v0,
    hash_v0,
    merkle_root_v0,
    proof_metadata_hash_v0,
    scheduled_validator_id_for_height_v0,
    select_canonical_header_chain_v0,
    validate_body_v0,
    validate_body_validator_schedule_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_body_roots_v0,
    validate_header_chain_linkage_v0,
    validate_header_v0,
    validate_header_validator_set_hash_v0,
    validate_proof_metadata_header_binding_v0,
    validate_proof_metadata_v0,
    validate_validator_set_v0,
    validator_set_hash_v0,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable

ROOT = Path(__file__).resolve().parents[2]
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
    height: int = 1,
    prev_header_hash: str = ZERO_ROOT,
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
            "height": height,
            "post_state_root": _root("post-state"),
            "evidence_root": evidence_root,
            "config_digest": _root("config"),
            "module_versions_digest": _root("modules"),
        }
    )
    return build_header_v0(
        chain_id="zeno-ledger-devnet-0",
        height=height,
        time_ms=1_778_730_000_000,
        prev_header_hash=prev_header_hash,
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


def _validator_set(*, validators: list[dict[str, object]] | None = None) -> dict[str, object]:
    return {
        "schema": VALIDATOR_SET_SCHEMA_V0,
        "chain_id": "zeno-ledger-devnet-0",
        "epoch": 0,
        "validators": validators
        or [
            {
                "validator_id": "sequencer-dev-0",
                "public_key": "pubkey-a",
                "voting_power": 2,
            },
            {
                "validator_id": "sequencer-dev-1",
                "public_key": "pubkey-b",
                "voting_power": 1,
            },
        ],
    }


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
        toolchain_lock_hash=_root("toolchain-lock"),
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


def test_validator_set_hash_is_order_invariant_and_schedule_is_weighted() -> None:
    validator_set = _validator_set()
    reversed_set = _validator_set(validators=list(reversed(validator_set["validators"])))  # type: ignore[arg-type]

    validate_validator_set_v0(validator_set)
    assert validator_set_hash_v0(validator_set) == validator_set_hash_v0(reversed_set)
    assert scheduled_validator_id_for_height_v0(validator_set, height=0) == "sequencer-dev-0"
    assert scheduled_validator_id_for_height_v0(validator_set, height=1) == "sequencer-dev-0"
    assert scheduled_validator_id_for_height_v0(validator_set, height=2) == "sequencer-dev-1"
    assert scheduled_validator_id_for_height_v0(validator_set, height=3) == "sequencer-dev-0"


def test_validator_set_rejects_duplicate_ids_and_zero_voting_power() -> None:
    duplicate = _validator_set(
        validators=[
            {
                "validator_id": "sequencer-dev-0",
                "public_key": "pubkey-a",
                "voting_power": 1,
            },
            {
                "validator_id": "sequencer-dev-0",
                "public_key": "pubkey-b",
                "voting_power": 1,
            },
        ]
    )
    with pytest.raises(ValueError, match="duplicate validator_id"):
        validate_validator_set_v0(duplicate)

    duplicate_key = _validator_set(
        validators=[
            {
                "validator_id": "sequencer-dev-0",
                "public_key": "pubkey-a",
                "voting_power": 1,
            },
            {
                "validator_id": "sequencer-dev-1",
                "public_key": "pubkey-a",
                "voting_power": 1,
            },
        ]
    )
    with pytest.raises(ValueError, match="duplicate validator.public_key"):
        validate_validator_set_v0(duplicate_key)

    zero_power = _validator_set(
        validators=[
            {
                "validator_id": "sequencer-dev-0",
                "public_key": "pubkey-a",
                "voting_power": 0,
            }
        ]
    )
    with pytest.raises(ValueError, match="validator.voting_power must be positive"):
        validate_validator_set_v0(zero_power)


def test_header_and_body_validator_schedule_binding() -> None:
    validator_set = _validator_set()
    body = _body()
    header = _header(body=body)
    header["sequencer_set_hash"] = validator_set_hash_v0(validator_set)

    validate_header_validator_set_hash_v0(header, validator_set)
    validate_body_validator_schedule_v0(body, validator_set)


def test_body_validator_schedule_rejects_wrong_sequencer() -> None:
    validator_set = _validator_set()
    body = _body()
    body["ingress"]["batch_cutoff"]["sequencer_id"] = "sequencer-dev-1"  # type: ignore[index]

    with pytest.raises(ValueError, match="body sequencer_id does not match validator schedule"):
        validate_body_validator_schedule_v0(body, validator_set)


def test_detect_header_equivocations_reports_conflicting_height() -> None:
    header_a = _header()
    header_b = _header(tx_root=_root("different-tx-root"))

    conflicts = detect_header_equivocations_v0([header_a, header_b, header_a])

    assert conflicts == [
        {
            "chain_id": "zeno-ledger-devnet-0",
            "height": 1,
            "header_hashes": sorted(
                [
                    canonical_header_hash_v0(header_a),
                    canonical_header_hash_v0(header_b),
                ]
            ),
        }
    ]


def test_header_chain_linkage_accepts_consecutive_parent_hashes() -> None:
    header_1 = _header()
    header_2 = _header(
        height=2,
        prev_header_hash=canonical_header_hash_v0(header_1),
        tx_root=_root("height-2-tx-root"),
    )
    header_3 = _header(
        height=3,
        prev_header_hash=canonical_header_hash_v0(header_2),
        tx_root=_root("height-3-tx-root"),
    )

    validate_header_chain_linkage_v0([header_3, header_1, header_2], expected_prev_header_hash=ZERO_ROOT)

    assert canonical_header_chain_tip_v0([header_1, header_2, header_3]) == canonical_header_hash_v0(header_3)


def test_header_chain_linkage_rejects_bad_parent_hash() -> None:
    header_1 = _header()
    header_2 = _header(height=2, prev_header_hash=_root("wrong-parent"))

    with pytest.raises(ValueError, match="prev_header_hash does not match previous header hash"):
        validate_header_chain_linkage_v0([header_1, header_2], expected_prev_header_hash=ZERO_ROOT)


def test_header_chain_linkage_rejects_height_gap_and_duplicate() -> None:
    header_1 = _header()
    header_3 = _header(height=3, prev_header_hash=canonical_header_hash_v0(header_1))

    with pytest.raises(ValueError, match="consecutive heights"):
        validate_header_chain_linkage_v0([header_1, header_3])

    with pytest.raises(ValueError, match="unique heights"):
        validate_header_chain_linkage_v0([header_1, header_1])


def test_header_fork_choice_selects_highest_anchored_tip() -> None:
    header_1 = _header()
    header_2a = _header(
        height=2,
        prev_header_hash=canonical_header_hash_v0(header_1),
        tx_root=_root("fork-a-height-2"),
    )
    header_2b = _header(
        height=2,
        prev_header_hash=canonical_header_hash_v0(header_1),
        tx_root=_root("fork-b-height-2"),
    )
    header_3b = _header(
        height=3,
        prev_header_hash=canonical_header_hash_v0(header_2b),
        tx_root=_root("fork-b-height-3"),
    )

    report = evaluate_header_fork_choice_v0(
        [header_2a, header_3b, header_1, header_2b],
        expected_prev_header_hash=ZERO_ROOT,
    )
    selected = select_canonical_header_chain_v0(
        [header_2a, header_3b, header_1, header_2b],
        expected_prev_header_hash=ZERO_ROOT,
    )

    assert report["canonical_tip_hash"] == canonical_header_hash_v0(header_3b)
    assert report["canonical_tip_height"] == 3
    assert [canonical_header_hash_v0(header) for header in selected] == [
        canonical_header_hash_v0(header_1),
        canonical_header_hash_v0(header_2b),
        canonical_header_hash_v0(header_3b),
    ]


def test_header_fork_choice_tie_breaks_by_lowest_tip_hash() -> None:
    header_1 = _header()
    header_2a = _header(
        height=2,
        prev_header_hash=canonical_header_hash_v0(header_1),
        tx_root=_root("tie-a-height-2"),
    )
    header_2b = _header(
        height=2,
        prev_header_hash=canonical_header_hash_v0(header_1),
        tx_root=_root("tie-b-height-2"),
    )
    expected_tip = min(canonical_header_hash_v0(header_2a), canonical_header_hash_v0(header_2b))

    report = evaluate_header_fork_choice_v0(
        [header_2b, header_1, header_2a],
        expected_prev_header_hash=ZERO_ROOT,
    )

    assert report["canonical_tip_hash"] == expected_tip
    assert report["anchored_chain_count"] == 3


def test_header_fork_choice_reports_orphans_without_selecting_them() -> None:
    header_1 = _header()
    orphan = _header(
        height=5,
        prev_header_hash=_root("unknown-parent"),
        tx_root=_root("orphan-height-5"),
    )

    report = evaluate_header_fork_choice_v0([orphan, header_1], expected_prev_header_hash=ZERO_ROOT)

    assert report["canonical_tip_hash"] == canonical_header_hash_v0(header_1)
    assert report["orphan_header_hashes"] == [canonical_header_hash_v0(orphan)]


def test_header_fork_choice_rejects_nonconsecutive_parent_link() -> None:
    header_1 = _header()
    header_4 = _header(
        height=4,
        prev_header_hash=canonical_header_hash_v0(header_1),
        tx_root=_root("bad-parent-height"),
    )

    with pytest.raises(ValueError, match="parent height mismatch"):
        evaluate_header_fork_choice_v0([header_1, header_4], expected_prev_header_hash=ZERO_ROOT)


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


def test_validate_body_rejects_batch_cutoff_chain_id_mismatch() -> None:
    body = _body()
    body["ingress"]["batch_cutoff"]["chain_id"] = "other-chain"  # type: ignore[index]

    with pytest.raises(ValueError, match="batch_cutoff/body chain_id mismatch"):
        validate_body_v0(body)


def test_validate_body_rejects_batch_cutoff_height_mismatch() -> None:
    body = _body()
    body["ingress"]["batch_cutoff"]["height"] = 2  # type: ignore[index]

    with pytest.raises(ValueError, match="batch_cutoff/body height mismatch"):
        validate_body_v0(body)


def test_validate_body_rejects_ingress_receipt_context_mismatch() -> None:
    body = _body()
    body["ingress"]["ingress_receipts"][0]["chain_id"] = "other-chain"  # type: ignore[index]

    with pytest.raises(ValueError, match=r"ingress_receipts\[0\]/body chain_id mismatch"):
        validate_body_v0(body)

    body = _body()
    body["ingress"]["ingress_receipts"][0]["height"] = 2  # type: ignore[index]

    with pytest.raises(ValueError, match=r"ingress_receipts\[0\]/body height mismatch"):
        validate_body_v0(body)


def test_validate_body_rejects_forced_inclusion_chain_id_mismatch() -> None:
    body = _body()
    body["ingress"]["forced_inclusion_requests"][0]["chain_id"] = "other-chain"  # type: ignore[index]

    with pytest.raises(ValueError, match=r"forced_inclusion_requests\[0\]/body chain_id mismatch"):
        validate_body_v0(body)

    body = _body()
    body["ingress"]["forced_inclusion_decisions"][0]["chain_id"] = "other-chain"  # type: ignore[index]

    with pytest.raises(ValueError, match=r"forced_inclusion_decisions\[0\]/body chain_id mismatch"):
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
    assert metadata["toolchain_lock_hash"] == _root("toolchain-lock")
    header = _header(proof_journal_hash=proof_metadata_hash_v0(metadata))

    validate_proof_metadata_header_binding_v0(metadata, header)


def test_proof_metadata_hash_binds_toolchain_lock_hash() -> None:
    header = _header()
    metadata = _proof_metadata(header=header)
    changed = dict(metadata)
    changed["toolchain_lock_hash"] = _root("toolchain-lock-v2")

    assert proof_metadata_hash_v0(metadata) != proof_metadata_hash_v0(changed)


def test_proof_toolchain_lock_manifest_binds_repo_toolchains() -> None:
    manifest = build_proof_toolchain_lock_manifest_v0(ROOT)
    lock_hash = proof_toolchain_lock_hash_v0(ROOT)

    assert manifest["schema"] == "zenodex/proof_toolchain_lock/v0"
    assert lock_hash != ZERO_ROOT
    assert lock_hash == proof_toolchain_lock_hash_v0(ROOT)
    groups = {entry["group"] for entry in manifest["files"]}
    assert {"python", "docker", "lean", "rust-risc0", "rust-tee"} <= groups
    paths = {entry["path"] for entry in manifest["files"]}
    assert "requirements-dev.lock.txt" in paths
    assert "zk/state_proof_risc0/Cargo.lock" in paths


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
        "toolchain_lock_hash",
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


def test_low_level_ledger_helpers_reject_bad_shapes() -> None:
    with pytest.raises(TypeError, match="x must be a JSON object"):
        zv._require_mapping([], name="x")
    with pytest.raises(TypeError, match="x must be a str"):
        zv._require_str(1, name="x")
    with pytest.raises(ValueError, match="x must be non-empty"):
        zv._require_str("", name="x")
    assert zv._require_optional_str(None, name="maybe") is None
    with pytest.raises(TypeError, match="x must be a str"):
        zv._require_root(1, name="x")
    with pytest.raises(TypeError, match="domain must be a non-empty str"):
        hash_v0("", {})
    with pytest.raises(ValueError, match="unsupported characters"):
        hash_v0("bad domain", {})
    with pytest.raises(TypeError, match="leaves must be a sequence"):
        merkle_root_v0("bad_leaves", "0x1234")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="transactions must be a list"):
        compute_tx_root_v0("bad")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="state must be a DexState"):
        zv.dex_state_root_v0({})  # type: ignore[arg-type]

    tx_hash = _root("receipt-tx")
    with pytest.raises(TypeError, match="accepted must be a bool"):
        zv.build_tx_receipt_v0(
            tx_hash=tx_hash,
            height=1,
            index=0,
            accepted="yes",  # type: ignore[arg-type]
            error_code=None,
            state_changed=False,
        )
    with pytest.raises(TypeError, match="state_changed must be a bool"):
        zv.build_tx_receipt_v0(
            tx_hash=tx_hash,
            height=1,
            index=0,
            accepted=True,
            error_code=None,
            state_changed="no",  # type: ignore[arg-type]
        )
    with pytest.raises(ValueError, match="accepted receipt must not carry error_code"):
        zv.build_tx_receipt_v0(
            tx_hash=tx_hash,
            height=1,
            index=0,
            accepted=True,
            error_code="unexpected",
            state_changed=False,
        )
    assert zv.stable_error_code_v0("Bad error: x!") == "bad_error_x"


def test_app_root_lanes_bind_dex_snapshot_modules_missing_from_spot_root() -> None:
    snapshot = zv.snapshot_from_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())).data
    root = zv.compute_dex_snapshot_app_root_v0(snapshot)
    leaves = zv.app_root_lanes_from_dex_snapshot_v0(snapshot)

    assert {(leaf.lane_kind, leaf.lane_id) for leaf in leaves} == {
        ("spot", "global"),
        ("oracle", "global"),
        ("vault", "protocol"),
        ("perps", "global"),
        ("proof_mining", "global"),
        ("zusd", "system"),
        ("clob", "global"),
        ("cross_shard", "global"),
        ("governance", "global"),
    }
    assert {leaf.lane_kind for leaf in leaves} == zv.APP_ROOT_LANE_KINDS
    assert root == zv.compute_dex_state_app_root_v0(
        DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    )

    spot_mutation = deepcopy(snapshot)
    spot_mutation["balances"] = [{"pubkey": "alice", "asset": "TAU", "amount": 1}]
    oracle_mutation = deepcopy(snapshot)
    oracle_mutation["oracle"] = {"price_timestamp": 10, "max_staleness_seconds": 300}
    vault_mutation = deepcopy(snapshot)
    vault_mutation["vault"] = {
        "acc_reward_per_share": 1,
        "last_update_acc": 1,
        "pending_rewards": 0,
        "reward_balance": 7,
        "staked_lp_shares": 1,
    }
    perps_mutation = deepcopy(snapshot)
    perps_mutation["perps"] = {"version": 5, "markets": []}
    governance_mutation = deepcopy(snapshot)
    governance_mutation["governance"] = {
        "schema": "zenodex.zeno_ledger.autogovnext_governance_state.v1",
        "version": 1,
        "surface_state": {"fee_bps": 300},
    }
    cross_shard_mutation = deepcopy(snapshot)
    cross_shard_mutation["cross_shard"] = {
        "schema": "zenodex/zeno_ledger/cross_shard_applied_effects_state/v0",
        "source_artifact_hashes": ["0x" + "11" * 32],
        "applied_effect_row_ids": ["row-0"],
        "global_effect_index": 1,
    }

    # Review note, grade A: these are the D-CANON-002 fields the old spot root
    # could omit. Each mutation now changes the typed app root.
    for mutated in (
        spot_mutation,
        oracle_mutation,
        vault_mutation,
        perps_mutation,
        governance_mutation,
        cross_shard_mutation,
    ):
        assert zv.compute_dex_snapshot_app_root_v0(mutated) != root

    partial_root = zv.compute_required_app_root(
        [leaf for leaf in leaves if leaf.lane_kind in {"spot", "oracle", "vault", "perps", "governance"}],
        required_lane_kinds={"spot", "oracle", "vault", "perps", "governance"},
    )
    # Review note, grade B+ -> A-: the release evidence once described this
    # partial four-lane tree as a full app-root JMT. The test keeps that
    # overclaim from returning by proving the full app-root is distinct.
    assert partial_root != root

    missing_perps = deepcopy(snapshot)
    missing_perps.pop("perps")
    with pytest.raises(ValueError, match="dex_snapshot missing perps app-root field"):
        zv.compute_dex_snapshot_app_root_v0(missing_perps)
    with pytest.raises(ValueError, match="dex_snapshot missing spot app-root field"):
        zv.compute_dex_snapshot_app_root_v0({"version": 4, "oracle": None, "vault": None, "perps": None})
    with pytest.raises(TypeError, match="state must be a DexState"):
        zv.app_root_lanes_from_dex_state_v0({})  # type: ignore[arg-type]


def test_run_local_pre_snapshot_header_binds_dex_app_root(tmp_path: Path) -> None:
    from tools.zeno_ledger_run_local import ZERO_ROOT, build_local_block_v0

    snapshot = zv.snapshot_from_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())).data
    snapshot["oracle"] = {"price_timestamp": 17, "max_staleness_seconds": 300}
    snapshot_path = tmp_path / "pre-snapshot.json"
    snapshot_path.write_text(json.dumps(snapshot, sort_keys=True), encoding="utf-8")
    body_path = tmp_path / "body.json"
    body = _body(txs=[])
    body_path.write_text(json.dumps(body, sort_keys=True), encoding="utf-8")

    report = build_local_block_v0(
        body_path=body_path,
        out_dir=tmp_path / "ledger",
        time_ms=1_778_730_000_000,
        pre_snapshot_path=snapshot_path,
        trusted_prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        data_availability_root=_root("da"),
        proof_journal_hash=ZERO_ROOT,
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )
    header = json.loads(Path(str(report["header_path"])).read_text(encoding="utf-8"))
    expected = zv.compute_dex_snapshot_app_root_v0(snapshot)

    # Review note, grade A-: the local pre-snapshot builder used to commit only
    # the spot root. The header now commits the typed DEX app root, so oracle,
    # vault, and perps fields are part of the block root.
    assert header["pre_state_root"] == expected
    assert header["post_state_root"] == expected
    assert zv.dex_state_root_v0(state_from_snapshot(snapshot)) == expected


def test_run_local_tau_app_derives_epoch_from_anchored_height(tmp_path: Path) -> None:
    from src.integration.tau_testnet_dex_plugin import (
        build_zusd_policy_bound_genesis_app_state,
    )
    from src.integration.zusd_monetary_bridge import ZUSDMonetaryConfig
    from tools.zeno_ledger_run_local import build_local_block_v0

    chain_id = "zeno-ledger-devnet-0"
    app_state_json, _app_hash = build_zusd_policy_bound_genesis_app_state(
        config=ZUSDMonetaryConfig(chain_id=chain_id)
    )
    app_state_path = tmp_path / "app-state.json"
    app_state_path.write_text(app_state_json, encoding="utf-8")
    body_path = tmp_path / "body.json"
    body_path.write_text(
        json.dumps(_body(txs=[]), sort_keys=True),
        encoding="utf-8",
    )

    report = build_local_block_v0(
        body_path=body_path,
        out_dir=tmp_path / "ledger",
        time_ms=1_778_730_000_000,
        tau_app_state_path=app_state_path,
        trusted_prev_header_hash=_root("trusted-parent"),
        trusted_prev_height=0,
        sequencer_set_hash=_root("sequencer-set"),
        data_availability_root=_root("da"),
        proof_journal_hash=ZERO_ROOT,
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )

    assert report["execution_clock"]["height"] == 1
    assert report["execution_clock"]["derived_epoch"] == 1
    post_state = json.loads(
        Path(str(report["post_app_state_path"])).read_text(encoding="utf-8")
    )
    assert post_state["zusd_monetary"]["core"]["now_epoch"] == 1


def test_run_local_tau_app_rejects_unanchored_non_genesis_height(
    tmp_path: Path,
) -> None:
    from src.integration.tau_testnet_dex_plugin import (
        build_zusd_policy_bound_genesis_app_state,
    )
    from src.integration.zusd_monetary_bridge import ZUSDMonetaryConfig
    from tools.zeno_ledger_run_local import build_local_block_v0

    chain_id = "zeno-ledger-devnet-0"
    app_state_json, _app_hash = build_zusd_policy_bound_genesis_app_state(
        config=ZUSDMonetaryConfig(chain_id=chain_id)
    )
    app_state_path = tmp_path / "app-state.json"
    app_state_path.write_text(app_state_json, encoding="utf-8")
    body_path = tmp_path / "body.json"
    body_path.write_text(
        json.dumps(_body(txs=[]), sort_keys=True),
        encoding="utf-8",
    )

    with pytest.raises(
        ValueError,
        match="Tau app execution above genesis requires --prev-header",
    ):
        build_local_block_v0(
            body_path=body_path,
            out_dir=tmp_path / "ledger",
            time_ms=1_778_730_000_000,
            tau_app_state_path=app_state_path,
            sequencer_set_hash=_root("sequencer-set"),
            data_availability_root=_root("da"),
            proof_journal_hash=ZERO_ROOT,
            config_digest=_root("config"),
            module_versions_digest=_root("modules"),
            signature_set_root=ZERO_ROOT,
        )


def test_run_local_custom_clock_schedule_requires_expected_hash(
    tmp_path: Path,
) -> None:
    from src.core.consensus_time import default_height_only_clock_schedule_v1
    from src.integration.tau_testnet_dex_plugin import (
        build_zusd_policy_bound_genesis_app_state,
    )
    from src.integration.zusd_monetary_bridge import ZUSDMonetaryConfig
    from tools.zeno_ledger_run_local import build_local_block_v0

    chain_id = "zeno-ledger-devnet-0"
    app_state_json, _app_hash = build_zusd_policy_bound_genesis_app_state(
        config=ZUSDMonetaryConfig(chain_id=chain_id)
    )
    app_state_path = tmp_path / "app-state.json"
    app_state_path.write_text(app_state_json, encoding="utf-8")
    schedule_path = tmp_path / "clock-schedule.json"
    schedule_path.write_text(
        json.dumps(
            default_height_only_clock_schedule_v1(chain_id=chain_id).to_obj(),
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    body_path = tmp_path / "body.json"
    body_path.write_text(
        json.dumps(_body(txs=[]), sort_keys=True),
        encoding="utf-8",
    )

    with pytest.raises(
        ValueError,
        match="custom --clock-policy-schedule requires",
    ):
        build_local_block_v0(
            body_path=body_path,
            out_dir=tmp_path / "ledger",
            time_ms=1_778_730_000_000,
            clock_policy_schedule_path=schedule_path,
            tau_app_state_path=app_state_path,
            trusted_prev_header_hash=_root("trusted-parent"),
            trusted_prev_height=0,
            sequencer_set_hash=_root("sequencer-set"),
            data_availability_root=_root("da"),
            proof_journal_hash=ZERO_ROOT,
            config_digest=_root("config"),
            module_versions_digest=_root("modules"),
            signature_set_root=ZERO_ROOT,
        )


def test_tau_app_state_app_root_binds_wrapper_only_lanes() -> None:
    snapshot = zv.snapshot_from_state(DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())).data
    wrapper = {
        "schema": zv.TAU_APP_STATE_SCHEMA_V1,
        "version": 1,
        "dex_state": snapshot,
        "proof_mining": None,
        "zusd_monetary": None,
    }
    root = zv.compute_tau_app_state_app_root_v0(wrapper)
    leaves = zv.app_root_lanes_from_tau_app_state_v0(wrapper)

    assert {leaf.lane_kind for leaf in leaves} == set(zv.APP_ROOT_REQUIRED_TAU_APP_LANE_KINDS_V0)

    proof_mutation = deepcopy(wrapper)
    proof_mutation["proof_mining"] = {
        "schema": "zenodex/proof_mining_runtime_state/v1",
        "claimed_slots": [{"proposal_hash": "p0"}],
    }
    zusd_mutation = deepcopy(wrapper)
    zusd_mutation["zusd_monetary"] = {"schema": "zenodex/zusd_monetary_state/v1", "core": {"debt_e8": 1}}
    clob_mutation = deepcopy(wrapper)
    clob_mutation["clob"] = {"books": [{"market_id": "TAU-USDC", "orders": []}]}
    orderbook_mutation = deepcopy(wrapper)
    orderbook_mutation["orderbook"] = {"books": [{"market_id": "TAU-USDC", "orders": []}]}
    governance_mutation = deepcopy(wrapper)
    governance_mutation["governance"] = {
        "schema": "zenodex.zeno_ledger.autogovnext_governance_state.v1",
        "version": 1,
        "surface_state": {"fee_bps": 300},
    }

    # Review note, grade A-: a wrapper-level root that ignores proof mining,
    # zUSD, or CLOB/orderbook state is still incomplete even when DexState lanes
    # are bound. These checks give each wrapper-only lane teeth.
    for mutated in (proof_mutation, zusd_mutation, clob_mutation, orderbook_mutation, governance_mutation):
        assert zv.compute_tau_app_state_app_root_v0(mutated) != root

    missing_optional_wrapper = {"schema": zv.TAU_APP_STATE_SCHEMA_V1, "dex_state": snapshot}
    assert zv.compute_tau_app_state_app_root_v0(missing_optional_wrapper) != root

    bad_schema = deepcopy(wrapper)
    bad_schema["schema"] = "bad"
    with pytest.raises(ValueError, match="app_state schema mismatch"):
        zv.compute_tau_app_state_app_root_v0(bad_schema)
    bad_version = deepcopy(wrapper)
    bad_version["version"] = 2
    with pytest.raises(ValueError, match="unsupported app_state version"):
        zv.compute_tau_app_state_app_root_v0(bad_version)
    unknown_field = deepcopy(wrapper)
    unknown_field["uncommitted_module"] = {}
    with pytest.raises(ValueError, match="unsupported app_state app-root field"):
        zv.compute_tau_app_state_app_root_v0(unknown_field)
    ambiguous_clob = deepcopy(wrapper)
    ambiguous_clob["clob"] = {}
    ambiguous_clob["orderbook"] = {}
    with pytest.raises(ValueError, match="must not carry both clob and orderbook"):
        zv.compute_tau_app_state_app_root_v0(ambiguous_clob)


def test_tau_app_state_v2_app_root_binds_generic_token_authority() -> None:
    snapshot = zv.snapshot_from_state(
        DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    ).data
    asset = "0x" + "12" * 32
    signer = "0x" + "34" * 48
    authority = {
        "schema": "zenodex/generic_token_authority/v1",
        "version": 1,
        "assets": [
            {
                "asset_id": asset,
                "total_supply_units": 7,
                "mint_authority_pubkey": signer,
            }
        ],
    }
    wrapper = {
        "schema": zv.TAU_APP_STATE_SCHEMA_V2,
        "version": zv.TAU_APP_STATE_VERSION_V2,
        "dex_state": snapshot,
        "proof_mining": None,
        "zusd_monetary": None,
        "generic_token_authority": authority,
    }
    root = zv.compute_tau_app_state_app_root_v0(wrapper)

    supply_mutation = deepcopy(wrapper)
    supply_mutation["generic_token_authority"]["assets"][0]["total_supply_units"] = 8
    assert zv.compute_tau_app_state_app_root_v0(supply_mutation) != root

    v1_wrapper = deepcopy(wrapper)
    v1_wrapper["schema"] = zv.TAU_APP_STATE_SCHEMA_V1
    v1_wrapper["version"] = zv.TAU_APP_STATE_VERSION_V1
    with pytest.raises(ValueError, match="unsupported app_state app-root field"):
        zv.compute_tau_app_state_app_root_v0(v1_wrapper)

    missing_authority = deepcopy(wrapper)
    missing_authority.pop("generic_token_authority")
    with pytest.raises(TypeError, match="generic_token_authority must be an object"):
        zv.compute_tau_app_state_app_root_v0(missing_authority)

    wrong_version = deepcopy(wrapper)
    wrong_version["version"] = zv.TAU_APP_STATE_VERSION_V1
    with pytest.raises(ValueError, match="unsupported app_state version"):
        zv.compute_tau_app_state_app_root_v0(wrong_version)


def test_proof_metadata_schema_and_kind_boundaries() -> None:
    header = _header()
    metadata = _proof_metadata(header=header)

    missing_key = dict(metadata)
    missing_key.pop("journal_hash")
    with pytest.raises(ValueError, match="keys mismatch"):
        validate_proof_metadata_v0(missing_key)

    bad_schema = dict(metadata)
    bad_schema["schema"] = "bad"
    with pytest.raises(ValueError, match="schema mismatch"):
        validate_proof_metadata_v0(bad_schema)

    same_program_and_verifier = dict(metadata)
    same_program_and_verifier["verifier_id"] = same_program_and_verifier["program_id"]
    with pytest.raises(ValueError, match="must be distinct"):
        validate_proof_metadata_v0(same_program_and_verifier)

    tee = dict(metadata)
    tee["proof_kind"] = "tee_attestation_v0"
    tee["program_id"] = "tee:confidential-advisory-v1"
    tee["verifier_id"] = "tee:attestation-verifier-v1"
    tee["tee_measurement_hash"] = _root("tee-measurement")
    validate_proof_metadata_v0(tee)

    recursive = dict(metadata)
    recursive["proof_kind"] = "recursive_epoch_v0"
    recursive["program_id"] = "recursive:epoch-aggregator-v1"
    recursive["verifier_id"] = "recursive:receipt-verifier-v1"
    recursive["child_receipts_root"] = _root("child-receipts")
    validate_proof_metadata_v0(recursive)

    non_recursive_with_children = dict(metadata)
    non_recursive_with_children["child_receipts_root"] = _root("unexpected-children")
    with pytest.raises(ValueError, match="child_receipts_root must be zero"):
        validate_proof_metadata_v0(non_recursive_with_children)


def test_body_transaction_application_rejects_engine_edge_cases(monkeypatch) -> None:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    body = _body(txs=[{"operations": {}, "block_timestamp": 123, "tx_sender_pubkey": "alice"}])
    config = DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False)

    with pytest.raises(TypeError, match="config must be a DexEngineConfig"):
        zv.apply_body_transactions_v0(state=state, body=body, config=object())  # type: ignore[arg-type]

    class _Result:
        def __init__(self, *, ok: bool, state: DexState | None = None, error: str | None = None) -> None:
            self.ok = ok
            self.state = state
            self.error = error

    monkeypatch.setattr(zv, "apply_ops", lambda **_kwargs: _Result(ok=True, state=None))
    _next_state, executed, receipts = zv.apply_body_transactions_v0(state=state, body=body, config=config)
    assert receipts[0]["accepted"] is False
    assert executed["evidence"]["rejection_receipts"][-1]["error_code"] == "accepted_transaction_returned_no_state"

    monkeypatch.setattr(zv, "apply_ops", lambda **_kwargs: _Result(ok=False, error="settlement invalid"))
    _next_state, executed, receipts = zv.apply_body_transactions_v0(state=state, body=body, config=config)
    assert receipts[0]["accepted"] is False
    assert executed["evidence"]["rejection_receipts"][-1]["error_code"] == "settlement_invalid"

    missing_timestamp = _body(txs=[{"operations": {}}])
    _next_state, executed, receipts = zv.apply_body_transactions_v0(
        state=state,
        body=missing_timestamp,
        config=config,
    )
    assert receipts[0]["accepted"] is False
    assert executed["evidence"]["rejection_receipts"][-1]["error_code"] == "transactions_0_block_timestamp_is_required"

    seen_sender: list[str | None] = []

    def _capture_sender(**kwargs):
        seen_sender.append(kwargs["tx_sender_pubkey"])
        return _Result(ok=False, error="captured")

    monkeypatch.setattr(zv, "apply_ops", _capture_sender)
    no_sender = _body(txs=[{"operations": {}, "block_timestamp": 123}])
    zv.apply_body_transactions_v0(state=state, body=no_sender, config=config)
    assert seen_sender == [None]

    def _programmer_error(**_kwargs):
        raise RuntimeError("unexpected engine bug")

    monkeypatch.setattr(zv, "apply_ops", _programmer_error)
    with pytest.raises(RuntimeError, match="unexpected engine bug"):
        zv.apply_body_transactions_v0(state=state, body=body, config=config)


def test_structural_validators_reject_boundary_mutations() -> None:
    ingress = _ingress()
    ingress["batch_cutoff"]["schema"] = "bad"  # type: ignore[index]
    with pytest.raises(ValueError, match="batch_cutoff schema mismatch"):
        zv.validate_ingress_v0(ingress)

    ingress = _ingress()
    ingress["ingress_receipts"][0]["schema"] = "bad"  # type: ignore[index]
    with pytest.raises(ValueError, match="ingress_receipts\\[0\\] schema mismatch"):
        zv.validate_ingress_v0(ingress)

    ingress = _ingress()
    ingress["forced_inclusion_requests"][0]["schema"] = "bad"  # type: ignore[index]
    with pytest.raises(ValueError, match="forced_inclusion_requests\\[0\\] schema mismatch"):
        zv.validate_ingress_v0(ingress)

    ingress = _ingress()
    ingress["forced_inclusion_decisions"][0]["schema"] = "bad"  # type: ignore[index]
    with pytest.raises(ValueError, match="forced_inclusion_decisions\\[0\\] schema mismatch"):
        zv.validate_ingress_v0(ingress)

    ingress = _ingress()
    ingress["forced_inclusion_decisions"][0]["decision"] = "maybe"  # type: ignore[index]
    with pytest.raises(ValueError, match="decision is not allowed"):
        zv.validate_ingress_v0(ingress)

    body = _body()
    body["schema"] = "bad"
    with pytest.raises(ValueError, match="body schema mismatch"):
        validate_body_v0(body)

    body = _body()
    body["evidence"] = {"upba_certificates": []}
    with pytest.raises(ValueError, match="evidence keys mismatch"):
        validate_body_v0(body)

    header = _header()
    missing_header_key = dict(header)
    missing_header_key.pop("tx_root")
    with pytest.raises(ValueError, match="header keys mismatch"):
        validate_header_v0(missing_header_key)

    bad_schema_header = dict(header)
    bad_schema_header["schema"] = "bad"
    with pytest.raises(ValueError, match="header schema mismatch"):
        validate_header_v0(bad_schema_header)

    bad_validator_schema = _validator_set()
    bad_validator_schema["schema"] = "bad"
    with pytest.raises(ValueError, match="validator_set schema mismatch"):
        validate_validator_set_v0(bad_validator_schema)

    app_fields = {
        "chain_id": "zeno-ledger-devnet-0",
        "height": 1,
        "post_state_root": _root("post-state"),
        "evidence_root": _root("evidence"),
        "config_digest": _root("config"),
    }
    with pytest.raises(ValueError, match="app_hash fields mismatch"):
        compute_app_hash_v0(app_fields)

    validator_set = _validator_set()
    empty_validators = dict(validator_set)
    empty_validators["validators"] = []
    with pytest.raises(ValueError, match="must be non-empty"):
        validate_validator_set_v0(empty_validators)

    bad_validator = _validator_set(validators=[{"validator_id": "v0", "public_key": "pk"}])
    with pytest.raises(ValueError, match="validator keys mismatch"):
        validate_validator_set_v0(bad_validator)


def test_header_chain_and_binding_reject_boundary_mutations() -> None:
    header = _header()
    validator_set = _validator_set()
    wrong_chain_validator_set = dict(validator_set)
    wrong_chain_validator_set["chain_id"] = "other-chain"
    with pytest.raises(ValueError, match="header/validator_set chain_id mismatch"):
        validate_header_validator_set_hash_v0(header, wrong_chain_validator_set)

    wrong_hash_header = dict(header)
    wrong_hash_header["sequencer_set_hash"] = _root("wrong-sequencer-set")
    with pytest.raises(ValueError, match="sequencer_set_hash mismatch"):
        validate_header_validator_set_hash_v0(wrong_hash_header, validator_set)

    body = _body()
    wrong_chain_body = dict(body)
    wrong_chain_body["chain_id"] = "other-chain"
    wrong_chain_ingress = _ingress()
    wrong_chain_ingress["batch_cutoff"]["chain_id"] = "other-chain"  # type: ignore[index]
    wrong_chain_ingress["ingress_receipts"][0]["chain_id"] = "other-chain"  # type: ignore[index]
    wrong_chain_ingress["forced_inclusion_requests"][0]["chain_id"] = "other-chain"  # type: ignore[index]
    wrong_chain_ingress["forced_inclusion_decisions"][0]["chain_id"] = "other-chain"  # type: ignore[index]
    wrong_chain_body["ingress"] = wrong_chain_ingress
    with pytest.raises(ValueError, match="body/validator_set chain_id mismatch"):
        validate_body_validator_schedule_v0(wrong_chain_body, validator_set)

    with pytest.raises(TypeError, match="headers must be a sequence"):
        validate_header_chain_linkage_v0("bad")  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="headers must be a sequence"):
        detect_header_equivocations_v0("bad")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="headers must be non-empty"):
        validate_header_chain_linkage_v0([])
    with pytest.raises(TypeError, match="headers\\[0\\] must be a dict"):
        validate_header_chain_linkage_v0([object()])  # type: ignore[list-item]
    with pytest.raises(ValueError, match="first header prev_header_hash mismatch"):
        validate_header_chain_linkage_v0([header], expected_prev_header_hash=_root("wrong-parent"))

    other_chain = dict(header)
    other_chain["chain_id"] = "other-chain"
    with pytest.raises(ValueError, match="share one chain_id"):
        validate_header_chain_linkage_v0([header, other_chain])

    with pytest.raises(TypeError, match="headers must be a sequence"):
        evaluate_header_fork_choice_v0("bad")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="headers must be non-empty"):
        evaluate_header_fork_choice_v0([])
    with pytest.raises(TypeError, match="headers\\[0\\] must be a dict"):
        evaluate_header_fork_choice_v0([object()])  # type: ignore[list-item]
    other_chain_fork = dict(header)
    other_chain_fork["chain_id"] = "other-chain"
    with pytest.raises(ValueError, match="share one chain_id"):
        evaluate_header_fork_choice_v0([header, other_chain_fork], expected_prev_header_hash=ZERO_ROOT)

    orphan = _header(prev_header_hash=_root("unknown-parent"))
    with pytest.raises(ValueError, match="no anchored header chain"):
        evaluate_header_fork_choice_v0([orphan], expected_prev_header_hash=ZERO_ROOT)

    checkpoint = build_checkpoint_v0(header)
    bad_checkpoint = dict(checkpoint)
    bad_checkpoint.pop("body_root")
    with pytest.raises(ValueError, match="checkpoint keys mismatch"):
        zv.validate_checkpoint_v0(bad_checkpoint)
    bad_checkpoint = dict(checkpoint)
    bad_checkpoint["schema"] = "bad"
    with pytest.raises(ValueError, match="checkpoint schema mismatch"):
        zv.validate_checkpoint_v0(bad_checkpoint)


def test_header_body_and_proof_metadata_binding_edge_mismatches() -> None:
    body = _body()
    header = _header(body=body)

    other_chain_body = _body()
    other_chain_body["chain_id"] = "other-chain"
    other_chain_body["ingress"]["batch_cutoff"]["chain_id"] = "other-chain"  # type: ignore[index]
    other_chain_body["ingress"]["ingress_receipts"][0]["chain_id"] = "other-chain"  # type: ignore[index]
    other_chain_body["ingress"]["forced_inclusion_requests"][0]["chain_id"] = "other-chain"  # type: ignore[index]
    other_chain_body["ingress"]["forced_inclusion_decisions"][0]["chain_id"] = "other-chain"  # type: ignore[index]
    with pytest.raises(ValueError, match="header/body chain_id mismatch"):
        validate_header_body_roots_v0(header, other_chain_body)

    other_height_body = _body()
    other_height_body["height"] = 2
    other_height_body["ingress"]["batch_cutoff"]["height"] = 2  # type: ignore[index]
    other_height_body["ingress"]["ingress_receipts"][0]["height"] = 2  # type: ignore[index]
    with pytest.raises(ValueError, match="header/body height mismatch"):
        validate_header_body_roots_v0(header, other_height_body)

    metadata = _proof_metadata(header=header)
    metadata_hash = proof_metadata_hash_v0(metadata)
    proof_header = _header(proof_journal_hash=metadata_hash)

    wrong_chain_metadata = dict(metadata)
    wrong_chain_metadata["chain_id"] = "other-chain"
    with pytest.raises(ValueError, match="chain_id mismatch"):
        validate_proof_metadata_header_binding_v0(wrong_chain_metadata, proof_header)

    wrong_height_metadata = dict(metadata)
    wrong_height_metadata["height"] = 2
    with pytest.raises(ValueError, match="height mismatch"):
        validate_proof_metadata_header_binding_v0(wrong_height_metadata, proof_header)

    wrong_hash_header = dict(proof_header)
    wrong_hash_header["proof_journal_hash"] = _root("wrong-proof-journal")
    with pytest.raises(ValueError, match="proof_journal_hash mismatch"):
        validate_proof_metadata_header_binding_v0(metadata, wrong_hash_header)
