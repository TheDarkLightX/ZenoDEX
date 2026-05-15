"""Deterministic ZenoLedger v0 headers, roots, and checkpoints.

This module is intentionally narrow. It commits to ordered transaction bytes,
ingress accountability facts, settlement evidence, and DEX state roots. It does
not define new DEX execution semantics.
"""

from __future__ import annotations

import re
from copy import deepcopy
from typing import Any, Mapping, Sequence

from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)
from src.state.state_root import compute_state_root


HEADER_SCHEMA_V0 = "zenodex/zeno_ledger/header/v0"
BODY_SCHEMA_V0 = "zenodex/zeno_ledger/body/v0"
CHECKPOINT_SCHEMA_V0 = "zenodex/zeno_ledger/checkpoint/v0"
BATCH_CUTOFF_SCHEMA_V0 = "zenodex/zeno_ledger/batch_cutoff/v0"
INGRESS_RECEIPT_SCHEMA_V0 = "zenodex/zeno_ledger/ingress_receipt/v0"
FORCED_INCLUSION_REQUEST_SCHEMA_V0 = "zenodex/zeno_ledger/forced_inclusion_request/v0"
FORCED_INCLUSION_DECISION_SCHEMA_V0 = "zenodex/zeno_ledger/forced_inclusion_decision/v0"
TX_RECEIPT_SCHEMA_V0 = "zenodex/zeno_ledger/tx_receipt/v0"
PROOF_METADATA_SCHEMA_V0 = "zenodex/zeno_ledger/proof_metadata/v0"

LEDGER_ROOT_VERSION = 1
ROOT_NBYTES = 32
ZERO_ROOT_V0 = "0x" + "00" * ROOT_NBYTES

EMPTY_MERKLE_ROOT_V0 = sha256_hex(
    domain_sep_bytes("zeno_ledger_empty_merkle", version=LEDGER_ROOT_VERSION)
)

INGRESS_RECEIPT_STATUSES_V0 = frozenset(
    {
        "included",
        "pre_admission_rejected",
        "deferred_after_cutoff",
        "forced_inclusion_pending",
        "forced_inclusion_included",
        "forced_inclusion_rejected",
    }
)

FORCED_INCLUSION_DECISIONS_V0 = frozenset(
    {
        "included",
        "pre_admission_rejected",
        "expired_bad_request",
        "expired_missing_body",
    }
)

PROOF_KINDS_V0 = frozenset(
    {
        "deterministic_replay_v0",
        "risc0_zkvm_v0",
        "sp1_zkvm_v0",
        "tee_attestation_v0",
        "recursive_epoch_v0",
    }
)

ZK_PROOF_KINDS_V0 = frozenset({"risc0_zkvm_v0", "sp1_zkvm_v0"})

EVIDENCE_KEYS_V0 = (
    "upba_certificates",
    "price_grid_tables",
    "uniform_batch_hypergraph_roots",
    "oracle_packets",
    "proof_receipts",
    "rejection_receipts",
)

HEADER_ROOT_FIELDS_V0 = (
    "prev_header_hash",
    "sequencer_set_hash",
    "ingress_root",
    "tx_root",
    "pre_state_root",
    "post_state_root",
    "app_hash",
    "evidence_root",
    "body_root",
    "data_availability_root",
    "proof_journal_hash",
    "config_digest",
    "module_versions_digest",
    "signature_set_root",
)

APP_HASH_ROOT_FIELDS_V0 = (
    "post_state_root",
    "evidence_root",
    "config_digest",
    "module_versions_digest",
)

_DOMAIN_RE = re.compile(r"^[A-Za-z0-9_.:/-]+$")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_list(value: object, *, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not allow_empty and value == "":
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _require_optional_str(value: object, *, name: str) -> str | None:
    if value is None:
        return None
    return _require_str(value, name=name)


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_nonzero_root(value: object, *, name: str) -> str:
    root = _require_root(value, name=name)
    if root == ZERO_ROOT_V0:
        raise ValueError(f"{name} must be non-zero")
    return root


def _validate_domain(domain: str) -> str:
    if not isinstance(domain, str) or not domain:
        raise TypeError("domain must be a non-empty str")
    if not _DOMAIN_RE.fullmatch(domain):
        raise ValueError("domain contains unsupported characters")
    return domain


def canonical_json_bytes_v0(value: object) -> bytes:
    """Canonical JSON bytes used for ZenoLedger v0 commitments."""

    return canonical_json_bytes(value)


def hash_v0(domain: str, value: object | bytes) -> str:
    """Hash a value with ZenoLedger v0 domain separation."""

    domain = _validate_domain(domain)
    prefix = domain_sep_bytes(f"zeno_ledger_{domain}", version=LEDGER_ROOT_VERSION)
    if isinstance(value, (bytes, bytearray)):
        payload = prefix + encode_bytes(bytes(value))
    else:
        payload = prefix + encode_bytes(canonical_json_bytes_v0(value))
    return sha256_hex(payload)


def _root_bytes(root: str, *, name: str) -> bytes:
    _require_root(root, name=name)
    return hex_to_bytes_fixed(root, nbytes=ROOT_NBYTES, name=name)


def merkle_root_v0(domain: str, leaves: Sequence[str]) -> str:
    """Compute an ordered binary Merkle commitment over 32-byte leaf hashes."""

    domain = _validate_domain(domain)
    if not isinstance(leaves, Sequence) or isinstance(leaves, (str, bytes, bytearray)):
        raise TypeError("leaves must be a sequence of root strings")
    if len(leaves) == 0:
        return EMPTY_MERKLE_ROOT_V0

    nodes: list[bytes] = []
    for index, leaf in enumerate(leaves):
        leaf_bytes = _root_bytes(leaf, name=f"leaf[{index}]")
        nodes.append(
            bytes.fromhex(
                hash_v0(
                    f"merkle_leaf_{domain}",
                    domain_sep_bytes(f"zeno_ledger_leaf_index_{domain}", version=LEDGER_ROOT_VERSION)
                    + encode_uvarint(index)
                    + leaf_bytes,
                )[2:]
            )
        )

    level = 0
    while len(nodes) > 1:
        next_nodes: list[bytes] = []
        for pair_index in range(0, len(nodes), 2):
            left = nodes[pair_index]
            right = nodes[pair_index + 1] if pair_index + 1 < len(nodes) else left
            next_nodes.append(
                bytes.fromhex(
                    hash_v0(
                        f"merkle_node_{domain}",
                        domain_sep_bytes(
                            f"zeno_ledger_node_index_{domain}",
                            version=LEDGER_ROOT_VERSION,
                        )
                        + encode_uvarint(level)
                        + encode_uvarint(pair_index // 2)
                        + left
                        + right,
                    )[2:]
                )
            )
        nodes = next_nodes
        level += 1
    return "0x" + nodes[0].hex()


def tx_hash_v0(tx: object) -> str:
    return hash_v0("tx_v0", tx)


def compute_tx_root_v0(transactions: list[object]) -> str:
    _require_list(transactions, name="transactions")
    return merkle_root_v0("tx_root_v0", [tx_hash_v0(tx) for tx in transactions])


def dex_state_root_v0(state: DexState) -> str:
    if not isinstance(state, DexState):
        raise TypeError("state must be a DexState")
    return compute_state_root(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
    )


def _stable_error_code_v0(error: str | None) -> str:
    raw = "unknown_error" if not error else str(error).strip().lower()
    out = re.sub(r"[^a-z0-9_]+", "_", raw).strip("_")
    return out[:160] or "unknown_error"


def stable_error_code_v0(error: str | None) -> str:
    return _stable_error_code_v0(error)


def build_tx_receipt_v0(
    *,
    tx_hash: str,
    height: int,
    index: int,
    accepted: bool,
    error_code: str | None,
    state_changed: bool,
) -> dict[str, Any]:
    _require_root(tx_hash, name="tx_hash")
    _require_nonnegative_int(height, name="height")
    _require_nonnegative_int(index, name="index")
    if not isinstance(accepted, bool):
        raise TypeError("accepted must be a bool")
    if not isinstance(state_changed, bool):
        raise TypeError("state_changed must be a bool")
    if accepted and error_code is not None:
        raise ValueError("accepted receipt must not carry error_code")
    if not accepted:
        _require_str(error_code, name="error_code")
    body = {
        "schema": TX_RECEIPT_SCHEMA_V0,
        "tx_hash": tx_hash,
        "height": height,
        "index": index,
        "accepted": accepted,
        "error_code": error_code,
        "state_changed": state_changed,
    }
    return {**body, "receipt_hash": hash_v0("tx_receipt_v0", body)}


def build_proof_metadata_v0(
    *,
    chain_id: str,
    height: int,
    proof_kind: str,
    program_id: str,
    verifier_id: str,
    proof_commitment: str,
    public_input_hash: str,
    journal_hash: str,
    pre_state_root: str,
    post_state_root: str,
    tx_root: str,
    evidence_root: str,
    body_root: str,
    conflict_schedule_hash: str,
    feature_suite_hash: str,
    dependency_lock_hash: str,
    tee_measurement_hash: str = ZERO_ROOT_V0,
    child_receipts_root: str = ZERO_ROOT_V0,
) -> dict[str, Any]:
    """Build proof metadata that can be bound into `header.proof_journal_hash`.

    This object is backend-neutral. It does not verify Risc0/SP1/TEE cryptography;
    it records the public binding contract that those verifiers must satisfy.
    """

    metadata = {
        "schema": PROOF_METADATA_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "proof_kind": proof_kind,
        "program_id": program_id,
        "verifier_id": verifier_id,
        "proof_commitment": proof_commitment,
        "public_input_hash": public_input_hash,
        "journal_hash": journal_hash,
        "pre_state_root": pre_state_root,
        "post_state_root": post_state_root,
        "tx_root": tx_root,
        "evidence_root": evidence_root,
        "body_root": body_root,
        "conflict_schedule_hash": conflict_schedule_hash,
        "feature_suite_hash": feature_suite_hash,
        "dependency_lock_hash": dependency_lock_hash,
        "tee_measurement_hash": tee_measurement_hash,
        "child_receipts_root": child_receipts_root,
    }
    validate_proof_metadata_v0(metadata)
    return metadata


def validate_proof_metadata_v0(metadata: dict[str, Any]) -> None:
    obj = _require_mapping(metadata, name="proof_metadata")
    expected = {
        "schema",
        "chain_id",
        "height",
        "proof_kind",
        "program_id",
        "verifier_id",
        "proof_commitment",
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
        "tee_measurement_hash",
        "child_receipts_root",
    }
    if set(obj.keys()) != expected:
        raise ValueError("proof_metadata keys mismatch")
    if obj.get("schema") != PROOF_METADATA_SCHEMA_V0:
        raise ValueError("proof_metadata schema mismatch")

    _require_str(obj.get("chain_id"), name="proof_metadata.chain_id")
    _require_nonnegative_int(obj.get("height"), name="proof_metadata.height")
    proof_kind = _require_str(obj.get("proof_kind"), name="proof_metadata.proof_kind")
    if proof_kind not in PROOF_KINDS_V0:
        raise ValueError("proof_metadata proof_kind is not allowed")
    _require_str(obj.get("program_id"), name="proof_metadata.program_id")
    _require_str(obj.get("verifier_id"), name="proof_metadata.verifier_id")
    for key in (
        "proof_commitment",
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
        _require_nonzero_root(obj.get(key), name=f"proof_metadata.{key}")
    for key in (
        "tee_measurement_hash",
        "child_receipts_root",
    ):
        _require_root(obj.get(key), name=f"proof_metadata.{key}")

    tee_measurement_hash = obj["tee_measurement_hash"]
    child_receipts_root = obj["child_receipts_root"]
    if proof_kind == "tee_attestation_v0":
        _require_nonzero_root(tee_measurement_hash, name="proof_metadata.tee_measurement_hash")
    elif tee_measurement_hash != ZERO_ROOT_V0:
        raise ValueError("proof_metadata tee_measurement_hash must be zero for non-TEE proof")

    if proof_kind == "recursive_epoch_v0":
        _require_nonzero_root(child_receipts_root, name="proof_metadata.child_receipts_root")
    elif child_receipts_root != ZERO_ROOT_V0:
        raise ValueError("proof_metadata child_receipts_root must be zero for non-recursive proof")

    if proof_kind in ZK_PROOF_KINDS_V0 and obj["program_id"] == obj["verifier_id"]:
        raise ValueError("proof_metadata zk program_id and verifier_id must be distinct")


def proof_metadata_hash_v0(metadata: dict[str, Any]) -> str:
    validate_proof_metadata_v0(metadata)
    return hash_v0("proof_metadata_v0", metadata)


def _extract_tx_operations_v0(tx: object, *, index: int) -> Mapping[str, Any]:
    obj = _require_mapping(tx, name=f"transactions[{index}]")
    operations = obj.get("operations")
    if operations is None:
        raise ValueError(f"transactions[{index}].operations is required")
    return _require_mapping(operations, name=f"transactions[{index}].operations")


def _extract_tx_block_timestamp_v0(tx: object, *, index: int, default: int | None) -> int:
    obj = _require_mapping(tx, name=f"transactions[{index}]")
    value = obj.get("block_timestamp", default)
    if value is None:
        raise ValueError(f"transactions[{index}].block_timestamp is required")
    return _require_nonnegative_int(value, name=f"transactions[{index}].block_timestamp")


def _extract_tx_sender_v0(tx: object, *, index: int) -> str | None:
    obj = _require_mapping(tx, name=f"transactions[{index}]")
    value = obj.get("tx_sender_pubkey")
    if value is None:
        return None
    return _require_str(value, name=f"transactions[{index}].tx_sender_pubkey")


def apply_body_transactions_v0(
    *,
    state: DexState,
    body: dict[str, Any],
    config: DexEngineConfig,
    default_block_timestamp: int | None = None,
) -> tuple[DexState, dict[str, Any], list[dict[str, Any]]]:
    """
    Execute `body.transactions` through `apply_ops`.

    Rejected transactions leave state unchanged and are committed into
    `body.evidence.rejection_receipts` in the returned body.
    """

    if not isinstance(config, DexEngineConfig):
        raise TypeError("config must be a DexEngineConfig")
    validate_body_v0(body)
    working_state = state
    executed_body = deepcopy(body)
    receipts: list[dict[str, Any]] = []
    rejection_receipts = executed_body["evidence"]["rejection_receipts"]
    height = _require_nonnegative_int(executed_body["height"], name="body.height")

    for index, tx in enumerate(executed_body["transactions"]):
        tx_hash = tx_hash_v0(tx)
        try:
            operations = dict(_extract_tx_operations_v0(tx, index=index))
            block_timestamp = _extract_tx_block_timestamp_v0(
                tx,
                index=index,
                default=default_block_timestamp,
            )
            tx_sender = _extract_tx_sender_v0(tx, index=index)
            result = apply_ops(
                config=config,
                state=working_state,
                operations=operations,
                block_timestamp=block_timestamp,
                tx_sender_pubkey=tx_sender,
            )
            if result.ok:
                if result.state is None:
                    raise ValueError("accepted transaction returned no state")
                state_changed = result.state is not working_state
                working_state = result.state
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=True,
                    error_code=None,
                    state_changed=state_changed,
                )
            else:
                receipt = build_tx_receipt_v0(
                    tx_hash=tx_hash,
                    height=height,
                    index=index,
                    accepted=False,
                    error_code=_stable_error_code_v0(result.error),
                    state_changed=False,
                )
                rejection_receipts.append(receipt)
        except Exception as exc:
            receipt = build_tx_receipt_v0(
                tx_hash=tx_hash,
                height=height,
                index=index,
                accepted=False,
                error_code=_stable_error_code_v0(str(exc)),
                state_changed=False,
            )
            rejection_receipts.append(receipt)
        receipts.append(receipt)

    validate_body_v0(executed_body)
    return working_state, executed_body, receipts


def _validate_batch_cutoff(batch_cutoff: object) -> None:
    obj = _require_mapping(batch_cutoff, name="batch_cutoff")
    if obj.get("schema") != BATCH_CUTOFF_SCHEMA_V0:
        raise ValueError("batch_cutoff schema mismatch")
    _require_str(obj.get("chain_id"), name="batch_cutoff.chain_id")
    _require_nonnegative_int(obj.get("height"), name="batch_cutoff.height")
    _require_nonnegative_int(obj.get("cutoff_time_ms"), name="batch_cutoff.cutoff_time_ms")
    _require_nonnegative_int(obj.get("cutoff_sequence"), name="batch_cutoff.cutoff_sequence")
    _require_str(obj.get("sequencer_id"), name="batch_cutoff.sequencer_id")
    _require_str(obj.get("policy_id"), name="batch_cutoff.policy_id")
    _require_root(obj.get("policy_digest"), name="batch_cutoff.policy_digest")


def _validate_ingress_receipt(receipt: object, *, index: int) -> None:
    obj = _require_mapping(receipt, name=f"ingress_receipts[{index}]")
    if obj.get("schema") != INGRESS_RECEIPT_SCHEMA_V0:
        raise ValueError(f"ingress_receipts[{index}] schema mismatch")
    _require_str(obj.get("chain_id"), name=f"ingress_receipts[{index}].chain_id")
    _require_root(obj.get("tx_hash"), name=f"ingress_receipts[{index}].tx_hash")
    _require_nonnegative_int(
        obj.get("received_time_ms"),
        name=f"ingress_receipts[{index}].received_time_ms",
    )
    _require_nonnegative_int(
        obj.get("received_sequence"),
        name=f"ingress_receipts[{index}].received_sequence",
    )
    _require_str(obj.get("sequencer_id"), name=f"ingress_receipts[{index}].sequencer_id")
    status = _require_str(obj.get("status"), name=f"ingress_receipts[{index}].status")
    if status not in INGRESS_RECEIPT_STATUSES_V0:
        raise ValueError(f"ingress_receipts[{index}] status is not allowed")
    _require_nonnegative_int(obj.get("height"), name=f"ingress_receipts[{index}].height")
    _require_nonnegative_int(obj.get("index"), name=f"ingress_receipts[{index}].index")
    _require_optional_str(obj.get("reject_code"), name=f"ingress_receipts[{index}].reject_code")
    _require_root(obj.get("receipt_hash"), name=f"ingress_receipts[{index}].receipt_hash")


def _validate_forced_inclusion_request(request: object, *, index: int) -> None:
    obj = _require_mapping(request, name=f"forced_inclusion_requests[{index}]")
    if obj.get("schema") != FORCED_INCLUSION_REQUEST_SCHEMA_V0:
        raise ValueError(f"forced_inclusion_requests[{index}] schema mismatch")
    _require_str(obj.get("chain_id"), name=f"forced_inclusion_requests[{index}].chain_id")
    _require_root(obj.get("tx_hash"), name=f"forced_inclusion_requests[{index}].tx_hash")
    _require_root(obj.get("tx_body_hash"), name=f"forced_inclusion_requests[{index}].tx_body_hash")
    _require_str(obj.get("submitter_id"), name=f"forced_inclusion_requests[{index}].submitter_id")
    _require_nonnegative_int(
        obj.get("first_seen_time_ms"),
        name=f"forced_inclusion_requests[{index}].first_seen_time_ms",
    )
    _require_nonnegative_int(
        obj.get("first_seen_sequence"),
        name=f"forced_inclusion_requests[{index}].first_seen_sequence",
    )
    _require_nonnegative_int(
        obj.get("deadline_height"),
        name=f"forced_inclusion_requests[{index}].deadline_height",
    )
    _require_root(obj.get("request_hash"), name=f"forced_inclusion_requests[{index}].request_hash")


def _validate_forced_inclusion_decision(decision: object, *, index: int) -> None:
    obj = _require_mapping(decision, name=f"forced_inclusion_decisions[{index}]")
    if obj.get("schema") != FORCED_INCLUSION_DECISION_SCHEMA_V0:
        raise ValueError(f"forced_inclusion_decisions[{index}] schema mismatch")
    _require_str(obj.get("chain_id"), name=f"forced_inclusion_decisions[{index}].chain_id")
    _require_nonnegative_int(obj.get("height"), name=f"forced_inclusion_decisions[{index}].height")
    _require_root(obj.get("request_hash"), name=f"forced_inclusion_decisions[{index}].request_hash")
    decision_value = _require_str(
        obj.get("decision"),
        name=f"forced_inclusion_decisions[{index}].decision",
    )
    if decision_value not in FORCED_INCLUSION_DECISIONS_V0:
        raise ValueError(f"forced_inclusion_decisions[{index}] decision is not allowed")
    _require_root(obj.get("tx_hash"), name=f"forced_inclusion_decisions[{index}].tx_hash")
    _require_nonnegative_int(obj.get("index"), name=f"forced_inclusion_decisions[{index}].index")
    _require_optional_str(
        obj.get("reject_code"),
        name=f"forced_inclusion_decisions[{index}].reject_code",
    )


def validate_ingress_v0(ingress: dict[str, Any]) -> None:
    obj = _require_mapping(ingress, name="ingress")
    expected = {
        "batch_cutoff",
        "ingress_receipts",
        "forced_inclusion_requests",
        "forced_inclusion_decisions",
    }
    if set(obj.keys()) != expected:
        raise ValueError("ingress keys mismatch")
    _validate_batch_cutoff(obj["batch_cutoff"])
    for index, receipt in enumerate(_require_list(obj["ingress_receipts"], name="ingress_receipts")):
        _validate_ingress_receipt(receipt, index=index)
    for index, request in enumerate(
        _require_list(obj["forced_inclusion_requests"], name="forced_inclusion_requests")
    ):
        _validate_forced_inclusion_request(request, index=index)
    for index, decision in enumerate(
        _require_list(obj["forced_inclusion_decisions"], name="forced_inclusion_decisions")
    ):
        _validate_forced_inclusion_decision(decision, index=index)


def compute_ingress_root_v0(ingress: dict[str, Any]) -> str:
    validate_ingress_v0(ingress)
    leaves: list[str] = [hash_v0("batch_cutoff_v0", ingress["batch_cutoff"])]
    leaves.extend(hash_v0("ingress_receipt_v0", item) for item in ingress["ingress_receipts"])
    leaves.extend(
        hash_v0("forced_inclusion_request_v0", item)
        for item in ingress["forced_inclusion_requests"]
    )
    leaves.extend(
        hash_v0("forced_inclusion_decision_v0", item)
        for item in ingress["forced_inclusion_decisions"]
    )
    return merkle_root_v0("ingress_root_v0", leaves)


def _validate_evidence(evidence: object) -> Mapping[str, Any]:
    obj = _require_mapping(evidence, name="evidence")
    if set(obj.keys()) != set(EVIDENCE_KEYS_V0):
        raise ValueError("evidence keys mismatch")
    for key in EVIDENCE_KEYS_V0:
        _require_list(obj[key], name=f"evidence.{key}")
    return obj


def compute_evidence_root_v0(evidence: dict[str, Any]) -> str:
    obj = _validate_evidence(evidence)
    leaves: list[str] = []
    for key in EVIDENCE_KEYS_V0:
        leaves.extend(hash_v0(f"evidence_{key}_v0", item) for item in obj[key])
    return merkle_root_v0("evidence_root_v0", leaves)


def validate_body_v0(body: dict[str, Any]) -> None:
    obj = _require_mapping(body, name="body")
    expected = {"schema", "chain_id", "height", "ingress", "transactions", "settlement_envelopes", "evidence"}
    if set(obj.keys()) != expected:
        raise ValueError("body keys mismatch")
    if obj.get("schema") != BODY_SCHEMA_V0:
        raise ValueError("body schema mismatch")
    _require_str(obj.get("chain_id"), name="body.chain_id")
    _require_nonnegative_int(obj.get("height"), name="body.height")
    validate_ingress_v0(obj["ingress"])
    _require_list(obj.get("transactions"), name="body.transactions")
    _require_list(obj.get("settlement_envelopes"), name="body.settlement_envelopes")
    _validate_evidence(obj.get("evidence"))


def canonical_body_root_v0(body: dict[str, Any]) -> str:
    validate_body_v0(body)
    return hash_v0("body_v0", body)


def compute_app_hash_v0(fields: Mapping[str, Any]) -> str:
    obj = _require_mapping(fields, name="app_hash_fields")
    expected = {"chain_id", "height", *APP_HASH_ROOT_FIELDS_V0}
    if set(obj.keys()) != expected:
        raise ValueError("app_hash fields mismatch")
    _require_str(obj.get("chain_id"), name="app_hash.chain_id")
    _require_nonnegative_int(obj.get("height"), name="app_hash.height")
    for key in APP_HASH_ROOT_FIELDS_V0:
        _require_root(obj.get(key), name=f"app_hash.{key}")
    return hash_v0("app_hash_v0", dict(obj))


def validate_header_v0(header: dict[str, Any]) -> None:
    obj = _require_mapping(header, name="header")
    expected = {"schema", "chain_id", "height", "time_ms", *HEADER_ROOT_FIELDS_V0}
    if set(obj.keys()) != expected:
        raise ValueError("header keys mismatch")
    if obj.get("schema") != HEADER_SCHEMA_V0:
        raise ValueError("header schema mismatch")
    _require_str(obj.get("chain_id"), name="header.chain_id")
    _require_nonnegative_int(obj.get("height"), name="header.height")
    _require_nonnegative_int(obj.get("time_ms"), name="header.time_ms")
    for key in HEADER_ROOT_FIELDS_V0:
        _require_root(obj.get(key), name=f"header.{key}")


def canonical_header_hash_v0(header: dict[str, Any]) -> str:
    validate_header_v0(header)
    return hash_v0("header_v0", header)


def build_header_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    prev_header_hash: str,
    sequencer_set_hash: str,
    ingress_root: str,
    tx_root: str,
    pre_state_root: str,
    post_state_root: str,
    app_hash: str,
    evidence_root: str,
    body_root: str,
    data_availability_root: str,
    proof_journal_hash: str,
    config_digest: str,
    module_versions_digest: str,
    signature_set_root: str,
) -> dict[str, Any]:
    header = {
        "schema": HEADER_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "time_ms": time_ms,
        "prev_header_hash": prev_header_hash,
        "sequencer_set_hash": sequencer_set_hash,
        "ingress_root": ingress_root,
        "tx_root": tx_root,
        "pre_state_root": pre_state_root,
        "post_state_root": post_state_root,
        "app_hash": app_hash,
        "evidence_root": evidence_root,
        "body_root": body_root,
        "data_availability_root": data_availability_root,
        "proof_journal_hash": proof_journal_hash,
        "config_digest": config_digest,
        "module_versions_digest": module_versions_digest,
        "signature_set_root": signature_set_root,
    }
    validate_header_v0(header)
    return header


def expected_header_roots_from_body_v0(body: dict[str, Any]) -> dict[str, str]:
    """Return the body-derived header root fields for a ZenoLedger v0 body."""

    validate_body_v0(body)
    return {
        "ingress_root": compute_ingress_root_v0(body["ingress"]),
        "tx_root": compute_tx_root_v0(body["transactions"]),
        "evidence_root": compute_evidence_root_v0(body["evidence"]),
        "body_root": canonical_body_root_v0(body),
    }


def validate_header_body_roots_v0(header: dict[str, Any], body: dict[str, Any]) -> None:
    """Fail closed unless a header commits to the supplied body."""

    validate_header_v0(header)
    validate_body_v0(body)
    if header["chain_id"] != body["chain_id"]:
        raise ValueError("header/body chain_id mismatch")
    if header["height"] != body["height"]:
        raise ValueError("header/body height mismatch")

    expected_roots = expected_header_roots_from_body_v0(body)
    for key, expected in expected_roots.items():
        if header[key] != expected:
            raise ValueError(f"header {key} mismatch")

    expected_app_hash = compute_app_hash_v0(
        {
            "chain_id": header["chain_id"],
            "height": header["height"],
            "post_state_root": header["post_state_root"],
            "evidence_root": header["evidence_root"],
            "config_digest": header["config_digest"],
            "module_versions_digest": header["module_versions_digest"],
        }
    )
    if header["app_hash"] != expected_app_hash:
        raise ValueError("header app_hash mismatch")


def validate_proof_metadata_header_binding_v0(
    metadata: dict[str, Any],
    header: dict[str, Any],
) -> None:
    """Fail closed unless proof metadata is exactly bound to a header."""

    validate_proof_metadata_v0(metadata)
    validate_header_v0(header)
    if metadata["chain_id"] != header["chain_id"]:
        raise ValueError("proof_metadata/header chain_id mismatch")
    if metadata["height"] != header["height"]:
        raise ValueError("proof_metadata/header height mismatch")
    for key in (
        "pre_state_root",
        "post_state_root",
        "tx_root",
        "evidence_root",
        "body_root",
    ):
        if metadata[key] != header[key]:
            raise ValueError(f"proof_metadata/header {key} mismatch")
    if proof_metadata_hash_v0(metadata) != header["proof_journal_hash"]:
        raise ValueError("proof_metadata/header proof_journal_hash mismatch")


def validate_checkpoint_v0(checkpoint: dict[str, Any]) -> None:
    obj = _require_mapping(checkpoint, name="checkpoint")
    expected = {
        "schema",
        "chain_id",
        "height",
        "header_hash",
        "app_hash",
        "post_state_root",
        "ingress_root",
        "evidence_root",
        "body_root",
        "config_digest",
        "proof_journal_hash",
        "sequencer_set_hash",
        "signature_set_root",
        "signature_set",
    }
    if set(obj.keys()) != expected:
        raise ValueError("checkpoint keys mismatch")
    if obj.get("schema") != CHECKPOINT_SCHEMA_V0:
        raise ValueError("checkpoint schema mismatch")
    _require_str(obj.get("chain_id"), name="checkpoint.chain_id")
    _require_nonnegative_int(obj.get("height"), name="checkpoint.height")
    for key in (
        "header_hash",
        "app_hash",
        "post_state_root",
        "ingress_root",
        "evidence_root",
        "body_root",
        "config_digest",
        "proof_journal_hash",
        "sequencer_set_hash",
        "signature_set_root",
    ):
        _require_root(obj.get(key), name=f"checkpoint.{key}")
    _require_list(obj.get("signature_set"), name="checkpoint.signature_set")


def build_checkpoint_v0(header: dict[str, Any], *, signature_set: list[object] | None = None) -> dict[str, Any]:
    validate_header_v0(header)
    checkpoint = {
        "schema": CHECKPOINT_SCHEMA_V0,
        "chain_id": header["chain_id"],
        "height": header["height"],
        "header_hash": canonical_header_hash_v0(header),
        "app_hash": header["app_hash"],
        "post_state_root": header["post_state_root"],
        "ingress_root": header["ingress_root"],
        "evidence_root": header["evidence_root"],
        "body_root": header["body_root"],
        "config_digest": header["config_digest"],
        "proof_journal_hash": header["proof_journal_hash"],
        "sequencer_set_hash": header["sequencer_set_hash"],
        "signature_set_root": header["signature_set_root"],
        "signature_set": [] if signature_set is None else signature_set,
    }
    validate_checkpoint_v0(checkpoint)
    return checkpoint


def validate_checkpoint_header_binding_v0(
    checkpoint: dict[str, Any],
    header: dict[str, Any],
) -> None:
    """Fail closed unless a checkpoint is exactly derived from `header`."""

    validate_checkpoint_v0(checkpoint)
    validate_header_v0(header)
    expected = build_checkpoint_v0(
        header,
        signature_set=checkpoint["signature_set"],
    )
    if checkpoint != expected:
        raise ValueError("checkpoint/header binding mismatch")
