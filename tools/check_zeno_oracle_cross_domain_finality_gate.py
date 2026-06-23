#!/usr/bin/env python3
"""Check local cross-domain finality receipts for a ZenoOracle accepted read."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


POLICY_SCHEMA = "zenodex.oracle.cross_domain_finality_policy.v1"
READ_SCHEMA = "zenodex.oracle.cross_domain_accepted_read.v1"
RECEIPT_BUNDLE_SCHEMA = "zenodex.oracle.cross_domain_finality_receipt_bundle.v1"
RECEIPT_SCHEMA = "zenodex.oracle.cross_domain_finality_receipt.v1"
REPORT_SCHEMA = "zenodex.oracle.cross_domain_finality_gate_check.v1"
ADDRESS_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
SHA_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TX_RE = re.compile(r"^0x[0-9a-fA-F]{64}$")
REQUIRED_RECEIPT_KINDS = {"source_finality_checkpoint", "target_adapter_acceptance"}
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_cross_domain_finality",
    "does_not_claim_live_finality_adapter_receipts",
    "does_not_claim_live_oracle_network_safety",
}
RECEIPT_NOT_CLAIMS = {
    "does_not_claim_receipts_verified_against_live_rpc",
    "does_not_claim_finality_truth_beyond_receipt_bundle",
}
GO_LIVE_BLOCKERS = [
    "live_finality_adapter_receipts_not_verified_onchain",
    "cross_domain_finality_public_soak_not_completed",
    "target_adapter_deployment_not_verified_by_this_checker",
]
POLICY_KEYS = {
    "schema",
    "policy_id",
    "policy_name",
    "source_chain_id",
    "target_chain_id",
    "adapter_id",
    "adapter_contract",
    "min_confirmations",
    "max_reorg_depth",
    "finality_mode",
    "not_claimed",
}
READ_KEYS = {
    "schema",
    "read_id",
    "policy_id",
    "query_id",
    "value_hash",
    "source_chain_id",
    "target_chain_id",
    "observed_source_block_number",
    "observed_source_block_hash",
    "aggregate_root",
    "receipt_graph_root",
}
BUNDLE_KEYS = {"schema", "policy_id", "accepted_read_id", "receipts", "not_claimed"}
RECEIPT_KEYS = {
    "schema",
    "receipt_id",
    "kind",
    "chain_id",
    "contract_address",
    "tx_hash",
    "block_number",
    "block_hash",
    "log_index",
    "payload",
}
SOURCE_PAYLOAD_KEYS = {
    "policy_id",
    "accepted_read_id",
    "source_chain_id",
    "observed_source_block_number",
    "observed_source_block_hash",
    "finality_mode",
    "finalized",
    "finalized_block_number",
    "confirmation_count",
    "reorg_depth_observed",
    "finality_root",
}
TARGET_PAYLOAD_KEYS = {
    "policy_id",
    "accepted_read_id",
    "target_chain_id",
    "adapter_id",
    "adapter_contract",
    "finality_receipt_id",
    "query_id",
    "value_hash",
    "finality_root",
}


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def policy_content_hash(policy: Mapping[str, Any]) -> str:
    payload = dict(policy)
    payload.pop("policy_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def read_content_hash(read: Mapping[str, Any]) -> str:
    payload = dict(read)
    payload.pop("read_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def receipt_content_hash(receipt: Mapping[str, Any]) -> str:
    payload = dict(receipt)
    payload.pop("receipt_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _sha(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _tx(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and SHA_RE.fullmatch(value) is not None


def _is_address(value: Any) -> bool:
    return isinstance(value, str) and ADDRESS_RE.fullmatch(value) is not None


def _is_tx(value: Any) -> bool:
    return isinstance(value, str) and TX_RE.fullmatch(value) is not None


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _string_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{key}_must_be_nonempty_string")
        return None
    return value


def _int_field(obj: Mapping[str, Any], key: str, errors: list[str], *, minimum: int) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{key}_must_be_int")
        return None
    if value < minimum:
        errors.append(f"{key}_below_min:{minimum}")
    return int(value)


def _object_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any]:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return {}
    return value


def _check_not_claims(
    obj: Mapping[str, Any],
    *,
    required: set[str],
    label: str,
    errors: list[str],
) -> None:
    raw = obj.get("not_claimed")
    if not isinstance(raw, list):
        errors.append(f"{label}_not_claimed_must_be_list")
        return
    values = {item for item in raw if isinstance(item, str)}
    errors.extend(f"missing_{label}_not_claim:{item}" for item in sorted(required - values))


def _receipt(
    *,
    kind: str,
    chain_id: str,
    contract_address: str,
    tx_hash: str,
    block_number: int,
    block_hash: str,
    log_index: int,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "kind": kind,
        "chain_id": chain_id,
        "contract_address": contract_address,
        "tx_hash": tx_hash,
        "block_number": int(block_number),
        "block_hash": block_hash,
        "log_index": int(log_index),
        "payload": dict(payload),
    }
    receipt["receipt_id"] = receipt_content_hash(receipt)
    return receipt


def sample_policy() -> dict[str, Any]:
    policy: dict[str, Any] = {
        "schema": POLICY_SCHEMA,
        "policy_name": "zenodex-cross-domain-finality-mainnet-candidate-v1",
        "source_chain_id": "zenodex.source-l2-a",
        "target_chain_id": "zenodex.mainnet-candidate-1",
        "adapter_id": "zenodex-finality-adapter-v1",
        "adapter_contract": "0x" + "41" * 20,
        "min_confirmations": 64,
        "max_reorg_depth": 2,
        "finality_mode": "checkpointed-replay",
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def sample_read(policy: Mapping[str, Any] | None = None) -> dict[str, Any]:
    policy = sample_policy() if policy is None else policy
    read: dict[str, Any] = {
        "schema": READ_SCHEMA,
        "policy_id": policy.get("policy_id"),
        "query_id": "oracle:eth-usdc:median3:v1",
        "value_hash": _sha("zenodex.oracle.read.value.eth-usdc.100000000"),
        "source_chain_id": policy.get("source_chain_id"),
        "target_chain_id": policy.get("target_chain_id"),
        "observed_source_block_number": 2_000_000,
        "observed_source_block_hash": _sha("zenodex.source-l2-a.block.2000000"),
        "aggregate_root": _sha("zenodex.oracle.aggregate.eth-usdc.2000000"),
        "receipt_graph_root": _sha("zenodex.oracle.receipt-graph.eth-usdc.2000000"),
    }
    read["read_id"] = read_content_hash(read)
    return read


def sample_receipt_bundle(
    policy: Mapping[str, Any] | None = None,
    read: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    policy = sample_policy() if policy is None else policy
    read = sample_read(policy) if read is None else read
    observed_block = int(read["observed_source_block_number"])
    min_confirmations = int(policy["min_confirmations"])
    finality_root = _sha(f"finality:{read['read_id']}:{observed_block + min_confirmations}")
    source_receipt = _receipt(
        kind="source_finality_checkpoint",
        chain_id=str(policy["source_chain_id"]),
        contract_address="0x" + "42" * 20,
        tx_hash=_tx("source-finality-checkpoint"),
        block_number=observed_block + min_confirmations,
        block_hash=_sha("zenodex.source-l2-a.finality.block"),
        log_index=0,
        payload={
            "policy_id": policy["policy_id"],
            "accepted_read_id": read["read_id"],
            "source_chain_id": policy["source_chain_id"],
            "observed_source_block_number": observed_block,
            "observed_source_block_hash": read["observed_source_block_hash"],
            "finality_mode": policy["finality_mode"],
            "finalized": True,
            "finalized_block_number": observed_block + min_confirmations,
            "confirmation_count": min_confirmations,
            "reorg_depth_observed": 1,
            "finality_root": finality_root,
        },
    )
    target_receipt = _receipt(
        kind="target_adapter_acceptance",
        chain_id=str(policy["target_chain_id"]),
        contract_address=str(policy["adapter_contract"]),
        tx_hash=_tx("target-adapter-acceptance"),
        block_number=3_000_000,
        block_hash=_sha("zenodex.mainnet-candidate-1.adapter.block"),
        log_index=2,
        payload={
            "policy_id": policy["policy_id"],
            "accepted_read_id": read["read_id"],
            "target_chain_id": policy["target_chain_id"],
            "adapter_id": policy["adapter_id"],
            "adapter_contract": policy["adapter_contract"],
            "finality_receipt_id": source_receipt["receipt_id"],
            "query_id": read["query_id"],
            "value_hash": read["value_hash"],
            "finality_root": finality_root,
        },
    )
    return {
        "schema": RECEIPT_BUNDLE_SCHEMA,
        "policy_id": policy["policy_id"],
        "accepted_read_id": read["read_id"],
        "receipts": [source_receipt, target_receipt],
        "not_claimed": sorted(RECEIPT_NOT_CLAIMS),
    }


def _validate_policy(policy: Mapping[str, Any], errors: list[str]) -> None:
    _unknown_fields(policy, allowed=POLICY_KEYS, label="policy", errors=errors)
    if policy.get("schema") != POLICY_SCHEMA:
        errors.append("policy_schema_mismatch")
    if policy.get("policy_id") != policy_content_hash(policy):
        errors.append("policy_id_mismatch")
    for key in ("policy_name", "source_chain_id", "target_chain_id", "adapter_id", "finality_mode"):
        _string_field(policy, key, errors)
    if not _is_address(policy.get("adapter_contract")):
        errors.append("adapter_contract_must_be_address")
    _int_field(policy, "min_confirmations", errors, minimum=1)
    _int_field(policy, "max_reorg_depth", errors, minimum=0)
    _check_not_claims(policy, required=REQUIRED_NOT_CLAIMS, label="policy", errors=errors)


def _validate_read(policy: Mapping[str, Any], read: Mapping[str, Any], errors: list[str]) -> None:
    _unknown_fields(read, allowed=READ_KEYS, label="read", errors=errors)
    if read.get("schema") != READ_SCHEMA:
        errors.append("read_schema_mismatch")
    if read.get("read_id") != read_content_hash(read):
        errors.append("read_id_mismatch")
    if read.get("policy_id") != policy.get("policy_id"):
        errors.append("read_policy_id_mismatch")
    for key in ("query_id", "source_chain_id", "target_chain_id"):
        _string_field(read, key, errors)
    if read.get("source_chain_id") != policy.get("source_chain_id"):
        errors.append("read_source_chain_id_mismatch")
    if read.get("target_chain_id") != policy.get("target_chain_id"):
        errors.append("read_target_chain_id_mismatch")
    _int_field(read, "observed_source_block_number", errors, minimum=0)
    for key in ("value_hash", "observed_source_block_hash", "aggregate_root", "receipt_graph_root"):
        if not _is_sha(read.get(key)):
            errors.append(f"{key}_must_be_sha256")


def _validate_receipt_shape(receipt: Mapping[str, Any], *, index: int, errors: list[str]) -> Mapping[str, Any]:
    _unknown_fields(receipt, allowed=RECEIPT_KEYS, label=f"receipt_{index}", errors=errors)
    if receipt.get("schema") != RECEIPT_SCHEMA:
        errors.append(f"receipt_{index}_schema_mismatch")
    if receipt.get("receipt_id") != receipt_content_hash(receipt):
        errors.append(f"receipt_{index}_id_mismatch")
    kind = receipt.get("kind")
    if kind not in REQUIRED_RECEIPT_KINDS:
        errors.append(f"receipt_{index}_kind_unknown:{kind}")
    if not isinstance(receipt.get("chain_id"), str) or not receipt.get("chain_id"):
        errors.append(f"receipt_{index}_chain_id_invalid")
    if not _is_address(receipt.get("contract_address")):
        errors.append(f"receipt_{index}_contract_address_must_be_address")
    if not _is_tx(receipt.get("tx_hash")):
        errors.append(f"receipt_{index}_tx_hash_invalid")
    _int_field(receipt, "block_number", errors, minimum=0)
    _int_field(receipt, "log_index", errors, minimum=0)
    if not _is_sha(receipt.get("block_hash")):
        errors.append(f"receipt_{index}_block_hash_must_be_sha256")
    return _object_field(receipt, "payload", errors)


def _validate_source_payload(
    policy: Mapping[str, Any],
    read: Mapping[str, Any],
    payload: Mapping[str, Any],
    errors: list[str],
) -> None:
    _unknown_fields(payload, allowed=SOURCE_PAYLOAD_KEYS, label="source_payload", errors=errors)
    if payload.get("policy_id") != policy.get("policy_id"):
        errors.append("source_payload_policy_id_mismatch")
    if payload.get("accepted_read_id") != read.get("read_id"):
        errors.append("source_payload_read_id_mismatch")
    if payload.get("source_chain_id") != policy.get("source_chain_id"):
        errors.append("source_payload_chain_id_mismatch")
    if payload.get("observed_source_block_number") != read.get("observed_source_block_number"):
        errors.append("source_payload_observed_block_number_mismatch")
    if payload.get("observed_source_block_hash") != read.get("observed_source_block_hash"):
        errors.append("source_payload_observed_block_hash_mismatch")
    if payload.get("finality_mode") != policy.get("finality_mode"):
        errors.append("source_payload_finality_mode_mismatch")
    if payload.get("finalized") is not True:
        errors.append("source_payload_not_finalized")
    finalized_block = _int_field(payload, "finalized_block_number", errors, minimum=0)
    confirmation_count = _int_field(payload, "confirmation_count", errors, minimum=0)
    reorg_depth = _int_field(payload, "reorg_depth_observed", errors, minimum=0)
    observed_block = read.get("observed_source_block_number")
    min_confirmations = policy.get("min_confirmations")
    max_reorg_depth = policy.get("max_reorg_depth")
    if isinstance(confirmation_count, int) and isinstance(min_confirmations, int):
        if confirmation_count < min_confirmations:
            errors.append("source_payload_confirmation_count_below_policy")
    if isinstance(finalized_block, int) and isinstance(observed_block, int) and isinstance(min_confirmations, int):
        if finalized_block < observed_block + min_confirmations:
            errors.append("source_payload_finalized_block_before_confirmation_floor")
    if isinstance(reorg_depth, int) and isinstance(max_reorg_depth, int):
        if reorg_depth > max_reorg_depth:
            errors.append("source_payload_reorg_depth_above_policy")
    if not _is_sha(payload.get("finality_root")):
        errors.append("source_payload_finality_root_must_be_sha256")


def _validate_target_payload(
    policy: Mapping[str, Any],
    read: Mapping[str, Any],
    payload: Mapping[str, Any],
    *,
    source_receipt_id: str | None,
    source_finality_root: str | None,
    errors: list[str],
) -> None:
    _unknown_fields(payload, allowed=TARGET_PAYLOAD_KEYS, label="target_payload", errors=errors)
    if payload.get("policy_id") != policy.get("policy_id"):
        errors.append("target_payload_policy_id_mismatch")
    if payload.get("accepted_read_id") != read.get("read_id"):
        errors.append("target_payload_read_id_mismatch")
    if payload.get("target_chain_id") != policy.get("target_chain_id"):
        errors.append("target_payload_chain_id_mismatch")
    if payload.get("adapter_id") != policy.get("adapter_id"):
        errors.append("target_payload_adapter_id_mismatch")
    if payload.get("adapter_contract") != policy.get("adapter_contract"):
        errors.append("target_payload_adapter_contract_mismatch")
    if payload.get("finality_receipt_id") != source_receipt_id:
        errors.append("target_payload_finality_receipt_id_mismatch")
    if payload.get("query_id") != read.get("query_id"):
        errors.append("target_payload_query_id_mismatch")
    if payload.get("value_hash") != read.get("value_hash"):
        errors.append("target_payload_value_hash_mismatch")
    if payload.get("finality_root") != source_finality_root:
        errors.append("target_payload_finality_root_mismatch")


def check_finality_gate(
    policy: Mapping[str, Any],
    read: Mapping[str, Any],
    receipt_bundle: Mapping[str, Any] | None,
    *,
    require_live: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    _validate_policy(policy, errors)
    _validate_read(policy, read, errors)

    receipts_by_kind: dict[str, Mapping[str, Any]] = {}
    source_payload: Mapping[str, Any] = {}
    if receipt_bundle is None:
        errors.append("receipt_bundle_required")
        receipt_bundle_status = "missing"
    else:
        receipt_bundle_status = "accepted"
        _unknown_fields(receipt_bundle, allowed=BUNDLE_KEYS, label="receipt_bundle", errors=errors)
        if receipt_bundle.get("schema") != RECEIPT_BUNDLE_SCHEMA:
            errors.append("receipt_bundle_schema_mismatch")
        if receipt_bundle.get("policy_id") != policy.get("policy_id"):
            errors.append("receipt_bundle_policy_id_mismatch")
        if receipt_bundle.get("accepted_read_id") != read.get("read_id"):
            errors.append("receipt_bundle_read_id_mismatch")
        _check_not_claims(receipt_bundle, required=RECEIPT_NOT_CLAIMS, label="receipt_bundle", errors=errors)
        receipts = receipt_bundle.get("receipts")
        if not isinstance(receipts, list):
            errors.append("receipts_must_be_list")
            receipts = []
        for index, receipt in enumerate(receipts):
            if not isinstance(receipt, Mapping):
                errors.append(f"receipt_{index}_must_be_object")
                continue
            payload = _validate_receipt_shape(receipt, index=index, errors=errors)
            kind = receipt.get("kind")
            if isinstance(kind, str) and kind in receipts_by_kind:
                errors.append(f"duplicate_receipt_kind:{kind}")
            if isinstance(kind, str):
                receipts_by_kind[kind] = receipt
            if kind == "source_finality_checkpoint":
                if receipt.get("chain_id") != policy.get("source_chain_id"):
                    errors.append("source_receipt_chain_id_mismatch")
                _validate_source_payload(policy, read, payload, errors)
                receipt_block = receipt.get("block_number")
                finalized_block = payload.get("finalized_block_number")
                if (
                    isinstance(receipt_block, int)
                    and not isinstance(receipt_block, bool)
                    and isinstance(finalized_block, int)
                    and not isinstance(finalized_block, bool)
                    and receipt_block < finalized_block
                ):
                    errors.append("source_receipt_block_before_finalized_block")
                source_payload = payload
            elif kind == "target_adapter_acceptance":
                if receipt.get("chain_id") != policy.get("target_chain_id"):
                    errors.append("target_receipt_chain_id_mismatch")
                if receipt.get("contract_address") != policy.get("adapter_contract"):
                    errors.append("target_receipt_contract_mismatch")

        missing = sorted(REQUIRED_RECEIPT_KINDS - set(receipts_by_kind))
        errors.extend(f"missing_receipt_kind:{kind}" for kind in missing)
        source_receipt = receipts_by_kind.get("source_finality_checkpoint")
        source_receipt_id = source_receipt.get("receipt_id") if isinstance(source_receipt, Mapping) else None
        source_finality_root = source_payload.get("finality_root") if isinstance(source_payload, Mapping) else None
        target_receipt = receipts_by_kind.get("target_adapter_acceptance")
        if isinstance(target_receipt, Mapping):
            target_payload = _object_field(target_receipt, "payload", errors)
            _validate_target_payload(
                policy,
                read,
                target_payload,
                source_receipt_id=source_receipt_id if isinstance(source_receipt_id, str) else None,
                source_finality_root=source_finality_root if isinstance(source_finality_root, str) else None,
                errors=errors,
            )

    if require_live:
        errors.extend(GO_LIVE_BLOCKERS)
    if receipt_bundle_status == "accepted" and errors:
        receipt_bundle_status = "rejected"
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "error_count": len(errors),
        "errors": errors,
        "policy_id": policy.get("policy_id"),
        "accepted_read_id": read.get("read_id"),
        "receipt_bundle_status": receipt_bundle_status,
        "receipt_kind_count": len(receipts_by_kind),
        "required_receipt_kinds": sorted(REQUIRED_RECEIPT_KINDS),
        "go_live_blockers": list(GO_LIVE_BLOCKERS),
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must be a JSON object")
    return obj


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, help="cross-domain finality policy JSON")
    parser.add_argument("--read", type=Path, help="accepted read JSON")
    parser.add_argument("--receipts", type=Path, help="cross-domain finality receipt bundle JSON")
    parser.add_argument("--sample-policy", action="store_true", help="emit the built-in sample policy")
    parser.add_argument("--sample-read", action="store_true", help="emit the built-in sample accepted read")
    parser.add_argument("--sample-receipts", action="store_true", help="emit the built-in sample receipt bundle")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail while live finality blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    policy = _load_json(args.policy) if args.policy else sample_policy()
    read = _load_json(args.read) if args.read else sample_read(policy)
    if args.sample_policy:
        print(json.dumps(policy, indent=2, sort_keys=True))
        return 0
    if args.sample_read:
        print(json.dumps(read, indent=2, sort_keys=True))
        return 0
    if args.sample_receipts:
        print(json.dumps(sample_receipt_bundle(policy, read), indent=2, sort_keys=True))
        return 0
    using_default_samples = args.policy is None and args.read is None and args.receipts is None
    receipt_bundle = sample_receipt_bundle(policy, read) if using_default_samples else None
    if args.receipts is not None:
        receipt_bundle = _load_json(args.receipts)
    result = check_finality_gate(policy, read, receipt_bundle, require_live=args.require_live)
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"receipt_bundle_status = {result['receipt_bundle_status']}")
        print(f"receipt_kind_count = {result['receipt_kind_count']}")
        print(f"error_count = {result['error_count']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
