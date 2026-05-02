#!/usr/bin/env python3
"""Zeno Oracle public verifier shell.

This is a narrow local verifier for the first public Oracle receipt-bundle
shape. It does not contact a network and does not claim source honesty or true
market price. It checks whether a bundle is structurally safe enough to be
treated as an accepted critical-read receipt bundle by downstream tooling.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


BUNDLE_SCHEMA = "zenodex.oracle.receipt_bundle.v1"
RESULT_SCHEMA = "zenodex.oracle.verify_result.v1"
READ_TYPE = "accepted_read_receipt"
ACTION_TYPE = "consumer_action_receipt"
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}
NOT_CLAIMED = [
    "does_not_claim_true_market_price",
    "does_not_claim_source_honesty",
    "does_not_claim_production_network_live",
]


@dataclass(frozen=True)
class VerifyResult:
    status: str
    errors: list[str]
    query_id: str | None = None
    read_receipt_id: str | None = None
    consumer_action_receipt_id: str | None = None
    evidence_class: str | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "query_id": self.query_id,
            "read_receipt_id": self.read_receipt_id,
            "consumer_action_receipt_id": self.consumer_action_receipt_id,
            "evidence_class": self.evidence_class,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _get_mapping(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any] | None:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return None
    return value


def _get_bool(obj: Mapping[str, Any], key: str, errors: list[str]) -> bool:
    value = obj.get(key)
    if not isinstance(value, bool):
        errors.append(f"{key}_must_be_bool")
        return False
    return value


def _get_hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _receipt_index(receipts_raw: object, errors: list[str]) -> dict[str, Mapping[str, Any]]:
    if not isinstance(receipts_raw, list):
        errors.append("receipts_must_be_list")
        return {}

    index: dict[str, Mapping[str, Any]] = {}
    for pos, receipt in enumerate(receipts_raw):
        if not isinstance(receipt, Mapping):
            errors.append(f"receipt_{pos}_must_be_object")
            continue
        receipt_id = receipt.get("id")
        if not _is_hash(receipt_id):
            errors.append(f"receipt_{pos}_id_must_be_sha256")
            continue
        receipt_id = str(receipt_id)
        if receipt_id in index:
            errors.append(f"duplicate_receipt_id:{receipt_id}")
            continue
        index[receipt_id] = receipt
    return index


def _dependencies_ok(index: Mapping[str, Mapping[str, Any]], errors: list[str]) -> None:
    for receipt_id, receipt in index.items():
        deps = receipt.get("depends_on", [])
        if deps is None:
            deps = []
        if not isinstance(deps, list):
            errors.append(f"depends_on_must_be_list:{receipt_id}")
            continue
        for dep in deps:
            if not _is_hash(dep):
                errors.append(f"dependency_id_must_be_sha256:{receipt_id}")
            elif dep not in index:
                errors.append(f"missing_dependency:{receipt_id}->{dep}")


def _read_receipt_ok(read: Mapping[str, Any], errors: list[str]) -> tuple[str | None, str | None, str | None]:
    if read.get("type") != READ_TYPE:
        errors.append("read_receipt_type_mismatch")
    if read.get("status") != "accepted":
        errors.append("read_receipt_not_accepted")

    query_id = _get_hash(read, "query_id", errors)
    value_hash = _get_hash(read, "value_hash", errors)
    evidence_class_raw = read.get("evidence_class")
    evidence_class = evidence_class_raw if isinstance(evidence_class_raw, str) else None
    if evidence_class not in EVIDENCE_RANK:
        errors.append("evidence_class_invalid")
    elif EVIDENCE_RANK[evidence_class] < EVIDENCE_RANK["O3"]:
        errors.append("critical_read_requires_o3_or_higher")

    for key in ("fresh", "dispute_clear", "uncertainty_accepted"):
        if not _get_bool(read, key, errors):
            errors.append(f"read_{key}_required")

    return query_id, value_hash, evidence_class


def _action_receipt_ok(
    *,
    action: Mapping[str, Any],
    read_id: str,
    read_query_id: str | None,
    read_value_hash: str | None,
    errors: list[str],
) -> str | None:
    if action.get("type") != ACTION_TYPE:
        errors.append("consumer_action_type_mismatch")
    if action.get("status") != "accepted":
        errors.append("consumer_action_not_accepted")

    action_query_id = _get_hash(action, "query_id", errors)
    action_value_hash = _get_hash(action, "value_hash", errors)
    action_read_id = _get_hash(action, "read_receipt_id", errors)
    if action_read_id is not None and action_read_id != read_id:
        errors.append("consumer_action_read_id_mismatch")
    if read_query_id is not None and action_query_id is not None and action_query_id != read_query_id:
        errors.append("consumer_action_query_id_mismatch")
    if read_value_hash is not None and action_value_hash is not None and action_value_hash != read_value_hash:
        errors.append("consumer_action_value_hash_mismatch")

    if not _get_bool(action, "critical", errors):
        errors.append("consumer_action_must_be_critical")
    if _get_bool(action, "emergency_oracle_bypass", errors):
        errors.append("emergency_oracle_bypass_rejected")

    deps = action.get("depends_on", [])
    if isinstance(deps, list) and read_id not in deps:
        errors.append("consumer_action_must_depend_on_read_receipt")
    return action_query_id


def verify_bundle(bundle: Mapping[str, Any]) -> VerifyResult:
    errors: list[str] = []
    if bundle.get("schema") != BUNDLE_SCHEMA:
        errors.append("bundle_schema_mismatch")

    terminal = _get_mapping(bundle, "terminal", errors)
    read_id = _get_hash(terminal or {}, "read_receipt_id", errors)
    action_id = _get_hash(terminal or {}, "consumer_action_receipt_id", errors)
    index = _receipt_index(bundle.get("receipts"), errors)
    _dependencies_ok(index, errors)

    read = index.get(read_id) if read_id is not None else None
    action = index.get(action_id) if action_id is not None else None
    if read is None:
        errors.append("terminal_read_receipt_missing")
    if action is None:
        errors.append("terminal_consumer_action_receipt_missing")

    query_id: str | None = None
    evidence_class: str | None = None
    value_hash: str | None = None
    if read is not None:
        query_id, value_hash, evidence_class = _read_receipt_ok(read, errors)
    if action is not None and read_id is not None:
        action_query_id = _action_receipt_ok(
            action=action,
            read_id=read_id,
            read_query_id=query_id,
            read_value_hash=value_hash,
            errors=errors,
        )
        query_id = query_id or action_query_id

    return VerifyResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        query_id=query_id,
        read_receipt_id=read_id,
        consumer_action_receipt_id=action_id,
        evidence_class=evidence_class,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("bundle root must be a JSON object")
    return obj


def _write_result(result: VerifyResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        bundle = _load_json(Path(args.bundle))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = VerifyResult(status="inconclusive", errors=[f"bundle_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_bundle(bundle)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify a local Oracle receipt bundle")
    verify.add_argument("bundle", help="path to a receipt bundle JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
