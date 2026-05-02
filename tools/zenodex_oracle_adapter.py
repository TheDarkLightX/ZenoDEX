#!/usr/bin/env python3
"""Verify a downstream ZenoDEX action against an Oracle receipt bundle."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle import EVIDENCE_RANK, sample_bundle, verify_bundle  # noqa: E402


ACTION_SCHEMA = "zenodex.oracle.consumer_action_binding.v1"
RESULT_SCHEMA = "zenodex.oracle.adapter_verify_result.v1"
MAX_ACTION_BYTES = 250_000
MAX_BUNDLE_BYTES = 1_000_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
ACTION_KEYS = {
    "schema",
    "consumer_module",
    "action_kind",
    "action_id",
    "action_epoch",
    "query_id",
    "value_hash",
    "required_evidence_floor",
    "max_freshness_window_epochs",
    "read_receipt_id",
    "consumer_action_receipt_id",
    "critical",
}
NOT_CLAIMED = [
    "does_not_claim_true_market_price",
    "does_not_claim_reporter_honesty",
    "does_not_claim_production_oracle_network_live",
    "does_not_claim_downstream_module_integrated",
]


@dataclass(frozen=True)
class AdapterVerifyResult:
    status: str
    errors: list[str]
    consumer_module: str | None = None
    action_kind: str | None = None
    action_id: str | None = None
    query_id: str | None = None
    value_hash: str | None = None
    evidence_class: str | None = None
    required_evidence_floor: str | None = None
    action_epoch: int | None = None
    freshness_window_epochs: int | None = None
    max_freshness_window_epochs: int | None = None
    read_receipt_id: str | None = None
    consumer_action_receipt_id: str | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "consumer_module": self.consumer_module,
            "action_kind": self.action_kind,
            "action_id": self.action_id,
            "query_id": self.query_id,
            "value_hash": self.value_hash,
            "evidence_class": self.evidence_class,
            "required_evidence_floor": self.required_evidence_floor,
            "action_epoch": self.action_epoch,
            "freshness_window_epochs": self.freshness_window_epochs,
            "max_freshness_window_epochs": self.max_freshness_window_epochs,
            "read_receipt_id": self.read_receipt_id,
            "consumer_action_receipt_id": self.consumer_action_receipt_id,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_action_and_bundle() -> tuple[dict[str, Any], dict[str, Any]]:
    bundle = sample_bundle()
    result = verify_bundle(bundle)
    if result.status != "accepted":  # pragma: no cover - protects the sample helper contract
        raise RuntimeError("sample bundle did not verify")
    action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": result.consumer_module,
        "action_kind": result.action_kind,
        "action_id": result.action_id,
        "action_epoch": result.action_epoch,
        "query_id": result.query_id,
        "value_hash": result.value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": result.freshness_window_epochs,
        "read_receipt_id": result.read_receipt_id,
        "consumer_action_receipt_id": result.consumer_action_receipt_id,
        "critical": True,
    }
    return action, bundle


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _unknown_fields(
    obj: Mapping[str, Any],
    *,
    allowed: set[str],
    label: str,
    errors: list[str],
) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _int_ge_zero(obj: Mapping[str, Any], key: str, errors: list[str]) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        errors.append(f"{key}_must_be_int_ge_0")
        return None
    return int(value)


def _evidence_floor(obj: Mapping[str, Any], errors: list[str]) -> str | None:
    value = obj.get("required_evidence_floor")
    if not isinstance(value, str) or value not in EVIDENCE_RANK:
        errors.append("required_evidence_floor_invalid")
        return None
    if EVIDENCE_RANK[value] < EVIDENCE_RANK["O3"]:
        errors.append("required_evidence_floor_below_critical_minimum")
    return value


def _load_json(path: Path, *, max_bytes: int, label: str) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > max_bytes:
        raise ValueError(f"{label}_file_too_large:{size}>{max_bytes}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError(f"{label} root must be a JSON object")
    return obj


def verify_oracle_use(action: Mapping[str, Any], bundle: Mapping[str, Any]) -> AdapterVerifyResult:
    errors: list[str] = []
    _unknown_fields(action, allowed=ACTION_KEYS, label="action", errors=errors)
    if action.get("schema") != ACTION_SCHEMA:
        errors.append("action_schema_mismatch")

    consumer_module = _token(action, "consumer_module", errors)
    action_kind = _token(action, "action_kind", errors)
    action_id = _hash(action, "action_id", errors)
    action_epoch = _int_ge_zero(action, "action_epoch", errors)
    query_id = _hash(action, "query_id", errors)
    value_hash = _hash(action, "value_hash", errors)
    required_evidence_floor = _evidence_floor(action, errors)
    max_freshness_window_epochs = _int_ge_zero(action, "max_freshness_window_epochs", errors)
    read_receipt_id = _hash(action, "read_receipt_id", errors)
    consumer_action_receipt_id = _hash(action, "consumer_action_receipt_id", errors)
    if action.get("critical") is not True:
        errors.append("action_must_be_critical")

    bundle_result = verify_bundle(bundle)
    if bundle_result.status != "accepted":
        errors.append("oracle_bundle_not_accepted")
        errors.extend(f"bundle:{error}" for error in bundle_result.errors)
    else:
        if consumer_module is not None and bundle_result.consumer_module != consumer_module:
            errors.append("adapter_consumer_module_mismatch")
        if action_kind is not None and bundle_result.action_kind != action_kind:
            errors.append("adapter_action_kind_mismatch")
        if action_id is not None and bundle_result.action_id != action_id:
            errors.append("adapter_action_id_mismatch")
        if action_epoch is not None and bundle_result.action_epoch != action_epoch:
            errors.append("adapter_action_epoch_mismatch")
        if query_id is not None and bundle_result.query_id != query_id:
            errors.append("adapter_query_id_mismatch")
        if value_hash is not None and bundle_result.value_hash != value_hash:
            errors.append("adapter_value_hash_mismatch")
        if read_receipt_id is not None and bundle_result.read_receipt_id != read_receipt_id:
            errors.append("adapter_read_receipt_id_mismatch")
        if (
            consumer_action_receipt_id is not None
            and bundle_result.consumer_action_receipt_id != consumer_action_receipt_id
        ):
            errors.append("adapter_consumer_action_receipt_id_mismatch")
        if (
            required_evidence_floor is not None
            and bundle_result.evidence_class is not None
            and EVIDENCE_RANK[bundle_result.evidence_class] < EVIDENCE_RANK[required_evidence_floor]
        ):
            errors.append("adapter_evidence_below_required_floor")
        if (
            max_freshness_window_epochs is not None
            and bundle_result.freshness_window_epochs is not None
            and bundle_result.freshness_window_epochs > max_freshness_window_epochs
        ):
            errors.append("adapter_freshness_window_exceeds_action_limit")

    return AdapterVerifyResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        consumer_module=consumer_module,
        action_kind=action_kind,
        action_id=action_id,
        query_id=query_id,
        value_hash=value_hash,
        evidence_class=bundle_result.evidence_class,
        required_evidence_floor=required_evidence_floor,
        action_epoch=action_epoch,
        freshness_window_epochs=bundle_result.freshness_window_epochs,
        max_freshness_window_epochs=max_freshness_window_epochs,
        read_receipt_id=read_receipt_id,
        consumer_action_receipt_id=consumer_action_receipt_id,
    )


def _write_result(result: AdapterVerifyResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        action = _load_json(Path(args.action), max_bytes=MAX_ACTION_BYTES, label="action")
        bundle = _load_json(Path(args.bundle), max_bytes=MAX_BUNDLE_BYTES, label="bundle")
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = AdapterVerifyResult(status="inconclusive", errors=[f"adapter_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_oracle_use(action, bundle)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    action, bundle = sample_action_and_bundle()
    if args.action_output:
        Path(args.action_output).write_text(
            json.dumps(action, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.bundle_output:
        Path(args.bundle_output).write_text(
            json.dumps(bundle, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if not args.action_output and not args.bundle_output:
        sys.stdout.write(
            json.dumps({"action": action, "bundle": bundle}, indent=2, sort_keys=True) + "\n"
        )
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify a downstream action against an Oracle bundle")
    verify.add_argument("--action", required=True, help="path to a consumer action binding JSON file")
    verify.add_argument("--bundle", required=True, help="path to an Oracle receipt bundle JSON file")
    verify.add_argument("--output", help="optional output path for the adapter result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted action and receipt bundle")
    sample.add_argument("--action-output", help="optional output path for the sample action JSON")
    sample.add_argument("--bundle-output", help="optional output path for the sample bundle JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
