#!/usr/bin/env python3
"""Pre-MVP Zeno Oracle reporter/validator CLI.

This command is intentionally local-only. It gives operators and reporters a
single deterministic entrypoint for identity setup, query inspection, report
dry-runs, and verifier execution while the production Oracle network is still
under development.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import io
import json
import math
import os
import re
import secrets
import stat
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_HOME = Path.home() / ".zenodex" / "oracle"
SCHEMA = "zenodex.oracle.cli.result.v1"
CLI_VERSION = "0.1.0-pre-mvp"
DEFAULT_REQUIRED_BOND_E8 = 100_000_000
DEFAULT_REPORT_REWARD_E8 = 10_000
DEFAULT_DISPUTE_BOND_E8 = 10_000_000
DEFAULT_SLASH_E8 = 100_000_000
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}
BUNDLE_SCHEMA = "zenodex.oracle.receipt_bundle.v1"
RESULT_SCHEMA = "zenodex.oracle.verify_result.v1"
READ_TYPE = "accepted_read_receipt"
ACTION_TYPE = "consumer_action_receipt"
SUPPORTED_RECEIPT_TYPES = {READ_TYPE, ACTION_TYPE}
MAX_BUNDLE_BYTES = 1_000_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,95}$")
BUNDLE_KEYS = {"schema", "terminal", "receipts"}
TERMINAL_KEYS = {"read_receipt_id", "consumer_action_receipt_id"}
READ_RECEIPT_KEYS = {
    "id",
    "type",
    "status",
    "query_id",
    "value_hash",
    "evidence_class",
    "fresh",
    "observed_epoch",
    "expires_at_epoch",
    "dispute_clear",
    "uncertainty_accepted",
    "depends_on",
}
ACTION_RECEIPT_KEYS = {
    "id",
    "type",
    "status",
    "consumer_module",
    "action_kind",
    "action_id",
    "action_epoch",
    "freshness_window_epochs",
    "query_id",
    "value_hash",
    "read_receipt_id",
    "critical",
    "emergency_oracle_bypass",
    "depends_on",
}
RECEIPT_BUNDLE_VERIFY_SUBCOMMANDS = frozenset(
    {"authorization", "evidence", "local-state", "receipt"}
)
NOT_CLAIMED = [
    "does_not_claim_true_market_price",
    "does_not_claim_source_honesty",
    "does_not_claim_production_network_live",
]
ASSET_CLASSES = ("crypto", "stablecoin", "equity", "rwa", "real_estate", "fx", "commodity")
SOURCE_KINDS = (
    "cex",
    "dex",
    "twap",
    "broker",
    "custodian",
    "appraisal",
    "rwa_servicer",
    "manual",
    "other",
)
SOURCE_ASSURANCE_CLASSES = ("S0", "S1", "S2", "S3", "S4", "S5")
AUTHORIZATION_RUNTIME_REQUIRED_KEYS = frozenset(
    {
        "consumer_module",
        "action_kind",
        "action_id",
        "action_facts_hash",
        "pre_state_hash",
        "profile_id",
        "query_id",
        "runtime_value_e8",
        "now_epoch",
    }
)
AUTHORIZATION_RUNTIME_OPTIONAL_KEYS = frozenset(
    {"runtime_notional_value_e8", "max_freshness_window_epochs"}
)


class _DuplicateJsonKeyError(ValueError):
    def __init__(self, key: str) -> None:
        self.key = key
        super().__init__(f"duplicate JSON key: {key}")


class _NonFiniteJsonConstantError(ValueError):
    def __init__(self, value: str) -> None:
        self.value = value
        super().__init__(f"non-finite JSON constant: {value}")


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise _DuplicateJsonKeyError(key)
        value[key] = item
    return value


def _reject_nonfinite_json_constant(value: str) -> None:
    raise _NonFiniteJsonConstantError(value)


def _strict_json_loads(text: str) -> Any:
    return json.loads(
        text,
        object_pairs_hook=_reject_duplicate_json_keys,
        parse_constant=_reject_nonfinite_json_constant,
    )


if getattr(sys, "frozen", False):
    ROOT = Path(getattr(sys, "_MEIPASS", Path(sys.executable).resolve().parent))
sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_signature import (  # noqa: E402
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_oracle_authority import (  # noqa: E402
    build_oracle_authority_exercise_v1,
    build_oracle_authority_profile_v1,
    evaluate_oracle_authority_exercise_v1,
    evaluate_oracle_authority_profile_v1,
)
from src.integration.zeno_oracle_authorization import (  # noqa: E402
    RuntimeActionFacts,
    economic_envelope_hash,
    runtime_from_obj,
)


def _canonical_bytes(payload: Mapping[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
        "utf-8"
    )


def semantic_hash(domain: str, payload: Mapping[str, Any]) -> str:
    digest = hashlib.sha256(domain.encode("utf-8") + b"\x00" + _canonical_bytes(payload)).hexdigest()
    return f"sha256:{digest}"


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def _canonical_json_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(
        obj,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def receipt_content_hash(receipt: Mapping[str, Any]) -> str:
    body = {key: value for key, value in receipt.items() if key != "id"}
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(body)).hexdigest()


def sample_bundle() -> dict[str, Any]:
    query_id = sample_hash("zenodex-oracle-sample-query")
    value_hash = sample_hash("zenodex-oracle-sample-value")
    read = {
        "type": READ_TYPE,
        "status": "accepted",
        "query_id": query_id,
        "value_hash": value_hash,
        "evidence_class": "O3",
        "fresh": True,
        "observed_epoch": 100,
        "expires_at_epoch": 104,
        "dispute_clear": True,
        "uncertainty_accepted": True,
        "depends_on": [],
    }
    read_id = receipt_content_hash(read)
    read["id"] = read_id
    action = {
        "type": ACTION_TYPE,
        "status": "accepted",
        "consumer_module": "zenodex.oracle.sample",
        "action_kind": "sample_critical_read",
        "action_id": sample_hash("zenodex-oracle-sample-downstream-action"),
        "action_epoch": 102,
        "freshness_window_epochs": 4,
        "query_id": query_id,
        "value_hash": value_hash,
        "read_receipt_id": read_id,
        "critical": True,
        "emergency_oracle_bypass": False,
        "depends_on": [read_id],
    }
    action_id = receipt_content_hash(action)
    action["id"] = action_id
    return {
        "schema": BUNDLE_SCHEMA,
        "terminal": {
            "read_receipt_id": read_id,
            "consumer_action_receipt_id": action_id,
        },
        "receipts": [read, action],
    }


@dataclass(frozen=True)
class VerifyResult:
    status: str
    errors: list[str]
    query_id: str | None = None
    value_hash: str | None = None
    read_receipt_id: str | None = None
    consumer_action_receipt_id: str | None = None
    evidence_class: str | None = None
    consumer_module: str | None = None
    action_kind: str | None = None
    action_id: str | None = None
    observed_epoch: int | None = None
    expires_at_epoch: int | None = None
    action_epoch: int | None = None
    freshness_window_epochs: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "query_id": self.query_id,
            "value_hash": self.value_hash,
            "read_receipt_id": self.read_receipt_id,
            "consumer_action_receipt_id": self.consumer_action_receipt_id,
            "evidence_class": self.evidence_class,
            "consumer_module": self.consumer_module,
            "action_kind": self.action_kind,
            "action_id": self.action_id,
            "observed_epoch": self.observed_epoch,
            "expires_at_epoch": self.expires_at_epoch,
            "action_epoch": self.action_epoch,
            "freshness_window_epochs": self.freshness_window_epochs,
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


def _get_token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _get_int_ge(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int = 0,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
        errors.append(f"{key}_must_be_int_ge_{minimum}")
        return None
    return int(value)


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


def _receipt_positions(receipts_raw: object) -> dict[str, int]:
    if not isinstance(receipts_raw, list):
        return {}

    positions: dict[str, int] = {}
    for pos, receipt in enumerate(receipts_raw):
        if not isinstance(receipt, Mapping):
            continue
        receipt_id = receipt.get("id")
        if _is_hash(receipt_id) and str(receipt_id) not in positions:
            positions[str(receipt_id)] = int(pos)
    return positions


def _receipt_types_ok(index: Mapping[str, Mapping[str, Any]], errors: list[str]) -> None:
    for receipt_id, receipt in index.items():
        if receipt.get("type") not in SUPPORTED_RECEIPT_TYPES:
            errors.append(f"unsupported_receipt_type:{receipt_id}")


def _receipt_content_hashes_ok(index: Mapping[str, Mapping[str, Any]], errors: list[str]) -> None:
    for receipt_id, receipt in index.items():
        try:
            expected = receipt_content_hash(receipt)
        except (TypeError, ValueError):
            errors.append(f"receipt_content_hash_unencodable:{receipt_id}")
            continue
        if receipt_id != expected:
            errors.append(f"receipt_content_hash_mismatch:{receipt_id}")


def _receipt_shapes_ok(index: Mapping[str, Mapping[str, Any]], errors: list[str]) -> None:
    for receipt in index.values():
        receipt_type = receipt.get("type")
        if receipt_type == READ_TYPE:
            _unknown_fields(
                receipt,
                allowed=READ_RECEIPT_KEYS,
                label="read_receipt",
                errors=errors,
            )
        elif receipt_type == ACTION_TYPE:
            _unknown_fields(
                receipt,
                allowed=ACTION_RECEIPT_KEYS,
                label="consumer_action_receipt",
                errors=errors,
            )


def _dependencies_ok(index: Mapping[str, Mapping[str, Any]], errors: list[str]) -> None:
    for receipt_id, receipt in index.items():
        deps = receipt.get("depends_on", [])
        if deps is None:
            deps = []
        if not isinstance(deps, list):
            errors.append(f"depends_on_must_be_list:{receipt_id}")
            continue
        seen_deps: set[str] = set()
        for dep in deps:
            if not _is_hash(dep):
                errors.append(f"dependency_id_must_be_sha256:{receipt_id}")
            elif dep not in index:
                errors.append(f"missing_dependency:{receipt_id}->{dep}")
            elif dep == receipt_id:
                errors.append(f"dependency_self_reference:{receipt_id}")
            elif dep in seen_deps:
                errors.append(f"duplicate_dependency:{receipt_id}->{dep}")
            if isinstance(dep, str):
                seen_deps.add(dep)


def _dependency_order_ok(
    index: Mapping[str, Mapping[str, Any]],
    positions: Mapping[str, int],
    errors: list[str],
) -> None:
    for receipt_id, receipt in index.items():
        deps = receipt.get("depends_on", [])
        if not isinstance(deps, list):
            continue
        receipt_pos = positions.get(receipt_id)
        if receipt_pos is None:
            continue
        for dep in deps:
            if isinstance(dep, str) and dep in positions and positions[dep] > receipt_pos:
                errors.append(f"dependency_order_violation:{receipt_id}->{dep}")


def _dependency_closure(
    index: Mapping[str, Mapping[str, Any]],
    terminal_ids: list[str],
) -> set[str]:
    reachable: set[str] = set()
    stack = [receipt_id for receipt_id in terminal_ids if receipt_id in index]
    while stack:
        receipt_id = stack.pop()
        if receipt_id in reachable:
            continue
        reachable.add(receipt_id)
        deps = index[receipt_id].get("depends_on", [])
        if not isinstance(deps, list):
            continue
        for dep in deps:
            if isinstance(dep, str) and dep in index and dep not in reachable:
                stack.append(dep)
    return reachable


def _no_unreachable_receipts(
    index: Mapping[str, Mapping[str, Any]],
    terminal_ids: list[str],
    errors: list[str],
) -> None:
    reachable = _dependency_closure(index, terminal_ids)
    for receipt_id in sorted(index):
        if receipt_id not in reachable:
            errors.append(f"unreachable_receipt:{receipt_id}")


def _read_receipt_ok(
    read: Mapping[str, Any],
    errors: list[str],
) -> tuple[str | None, str | None, str | None, int | None, int | None]:
    if read.get("type") != READ_TYPE:
        errors.append("read_receipt_type_mismatch")
    if read.get("status") != "accepted":
        errors.append("read_receipt_not_accepted")

    query_id = _get_hash(read, "query_id", errors)
    value_hash = _get_hash(read, "value_hash", errors)
    observed_epoch = _get_int_ge(read, "observed_epoch", errors)
    expires_at_epoch = _get_int_ge(read, "expires_at_epoch", errors)
    if (
        observed_epoch is not None
        and expires_at_epoch is not None
        and expires_at_epoch < observed_epoch
    ):
        errors.append("read_expires_before_observed")
    evidence_class_raw = read.get("evidence_class")
    evidence_class = evidence_class_raw if isinstance(evidence_class_raw, str) else None
    if evidence_class not in EVIDENCE_RANK:
        errors.append("evidence_class_invalid")
    elif EVIDENCE_RANK[evidence_class] < EVIDENCE_RANK["O3"]:
        errors.append("critical_read_requires_o3_or_higher")

    for key in ("fresh", "dispute_clear", "uncertainty_accepted"):
        if not _get_bool(read, key, errors):
            errors.append(f"read_{key}_required")

    deps = read.get("depends_on", [])
    if isinstance(deps, list) and deps:
        errors.append("read_receipt_must_have_no_dependencies")

    return query_id, value_hash, evidence_class, observed_epoch, expires_at_epoch


def _action_receipt_ok(
    *,
    action: Mapping[str, Any],
    read_id: str,
    read_query_id: str | None,
    read_value_hash: str | None,
    read_observed_epoch: int | None,
    read_expires_at_epoch: int | None,
    errors: list[str],
) -> tuple[str | None, str | None, str | None, str | None, int | None, int | None]:
    if action.get("type") != ACTION_TYPE:
        errors.append("consumer_action_type_mismatch")
    if action.get("status") != "accepted":
        errors.append("consumer_action_not_accepted")

    consumer_module = _get_token(action, "consumer_module", errors)
    action_kind = _get_token(action, "action_kind", errors)
    downstream_action_id = _get_hash(action, "action_id", errors)
    action_epoch = _get_int_ge(action, "action_epoch", errors)
    freshness_window_epochs = _get_int_ge(action, "freshness_window_epochs", errors)
    action_query_id = _get_hash(action, "query_id", errors)
    action_value_hash = _get_hash(action, "value_hash", errors)
    action_read_id = _get_hash(action, "read_receipt_id", errors)
    if action_read_id is not None and action_read_id != read_id:
        errors.append("consumer_action_read_id_mismatch")
    if read_query_id is not None and action_query_id is not None and action_query_id != read_query_id:
        errors.append("consumer_action_query_id_mismatch")
    if read_value_hash is not None and action_value_hash is not None and action_value_hash != read_value_hash:
        errors.append("consumer_action_value_hash_mismatch")
    if (
        action_epoch is not None
        and read_observed_epoch is not None
        and action_epoch < read_observed_epoch
    ):
        errors.append("consumer_action_before_read_observation")
    if (
        action_epoch is not None
        and read_expires_at_epoch is not None
        and action_epoch > read_expires_at_epoch
    ):
        errors.append("consumer_action_after_read_expiry")
    if (
        action_epoch is not None
        and read_observed_epoch is not None
        and freshness_window_epochs is not None
        and action_epoch - read_observed_epoch > freshness_window_epochs
    ):
        errors.append("consumer_action_exceeds_freshness_window")

    if not _get_bool(action, "critical", errors):
        errors.append("consumer_action_must_be_critical")
    if _get_bool(action, "emergency_oracle_bypass", errors):
        errors.append("emergency_oracle_bypass_rejected")

    deps = action.get("depends_on", [])
    if isinstance(deps, list) and read_id not in deps:
        errors.append("consumer_action_must_depend_on_read_receipt")
    if isinstance(deps, list) and deps != [read_id]:
        errors.append("consumer_action_dependency_must_equal_read_receipt")
    return (
        action_query_id,
        consumer_module,
        action_kind,
        downstream_action_id,
        action_epoch,
        freshness_window_epochs,
    )


def verify_bundle(bundle: Mapping[str, Any]) -> VerifyResult:
    errors: list[str] = []
    _unknown_fields(bundle, allowed=BUNDLE_KEYS, label="bundle", errors=errors)
    if bundle.get("schema") != BUNDLE_SCHEMA:
        errors.append("bundle_schema_mismatch")

    terminal = _get_mapping(bundle, "terminal", errors)
    if terminal is not None:
        _unknown_fields(terminal, allowed=TERMINAL_KEYS, label="terminal", errors=errors)
    read_id = _get_hash(terminal or {}, "read_receipt_id", errors)
    action_id = _get_hash(terminal or {}, "consumer_action_receipt_id", errors)
    if read_id is not None and action_id is not None and read_id == action_id:
        errors.append("terminal_receipts_must_be_distinct")
    receipts_raw = bundle.get("receipts")
    index = _receipt_index(receipts_raw, errors)
    positions = _receipt_positions(receipts_raw)
    _receipt_content_hashes_ok(index, errors)
    _receipt_shapes_ok(index, errors)
    _receipt_types_ok(index, errors)
    _dependencies_ok(index, errors)
    _dependency_order_ok(index, positions, errors)
    terminal_ids = [receipt_id for receipt_id in (read_id, action_id) if receipt_id is not None]
    _no_unreachable_receipts(index, terminal_ids, errors)

    read = index.get(read_id) if read_id is not None else None
    action = index.get(action_id) if action_id is not None else None
    if read is None:
        errors.append("terminal_read_receipt_missing")
    if action is None:
        errors.append("terminal_consumer_action_receipt_missing")

    query_id: str | None = None
    evidence_class: str | None = None
    value_hash: str | None = None
    observed_epoch: int | None = None
    expires_at_epoch: int | None = None
    consumer_module: str | None = None
    action_kind: str | None = None
    downstream_action_id: str | None = None
    action_epoch: int | None = None
    freshness_window_epochs: int | None = None
    if read is not None:
        query_id, value_hash, evidence_class, observed_epoch, expires_at_epoch = _read_receipt_ok(
            read, errors
        )
    if action is not None and read_id is not None:
        (
            action_query_id,
            consumer_module,
            action_kind,
            downstream_action_id,
            action_epoch,
            freshness_window_epochs,
        ) = _action_receipt_ok(
            action=action,
            read_id=read_id,
            read_query_id=query_id,
            read_value_hash=value_hash,
            read_observed_epoch=observed_epoch,
            read_expires_at_epoch=expires_at_epoch,
            errors=errors,
        )
        query_id = query_id or action_query_id

    return VerifyResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        query_id=query_id,
        value_hash=value_hash,
        read_receipt_id=read_id,
        consumer_action_receipt_id=action_id,
        evidence_class=evidence_class,
        consumer_module=consumer_module,
        action_kind=action_kind,
        action_id=downstream_action_id,
        observed_epoch=observed_epoch,
        expires_at_epoch=expires_at_epoch,
        action_epoch=action_epoch,
        freshness_window_epochs=freshness_window_epochs,
    )


def _load_receipt_bundle_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_BUNDLE_BYTES:
        raise ValueError(f"bundle_file_too_large:{size}>{MAX_BUNDLE_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = _strict_json_loads(handle.read())
    if type(obj) is not dict:
        raise ValueError("bundle root must be a JSON object")
    return obj


def _write_receipt_bundle_result(result: VerifyResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify_receipt_bundle(args: argparse.Namespace) -> int:
    try:
        bundle = _load_receipt_bundle_json(Path(args.bundle))
    except Exception as exc:
        result = VerifyResult(status="inconclusive", errors=[f"bundle_load_failed:{exc}"])
        _write_receipt_bundle_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_bundle(bundle)
    _write_receipt_bundle_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample_bundle(args: argparse.Namespace) -> int:
    text = json.dumps(sample_bundle(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def _load_json(path: Path) -> Any:
    return _strict_json_loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def _append_jsonl(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True))
        handle.write("\n")


def _emit(payload: Mapping[str, Any], *, json_out: bool) -> None:
    if json_out:
        print(json.dumps(payload, sort_keys=True, indent=2))
        return
    for key, value in payload.items():
        if isinstance(value, (dict, list)):
            print(f"{key}: {json.dumps(value, sort_keys=True)}")
        else:
            print(f"{key}: {value}")


def _git_commit() -> str:
    proc = subprocess.run(
        ["git", "rev-parse", "--short=12", "HEAD"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return proc.stdout.strip() if proc.returncode == 0 else "unknown"


def _asset_manifest() -> dict[str, str]:
    candidates = {
        "zeno_oracle_icon_256": ROOT / "assets/branding/zeno-oracle/zeno_oracle_icon_256.png",
        "zeno_oracle_icon_512": ROOT / "assets/branding/zeno-oracle/zeno_oracle_icon_512.png",
        "zeno_oracle_favicon": ROOT / "assets/branding/zeno-oracle/zeno_oracle_favicon.ico",
    }
    result: dict[str, str] = {}
    for name, path in candidates.items():
        if path.exists():
            result[name] = "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def _home(args: argparse.Namespace) -> Path:
    return Path(getattr(args, "home", None) or DEFAULT_HOME).expanduser()


def _registry_path(home: Path) -> Path:
    return home / "data" / "reporter_registry.json"


def _rewards_path(home: Path) -> Path:
    return home / "data" / "rewards.json"


def _reports_log_path(home: Path) -> Path:
    return home / "data" / "reports.jsonl"


def _query_registry_path(home: Path) -> Path:
    return home / "data" / "queries.json"


def _source_registry_path(home: Path) -> Path:
    return home / "data" / "source_registry.json"


def _aggregates_log_path(home: Path) -> Path:
    return home / "data" / "aggregates.jsonl"


def _reads_log_path(home: Path) -> Path:
    return home / "data" / "accepted_reads.jsonl"


def _authorizations_log_path(home: Path) -> Path:
    return home / "data" / "oracle_authorizations.jsonl"


def _disputes_path(home: Path) -> Path:
    return home / "data" / "disputes.json"


def _disputes_log_path(home: Path) -> Path:
    return home / "data" / "disputes.jsonl"


def _load_mapping_or_default(path: Path, default: Mapping[str, Any]) -> dict[str, Any]:
    if not path.exists():
        return dict(default)
    data = _load_json(path)
    if not isinstance(data, dict):
        raise SystemExit(f"{path} must contain a JSON object")
    return data


def _load_identity(home: Path) -> dict[str, Any]:
    data = _load_json(_key_path(home))
    if not isinstance(data, dict):
        raise SystemExit("identity file must be an object")
    for key in ("reporter_id", "public_key", "secret_key"):
        if not isinstance(data.get(key), str) or not data.get(key):
            raise SystemExit(f"identity is missing {key}")
    return data


def _load_reporter_registry(home: Path) -> dict[str, Any]:
    return _load_mapping_or_default(
        _registry_path(home),
        {
            "schema": "zeno_oracle.local_reporter_registry.v1",
            "reporters": {},
            "production_authority": False,
        },
    )


def _load_rewards(home: Path) -> dict[str, Any]:
    return _load_mapping_or_default(
        _rewards_path(home),
        {
            "schema": "zeno_oracle.local_reporter_rewards.v1",
            "reporters": {},
            "production_authority": False,
        },
    )


def _load_query_registry(home: Path) -> dict[str, Any]:
    return _load_mapping_or_default(
        _query_registry_path(home),
        {
            "schema": "zeno_oracle.local_query_registry.v1",
            "queries": [],
            "production_authority": False,
        },
    )


def _load_source_registry(home: Path) -> dict[str, Any]:
    return _load_mapping_or_default(
        _source_registry_path(home),
        {
            "schema": "zeno_oracle.local_source_registry.v1",
            "sources": {},
            "production_authority": False,
        },
    )


def _load_disputes(home: Path) -> dict[str, Any]:
    return _load_mapping_or_default(
        _disputes_path(home),
        {
            "schema": "zeno_oracle.local_dispute_registry.v1",
            "disputes": {},
            "production_authority": False,
        },
    )


def _registry_reporters(registry: Mapping[str, Any]) -> dict[str, Any]:
    reporters = registry.get("reporters")
    if not isinstance(reporters, dict):
        raise SystemExit("reporter registry reporters must be an object")
    return reporters


def _reward_reporters(rewards: Mapping[str, Any]) -> dict[str, Any]:
    reporters = rewards.get("reporters")
    if not isinstance(reporters, dict):
        raise SystemExit("reward ledger reporters must be an object")
    return reporters


def _dispute_entries(disputes: Mapping[str, Any]) -> dict[str, Any]:
    entries = disputes.get("disputes")
    if not isinstance(entries, dict):
        raise SystemExit("dispute registry disputes must be an object")
    return entries


def _source_entries(registry: Mapping[str, Any]) -> dict[str, Any]:
    sources = registry.get("sources")
    if not isinstance(sources, dict):
        raise SystemExit("source registry sources must be an object")
    return sources


def _local_query_ids(home: Path) -> set[str]:
    registry = _load_query_registry(home)
    return {str(query["query_id"]) for query in _registry_queries(registry) if query.get("query_id")}


def _find_local_query(home: Path, query_id: str) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any] | None]:
    registry = _load_query_registry(home)
    queries = _registry_queries(registry)
    for query in queries:
        if query.get("query_id") == query_id:
            return registry, queries, query
    return registry, queries, None


def _require_known_local_query_if_configured(home: Path, query_id: str) -> None:
    _registry, queries, query = _find_local_query(home, query_id)
    if queries and query is None:
        raise SystemExit(f"query_id is not in the local query registry: {query_id}")


def _replace_query(registry: dict[str, Any], queries: list[dict[str, Any]], updated: Mapping[str, Any]) -> None:
    query_id = updated.get("query_id")
    registry["queries"] = sorted(
        [dict(updated) if query.get("query_id") == query_id else query for query in queries],
        key=lambda item: str(item.get("query_id", "")),
    )


def cmd_version(args: argparse.Namespace) -> int:
    payload = {
        "schema": SCHEMA,
        "name": "zenodex-oracle",
        "version": CLI_VERSION,
        "commit": _git_commit(),
        "build_target": "native-binary" if getattr(sys, "frozen", False) else "python-local",
        "supported_schema_versions": [
            "zeno_oracle.oracle_authorization.v1",
            "zenodex/oracle-authorization-semantic-binding-check/v1",
        ],
        "asset_manifest": _asset_manifest(),
        "production_authority": False,
    }
    _emit(payload, json_out=args.json)
    return 0


def cmd_init(args: argparse.Namespace) -> int:
    home = _home(args)
    for child in ("keys", "data", "receipts", "logs"):
        (home / child).mkdir(parents=True, exist_ok=True)
    config = home / "config.toml"
    if config.exists() and not args.force:
        raise SystemExit(f"{config} already exists; pass --force to overwrite")
    config.write_text(
        "\n".join(
            [
                "[node]",
                'api_url = "http://127.0.0.1:8000"',
                'chain_id = "tau-devnet"',
                "",
                "[reporter]",
                f'home = "{home}"',
                f'key_path = "{home / "keys" / "reporter.key.json"}"',
                'mode = "dev_allowlist"',
                "",
                "[registry]",
                'query_registry_path = "queries.json"',
                'reporter_registry_path = "reporters.json"',
                'source_registry_path = "source_registry.json"',
                "",
            ]
        ),
        encoding="utf-8",
    )
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "config": str(config),
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _key_path(home: Path) -> Path:
    return home / "keys" / "reporter.key.json"


def _identity_from_secret(secret_hex: str) -> dict[str, Any]:
    public_key = hashlib.sha256(bytes.fromhex(secret_hex)).hexdigest()
    reporter_id = semantic_hash("zeno_oracle.reporter_id.v1", {"public_key": public_key})
    return {
        "schema": "zeno_oracle.local_reporter_identity.v1",
        "signature_scheme": "local-dev-sha256:v1",
        "reporter_id": reporter_id,
        "public_key": public_key,
        "not_claimed": [
            "does_not_replace_production_wallet_or_ed25519_key_management",
            "does_not_authorize_permissionless_reporting_without_registry_admission",
        ],
    }


def cmd_identity_create(args: argparse.Namespace) -> int:
    home = _home(args)
    path = _key_path(home)
    if path.exists() and not args.force:
        raise SystemExit(f"{path} already exists; pass --force to overwrite")
    secret_hex = secrets.token_hex(32)
    identity = _identity_from_secret(secret_hex)
    payload = {
        **identity,
        "secret_key": secret_hex,
    }
    _write_json(path, payload)
    os.chmod(path, stat.S_IRUSR | stat.S_IWUSR)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "key_path": str(path),
            "reporter_id": identity["reporter_id"],
            "public_key": identity["public_key"],
            "signature_scheme": identity["signature_scheme"],
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_identity_show(args: argparse.Namespace) -> int:
    path = _key_path(_home(args))
    data = _load_json(path)
    if not isinstance(data, dict):
        raise SystemExit("identity file must be an object")
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "key_path": str(path),
            "reporter_id": data.get("reporter_id"),
            "public_key": data.get("public_key"),
            "signature_scheme": data.get("signature_scheme"),
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _now_epoch(args: argparse.Namespace) -> int:
    raw = getattr(args, "epoch", None)
    if raw is not None:
        return int(raw)
    return int(time.time())


def cmd_reporter_register(args: argparse.Namespace) -> int:
    home = _home(args)
    identity = _load_identity(home)
    registry = _load_reporter_registry(home)
    reporters = _registry_reporters(registry)
    reporter_id = str(identity["reporter_id"])
    existing = reporters.get(reporter_id)
    if existing is not None and not args.force:
        raise SystemExit(f"reporter already registered: {reporter_id}; pass --force to overwrite")
    query_ids = [str(item) for item in args.query_id]
    required_bond_e8 = int(args.required_bond_e8)
    if required_bond_e8 < 0:
        raise SystemExit("required-bond-e8 must be non-negative")
    for query_id in query_ids:
        _require_known_local_query_if_configured(home, query_id)
    reporters[reporter_id] = {
        "schema": "zeno_oracle.local_reporter_entry.v1",
        "reporter_id": reporter_id,
        "public_key": identity["public_key"],
        "display_name": args.display_name,
        "control_group_id": args.control_group_id or reporter_id,
        "registered_epoch": _now_epoch(args),
        "active": False,
        "bond_asset": args.bond_asset,
        "bond_amount_e8": 0,
        "required_bond_e8": required_bond_e8,
        "last_sequence": 0,
        "slash_state": "clear",
        "query_ids": query_ids,
    }
    _write_json(_registry_path(home), registry)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "reporter_id": reporter_id,
            "active": False,
            "required_bond_e8": required_bond_e8,
            "control_group_id": reporters[reporter_id]["control_group_id"],
            "query_ids": query_ids,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_reporter_bond(args: argparse.Namespace) -> int:
    home = _home(args)
    identity = _load_identity(home)
    registry = _load_reporter_registry(home)
    reporters = _registry_reporters(registry)
    reporter_id = str(identity["reporter_id"])
    entry = reporters.get(reporter_id)
    if not isinstance(entry, dict):
        raise SystemExit("reporter must be registered before bonding")
    amount = _positive_int(str(args.amount_e8), name="amount-e8")
    entry["bond_asset"] = args.asset
    entry["bond_amount_e8"] = int(entry.get("bond_amount_e8", 0)) + amount
    entry["active"] = int(entry["bond_amount_e8"]) >= int(entry.get("required_bond_e8", 0))
    _write_json(_registry_path(home), registry)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "reporter_id": reporter_id,
            "bond_asset": entry["bond_asset"],
            "bond_amount_e8": entry["bond_amount_e8"],
            "required_bond_e8": entry.get("required_bond_e8", 0),
            "active": entry["active"],
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_reporter_show(args: argparse.Namespace) -> int:
    home = _home(args)
    reporter_id = args.reporter_id
    if reporter_id is None:
        reporter_id = str(_load_identity(home)["reporter_id"])
    registry = _load_reporter_registry(home)
    reporters = _registry_reporters(registry)
    entry = reporters.get(reporter_id)
    if not isinstance(entry, dict):
        raise SystemExit(f"reporter not found: {reporter_id}")
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "reporter": entry,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_reporter_list(args: argparse.Namespace) -> int:
    home = _home(args)
    registry = _load_reporter_registry(home)
    rows = [
        dict(entry)
        for _reporter_id, entry in sorted(_registry_reporters(registry).items())
        if isinstance(entry, dict)
    ]
    if args.active_only:
        rows = [row for row in rows if row.get("active") is True]
    if args.query_id:
        rows = [
            row
            for row in rows
            if not isinstance(row.get("query_ids"), list) or not row.get("query_ids") or args.query_id in row["query_ids"]
        ]
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "count": len(rows),
            "reporters": rows,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_reporter_deactivate(args: argparse.Namespace) -> int:
    home = _home(args)
    reporter_id = args.reporter_id
    if reporter_id is None:
        reporter_id = str(_load_identity(home)["reporter_id"])
    registry = _load_reporter_registry(home)
    reporters = _registry_reporters(registry)
    entry = reporters.get(reporter_id)
    if not isinstance(entry, dict):
        raise SystemExit(f"reporter not found: {reporter_id}")
    entry["active"] = False
    entry["deactivated_epoch"] = _now_epoch(args)
    reporters[reporter_id] = entry
    registry["reporters"] = {key: reporters[key] for key in sorted(reporters)}
    _write_json(_registry_path(home), registry)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "reporter_id": reporter_id,
            "reporter": entry,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _stable_source_snapshot(entry: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "source_id": str(entry.get("source_id", "")),
        "source_kind": str(entry.get("source_kind", "")),
        "operator_id": str(entry.get("operator_id", "")),
        "source_control_group_id": str(entry.get("source_control_group_id", "")),
        "venue_id": str(entry.get("venue_id", "")),
        "data_family_id": str(entry.get("data_family_id", "")),
        "transport_id": str(entry.get("transport_id", "")),
        "jurisdiction": str(entry.get("jurisdiction", "")),
        "asset_classes": sorted(str(item) for item in entry.get("asset_classes", []) if isinstance(item, str)),
        "query_ids": sorted(str(item) for item in entry.get("query_ids", []) if isinstance(item, str)),
        "assurance_class": str(entry.get("assurance_class", "")),
        "active": bool(entry.get("active")),
        "registered_epoch": int(entry.get("registered_epoch", 0)),
    }


def _stable_reporter_snapshot(entry: Mapping[str, Any], reporter_id: str) -> dict[str, Any]:
    return {
        "active": bool(entry.get("active")),
        "bond_amount_e8": int(entry.get("bond_amount_e8", 0)),
        "control_group_id": str(entry.get("control_group_id", reporter_id)),
        "required_bond_e8": int(entry.get("required_bond_e8", 0)),
        "slash_state": str(entry.get("slash_state", "")),
        "query_ids": sorted(str(item) for item in entry.get("query_ids", []) if isinstance(item, str)),
    }


def _state_snapshot_hash(domain: str, snapshot: Mapping[str, Any] | None) -> str:
    return semantic_hash(domain, {"snapshot": None if snapshot is None else dict(snapshot)})


def _reporter_state_hash(snapshot: Mapping[str, Any]) -> str:
    return _state_snapshot_hash("zeno_oracle.reporter_state_at_submit.v1", snapshot)


def _source_state_hash(snapshot: Mapping[str, Any] | None) -> str:
    return _state_snapshot_hash("zeno_oracle.source_state_at_submit.v1", snapshot)


def cmd_source_register(args: argparse.Namespace) -> int:
    home = _home(args)
    registry = _load_source_registry(home)
    sources = _source_entries(registry)
    source_id = str(args.source_id).strip()
    if not source_id:
        raise SystemExit("source-id must be non-empty")
    if source_id in sources and not args.force:
        raise SystemExit(f"source already registered: {source_id}; pass --force to overwrite")
    asset_classes = sorted({str(item).strip().lower() for item in args.asset_class})
    if not asset_classes:
        asset_classes = list(ASSET_CLASSES)
    invalid_asset_classes = [item for item in asset_classes if item not in ASSET_CLASSES]
    if invalid_asset_classes:
        raise SystemExit(f"invalid asset-class values: {', '.join(invalid_asset_classes)}")
    query_ids = sorted({str(item) for item in args.query_id})
    for query_id in query_ids:
        _require_known_local_query_if_configured(home, query_id)
    source_kind = str(args.source_kind).strip().lower()
    if source_kind not in SOURCE_KINDS:
        raise SystemExit(f"source-kind must be one of: {', '.join(SOURCE_KINDS)}")
    assurance_class = str(args.assurance_class).strip().upper()
    if assurance_class not in SOURCE_ASSURANCE_CLASSES:
        raise SystemExit(f"assurance-class must be one of: {', '.join(SOURCE_ASSURANCE_CLASSES)}")
    entry = {
        "schema": "zeno_oracle.local_source_entry.v1",
        "source_id": source_id,
        "source_kind": source_kind,
        "operator_id": args.operator_id or source_id,
        "source_control_group_id": args.control_group_id or args.operator_id or source_id,
        "venue_id": args.venue_id or source_id,
        "data_family_id": args.data_family_id,
        "transport_id": args.transport_id,
        "jurisdiction": args.jurisdiction,
        "asset_classes": asset_classes,
        "query_ids": query_ids,
        "assurance_class": assurance_class,
        "registered_epoch": _now_epoch(args),
        "deactivated_epoch": None,
        "active": True,
        "not_claimed": [
            "does_not_prove_hidden_beneficial_ownership_absent",
            "does_not_prove_source_data_is_true_without_external_audit",
        ],
        "production_authority": False,
    }
    sources[source_id] = entry
    registry["sources"] = {key: sources[key] for key in sorted(sources)}
    _write_json(_source_registry_path(home), registry)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "source_id": source_id,
            "source": entry,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_source_list(args: argparse.Namespace) -> int:
    home = _home(args)
    registry = _load_source_registry(home)
    rows = [
        dict(entry)
        for _source_id, entry in sorted(_source_entries(registry).items())
        if isinstance(entry, dict)
    ]
    if args.active_only:
        rows = [row for row in rows if row.get("active") is True]
    if args.asset_class:
        rows = [
            row
            for row in rows
            if str(args.asset_class).lower() in {str(item).lower() for item in row.get("asset_classes", [])}
        ]
    if args.query_id:
        rows = [
            row
            for row in rows
            if not isinstance(row.get("query_ids"), list) or not row.get("query_ids") or args.query_id in row["query_ids"]
        ]
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "count": len(rows),
            "sources": rows,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_source_show(args: argparse.Namespace) -> int:
    home = _home(args)
    registry = _load_source_registry(home)
    entry = _source_entries(registry).get(args.source_id)
    if not isinstance(entry, dict):
        raise SystemExit(f"source not found: {args.source_id}")
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "source": entry,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_source_deactivate(args: argparse.Namespace) -> int:
    home = _home(args)
    registry = _load_source_registry(home)
    sources = _source_entries(registry)
    entry = sources.get(args.source_id)
    if not isinstance(entry, dict):
        raise SystemExit(f"source not found: {args.source_id}")
    entry["active"] = False
    entry["deactivated_epoch"] = _now_epoch(args)
    sources[args.source_id] = entry
    registry["sources"] = {key: sources[key] for key in sorted(sources)}
    _write_json(_source_registry_path(home), registry)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "source_id": args.source_id,
            "source": entry,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _sign_local_report(secret_hex: str, signing_payload_hash: str) -> str:
    secret = bytes.fromhex(secret_hex)
    digest = hashlib.sha256(secret + signing_payload_hash.encode("utf-8")).hexdigest()
    return f"local-dev-sha256:{digest}"


def _registry_queries(registry: Any) -> list[dict[str, Any]]:
    if isinstance(registry, list):
        queries = registry
    elif isinstance(registry, dict):
        value = registry.get("queries", registry.get("items", []))
        queries = value if isinstance(value, list) else []
    else:
        queries = []
    return [item for item in queries if isinstance(item, dict)]


def _query_registry_from_args(args: argparse.Namespace) -> tuple[Path, list[dict[str, Any]]]:
    if getattr(args, "registry", None):
        path = Path(args.registry)
        return path, _registry_queries(_load_json(path))
    home = _home(args)
    path = _query_registry_path(home)
    return path, _registry_queries(_load_query_registry(home))


def cmd_query_register(args: argparse.Namespace) -> int:
    home = _home(args)
    registry = _load_query_registry(home)
    queries = _registry_queries(registry)
    base_asset = args.base_asset.upper()
    quote_asset = args.quote_asset.upper()
    if base_asset == quote_asset:
        raise SystemExit("base-asset and quote-asset must differ")
    if int(args.scale) <= 0:
        raise SystemExit("scale must be positive")
    if int(args.min_reporters) <= 0:
        raise SystemExit("min-reporters must be positive")
    if int(args.freshness_window_epochs) <= 0:
        raise SystemExit("freshness-window-epochs must be positive")
    if int(args.max_deviation_bps) < 0:
        raise SystemExit("max-deviation-bps must be non-negative")
    if int(args.high_uncertainty_confidence_e8) < 0:
        raise SystemExit("high-uncertainty-confidence-e8 must be non-negative")
    for name in (
        "report_reward_e8",
        "reward_budget_e8",
        "dispute_bond_e8",
        "default_slash_e8",
    ):
        if int(getattr(args, name)) < 0:
            raise SystemExit(f"{name.replace('_', '-')} must be non-negative")
    asset_class = str(args.asset_class).strip().lower()
    if asset_class not in ASSET_CLASSES:
        raise SystemExit(f"asset-class must be one of: {', '.join(ASSET_CLASSES)}")
    query_body = {
        "schema": "zeno_oracle.query.v1",
        "query_type": args.query_type,
        "feed_id": args.feed_id or f"feed:{base_asset}-{quote_asset}:v1",
        "base_asset": base_asset,
        "quote_asset": quote_asset,
        "asset_class": asset_class,
        "jurisdiction": args.jurisdiction,
        "market_hours_policy_id": args.market_hours_policy_id,
        "valuation_policy_id": args.valuation_policy_id,
        "scale": int(args.scale),
        "evidence_floor": args.evidence_floor,
        "freshness_window_epochs": int(args.freshness_window_epochs),
        "min_reporters": int(args.min_reporters),
        "max_deviation_bps": int(args.max_deviation_bps),
        "high_uncertainty_confidence_e8": int(args.high_uncertainty_confidence_e8),
        "source_policy_id": args.source_policy_id,
        "report_reward_e8": int(args.report_reward_e8),
        "reward_budget_e8": int(args.reward_budget_e8),
        "reward_spent_e8": 0,
        "dispute_bond_e8": int(args.dispute_bond_e8),
        "default_slash_e8": int(args.default_slash_e8),
        "status": "active",
    }
    query_id = args.query_id or semantic_hash("zeno_oracle.query.v1", query_body)
    query = {**query_body, "query_id": query_id}
    replacement = False
    for idx, existing in enumerate(queries):
        if existing.get("query_id") == query_id:
            if not args.force:
                raise SystemExit(f"query already exists: {query_id}; pass --force to overwrite")
            queries[idx] = query
            replacement = True
            break
    if not replacement:
        queries.append(query)
    registry["queries"] = sorted(queries, key=lambda item: str(item.get("query_id", "")))
    _write_json(_query_registry_path(home), registry)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "query_id": query_id,
            "query": query,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_query_fund(args: argparse.Namespace) -> int:
    home = _home(args)
    amount = _positive_int(str(args.amount_e8), name="amount-e8")
    registry, queries, query = _find_local_query(home, args.query_id)
    if query is None:
        raise SystemExit(f"query_id not found: {args.query_id}")
    query["reward_budget_e8"] = int(query.get("reward_budget_e8", 0)) + amount
    query.setdefault("reward_spent_e8", 0)
    _replace_query(registry, queries, query)
    _write_json(_query_registry_path(home), registry)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "query_id": args.query_id,
            "reward_budget_e8": query["reward_budget_e8"],
            "reward_spent_e8": query["reward_spent_e8"],
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_query_list(args: argparse.Namespace) -> int:
    path, queries = _query_registry_from_args(args)
    payload = {
        "schema": SCHEMA,
        "ok": True,
        "registry": str(path),
        "count": len(queries),
        "queries": queries,
    }
    _emit(payload, json_out=args.json)
    return 0


def cmd_query_show(args: argparse.Namespace) -> int:
    _path, queries = _query_registry_from_args(args)
    for query in queries:
        if query.get("query_id") == args.query_id:
            _emit({"schema": SCHEMA, "ok": True, "query": query}, json_out=args.json)
            return 0
    raise SystemExit(f"query_id not found: {args.query_id}")


def _latest_aggregate_for_query(home: Path, query_id: str) -> dict[str, Any] | None:
    candidates = [
        aggregate
        for aggregate in _iter_jsonl(_aggregates_log_path(home))
        if aggregate.get("query_id") == query_id
    ]
    if not candidates:
        return None
    return max(candidates, key=lambda item: int(item.get("aggregate_epoch", 0)))


def _latest_read_for_query(home: Path, query_id: str) -> dict[str, Any] | None:
    candidates = [read for read in _iter_jsonl(_reads_log_path(home)) if read.get("query_id") == query_id]
    if not candidates:
        return None
    return max(candidates, key=lambda item: int(item.get("expires_at_epoch", 0)))


def _disputed_report_ids_from_snapshot(disputes: Mapping[str, Any]) -> set[str]:
    disputed: set[str] = set()
    for entry in _dispute_entries(disputes).values():
        if isinstance(entry, dict) and entry.get("status") in {"open", "upheld"} and entry.get("report_id"):
            disputed.add(str(entry["report_id"]))
    return disputed


def _disputed_report_ids(home: Path) -> set[str]:
    return _disputed_report_ids_from_snapshot(_load_disputes(home))


def _aggregate_has_disputed_reports_in_snapshot(
    disputes: Mapping[str, Any],
    aggregate: Mapping[str, Any] | None,
) -> bool:
    if aggregate is None:
        return False
    disputed = _disputed_report_ids_from_snapshot(disputes)
    return any(str(report_id) in disputed for report_id in aggregate.get("included_report_ids", []))


def _aggregate_has_disputed_reports(home: Path, aggregate: Mapping[str, Any] | None) -> bool:
    return _aggregate_has_disputed_reports_in_snapshot(_load_disputes(home), aggregate)


def _dispute_state_for_report_ids_from_snapshot(
    disputes: Mapping[str, Any],
    report_ids: Sequence[str],
) -> tuple[list[dict[str, Any]], str]:
    wanted = {str(report_id) for report_id in report_ids}
    entries: list[dict[str, Any]] = []
    for entry in _dispute_entries(disputes).values():
        if not isinstance(entry, dict):
            continue
        report_id = entry.get("report_id")
        if str(report_id) not in wanted:
            continue
        entries.append(
            {
                "dispute_id": str(entry.get("dispute_id", "")),
                "report_id": str(report_id),
                "reporter_id": str(entry.get("reporter_id", "")),
                "status": str(entry.get("status", "")),
                "slash_e8": int(entry.get("slash_e8", 0)),
            }
        )
    entries.sort(key=lambda item: (item["report_id"], item["dispute_id"]))
    return entries, semantic_hash("zeno_oracle.dispute_state_root.v1", {"disputes": entries})


def _dispute_state_for_report_ids(home: Path, report_ids: Sequence[str]) -> tuple[list[dict[str, Any]], str]:
    return _dispute_state_for_report_ids_from_snapshot(_load_disputes(home), report_ids)


def _query_status(home: Path, query: Mapping[str, Any], now_epoch: int) -> dict[str, Any]:
    query_id = str(query["query_id"])
    aggregate = _latest_aggregate_for_query(home, query_id)
    read = _latest_read_for_query(home, query_id)
    labels = ["devnet-only"]
    fresh = read is not None and int(read.get("expires_at_epoch", -1)) >= int(now_epoch)
    if fresh:
        labels.append("fresh")
    else:
        labels.append("stale")
    if _aggregate_has_disputed_reports(home, aggregate):
        labels.append("disputed")
    if aggregate is not None:
        confidence = int(aggregate.get("confidence_e8", 0))
        uncertainty_limit = int(query.get("high_uncertainty_confidence_e8", 0))
        if uncertainty_limit > 0 and confidence >= uncertainty_limit:
            labels.append("high-uncertainty")
    else:
        labels.append("no-aggregate")
    return {
        "query_id": query_id,
        "feed_id": query.get("feed_id", f"feed:{query_id}"),
        "base_asset": query.get("base_asset"),
        "quote_asset": query.get("quote_asset"),
        "asset_class": query.get("asset_class", "crypto"),
        "query_type": query.get("query_type", "spot_price"),
        "evidence_floor": query.get("evidence_floor", "O3"),
        "source_policy_id": query.get("source_policy_id", "source-policy:declared-diverse-v1"),
        "jurisdiction": query.get("jurisdiction", "global"),
        "market_hours_policy_id": query.get("market_hours_policy_id", "always-open-v1"),
        "valuation_policy_id": query.get("valuation_policy_id", "spot-observed-v1"),
        "status": sorted(set(labels)),
        "latest_aggregate_id": None if aggregate is None else aggregate.get("aggregate_id"),
        "latest_read_id": None if read is None else read.get("read_id"),
        "latest_value_e8": None if aggregate is None else aggregate.get("value_e8"),
        "confidence_e8": None if aggregate is None else aggregate.get("confidence_e8"),
        "deviation_bps": None if aggregate is None else aggregate.get("deviation_bps"),
        "expires_at_epoch": None if read is None else read.get("expires_at_epoch"),
        "now_epoch": int(now_epoch),
        "production_authority": False,
    }


def cmd_query_status(args: argparse.Namespace) -> int:
    home = _home(args)
    if args.all:
        registry = _load_query_registry(home)
        queries = _registry_queries(registry)
        now_epoch = int(args.now_epoch if args.now_epoch is not None else time.time())
        statuses = [_query_status(home, query, now_epoch) for query in queries if query.get("query_id")]
        _emit(
            {
                "schema": SCHEMA,
                "ok": True,
                "home": str(home),
                "count": len(statuses),
                "feed_statuses": statuses,
                "production_authority": False,
            },
            json_out=args.json,
        )
        return 0
    if not args.query_id:
        raise SystemExit("query status requires --query-id unless --all is passed")
    _registry, queries, query = _find_local_query(home, args.query_id)
    if query is None:
        raise SystemExit(f"query_id not found: {args.query_id}")
    now_epoch = int(args.now_epoch if args.now_epoch is not None else time.time())
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "feed_status": _query_status(home, query, now_epoch),
        },
        json_out=args.json,
    )
    return 0


def _positive_int(raw: str, *, name: str) -> int:
    if not raw.isdecimal():
        raise argparse.ArgumentTypeError(f"{name} must be a positive integer, not a float")
    value = int(raw)
    if value <= 0:
        raise argparse.ArgumentTypeError(f"{name} must be positive")
    return value


def _require_evidence_at_least(actual: str, minimum: str) -> None:
    if actual not in EVIDENCE_RANK:
        raise SystemExit(f"unknown evidence class: {actual}")
    if minimum not in EVIDENCE_RANK:
        raise SystemExit(f"unknown minimum evidence class: {minimum}")
    if EVIDENCE_RANK[actual] < EVIDENCE_RANK[minimum]:
        raise SystemExit(f"evidence class {actual} is below required {minimum}")


def _is_critical_profile(profile_id: object) -> bool:
    if not isinstance(profile_id, str):
        return False
    normalized = profile_id.lower()
    for separator in (":", "/", "_", "."):
        normalized = normalized.replace(separator, "-")
    return "critical" in {token for token in normalized.split("-") if token}


def _require_read_profile_evidence(profile_id: object, evidence_class: str) -> None:
    if _is_critical_profile(profile_id):
        _require_evidence_at_least(evidence_class, "O3")


def _source_policy_requires_registered(source_policy_id: object) -> bool:
    return str(source_policy_id) in {
        "registered-diverse-v1",
        "source-policy:registered-diverse-v1",
        "source-policy:registered-control-groups-v1",
        "registered-independent-v1",
        "source-policy:registered-independent-v1",
    }


def _source_policy_requires_reporter_source_independence(source_policy_id: object) -> bool:
    return str(source_policy_id) in {
        "registered-independent-v1",
        "source-policy:registered-independent-v1",
    }


def _source_state_for_submit(
    *,
    home: Path,
    query: Mapping[str, Any] | None,
    source_id: str,
) -> dict[str, Any] | None:
    registry = _load_source_registry(home)
    sources = _source_entries(registry)
    entry = sources.get(source_id)
    requires_registered = _source_policy_requires_registered(
        None if query is None else query.get("source_policy_id")
    )
    if entry is None:
        if requires_registered:
            raise SystemExit(f"source_id is not registered for registered source policy: {source_id}")
        return None
    if not isinstance(entry, dict):
        raise SystemExit(f"source registry entry must be an object: {source_id}")
    if entry.get("active") is not True:
        raise SystemExit(f"source is not active: {source_id}")
    query_id = None if query is None else str(query.get("query_id"))
    query_ids = entry.get("query_ids")
    if isinstance(query_ids, list) and query_ids and query_id not in {str(item) for item in query_ids}:
        raise SystemExit(f"source is not registered for query_id: {query_id}")
    asset_class = None if query is None else str(query.get("asset_class", "crypto")).lower()
    asset_classes = entry.get("asset_classes")
    if isinstance(asset_classes, list) and asset_classes and asset_class not in {
        str(item).lower() for item in asset_classes
    }:
        raise SystemExit(f"source is not registered for asset_class: {asset_class}")
    return _stable_source_snapshot(entry)


def cmd_report_dry_run(args: argparse.Namespace) -> int:
    price_e8 = _positive_int(str(args.price_e8), name="price-e8")
    source_epoch = _positive_int(str(args.source_observed_epoch), name="source-observed-epoch")
    payload = {
        "schema": "zeno_oracle.report.dry_run.v1",
        "query_id": args.query_id,
        "reporter_id": args.reporter_id,
        "source_id": args.source_id,
        "value_kind": "price_e8",
        "price_e8": price_e8,
        "source_observed_epoch": source_epoch,
        "reported_epoch": int(args.reported_epoch if args.reported_epoch is not None else source_epoch),
    }
    signing_payload_hash = semantic_hash("zeno_oracle.report_signing_payload.v1", payload)
    report_id = semantic_hash("zeno_oracle.report.v1", {**payload, "signing_payload_hash": signing_payload_hash})
    result = {
        "schema": SCHEMA,
        "ok": True,
        "dry_run": True,
        "report_id": report_id,
        "signing_payload_hash": signing_payload_hash,
        "report": payload,
        "production_authority": False,
    }
    if args.out:
        _write_json(Path(args.out), result)
    _emit(result, json_out=args.json)
    return 0


def _build_report_payload(
    *,
    query_id: str,
    reporter_id: str,
    source_id: str,
    price_e8: int,
    source_observed_epoch: int,
    reported_epoch: int,
    sequence: int,
    reporter_state_hash: str | None = None,
    source_state_hash: str | None = None,
) -> dict[str, Any]:
    payload = {
        "schema": "zeno_oracle.report.v1",
        "query_id": query_id,
        "reporter_id": reporter_id,
        "source_id": source_id,
        "value_kind": "price_e8",
        "price_e8": int(price_e8),
        "source_observed_epoch": int(source_observed_epoch),
        "reported_epoch": int(reported_epoch),
        "sequence": int(sequence),
    }
    if reporter_state_hash is not None:
        payload["reporter_state_hash"] = reporter_state_hash
    if source_state_hash is not None:
        payload["source_state_hash"] = source_state_hash
    return payload


def _report_hashes(payload: Mapping[str, Any]) -> tuple[str, str]:
    signing_payload_hash = semantic_hash("zeno_oracle.report_signing_payload.v1", payload)
    report_id = semantic_hash(
        "zeno_oracle.report.v1",
        {**payload, "signing_payload_hash": signing_payload_hash},
    )
    return signing_payload_hash, report_id


def _median_int(values: list[int]) -> int:
    if not values:
        raise ValueError("cannot compute median of empty list")
    ordered = sorted(values)
    return int(ordered[len(ordered) // 2])


def _deviation_bps(values: list[int], median: int) -> int:
    if median <= 0 or not values:
        return 0
    spread = max(values) - min(values)
    return int(math.ceil((spread * 10_000) / median))


def _latest_reports_for_query(home: Path, query_id: str) -> list[dict[str, Any]]:
    latest: dict[str, dict[str, Any]] = {}
    for report in _iter_jsonl(_reports_log_path(home)):
        if report.get("query_id") != query_id:
            continue
        reporter_id = report.get("reporter_id")
        if not isinstance(reporter_id, str):
            continue
        previous = latest.get(reporter_id)
        if previous is None or int(report.get("sequence", 0)) > int(previous.get("sequence", 0)):
            latest[reporter_id] = report
    return [latest[key] for key in sorted(latest)]


def _aggregate_from_reports(*, query: Mapping[str, Any], reports: list[dict[str, Any]], epoch: int) -> dict[str, Any]:
    query_id = str(query["query_id"])
    if len(reports) < int(query.get("min_reporters", 1)):
        raise SystemExit("not enough distinct reporter reports for aggregate")
    reporter_ids = [str(report.get("reporter_id")) for report in reports]
    if len(set(reporter_ids)) != len(reporter_ids):
        raise SystemExit("aggregate reports must have distinct reporter_id values")
    reporter_control_groups: list[str] = []
    for report in reports:
        snapshot = report.get("reporter_state_at_submit")
        if isinstance(snapshot, Mapping) and snapshot.get("control_group_id"):
            reporter_control_groups.append(str(snapshot["control_group_id"]))
        else:
            reporter_control_groups.append(str(report.get("reporter_id")))
    source_ids = [str(report.get("source_id", "")).strip() for report in reports]
    if any(not source_id for source_id in source_ids):
        raise SystemExit("aggregate reports must have non-empty source_id values")
    evidence_floor = str(query.get("evidence_floor", "O3"))
    source_policy_id = str(query.get("source_policy_id", "source-policy:declared-diverse-v1"))
    requires_registered_sources = _source_policy_requires_registered(source_policy_id)
    requires_reporter_source_independence = _source_policy_requires_reporter_source_independence(source_policy_id)
    requires_source_diversity = (
        EVIDENCE_RANK.get(evidence_floor, 0) >= EVIDENCE_RANK["O3"]
        or source_policy_id in {"declared-diverse-v1", "source-policy:declared-diverse-v1"}
        or requires_registered_sources
    )
    source_snapshots: list[dict[str, Any]] = []
    for report in reports:
        snapshot = report.get("source_state_at_submit")
        if isinstance(snapshot, Mapping):
            source_snapshots.append(dict(snapshot))
        elif requires_registered_sources:
            raise SystemExit("registered source policy requires source_state_at_submit on every report")
    if requires_source_diversity and len(set(source_ids)) != len(source_ids):
        raise SystemExit("aggregate reports must have distinct source_id values")
    if requires_source_diversity and len(set(reporter_control_groups)) != len(reporter_control_groups):
        raise SystemExit("aggregate reports must have distinct reporter control_group_id values")
    if requires_registered_sources:
        if any(snapshot.get("active") is not True for snapshot in source_snapshots):
            raise SystemExit("registered source policy requires active source snapshots")
        for report, snapshot in zip(reports, source_snapshots, strict=True):
            if snapshot.get("source_id") != report.get("source_id"):
                raise SystemExit("registered source policy requires source snapshot to match report source_id")
            for key in (
                "source_control_group_id",
                "venue_id",
                "data_family_id",
                "transport_id",
                "assurance_class",
            ):
                if not isinstance(snapshot.get(key), str) or not snapshot.get(key):
                    raise SystemExit(f"registered source policy requires non-empty {key} values")
        source_control_groups = [
            str(snapshot.get("source_control_group_id", snapshot.get("source_id", "")))
            for snapshot in source_snapshots
        ]
        venue_ids = [str(snapshot.get("venue_id", snapshot.get("source_id", ""))) for snapshot in source_snapshots]
        data_family_ids = [
            str(snapshot.get("data_family_id", snapshot.get("source_id", "")))
            for snapshot in source_snapshots
        ]
        transport_ids = [
            str(snapshot.get("transport_id", snapshot.get("source_id", "")))
            for snapshot in source_snapshots
        ]
        if len(set(source_control_groups)) != len(source_control_groups):
            raise SystemExit("registered source policy requires distinct source_control_group_id values")
        if len(set(venue_ids)) != len(venue_ids):
            raise SystemExit("registered source policy requires distinct venue_id values")
        if len(set(data_family_ids)) != len(data_family_ids):
            raise SystemExit("registered source policy requires distinct data_family_id values")
        if len(set(transport_ids)) != len(transport_ids):
            raise SystemExit("registered source policy requires distinct transport_id values")
        if requires_reporter_source_independence:
            overlap = sorted(set(reporter_control_groups).intersection(set(source_control_groups)))
            if overlap:
                raise SystemExit(
                    "registered independent source policy rejects reporter/source control_group overlap"
                )
    values = [int(report["price_e8"]) for report in reports]
    median = _median_int(values)
    confidence = max(abs(value - median) for value in values)
    deviation_bps = _deviation_bps(values, median)
    observed_epoch = min(int(report["source_observed_epoch"]) for report in reports)
    included_report_ids = sorted(str(report["report_id"]) for report in reports)
    included_source_ids = sorted(source_ids)
    body = {
        "schema": "zeno_oracle.aggregate.v1",
        "query_id": query_id,
        "aggregate_kind": "median_latest_distinct_reporters_distinct_sources",
        "evidence_class": evidence_floor,
        "value_e8": median,
        "confidence_e8": int(confidence),
        "deviation_bps": int(deviation_bps),
        "observed_epoch": observed_epoch,
        "aggregate_epoch": int(epoch),
        "min_reporters": int(query.get("min_reporters", 1)),
        "reporter_count": len(reports),
        "source_policy_id": source_policy_id,
        "source_count": len(set(source_ids)),
        "reporter_control_group_count": len(set(reporter_control_groups)),
        "included_source_ids": included_source_ids,
        "included_report_ids": included_report_ids,
        "feed_registry_root": _feed_registry_root(query),
        "query_policy_root": _query_registry_root(query),
        "source_registry_root": _source_registry_root(reports),
        "reporter_registry_root": _reporter_registry_root(reports),
        "production_authority": False,
    }
    return {**body, "aggregate_id": semantic_hash("zeno_oracle.aggregate.v1", body)}


def oracle_value_hash(*, query_id: str, value_e8: int, observed_epoch: int) -> str:
    return semantic_hash(
        "zenodex.oracle.value.v1",
        {
            "observed_epoch": int(observed_epoch),
            "query_id": str(query_id),
            "value_e8": int(value_e8),
        },
    )


def _aggregates_by_id(home: Path) -> dict[str, dict[str, Any]]:
    return {
        str(aggregate["aggregate_id"]): aggregate
        for aggregate in _iter_jsonl(_aggregates_log_path(home))
        if aggregate.get("aggregate_id")
    }


def _reads_by_id(home: Path) -> dict[str, dict[str, Any]]:
    return {
        str(read["read_id"]): read
        for read in _iter_jsonl(_reads_log_path(home))
        if read.get("read_id")
    }


def _reports_by_id(home: Path) -> dict[str, dict[str, Any]]:
    return {
        str(report["report_id"]): report
        for report in _iter_jsonl(_reports_log_path(home))
        if report.get("report_id")
    }


def _query_registry_root(query: Mapping[str, Any]) -> str:
    policy_keys = (
        "schema",
        "query_type",
        "query_id",
        "feed_id",
        "base_asset",
        "quote_asset",
        "asset_class",
        "jurisdiction",
        "market_hours_policy_id",
        "valuation_policy_id",
        "scale",
        "evidence_floor",
        "freshness_window_epochs",
        "min_reporters",
        "max_deviation_bps",
        "high_uncertainty_confidence_e8",
        "source_policy_id",
        "report_reward_e8",
        "dispute_bond_e8",
        "default_slash_e8",
        "status",
    )
    return semantic_hash(
        "zeno_oracle.query_policy_root.v1",
        {key: query.get(key) for key in policy_keys if key in query},
    )


def _feed_registry_root(query: Mapping[str, Any]) -> str:
    return semantic_hash(
        "zeno_oracle.feed_registry_root.v1",
        {
            "feed_id": query.get("feed_id", f"feed:{query.get('query_id')}"),
            "query_id": query.get("query_id"),
            "status": query.get("status"),
            "evidence_floor": query.get("evidence_floor"),
        },
    )


def _source_registry_root(reports: list[Mapping[str, Any]]) -> str:
    source_entries: list[dict[str, Any]] = []
    fallback_source_ids: list[str] = []
    for report in reports:
        source_id = report.get("source_id")
        if source_id:
            fallback_source_ids.append(str(source_id))
        snapshot = report.get("source_state_at_submit")
        if isinstance(snapshot, Mapping):
            source_entries.append(
                {
                    "active": bool(snapshot.get("active")),
                    "asset_classes": sorted(
                        str(item) for item in snapshot.get("asset_classes", []) if isinstance(item, str)
                    ),
                    "assurance_class": str(snapshot.get("assurance_class", "")),
                    "data_family_id": str(snapshot.get("data_family_id", "")),
                    "jurisdiction": str(snapshot.get("jurisdiction", "")),
                    "operator_id": str(snapshot.get("operator_id", "")),
                    "query_ids": sorted(
                        str(item) for item in snapshot.get("query_ids", []) if isinstance(item, str)
                    ),
                    "registered_epoch": int(snapshot.get("registered_epoch", 0)),
                    "source_control_group_id": str(snapshot.get("source_control_group_id", "")),
                    "source_id": str(snapshot.get("source_id", source_id or "")),
                    "source_kind": str(snapshot.get("source_kind", "")),
                    "transport_id": str(snapshot.get("transport_id", "")),
                    "venue_id": str(snapshot.get("venue_id", "")),
                }
            )
    if source_entries:
        source_entries.sort(key=lambda item: item["source_id"])
        return semantic_hash("zeno_oracle.source_registry_root.v1", {"sources": source_entries})
    source_ids = sorted(set(fallback_source_ids))
    return semantic_hash("zeno_oracle.source_registry_root.v1", {"source_ids": source_ids})


def _reporter_registry_root(reports: list[Mapping[str, Any]]) -> str:
    reporter_entries = []
    for report in reports:
        reporter_id = report.get("reporter_id")
        if not reporter_id:
            continue
        snapshot = report.get("reporter_state_at_submit")
        control_group_id = None
        if isinstance(snapshot, Mapping):
            control_group_id = snapshot.get("control_group_id")
        reporter_entries.append(
            {
                "control_group_id": str(control_group_id or reporter_id),
                "reporter_id": str(reporter_id),
            }
        )
    reporter_entries.sort(key=lambda item: (item["control_group_id"], item["reporter_id"]))
    return semantic_hash("zeno_oracle.reporter_registry_root.v1", {"reporters": reporter_entries})


def _report_leaf_commitments(reports: list[Mapping[str, Any]]) -> list[dict[str, Any]]:
    leaves: list[dict[str, Any]] = []
    for report in reports:
        snapshot = report.get("reporter_state_at_submit")
        snapshot_obj = snapshot if isinstance(snapshot, Mapping) else {}
        source_snapshot = report.get("source_state_at_submit")
        source_snapshot_obj = source_snapshot if isinstance(source_snapshot, Mapping) else {}
        leaves.append(
            {
                "active": bool(snapshot_obj.get("active")),
                "bond_amount_e8": int(snapshot_obj.get("bond_amount_e8", 0)),
                "control_group_id": str(snapshot_obj.get("control_group_id", report.get("reporter_id", ""))),
                "price_e8": int(report.get("price_e8", 0)),
                "query_id": str(report.get("query_id", "")),
                "query_ids": sorted(str(item) for item in snapshot_obj.get("query_ids", []) if isinstance(item, str)),
                "report_id": str(report.get("report_id", "")),
                "reported_epoch": int(report.get("reported_epoch", 0)),
                "reporter_id": str(report.get("reporter_id", "")),
                "reporter_state_hash": str(report.get("reporter_state_hash", "")),
                "required_bond_e8": int(snapshot_obj.get("required_bond_e8", 0)),
                "sequence": int(report.get("sequence", 0)),
                "signature": str(report.get("signature", "")),
                "signing_payload_hash": str(report.get("signing_payload_hash", "")),
                "slash_state": str(snapshot_obj.get("slash_state", "")),
                "source_id": str(report.get("source_id", "")),
                "source_observed_epoch": int(report.get("source_observed_epoch", 0)),
                "source_state_hash": str(report.get("source_state_hash", "")),
                "source_state_at_submit": _stable_source_snapshot(source_snapshot_obj) if source_snapshot_obj else None,
            }
        )
    leaves.sort(key=lambda item: item["report_id"])
    return leaves


def _receipt_graph_from_read(
    home: Path,
    read: Mapping[str, Any],
    *,
    dispute_snapshot: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    aggregate = _aggregates_by_id(home).get(str(read.get("aggregate_id")))
    if not isinstance(aggregate, dict):
        raise SystemExit(f"accepted read references unknown aggregate_id: {read.get('aggregate_id')}")
    reports_by_id = _reports_by_id(home)
    included_reports = []
    for report_id in aggregate.get("included_report_ids", []):
        report = reports_by_id.get(str(report_id))
        if not isinstance(report, dict):
            raise SystemExit(f"aggregate references unknown report_id: {report_id}")
        included_reports.append(report)
    _registry, _queries, query = _find_local_query(home, str(read.get("query_id")))
    if query is None:
        raise SystemExit(f"accepted read references unknown query_id: {read.get('query_id')}")
    if aggregate.get("feed_registry_root") != _feed_registry_root(query):
        raise SystemExit("accepted read aggregate feed_registry_root does not match active query")
    if aggregate.get("query_policy_root") != _query_registry_root(query):
        raise SystemExit("accepted read aggregate query_policy_root does not match active query")
    source_registry_root = _source_registry_root(included_reports)
    reporter_registry_root = _reporter_registry_root(included_reports)
    if aggregate.get("source_registry_root") != source_registry_root:
        raise SystemExit("accepted read aggregate source_registry_root does not match report inputs")
    if aggregate.get("reporter_registry_root") != reporter_registry_root:
        raise SystemExit("accepted read aggregate reporter_registry_root does not match report inputs")
    report_leaf_commitments = _report_leaf_commitments(included_reports)
    report_ids = [str(report_id) for report_id in aggregate.get("included_report_ids", [])]
    if dispute_snapshot is None:
        dispute_entries, dispute_state_root = _dispute_state_for_report_ids(home, report_ids)
    else:
        dispute_entries, dispute_state_root = _dispute_state_for_report_ids_from_snapshot(
            dispute_snapshot,
            report_ids,
        )
    disputed_report_ids = sorted(
        {
            entry["report_id"]
            for entry in dispute_entries
            if entry.get("status") in {"open", "upheld"}
        }
    )
    body = {
        "schema": "zeno_oracle.receipt_graph.v1",
        "read_id": read["read_id"],
        "aggregate_id": aggregate["aggregate_id"],
        "query_id": read["query_id"],
        "value_hash": read.get("value_hash"),
        "value_e8": int(read.get("value_e8", 0)),
        "confidence_e8": int(read.get("confidence_e8", 0)),
        "deviation_bps": int(read.get("deviation_bps", 0)),
        "observed_epoch": int(read.get("observed_epoch", 0)),
        "expires_at_epoch": int(read.get("expires_at_epoch", 0)),
        "read_evidence_class": read.get("evidence_class"),
        "aggregate_evidence_class": aggregate.get("evidence_class"),
        "reporter_count": int(aggregate.get("reporter_count", 0)),
        "min_reporters": int(aggregate.get("min_reporters", 0)),
        "source_policy_id": aggregate.get("source_policy_id"),
        "source_count": int(aggregate.get("source_count", 0)),
        "reporter_control_group_count": int(aggregate.get("reporter_control_group_count", 0)),
        "included_source_ids": list(aggregate.get("included_source_ids", [])),
        "included_report_ids": list(aggregate.get("included_report_ids", [])),
        "report_leaf_commitments": report_leaf_commitments,
        "report_leaf_root": semantic_hash(
            "zeno_oracle.report_leaf_root.v1",
            {"reports": report_leaf_commitments},
        ),
        "dispute_state_root": dispute_state_root,
        "disputed_report_ids": disputed_report_ids,
        "feed_registry_root": aggregate.get("feed_registry_root"),
        "query_policy_root": aggregate.get("query_policy_root"),
        "source_registry_root": source_registry_root,
        "reporter_registry_root": reporter_registry_root,
    }
    return {**body, "receipt_graph_root": semantic_hash("zeno_oracle.receipt_graph.v1", body)}


def _accepted_read_from_aggregate(
    *,
    query: Mapping[str, Any],
    aggregate: Mapping[str, Any],
    consumer_module: str,
    profile_id: str,
) -> dict[str, Any]:
    observed_epoch = int(aggregate["observed_epoch"])
    value_e8 = int(aggregate["value_e8"])
    query_freshness_window = int(query.get("freshness_window_epochs", 0))
    try:
        from src.integration.zeno_oracle_authorization import (
            CRITICAL_PROFILE_MAX_FRESHNESS_WINDOW_EPOCHS,
        )
    except Exception:  # pragma: no cover - CLI packaging fallback
        profile_freshness_window = None
    else:
        profile_freshness_window = CRITICAL_PROFILE_MAX_FRESHNESS_WINDOW_EPOCHS.get(profile_id)
    effective_freshness_window = (
        query_freshness_window
        if profile_freshness_window is None
        else min(query_freshness_window, int(profile_freshness_window))
    )
    body = {
        "schema": "zeno_oracle.accepted_read.v1",
        "aggregate_id": aggregate["aggregate_id"],
        "query_id": aggregate["query_id"],
        "consumer_module": consumer_module,
        "profile_id": profile_id,
        "value_e8": value_e8,
        "value_hash": oracle_value_hash(
            query_id=str(aggregate["query_id"]),
            value_e8=value_e8,
            observed_epoch=observed_epoch,
        ),
        "confidence_e8": int(aggregate["confidence_e8"]),
        "deviation_bps": int(aggregate["deviation_bps"]),
        "observed_epoch": observed_epoch,
        "expires_at_epoch": observed_epoch + effective_freshness_window,
        "evidence_class": aggregate.get("evidence_class", query.get("evidence_floor", "O3")),
        "production_authority": False,
    }
    return {**body, "read_id": semantic_hash("zeno_oracle.accepted_read.v1", body)}


def _require_submit_ready(entry: Mapping[str, Any], query_id: str) -> None:
    if entry.get("slash_state") != "clear":
        raise SystemExit("reporter slash_state must be clear")
    if entry.get("active") is not True:
        raise SystemExit("reporter is not active; register and bond first")
    if int(entry.get("bond_amount_e8", 0)) < int(entry.get("required_bond_e8", 0)):
        raise SystemExit("reporter bond is below required_bond_e8")
    query_ids = entry.get("query_ids")
    if isinstance(query_ids, list) and query_ids and query_id not in query_ids:
        raise SystemExit(f"reporter is not registered for query_id: {query_id}")


def cmd_report_submit(args: argparse.Namespace) -> int:
    home = _home(args)
    identity = _load_identity(home)
    reporter_id = str(identity["reporter_id"])
    registry = _load_reporter_registry(home)
    reporters = _registry_reporters(registry)
    entry = reporters.get(reporter_id)
    if not isinstance(entry, dict):
        raise SystemExit("reporter must be registered before submitting reports")
    _require_known_local_query_if_configured(home, args.query_id)
    _require_submit_ready(entry, args.query_id)
    query_registry, queries, query = _find_local_query(home, args.query_id)
    reward_e8 = int(
        args.reward_e8
        if args.reward_e8 is not None
        else (query.get("report_reward_e8", DEFAULT_REPORT_REWARD_E8) if query is not None else DEFAULT_REPORT_REWARD_E8)
    )
    if reward_e8 < 0:
        raise SystemExit("reward-e8 must be non-negative")
    if query is not None:
        budget = int(query.get("reward_budget_e8", 0))
        spent = int(query.get("reward_spent_e8", 0))
        if spent + reward_e8 > budget:
            raise SystemExit("query reward budget is insufficient for this report")

    price_e8 = _positive_int(str(args.price_e8), name="price-e8")
    source_epoch = _positive_int(str(args.source_observed_epoch), name="source-observed-epoch")
    reported_epoch = int(args.reported_epoch if args.reported_epoch is not None else source_epoch)
    if reported_epoch < source_epoch:
        raise SystemExit("reported-epoch must be >= source-observed-epoch")
    source_state = _source_state_for_submit(home=home, query=query, source_id=args.source_id)
    sequence = int(entry.get("last_sequence", 0)) + 1
    reporter_state = _stable_reporter_snapshot(entry, reporter_id)
    report = _build_report_payload(
        query_id=args.query_id,
        reporter_id=reporter_id,
        source_id=args.source_id,
        price_e8=price_e8,
        source_observed_epoch=source_epoch,
        reported_epoch=reported_epoch,
        sequence=sequence,
        reporter_state_hash=_reporter_state_hash(reporter_state),
        source_state_hash=_source_state_hash(source_state),
    )
    signing_payload_hash, report_id = _report_hashes(report)
    signed_report = {
        **report,
        "signing_payload_hash": signing_payload_hash,
        "report_id": report_id,
        "reward_e8": reward_e8,
        "reporter_state_at_submit": reporter_state,
        "signature_scheme": "local-dev-sha256:v1",
        "signature": _sign_local_report(str(identity["secret_key"]), signing_payload_hash),
        "production_authority": False,
    }
    if source_state is not None:
        signed_report["source_state_at_submit"] = source_state

    entry["last_sequence"] = sequence
    _write_json(_registry_path(home), registry)
    if query is not None:
        query["reward_spent_e8"] = int(query.get("reward_spent_e8", 0)) + reward_e8
        _replace_query(query_registry, queries, query)
        _write_json(_query_registry_path(home), query_registry)

    rewards = _load_rewards(home)
    reward_reporters = _reward_reporters(rewards)
    reward_entry = reward_reporters.setdefault(
        reporter_id,
        {
            "reporter_id": reporter_id,
            "pending_rewards_e8": 0,
            "paid_rewards_e8": 0,
            "accepted_report_count": 0,
            "slash_debt_e8": 0,
            "slashed_rewards_e8": 0,
        },
    )
    reward_entry["pending_rewards_e8"] = int(reward_entry.get("pending_rewards_e8", 0)) + reward_e8
    reward_entry["accepted_report_count"] = int(reward_entry.get("accepted_report_count", 0)) + 1
    _write_json(_rewards_path(home), rewards)

    receipt_path = home / "receipts" / "reports" / f"{report_id.replace(':', '_')}.json"
    _write_json(receipt_path, signed_report)
    _append_jsonl(_reports_log_path(home), signed_report)
    result = {
        "schema": SCHEMA,
        "ok": True,
        "home": str(home),
        "report_id": report_id,
        "signing_payload_hash": signing_payload_hash,
        "sequence": sequence,
        "receipt_path": str(receipt_path),
        "pending_rewards_e8": reward_entry["pending_rewards_e8"],
        "reward_e8": reward_e8,
        "production_authority": False,
    }
    if args.out:
        _write_json(Path(args.out), result)
    _emit(result, json_out=args.json)
    return 0


def cmd_aggregate_build(args: argparse.Namespace) -> int:
    home = _home(args)
    _registry, _queries, query = _find_local_query(home, args.query_id)
    if query is None:
        raise SystemExit(f"query_id not found: {args.query_id}")
    if query.get("status") != "active":
        raise SystemExit(f"query is not active: {args.query_id}")
    reports = _latest_reports_for_query(home, args.query_id)
    aggregate = _aggregate_from_reports(query=query, reports=reports, epoch=_now_epoch(args))
    max_deviation = int(query.get("max_deviation_bps", 0))
    if max_deviation > 0 and int(aggregate["deviation_bps"]) > max_deviation:
        raise SystemExit("aggregate deviation_bps exceeds query max_deviation_bps")
    receipt_path = home / "receipts" / "aggregates" / f"{aggregate['aggregate_id'].replace(':', '_')}.json"
    _write_json(receipt_path, aggregate)
    _append_jsonl(_aggregates_log_path(home), aggregate)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "aggregate_id": aggregate["aggregate_id"],
            "receipt_path": str(receipt_path),
            "aggregate": aggregate,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_read_accept(args: argparse.Namespace) -> int:
    home = _home(args)
    aggregate = _aggregates_by_id(home).get(args.aggregate_id)
    if not isinstance(aggregate, dict):
        raise SystemExit(f"aggregate_id not found: {args.aggregate_id}")
    _registry, _queries, query = _find_local_query(home, str(aggregate["query_id"]))
    if query is None:
        raise SystemExit(f"query_id not found: {aggregate['query_id']}")
    if query.get("status") != "active":
        raise SystemExit(f"query is not active: {aggregate['query_id']}")
    if aggregate.get("feed_registry_root") != _feed_registry_root(query):
        raise SystemExit("aggregate feed_registry_root does not match active query")
    if aggregate.get("query_policy_root") != _query_registry_root(query):
        raise SystemExit("aggregate query_policy_root does not match active query")
    if _aggregate_has_disputed_reports(home, aggregate):
        raise SystemExit("aggregate includes open or upheld disputed reports")
    max_deviation = int(query.get("max_deviation_bps", 0))
    if max_deviation > 0 and int(aggregate.get("deviation_bps", 0)) > max_deviation:
        raise SystemExit("aggregate deviation_bps exceeds query max_deviation_bps")
    _require_read_profile_evidence(
        args.profile_id,
        str(aggregate.get("evidence_class", query.get("evidence_floor", ""))),
    )
    read = _accepted_read_from_aggregate(
        query=query,
        aggregate=aggregate,
        consumer_module=args.consumer_module,
        profile_id=args.profile_id,
    )
    receipt_path = home / "receipts" / "reads" / f"{read['read_id'].replace(':', '_')}.json"
    _write_json(receipt_path, read)
    _append_jsonl(_reads_log_path(home), read)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "read_id": read["read_id"],
            "receipt_path": str(receipt_path),
            "read": read,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _authorization_bundle_from_read(
    *,
    home: Path,
    read: Mapping[str, Any],
    runtime: RuntimeActionFacts,
    economic_envelope_id: str,
    dispute_snapshot: Mapping[str, Any],
    economic_envelope: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    _registry, _queries, query = _find_local_query(home, str(read["query_id"]))
    if query is None:
        raise SystemExit(f"query_id not found: {read['query_id']}")
    graph = _receipt_graph_from_read(
        home,
        read,
        dispute_snapshot=dispute_snapshot,
    )
    authorization = {
        "consumer_module": read["consumer_module"],
        "action_kind": runtime.action_kind,
        "action_id": runtime.action_id,
        "action_facts_hash": runtime.action_facts_hash,
        "pre_state_hash": runtime.pre_state_hash,
        "profile_id": read["profile_id"],
        "query_id": read["query_id"],
        "value_e8": int(read["value_e8"]),
        "value_hash": read["value_hash"],
        "confidence_e8": int(read["confidence_e8"]),
        "deviation_bps": int(read["deviation_bps"]),
        "observed_epoch": int(read["observed_epoch"]),
        "expires_at_epoch": int(read["expires_at_epoch"]),
        "feed_id": str(query.get("feed_id", f"feed:{read['query_id']}")),
        "feed_registry_root": graph["feed_registry_root"],
        "query_policy_root": graph["query_policy_root"],
        "source_registry_root": graph["source_registry_root"],
        "reporter_registry_root": graph["reporter_registry_root"],
        "evidence_class": str(read.get("evidence_class", "")),
        "economic_envelope_id": economic_envelope_id,
        "receipt_graph_root": graph["receipt_graph_root"],
    }
    runtime_action: dict[str, Any] = {
        "consumer_module": runtime.consumer_module,
        "action_kind": runtime.action_kind,
        "action_id": runtime.action_id,
        "action_facts_hash": runtime.action_facts_hash,
        "pre_state_hash": runtime.pre_state_hash,
        "profile_id": runtime.profile_id,
        "query_id": runtime.query_id,
        "runtime_value_e8": runtime.runtime_value_e8,
        "now_epoch": runtime.now_epoch,
    }
    if runtime.runtime_notional_value_e8 is not None:
        runtime_action["runtime_notional_value_e8"] = runtime.runtime_notional_value_e8
    if runtime.max_freshness_window_epochs is not None:
        runtime_action["max_freshness_window_epochs"] = runtime.max_freshness_window_epochs
    bundle = {
        "schema": "zeno_oracle.oracle_authorization_bundle.v1",
        "authorization": authorization,
        "runtime_action": runtime_action,
        "receipt_graph": graph,
        "production_authority": False,
    }
    if economic_envelope is not None:
        bundle["economic_envelope"] = dict(economic_envelope)
    bundle["authorization_id"] = semantic_hash("zeno_oracle.oracle_authorization.v1", authorization)
    return bundle


def _verified_economic_envelope_from_args(
    args: argparse.Namespace,
) -> tuple[dict[str, Any] | None, str]:
    raw_envelope = getattr(args, "economic_envelope", None)
    require_envelope = bool(getattr(args, "require_economic_envelope", False))
    if raw_envelope is None:
        if require_envelope:
            raise SystemExit("economic_envelope is required for exact authorization build")
        return None, str(getattr(args, "economic_envelope_id", "econ:local-dev-v1"))
    if type(raw_envelope) is not dict:
        raise SystemExit("economic_envelope must be an exact object")

    from src.core.oracle_economic_security import verify_economic_security_envelope

    verification = verify_economic_security_envelope(raw_envelope)
    if verification.status != "accepted":
        raise SystemExit(
            "economic_envelope rejected: " + ", ".join(verification.errors)
        )
    owned_envelope = dict(raw_envelope)
    return owned_envelope, economic_envelope_hash(owned_envelope)


def _authorization_runtime_from_args(
    args: argparse.Namespace,
    read: Mapping[str, Any],
) -> tuple[RuntimeActionFacts, str]:
    raw_runtime = getattr(args, "runtime_action", None)
    binding_source = "consumer_runtime_exact"
    if raw_runtime is None:
        if getattr(args, "require_runtime_action", False):
            raise SystemExit("runtime_action is required for API authorization build")
        binding_source = "legacy_loose_fields"
        raw_now_epoch = getattr(args, "now_epoch", None)
        if raw_now_epoch is None:
            raw_now_epoch = read["observed_epoch"]
        raw_runtime = {
            "consumer_module": read["consumer_module"],
            "action_kind": args.action_kind,
            "action_id": args.action_id,
            "action_facts_hash": args.action_facts_hash,
            "pre_state_hash": args.pre_state_hash,
            "profile_id": read["profile_id"],
            "query_id": read["query_id"],
            "runtime_value_e8": read["value_e8"],
            "now_epoch": raw_now_epoch,
        }
    if type(raw_runtime) is dict:
        runtime_keys = frozenset(raw_runtime)
        missing = sorted(AUTHORIZATION_RUNTIME_REQUIRED_KEYS - runtime_keys)
        unknown = sorted(
            runtime_keys
            - AUTHORIZATION_RUNTIME_REQUIRED_KEYS
            - AUTHORIZATION_RUNTIME_OPTIONAL_KEYS
        )
        if missing:
            raise SystemExit(f"runtime_action missing fields: {', '.join(missing)}")
        if unknown:
            raise SystemExit(f"runtime_action has unknown fields: {', '.join(unknown)}")
    runtime = runtime_from_obj(raw_runtime)
    expected = {
        "consumer_module": read.get("consumer_module"),
        "profile_id": read.get("profile_id"),
        "query_id": read.get("query_id"),
        "runtime_value_e8": read.get("value_e8"),
    }
    actual = {
        "consumer_module": runtime.consumer_module,
        "profile_id": runtime.profile_id,
        "query_id": runtime.query_id,
        "runtime_value_e8": runtime.runtime_value_e8,
    }
    for field in ("consumer_module", "profile_id", "query_id", "runtime_value_e8"):
        if type(actual[field]) is not type(expected[field]) or actual[field] != expected[field]:
            raise SystemExit(f"runtime_action {field} does not match accepted read")
    return runtime, binding_source


@contextlib.contextmanager
def _authorization_persistence_lock(home: Path) -> Iterator[None]:
    """Linearize dispute-state publication with authorization commit.

    A dispute registry commit that wins this lock prevents later authorization
    issuance for its report. An authorization committed first remains a
    historical artifact if a dispute is opened later. Settlement-time
    revocation policy is outside this local pre-MVP boundary.
    """

    lock_path = home / "data" / "oracle_authorizations.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    directory_fd = os.open(path, flags)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)


def _ensure_durable_directory(path: Path) -> None:
    missing: list[Path] = []
    cursor = path
    while not cursor.exists():
        missing.append(cursor)
        if cursor.parent == cursor:
            raise OSError(f"cannot create durable directory {path}")
        cursor = cursor.parent
    if not cursor.is_dir():
        raise NotADirectoryError(cursor)
    for directory in reversed(missing):
        directory.mkdir(exist_ok=True)
        _fsync_directory(directory.parent)
    if not path.is_dir():
        raise NotADirectoryError(path)


def _write_all(fd: int, payload: bytes) -> None:
    remaining = memoryview(payload)
    while remaining:
        written = os.write(fd, remaining)
        if written <= 0:
            raise OSError("durable write made no progress")
        remaining = remaining[written:]


def _atomic_replace_bytes(path: Path, payload: bytes) -> None:
    """Publish bytes through one same-directory, fsynced rename."""

    _ensure_durable_directory(path.parent)
    fd, raw_temp_path = tempfile.mkstemp(
        prefix=f".{path.name}.",
        suffix=".tmp",
        dir=path.parent,
    )
    temp_path = Path(raw_temp_path)
    try:
        try:
            _write_all(fd, payload)
            os.fsync(fd)
        finally:
            os.close(fd)
        os.replace(temp_path, path)
        _fsync_directory(path.parent)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temp_path.unlink()


def _write_dispute_registry_durable(
    home: Path,
    disputes: Mapping[str, Any],
) -> None:
    payload = (json.dumps(disputes, sort_keys=True, indent=2) + "\n").encode("utf-8")
    _atomic_replace_bytes(_disputes_path(home), payload)


def _sync_file_and_parent(path: Path) -> None:
    with path.open("rb") as handle:
        os.fsync(handle.fileno())
    _fsync_directory(path.parent)


def _authorization_receipt_path(home: Path, authorization_id: str) -> Path:
    return (
        home
        / "receipts"
        / "authorizations"
        / f"{authorization_id.replace(':', '_')}.json"
    )


def _authorization_bundle_identity(
    bundle: Mapping[str, Any],
    *,
    label: str,
) -> str:
    authorization_id = bundle.get("authorization_id")
    if type(authorization_id) is not str or SHA256_RE.fullmatch(authorization_id) is None:
        raise SystemExit(f"{label} has invalid authorization_id")
    authorization = bundle.get("authorization")
    if type(authorization) is not dict:
        raise SystemExit(f"{label} must contain an exact authorization object")
    expected_authorization_id = semantic_hash(
        "zeno_oracle.oracle_authorization.v1",
        authorization,
    )
    if authorization_id != expected_authorization_id:
        raise SystemExit(f"{label} authorization_id does not match authorization content")
    return authorization_id


def _authorization_receipt_bytes(bundle: Mapping[str, Any]) -> bytes:
    return (json.dumps(bundle, sort_keys=True, indent=2) + "\n").encode("utf-8")


def _authorization_index_line_bytes(bundle: Mapping[str, Any]) -> bytes:
    line = json.dumps(bundle, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return (line + "\n").encode("ascii")


def _write_authorization_receipt_atomic(
    receipt_path: Path,
    bundle: Mapping[str, Any],
) -> None:
    _atomic_replace_bytes(receipt_path, _authorization_receipt_bytes(bundle))


def _append_authorization_index_row(
    index_path: Path,
    bundle: Mapping[str, Any],
) -> None:
    _ensure_durable_directory(index_path.parent)
    fd = os.open(index_path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    try:
        _write_all(fd, _authorization_index_line_bytes(bundle))
        os.fsync(fd)
    finally:
        os.close(fd)
    _fsync_directory(index_path.parent)


def _read_authorization_index_prefix(
    index_path: Path,
) -> tuple[list[dict[str, Any]], bytes]:
    """Return complete rows and one untrusted unterminated crash fragment."""

    if not index_path.exists():
        return [], b""
    raw = index_path.read_bytes()
    if raw.endswith(b"\n"):
        complete = raw
        trailing_fragment = b""
    else:
        complete_end = raw.rfind(b"\n") + 1
        complete = raw[:complete_end]
        trailing_fragment = raw[complete_end:]

    rows: list[dict[str, Any]] = []
    for line_no, raw_line in enumerate(complete.split(b"\n")[:-1], start=1):
        if not raw_line.strip():
            continue
        try:
            line = raw_line.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise SystemExit(
                f"{index_path}:{line_no}: invalid authorization index UTF-8"
            ) from exc
        try:
            value = _strict_json_loads(line)
        except _DuplicateJsonKeyError as exc:
            raise SystemExit(
                f"{index_path}:{line_no}: "
                f"duplicate authorization index JSON key: {exc.key}"
            ) from exc
        except _NonFiniteJsonConstantError as exc:
            raise SystemExit(
                f"{index_path}:{line_no}: "
                f"non-finite authorization index JSON constant: {exc.value}"
            ) from exc
        except json.JSONDecodeError as exc:
            raise SystemExit(
                f"{index_path}:{line_no}: invalid authorization index JSON"
            ) from exc
        if type(value) is not dict:
            raise SystemExit(
                f"{index_path}:{line_no}: authorization index entry must be an object"
            )
        rows.append(value)
    return rows, trailing_fragment


def _load_canonical_authorization_receipt(
    home: Path,
    receipt_path: Path,
) -> dict[str, Any]:
    try:
        text = receipt_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise SystemExit(
            f"{receipt_path}: canonical authorization receipt could not be loaded"
        ) from exc
    try:
        bundle = _strict_json_loads(text)
    except _DuplicateJsonKeyError as exc:
        raise SystemExit(
            f"{receipt_path}: "
            f"duplicate canonical authorization receipt JSON key: {exc.key}"
        ) from exc
    except _NonFiniteJsonConstantError as exc:
        raise SystemExit(
            f"{receipt_path}: non-finite canonical authorization receipt "
            f"JSON constant: {exc.value}"
        ) from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(
            f"{receipt_path}: canonical authorization receipt contains invalid JSON"
        ) from exc
    if type(bundle) is not dict:
        raise SystemExit(f"{receipt_path}: canonical authorization receipt must be an object")
    authorization_id = _authorization_bundle_identity(
        bundle,
        label=f"{receipt_path}: canonical authorization receipt",
    )
    expected_path = _authorization_receipt_path(home, authorization_id)
    if receipt_path.name != expected_path.name:
        raise SystemExit(
            f"{receipt_path}: canonical authorization receipt filename does not match identity"
        )
    return bundle


def _canonical_authorization_receipts(home: Path) -> dict[str, dict[str, Any]]:
    receipt_dir = home / "receipts" / "authorizations"
    if not receipt_dir.exists():
        return {}
    receipts: dict[str, dict[str, Any]] = {}
    for receipt_path in sorted(receipt_dir.glob("*.json")):
        bundle = _load_canonical_authorization_receipt(home, receipt_path)
        authorization_id = str(bundle["authorization_id"])
        if authorization_id in receipts:
            raise SystemExit("authorization durable state has duplicate canonical receipts")
        receipts[authorization_id] = bundle
    return receipts


def _validate_authorization_index_rows(
    rows: Sequence[Mapping[str, Any]],
    receipts: Mapping[str, Mapping[str, Any]],
) -> list[str]:
    ordered_ids: list[str] = []
    seen: set[str] = set()
    for row in rows:
        authorization_id = row.get("authorization_id")
        if type(authorization_id) is not str or SHA256_RE.fullmatch(authorization_id) is None:
            raise SystemExit("authorization index row has invalid authorization_id")
        if authorization_id in seen:
            raise SystemExit("authorization durable state has duplicate index rows")
        receipt = receipts.get(authorization_id)
        if receipt is None:
            raise SystemExit("authorization durable state has index row without canonical receipt")
        if type(receipt) is not dict or receipt != row:
            raise SystemExit("authorization_id collision with different durable bundle")
        seen.add(authorization_id)
        ordered_ids.append(authorization_id)
    return ordered_ids


def _rebuild_authorization_index_locked(
    home: Path,
    complete_rows: Sequence[Mapping[str, Any]],
    receipts: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    ordered_ids = _validate_authorization_index_rows(complete_rows, receipts)
    missing_ids = sorted(set(receipts) - set(ordered_ids))
    rebuilt_rows = [dict(row) for row in complete_rows]
    rebuilt_rows.extend(dict(receipts[authorization_id]) for authorization_id in missing_ids)
    index_bytes = b"".join(_authorization_index_line_bytes(row) for row in rebuilt_rows)
    _atomic_replace_bytes(_authorizations_log_path(home), index_bytes)
    return rebuilt_rows


def _authorization_index_rows_locked(home: Path) -> tuple[list[dict[str, Any]], bool]:
    index_path = _authorizations_log_path(home)
    complete_rows, trailing_fragment = _read_authorization_index_prefix(index_path)
    receipts = _canonical_authorization_receipts(home)
    ordered_ids = _validate_authorization_index_rows(complete_rows, receipts)
    missing_receipts = set(receipts) - set(ordered_ids)
    if trailing_fragment or missing_receipts:
        rebuilt = _rebuild_authorization_index_locked(home, complete_rows, receipts)
        return rebuilt, True
    return complete_rows, False


def _authorization_rows(home: Path) -> list[dict[str, Any]]:
    """Validate complete index rows while ignoring one unterminated tail.

    This read-only path never repairs durable state. Recovery remains an
    explicit locked operation or part of an exact authorization retry.
    """

    rows, _trailing_fragment = _read_authorization_index_prefix(
        _authorizations_log_path(home)
    )
    receipts = _canonical_authorization_receipts(home)
    _validate_authorization_index_rows(rows, receipts)
    return rows


def _rebuild_authorization_index(home: Path) -> list[dict[str, Any]]:
    """Explicitly rebuild the derived index from canonical receipt files."""

    with _authorization_persistence_lock(home):
        complete_rows, _trailing_fragment = _read_authorization_index_prefix(
            _authorizations_log_path(home)
        )
        receipts = _canonical_authorization_receipts(home)
        return _rebuild_authorization_index_locked(home, complete_rows, receipts)


def _persist_authorization_bundle_locked(
    home: Path,
    bundle: dict[str, Any],
) -> tuple[Path, bool, bool]:
    authorization_id = _authorization_bundle_identity(
        bundle,
        label="authorization bundle",
    )
    receipt_path = _authorization_receipt_path(home, authorization_id)
    authorization_index_path = _authorizations_log_path(home)
    authorization_index, index_recovered = _authorization_index_rows_locked(home)
    authorization_rows = [
        row
        for row in authorization_index
        if row.get("authorization_id") == authorization_id
    ]
    if receipt_path.exists():
        existing_receipt = _load_canonical_authorization_receipt(home, receipt_path)
        if existing_receipt != bundle:
            raise SystemExit("authorization_id collision with different durable bundle")
        if len(authorization_rows) > 1:
            raise SystemExit("authorization durable state has duplicate index rows")
        if authorization_rows:
            if authorization_rows[0] != bundle:
                raise SystemExit("authorization_id collision with different durable bundle")
            _sync_file_and_parent(receipt_path)
            _sync_file_and_parent(authorization_index_path)
            return receipt_path, True, index_recovered
        _append_authorization_index_row(authorization_index_path, bundle)
        return receipt_path, True, True
    if authorization_rows:
        raise SystemExit("authorization durable state has index row without canonical receipt")
    _write_authorization_receipt_atomic(receipt_path, bundle)
    _append_authorization_index_row(authorization_index_path, bundle)
    return receipt_path, False, False


def _persist_authorization_bundle(
    home: Path,
    bundle: dict[str, Any],
) -> tuple[Path, bool, bool]:
    """Persist or exactly replay one content-addressed authorization bundle.

    A filesystem lock serializes CLI and server processes. The canonical
    receipt is written before the append-only dashboard index. An exact retry
    may repair the single recoverable crash state where that receipt exists and
    its matching index row is absent. Any other split state rejects so a caller
    cannot rewrite an existing authorization identity.
    """

    if type(bundle) is not dict:
        raise SystemExit("authorization bundle must be an exact object")
    with _authorization_persistence_lock(home):
        return _persist_authorization_bundle_locked(home, bundle)


def cmd_authorization_build(args: argparse.Namespace) -> int:
    home = _home(args)
    read = _reads_by_id(home).get(args.read_id)
    if not isinstance(read, dict):
        raise SystemExit(f"read_id not found: {args.read_id}")
    aggregate = _aggregates_by_id(home).get(str(read.get("aggregate_id")))
    _require_evidence_at_least(str(read.get("evidence_class", "")), args.min_evidence_class)
    runtime, runtime_binding_source = _authorization_runtime_from_args(args, read)
    economic_envelope, economic_envelope_id = _verified_economic_envelope_from_args(args)
    expected_receipt_graph_root = getattr(args, "expected_receipt_graph_root", None)
    if expected_receipt_graph_root is None and getattr(
        args,
        "require_expected_receipt_graph_root",
        False,
    ):
        raise SystemExit("expected_receipt_graph_root is required for API authorization build")
    if expected_receipt_graph_root is not None:
        if type(expected_receipt_graph_root) is not str or SHA256_RE.fullmatch(expected_receipt_graph_root) is None:
            raise SystemExit("expected_receipt_graph_root must be a canonical sha256 reference")
    from tools.check_oracle_authorization_semantic_binding import check_authorization_payload

    with _authorization_persistence_lock(home):
        dispute_snapshot = _load_disputes(home)
        if _aggregate_has_disputed_reports_in_snapshot(dispute_snapshot, aggregate):
            raise SystemExit(
                "accepted read aggregate includes open or upheld disputed reports"
            )
        bundle = _authorization_bundle_from_read(
            home=home,
            read=read,
            runtime=runtime,
            economic_envelope_id=economic_envelope_id,
            dispute_snapshot=dispute_snapshot,
            economic_envelope=economic_envelope,
        )
        if (
            expected_receipt_graph_root is not None
            and bundle["receipt_graph"]["receipt_graph_root"]
            != expected_receipt_graph_root
        ):
            raise SystemExit("receipt_graph_root does not match expected root")
        semantic_check = check_authorization_payload(bundle)
        bundle["semantic_check"] = semantic_check
        if semantic_check.get("typed_ok") is not True:
            raise SystemExit("generated OracleAuthorization failed semantic binding check")
        receipt_path, idempotent_replay, reconciled_orphan = (
            _persist_authorization_bundle_locked(home, bundle)
        )
    response = {
        "schema": SCHEMA,
        "ok": True,
        "home": str(home),
        "authorization_id": bundle["authorization_id"],
        "receipt_path": str(receipt_path),
        "authorization": bundle["authorization"],
        "runtime_action": bundle["runtime_action"],
        "runtime_binding_source": runtime_binding_source,
        "receipt_graph": bundle["receipt_graph"],
        "idempotent_replay": idempotent_replay,
        "reconciled_orphan_receipt": reconciled_orphan,
        "production_authority": False,
    }
    if economic_envelope is not None:
        response["economic_envelope"] = economic_envelope
    _emit(response, json_out=args.json)
    return 0


def cmd_rewards_inspect(args: argparse.Namespace) -> int:
    home = _home(args)
    reporter_id = args.reporter_id
    if reporter_id is None:
        reporter_id = str(_load_identity(home)["reporter_id"])
    rewards = _load_rewards(home)
    entry = _reward_reporters(rewards).get(reporter_id)
    if not isinstance(entry, dict):
        entry = {
            "reporter_id": reporter_id,
            "pending_rewards_e8": 0,
            "paid_rewards_e8": 0,
            "accepted_report_count": 0,
            "slash_debt_e8": 0,
            "slashed_rewards_e8": 0,
        }
    reward_receipt = _reward_entry_receipt(entry)
    receipt_path = home / "receipts" / "rewards" / f"{reward_receipt['reward_entry_id'].replace(':', '_')}.json"
    _write_json(receipt_path, reward_receipt)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "rewards": entry,
            "reward_receipt": reward_receipt,
            "receipt_path": str(receipt_path),
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_rewards_pay(args: argparse.Namespace) -> int:
    home = _home(args)
    reporter_id = args.reporter_id
    if reporter_id is None:
        reporter_id = str(_load_identity(home)["reporter_id"])
    rewards = _load_rewards(home)
    reporters = _reward_reporters(rewards)
    entry = reporters.setdefault(
        reporter_id,
        {
            "reporter_id": reporter_id,
            "pending_rewards_e8": 0,
            "paid_rewards_e8": 0,
            "accepted_report_count": 0,
            "slash_debt_e8": 0,
            "slashed_rewards_e8": 0,
        },
    )
    requested = int(args.amount_e8) if args.amount_e8 is not None else int(entry.get("pending_rewards_e8", 0))
    if requested < 0:
        raise SystemExit("amount-e8 must be non-negative")
    if requested > int(entry.get("pending_rewards_e8", 0)):
        raise SystemExit("amount-e8 exceeds pending rewards")
    entry["pending_rewards_e8"] = int(entry.get("pending_rewards_e8", 0)) - requested
    entry["paid_rewards_e8"] = int(entry.get("paid_rewards_e8", 0)) + requested
    _write_json(_rewards_path(home), rewards)
    reward_receipt = _reward_entry_receipt(entry)
    receipt_path = home / "receipts" / "rewards" / f"{reward_receipt['reward_entry_id'].replace(':', '_')}.json"
    _write_json(receipt_path, reward_receipt)
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "reporter_id": reporter_id,
            "paid_now_e8": requested,
            "rewards": entry,
            "reward_receipt": reward_receipt,
            "receipt_path": str(receipt_path),
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _reward_entry_receipt(entry: Mapping[str, Any]) -> dict[str, Any]:
    body = {
        "schema": "zeno_oracle.reward_ledger_entry.v1",
        "reporter_id": str(entry.get("reporter_id", "")),
        "pending_rewards_e8": int(entry.get("pending_rewards_e8", 0)),
        "paid_rewards_e8": int(entry.get("paid_rewards_e8", 0)),
        "accepted_report_count": int(entry.get("accepted_report_count", 0)),
        "slash_debt_e8": int(entry.get("slash_debt_e8", 0)),
        "slashed_rewards_e8": int(entry.get("slashed_rewards_e8", 0)),
        "production_authority": False,
    }
    return {**body, "reward_entry_id": semantic_hash("zeno_oracle.reward_ledger_entry.v1", body)}


def _slash_settlement_receipt(
    *,
    dispute_id: str,
    reporter_id: str,
    slash_e8: int,
    slash_result: Mapping[str, Any],
    resolved_epoch: int,
) -> dict[str, Any]:
    body = {
        "schema": "zeno_oracle.slash_settlement.v1",
        "dispute_id": str(dispute_id),
        "reporter_id": str(reporter_id),
        "slash_e8": int(slash_e8),
        "bond_slashed_e8": int(slash_result.get("bond_slashed_e8", 0)),
        "pending_reward_slashed_e8": int(slash_result.get("pending_reward_slashed_e8", 0)),
        "slash_debt_e8": int(slash_result.get("slash_debt_e8", 0)),
        "resolved_epoch": int(resolved_epoch),
        "production_authority": False,
    }
    return {**body, "slash_settlement_id": semantic_hash("zeno_oracle.slash_settlement.v1", body)}


def _report_ids_from_log(home: Path) -> set[str]:
    return {str(report["report_id"]) for report in _iter_jsonl(_reports_log_path(home)) if report.get("report_id")}


def cmd_dispute_open(args: argparse.Namespace) -> int:
    home = _home(args)
    bond_e8 = _positive_int(str(args.bond_e8), name="bond-e8")
    report_ids = _report_ids_from_log(home)
    if report_ids and args.report_id not in report_ids:
        raise SystemExit(f"report_id not found in local report log: {args.report_id}")
    body = {
        "schema": "zeno_oracle.local_dispute.v1",
        "report_id": args.report_id,
        "reporter_id": args.reporter_id,
        "opened_epoch": _now_epoch(args),
        "bond_e8": bond_e8,
        "reason": args.reason,
        "status": "open",
    }
    dispute_id = args.dispute_id or semantic_hash("zeno_oracle.dispute.v1", body)
    entry = {**body, "dispute_id": dispute_id}
    with _authorization_persistence_lock(home):
        disputes = _load_disputes(home)
        entries = _dispute_entries(disputes)
        if dispute_id in entries and not args.force:
            raise SystemExit(
                f"dispute already exists: {dispute_id}; pass --force to overwrite"
            )
        entries[dispute_id] = entry
        _write_dispute_registry_durable(home, disputes)
        _append_jsonl(_disputes_log_path(home), {"event": "open", **entry})
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "dispute_id": dispute_id,
            "dispute": entry,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _sorted_disputes(disputes: Mapping[str, Any]) -> list[dict[str, Any]]:
    entries = _dispute_entries(disputes)
    result: list[dict[str, Any]] = []
    for dispute_id in sorted(entries):
        entry = entries[dispute_id]
        if isinstance(entry, dict):
            result.append(dict(entry))
    return result


def cmd_dispute_list(args: argparse.Namespace) -> int:
    home = _home(args)
    disputes = _load_disputes(home)
    rows = _sorted_disputes(disputes)
    if args.status:
        rows = [row for row in rows if row.get("status") == args.status]
    if args.reporter_id:
        rows = [row for row in rows if row.get("reporter_id") == args.reporter_id]
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "count": len(rows),
            "disputes": rows,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def cmd_dispute_show(args: argparse.Namespace) -> int:
    home = _home(args)
    disputes = _load_disputes(home)
    entry = _dispute_entries(disputes).get(args.dispute_id)
    if not isinstance(entry, dict):
        raise SystemExit(f"dispute not found: {args.dispute_id}")
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "dispute": entry,
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _slash_reporter(
    *,
    home: Path,
    reporter_id: str,
    slash_e8: int,
) -> dict[str, Any]:
    registry = _load_reporter_registry(home)
    reporters = _registry_reporters(registry)
    entry = reporters.get(reporter_id)
    if not isinstance(entry, dict):
        raise SystemExit(f"reporter not found: {reporter_id}")
    rewards = _load_rewards(home)
    reward_reporters = _reward_reporters(rewards)
    reward_entry = reward_reporters.setdefault(
        reporter_id,
        {
            "reporter_id": reporter_id,
            "pending_rewards_e8": 0,
            "paid_rewards_e8": 0,
            "accepted_report_count": 0,
            "slash_debt_e8": 0,
            "slashed_rewards_e8": 0,
        },
    )
    remaining = int(slash_e8)
    bond_slash = min(int(entry.get("bond_amount_e8", 0)), remaining)
    entry["bond_amount_e8"] = int(entry.get("bond_amount_e8", 0)) - bond_slash
    remaining -= bond_slash
    reward_slash = min(int(reward_entry.get("pending_rewards_e8", 0)), remaining)
    reward_entry["pending_rewards_e8"] = int(reward_entry.get("pending_rewards_e8", 0)) - reward_slash
    reward_entry["slashed_rewards_e8"] = int(reward_entry.get("slashed_rewards_e8", 0)) + reward_slash
    remaining -= reward_slash
    reward_entry["slash_debt_e8"] = int(reward_entry.get("slash_debt_e8", 0)) + remaining
    entry["total_slashed_e8"] = int(entry.get("total_slashed_e8", 0)) + int(slash_e8)
    entry["slash_state"] = "slashed" if slash_e8 > 0 else entry.get("slash_state", "clear")
    entry["active"] = False
    _write_json(_registry_path(home), registry)
    _write_json(_rewards_path(home), rewards)
    return {
        "bond_slashed_e8": bond_slash,
        "pending_reward_slashed_e8": reward_slash,
        "slash_debt_e8": remaining,
        "reporter": entry,
        "rewards": reward_entry,
    }


def cmd_dispute_resolve(args: argparse.Namespace) -> int:
    home = _home(args)
    slash_result: dict[str, Any] | None = None
    slash_receipt: dict[str, Any] | None = None
    slash_receipt_path: Path | None = None
    slash_e8 = int(args.slash_e8 if args.slash_e8 is not None else 0)
    with _authorization_persistence_lock(home):
        disputes = _load_disputes(home)
        entries = _dispute_entries(disputes)
        entry = entries.get(args.dispute_id)
        if not isinstance(entry, dict):
            raise SystemExit(f"dispute not found: {args.dispute_id}")
        if entry.get("status") != "open" and not args.force:
            raise SystemExit(f"dispute is not open: {args.dispute_id}")
        if args.outcome == "upheld":
            if slash_e8 == 0:
                slash_e8 = DEFAULT_SLASH_E8
            if slash_e8 < 0:
                raise SystemExit("slash-e8 must be non-negative")
            slash_result = _slash_reporter(
                home=home,
                reporter_id=str(entry["reporter_id"]),
                slash_e8=slash_e8,
            )
        elif slash_e8 != 0:
            raise SystemExit("slash-e8 is only valid when outcome is upheld")
        entry["status"] = args.outcome
        entry["resolved_epoch"] = _now_epoch(args)
        entry["slash_e8"] = slash_e8
        entries[args.dispute_id] = entry
        if slash_result is not None:
            slash_receipt = _slash_settlement_receipt(
                dispute_id=str(args.dispute_id),
                reporter_id=str(entry["reporter_id"]),
                slash_e8=slash_e8,
                slash_result=slash_result,
                resolved_epoch=int(entry["resolved_epoch"]),
            )
            slash_receipt_path = (
                home
                / "receipts"
                / "slashes"
                / f"{slash_receipt['slash_settlement_id'].replace(':', '_')}.json"
            )
            _write_json(slash_receipt_path, slash_receipt)
        _write_dispute_registry_durable(home, disputes)
        _append_jsonl(
            _disputes_log_path(home),
            {
                "event": "resolve",
                "dispute_id": args.dispute_id,
                "outcome": args.outcome,
                "slash_e8": slash_e8,
                "slash_result": slash_result,
                "resolved_epoch": entry["resolved_epoch"],
            },
        )
    _emit(
        {
            "schema": SCHEMA,
            "ok": True,
            "home": str(home),
            "dispute": entry,
            "slash_result": slash_result,
            "slash_receipt": slash_receipt,
            "slash_receipt_path": None if slash_receipt_path is None else str(slash_receipt_path),
            "production_authority": False,
        },
        json_out=args.json,
    )
    return 0


def _iter_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    items: list[dict[str, Any]] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        value = _strict_json_loads(line)
        if not isinstance(value, dict):
            raise SystemExit(f"{path}:{line_no}: report log entry must be an object")
        items.append(value)
    return items


def _verify_disputes(home: Path, reports: list[dict[str, Any]], errors: list[str]) -> None:
    report_ids = {str(report["report_id"]) for report in reports if report.get("report_id")}
    disputes = _load_disputes(home)
    entries = _dispute_entries(disputes)
    dispute_events = _iter_jsonl(_disputes_log_path(home))
    opened_counts: dict[str, int] = {}
    resolved_counts: dict[str, int] = {}
    resolve_events: dict[str, dict[str, Any]] = {}
    for event in dispute_events:
        dispute_id = event.get("dispute_id")
        if not isinstance(dispute_id, str) or not dispute_id:
            errors.append("dispute event missing dispute_id")
            continue
        if event.get("event") == "open":
            opened_counts[dispute_id] = opened_counts.get(dispute_id, 0) + 1
        elif event.get("event") == "resolve":
            resolved_counts[dispute_id] = resolved_counts.get(dispute_id, 0) + 1
            resolve_events[dispute_id] = event
        else:
            errors.append(f"dispute {dispute_id} has unknown event type")
    slash_sums: dict[str, int] = {}
    reward_slash_sums: dict[str, int] = {}
    slash_debt_sums: dict[str, int] = {}
    for dispute_id, raw_entry in entries.items():
        if not isinstance(raw_entry, dict):
            errors.append(f"dispute {dispute_id} must be an object")
            continue
        if raw_entry.get("dispute_id") != dispute_id:
            errors.append(f"dispute {dispute_id} has mismatched dispute_id")
        if opened_counts.get(dispute_id, 0) == 0:
            errors.append(f"dispute {dispute_id} missing open event")
        if opened_counts.get(dispute_id, 0) > 1:
            errors.append(f"dispute {dispute_id} has duplicate open events")
        status = raw_entry.get("status")
        if status not in {"open", "upheld", "rejected"}:
            errors.append(f"dispute {dispute_id} has invalid status")
        if status in {"upheld", "rejected"} and resolved_counts.get(dispute_id, 0) == 0:
            errors.append(f"dispute {dispute_id} missing resolve event")
        if resolved_counts.get(dispute_id, 0) > 1:
            errors.append(f"dispute {dispute_id} has duplicate resolve events")
        report_id = raw_entry.get("report_id")
        if report_ids and report_id not in report_ids:
            errors.append(f"dispute {dispute_id} references unknown report_id")
        bond_e8 = raw_entry.get("bond_e8")
        if isinstance(bond_e8, bool) or not isinstance(bond_e8, int) or bond_e8 <= 0:
            errors.append(f"dispute {dispute_id} bond_e8 must be positive")
        slash_e8 = raw_entry.get("slash_e8", 0)
        if isinstance(slash_e8, bool) or not isinstance(slash_e8, int) or slash_e8 < 0:
            errors.append(f"dispute {dispute_id} slash_e8 must be a non-negative int")
            slash_e8 = 0
        if status == "rejected" and slash_e8 != 0:
            errors.append(f"dispute {dispute_id} rejected dispute cannot slash")
        resolve_event = resolve_events.get(dispute_id)
        if status in {"upheld", "rejected"} and isinstance(resolve_event, dict):
            if resolve_event.get("outcome") != status:
                errors.append(f"dispute {dispute_id} resolve event outcome mismatch")
            if resolve_event.get("slash_e8") != slash_e8:
                errors.append(f"dispute {dispute_id} resolve event slash_e8 mismatch")
            slash_result = resolve_event.get("slash_result")
            if status == "upheld":
                if not isinstance(slash_result, dict):
                    errors.append(f"dispute {dispute_id} upheld resolve event missing slash_result")
                else:
                    bond_slash = slash_result.get("bond_slashed_e8")
                    reward_slash = slash_result.get("pending_reward_slashed_e8")
                    slash_debt = slash_result.get("slash_debt_e8")
                    parts = (bond_slash, reward_slash, slash_debt)
                    if any(isinstance(part, bool) or not isinstance(part, int) or part < 0 for part in parts):
                        errors.append(f"dispute {dispute_id} slash_result fields must be non-negative ints")
                    else:
                        if int(bond_slash) + int(reward_slash) + int(slash_debt) != int(slash_e8):
                            errors.append(f"dispute {dispute_id} slash_result does not sum to slash_e8")
                        reporter_id_for_event = str(raw_entry.get("reporter_id"))
                        reward_slash_sums[reporter_id_for_event] = (
                            reward_slash_sums.get(reporter_id_for_event, 0) + int(reward_slash)
                        )
                        slash_debt_sums[reporter_id_for_event] = (
                            slash_debt_sums.get(reporter_id_for_event, 0) + int(slash_debt)
                        )
            elif slash_result is not None:
                errors.append(f"dispute {dispute_id} rejected resolve event cannot include slash_result")
        if status == "upheld":
            reporter_id = str(raw_entry.get("reporter_id"))
            slash_sums[reporter_id] = slash_sums.get(reporter_id, 0) + int(slash_e8)
    if slash_sums:
        registry = _load_reporter_registry(home)
        reporters = _registry_reporters(registry)
        rewards = _load_rewards(home)
        reward_entries = _reward_reporters(rewards)
        for reporter_id, expected in slash_sums.items():
            reporter = reporters.get(reporter_id)
            if not isinstance(reporter, dict):
                errors.append(f"upheld dispute reporter {reporter_id} missing from registry")
                continue
            if reporter.get("slash_state") != "slashed":
                errors.append(f"upheld dispute reporter {reporter_id} not marked slashed")
            if int(reporter.get("total_slashed_e8", 0)) != expected:
                errors.append(f"reporter {reporter_id} total_slashed_e8 does not match disputes")
            reward_entry = reward_entries.get(reporter_id)
            if not isinstance(reward_entry, dict):
                errors.append(f"upheld dispute reporter {reporter_id} missing reward entry")
                continue
            expected_reward_slash = reward_slash_sums.get(reporter_id, 0)
            if int(reward_entry.get("slashed_rewards_e8", 0)) != expected_reward_slash:
                errors.append(f"reporter {reporter_id} slashed_rewards_e8 does not match dispute slashes")
            expected_slash_debt = slash_debt_sums.get(reporter_id, 0)
            if int(reward_entry.get("slash_debt_e8", 0)) != expected_slash_debt:
                errors.append(f"reporter {reporter_id} slash_debt_e8 does not match dispute slashes")


def _verify_aggregates(
    home: Path,
    reports: list[dict[str, Any]],
    queries: list[dict[str, Any]],
    errors: list[str],
) -> None:
    reports_by_id = {str(report["report_id"]): report for report in reports if report.get("report_id")}
    queries_by_id = {str(query["query_id"]): query for query in queries if query.get("query_id")}
    for aggregate in _iter_jsonl(_aggregates_log_path(home)):
        aggregate_id = aggregate.get("aggregate_id")
        query_id = aggregate.get("query_id")
        if not isinstance(aggregate_id, str) or not aggregate_id:
            errors.append("aggregate missing aggregate_id")
            continue
        if not isinstance(query_id, str) or query_id not in queries_by_id:
            errors.append(f"aggregate {aggregate_id} references unknown query_id")
            continue
        included_ids = aggregate.get("included_report_ids")
        if not isinstance(included_ids, list) or not included_ids:
            errors.append(f"aggregate {aggregate_id} must include report ids")
            continue
        if len(set(included_ids)) != len(included_ids):
            errors.append(f"aggregate {aggregate_id} has duplicate included_report_ids")
            continue
        included_reports: list[dict[str, Any]] = []
        for report_id in included_ids:
            report = reports_by_id.get(str(report_id))
            if report is None:
                errors.append(f"aggregate {aggregate_id} references unknown report {report_id}")
                continue
            if report.get("query_id") != query_id:
                errors.append(f"aggregate {aggregate_id} mixes query ids")
            included_reports.append(report)
        if len(included_reports) != len(included_ids):
            continue
        try:
            expected = _aggregate_from_reports(
                query=queries_by_id[query_id],
                reports=included_reports,
                epoch=int(aggregate.get("aggregate_epoch")),
            )
        except SystemExit as exc:
            errors.append(f"aggregate {aggregate_id} could not be replayed: {exc}")
            continue
        except Exception as exc:
            errors.append(f"aggregate {aggregate_id} could not be replayed: {exc}")
            continue
        for key in (
            "aggregate_id",
            "value_e8",
            "confidence_e8",
            "deviation_bps",
            "observed_epoch",
            "reporter_count",
            "source_policy_id",
            "source_count",
            "reporter_control_group_count",
            "included_source_ids",
            "included_report_ids",
            "feed_registry_root",
            "query_policy_root",
            "source_registry_root",
            "reporter_registry_root",
        ):
            if aggregate.get(key) != expected.get(key):
                errors.append(f"aggregate {aggregate_id} {key} does not match replay")
        max_deviation = int(queries_by_id[query_id].get("max_deviation_bps", 0))
        if max_deviation > 0 and int(aggregate.get("deviation_bps", 0)) > max_deviation:
            errors.append(f"aggregate {aggregate_id} exceeds query max_deviation_bps")


def _verify_accepted_reads(home: Path, queries: list[dict[str, Any]], errors: list[str]) -> None:
    aggregates = _aggregates_by_id(home)
    queries_by_id = {str(query["query_id"]): query for query in queries if query.get("query_id")}
    for read in _iter_jsonl(_reads_log_path(home)):
        read_id = read.get("read_id")
        aggregate_id = read.get("aggregate_id")
        if not isinstance(read_id, str) or not read_id:
            errors.append("accepted read missing read_id")
            continue
        if not isinstance(aggregate_id, str) or aggregate_id not in aggregates:
            errors.append(f"accepted read {read_id} references unknown aggregate_id")
            continue
        aggregate = aggregates[aggregate_id]
        query_id = str(aggregate.get("query_id"))
        query = queries_by_id.get(query_id)
        if query is None:
            errors.append(f"accepted read {read_id} references unknown query_id")
            continue
        if _aggregate_has_disputed_reports(home, aggregate):
            errors.append(f"accepted read {read_id} aggregate includes open or upheld disputed reports")
        try:
            expected = _accepted_read_from_aggregate(
                query=query,
                aggregate=aggregate,
                consumer_module=str(read.get("consumer_module")),
                profile_id=str(read.get("profile_id")),
            )
        except Exception as exc:
            errors.append(f"accepted read {read_id} could not be replayed: {exc}")
            continue
        for key in (
            "read_id",
            "query_id",
            "value_e8",
            "value_hash",
            "confidence_e8",
            "deviation_bps",
            "observed_epoch",
            "expires_at_epoch",
            "evidence_class",
        ):
            if read.get(key) != expected.get(key):
                errors.append(f"accepted read {read_id} {key} does not match replay")
        try:
            _require_read_profile_evidence(read.get("profile_id"), str(read.get("evidence_class", "")))
        except SystemExit as exc:
            errors.append(f"accepted read {read_id} {exc}")
        if int(read.get("expires_at_epoch", 0)) < int(read.get("observed_epoch", 0)):
            errors.append(f"accepted read {read_id} expires before observed epoch")


def _verify_authorization_bundles(
    home: Path,
    errors: list[str],
    authorization_rows: Sequence[Mapping[str, Any]] | None = None,
) -> None:
    from tools.check_oracle_authorization_semantic_binding import check_authorization_payload

    reads = _reads_by_id(home)
    rows = _authorization_rows(home) if authorization_rows is None else authorization_rows
    for bundle in rows:
        authorization_id = bundle.get("authorization_id")
        if not isinstance(authorization_id, str) or not authorization_id:
            errors.append("authorization bundle missing authorization_id")
            continue
        auth = bundle.get("authorization")
        runtime = bundle.get("runtime_action")
        graph = bundle.get("receipt_graph")
        if not isinstance(auth, dict) or not isinstance(runtime, dict) or not isinstance(graph, dict):
            errors.append(f"authorization {authorization_id} must include authorization/runtime_action/receipt_graph")
            continue
        read_id = graph.get("read_id")
        read = reads.get(str(read_id))
        if not isinstance(read, dict):
            errors.append(f"authorization {authorization_id} references unknown read_id")
            continue
        try:
            expected_graph = _receipt_graph_from_read(home, read)
        except SystemExit as exc:
            errors.append(f"authorization {authorization_id} receipt graph could not be replayed: {exc}")
            continue
        except Exception as exc:
            errors.append(f"authorization {authorization_id} receipt graph could not be replayed: {exc}")
            continue
        if graph != expected_graph:
            errors.append(f"authorization {authorization_id} receipt_graph does not match replay")
        if auth.get("receipt_graph_root") != expected_graph.get("receipt_graph_root"):
            errors.append(f"authorization {authorization_id} receipt_graph_root does not match replay")
        for root_key in (
            "feed_registry_root",
            "query_policy_root",
            "source_registry_root",
            "reporter_registry_root",
        ):
            if auth.get(root_key) != expected_graph.get(root_key):
                errors.append(f"authorization {authorization_id} {root_key} does not match replay")
        for key in (
            "query_id",
            "value_e8",
            "value_hash",
            "confidence_e8",
            "deviation_bps",
            "observed_epoch",
            "expires_at_epoch",
            "profile_id",
            "consumer_module",
            "evidence_class",
        ):
            auth_key = "profile_id" if key == "profile_id" else key
            read_key = "profile_id" if key == "profile_id" else key
            if auth.get(auth_key) != read.get(read_key):
                errors.append(f"authorization {authorization_id} {key} does not match accepted read")
        expected_auth_id = semantic_hash("zeno_oracle.oracle_authorization.v1", auth)
        if authorization_id != expected_auth_id:
            errors.append(f"authorization {authorization_id} authorization_id does not match payload")
        try:
            semantic = check_authorization_payload(bundle)
        except Exception as exc:
            errors.append(f"authorization {authorization_id} semantic check raised: {exc}")
            continue
        if semantic.get("typed_ok") is not True:
            errors.append(f"authorization {authorization_id} typed semantic check failed")


def _receipt_id_from_check(payload: Mapping[str, Any], check: Mapping[str, Any]) -> str | None:
    receipt_kind = check.get("receipt_kind")
    if receipt_kind == "report":
        return str(check.get("expected_report_id") or payload.get("report_id") or "")
    if receipt_kind == "aggregate":
        return str(check.get("expected_aggregate_id") or payload.get("aggregate_id") or "")
    if receipt_kind == "accepted_read":
        return str(check.get("expected_read_id") or payload.get("read_id") or "")
    if receipt_kind == "dispute":
        return str(check.get("expected_dispute_id") or payload.get("dispute_id") or "")
    if receipt_kind == "receipt_graph":
        return str(check.get("expected_receipt_graph_root") or payload.get("receipt_graph_root") or "")
    if receipt_kind == "reward_ledger_entry":
        return str(check.get("expected_reward_entry_id") or payload.get("reward_entry_id") or "")
    if receipt_kind == "slash_settlement":
        return str(check.get("expected_slash_settlement_id") or payload.get("slash_settlement_id") or "")
    if receipt_kind == "oracle_authorization_bundle":
        return str(check.get("expected_authorization_id") or payload.get("authorization_id") or "")
    return None


def _verify_stored_receipt_files(
    home: Path,
    errors: list[str],
    authorization_rows: Sequence[Mapping[str, Any]] | None = None,
) -> None:
    rows = _authorization_rows(home) if authorization_rows is None else authorization_rows
    logged_ids: dict[str, set[str]] = {
        "reports": {str(row.get("report_id")) for row in _iter_jsonl(_reports_log_path(home)) if row.get("report_id")},
        "aggregates": {
            str(row.get("aggregate_id")) for row in _iter_jsonl(_aggregates_log_path(home)) if row.get("aggregate_id")
        },
        "reads": {str(row.get("read_id")) for row in _iter_jsonl(_reads_log_path(home)) if row.get("read_id")},
        "authorizations": {
            str(row.get("authorization_id"))
            for row in rows
            if row.get("authorization_id")
        },
    }
    expected_slash_receipt_ids: set[str] = set()
    dispute_entries = _dispute_entries(_load_disputes(home))
    for event in _iter_jsonl(_disputes_log_path(home)):
        if event.get("event") != "resolve" or event.get("outcome") != "upheld":
            continue
        dispute_id = str(event.get("dispute_id", ""))
        dispute = dispute_entries.get(dispute_id)
        slash_result = event.get("slash_result")
        if not isinstance(dispute, Mapping) or not isinstance(slash_result, Mapping):
            continue
        receipt = _slash_settlement_receipt(
            dispute_id=dispute_id,
            reporter_id=str(dispute.get("reporter_id", "")),
            slash_e8=int(event.get("slash_e8", 0)),
            slash_result=slash_result,
            resolved_epoch=int(event.get("resolved_epoch", 0)),
        )
        expected_slash_receipt_ids.add(str(receipt["slash_settlement_id"]))
    reward_reporter_ids = set(str(reporter_id) for reporter_id in _reward_reporters(_load_rewards(home)))

    for kind in ("reports", "aggregates", "reads", "authorizations", "rewards", "slashes"):
        receipt_dir = home / "receipts" / kind
        if not receipt_dir.exists():
            continue
        for path in sorted(receipt_dir.glob("*.json")):
            relative_path = path.relative_to(home)
            try:
                if kind == "authorizations":
                    payload = _load_canonical_authorization_receipt(home, path)
                else:
                    payload = _load_json(path)
            except (Exception, SystemExit) as exc:
                errors.append(f"stored receipt {relative_path} could not be loaded: {exc}")
                continue
            if not isinstance(payload, Mapping):
                errors.append(f"stored receipt {relative_path} root must be an object")
                continue
            check = verify_standalone_receipt(payload)
            if check.get("ok") is not True:
                for error in check.get("errors", ["unknown receipt error"]):
                    errors.append(f"stored receipt {relative_path} invalid: {error}")
            receipt_id = _receipt_id_from_check(payload, check)
            if receipt_id:
                expected_stem = receipt_id.replace(":", "_")
                if path.stem != expected_stem:
                    errors.append(f"stored receipt {relative_path} filename does not match receipt id")
                if kind in logged_ids and receipt_id not in logged_ids[kind]:
                    errors.append(f"stored receipt {relative_path} is not present in {kind} log")
                if kind == "slashes" and receipt_id not in expected_slash_receipt_ids:
                    errors.append(f"stored receipt {relative_path} does not match an upheld dispute resolution")
            if kind == "rewards":
                reporter_id = str(payload.get("reporter_id", ""))
                if reporter_id not in reward_reporter_ids:
                    errors.append(f"stored receipt {relative_path} references unknown reward reporter")


def _verify_report_log(home: Path) -> tuple[bool, list[str], dict[str, int], int]:
    errors: list[str] = []
    try:
        authorization_rows = _authorization_rows(home)
    except SystemExit as exc:
        errors.append(f"authorization durable state invalid: {exc}")
        authorization_rows = []
    identity: dict[str, Any] | None = None
    if _key_path(home).exists():
        identity = _load_identity(home)
    registry = _load_reporter_registry(home)
    reporters = _registry_reporters(registry)
    source_registry = _load_source_registry(home)
    sources = _source_entries(source_registry)
    rewards = _load_rewards(home)
    reward_reporters = _reward_reporters(rewards)
    _query_registry, queries, _unused = _find_local_query(home, "")
    query_ids = {str(query["query_id"]) for query in queries if query.get("query_id")}
    query_reward_sums: dict[str, int] = {}
    sequences: dict[str, int] = {}
    reward_counts: dict[str, int] = {}
    reward_sums: dict[str, int] = {}
    reports = _iter_jsonl(_reports_log_path(home))
    for report in reports:
        reporter_id = report.get("reporter_id")
        if not isinstance(reporter_id, str):
            errors.append("report missing reporter_id")
            continue
        entry = reporters.get(reporter_id)
        if not isinstance(entry, dict):
            errors.append(f"reporter {reporter_id} is not registered")
            continue
        query_id = str(report.get("query_id"))
        if query_ids and query_id not in query_ids:
            errors.append(f"report query_id is not in local registry: {query_id}")
        query = next((item for item in queries if item.get("query_id") == query_id), None)
        snapshot = report.get("reporter_state_at_submit")
        if not isinstance(snapshot, dict):
            errors.append(f"reporter {reporter_id} missing reporter_state_at_submit")
        else:
            if snapshot.get("active") is not True:
                errors.append(f"reporter {reporter_id} was not active at submit")
            if int(snapshot.get("bond_amount_e8", 0)) < int(snapshot.get("required_bond_e8", 0)):
                errors.append(f"reporter {reporter_id} bond snapshot below required amount")
            if not isinstance(snapshot.get("control_group_id"), str) or not snapshot.get("control_group_id"):
                errors.append(f"reporter {reporter_id} missing control_group_id at submit")
            if snapshot.get("slash_state") != "clear":
                errors.append(f"reporter {reporter_id} slash_state was not clear at submit")
            snapshot_queries = snapshot.get("query_ids")
            if isinstance(snapshot_queries, list) and snapshot_queries and query_id not in snapshot_queries:
                errors.append(f"reporter {reporter_id} was not registered for query_id at submit")
            if report.get("reporter_state_hash") != _reporter_state_hash(snapshot):
                errors.append(f"reporter {reporter_id} reporter_state_hash mismatch at sequence {report.get('sequence')}")
        source_id = report.get("source_id")
        if not isinstance(source_id, str) or not source_id:
            errors.append(f"reporter {reporter_id} missing source_id")
        source_snapshot = report.get("source_state_at_submit")
        if _source_policy_requires_registered(None if query is None else query.get("source_policy_id")):
            if not isinstance(source_snapshot, dict):
                errors.append(f"reporter {reporter_id} missing source_state_at_submit for registered source policy")
        if isinstance(source_snapshot, dict):
            if source_snapshot.get("source_id") != source_id:
                errors.append(f"reporter {reporter_id} source_state_at_submit source_id mismatch")
            if source_snapshot.get("active") is not True:
                errors.append(f"reporter {reporter_id} source was not active at submit")
            for key in (
                "source_control_group_id",
                "venue_id",
                "data_family_id",
                "transport_id",
                "assurance_class",
            ):
                if not isinstance(source_snapshot.get(key), str) or not source_snapshot.get(key):
                    errors.append(f"reporter {reporter_id} source_state_at_submit missing {key}")
            current_source = sources.get(str(source_id))
            if sources and not isinstance(current_source, dict):
                errors.append(f"report source_id is not in source registry: {source_id}")
        expected_source_state_hash = _source_state_hash(source_snapshot if isinstance(source_snapshot, Mapping) else None)
        if report.get("source_state_hash") != expected_source_state_hash:
            errors.append(f"reporter {reporter_id} source_state_hash mismatch at sequence {report.get('sequence')}")
        sequence = report.get("sequence")
        if isinstance(sequence, bool) or not isinstance(sequence, int):
            errors.append(f"reporter {reporter_id} report sequence must be an int")
            continue
        expected = sequences.get(reporter_id, 0) + 1
        if sequence != expected:
            errors.append(f"reporter {reporter_id} sequence {sequence} != expected {expected}")
        sequences[reporter_id] = sequence
        core = {
            key: report[key]
            for key in (
                "schema",
                "query_id",
                "reporter_id",
                "source_id",
                "value_kind",
                "price_e8",
                "source_observed_epoch",
                "reported_epoch",
                "sequence",
                "reporter_state_hash",
                "source_state_hash",
            )
            if key in report
        }
        signing_payload_hash, report_id = _report_hashes(core)
        if report.get("signing_payload_hash") != signing_payload_hash:
            errors.append(f"reporter {reporter_id} signing_payload_hash mismatch at sequence {sequence}")
        if report.get("report_id") != report_id:
            errors.append(f"reporter {reporter_id} report_id mismatch at sequence {sequence}")
        if identity is not None and identity.get("reporter_id") == reporter_id:
            expected_signature = _sign_local_report(str(identity["secret_key"]), signing_payload_hash)
            if report.get("signature") != expected_signature:
                errors.append(f"reporter {reporter_id} signature mismatch at sequence {sequence}")
        reward_e8 = report.get("reward_e8")
        if isinstance(reward_e8, bool) or not isinstance(reward_e8, int) or reward_e8 < 0:
            errors.append(f"reporter {reporter_id} reward_e8 must be a non-negative int")
            reward_e8 = 0
        reward_counts[reporter_id] = reward_counts.get(reporter_id, 0) + 1
        reward_sums[reporter_id] = reward_sums.get(reporter_id, 0) + int(reward_e8)
        query_reward_sums[query_id] = query_reward_sums.get(query_id, 0) + int(reward_e8)
    for reporter_id, count in reward_counts.items():
        reward_entry = reward_reporters.get(reporter_id)
        if not isinstance(reward_entry, dict):
            errors.append(f"reporter {reporter_id} missing reward entry")
            continue
        if int(reward_entry.get("accepted_report_count", -1)) != count:
            errors.append(f"reporter {reporter_id} accepted_report_count does not match replay")
        accounted = (
            int(reward_entry.get("pending_rewards_e8", 0))
            + int(reward_entry.get("paid_rewards_e8", 0))
            + int(reward_entry.get("slashed_rewards_e8", 0))
        )
        if accounted != reward_sums.get(reporter_id, 0):
            errors.append(f"reporter {reporter_id} reward accounting does not match replay")
    for reporter_id, entry in reporters.items():
        if not isinstance(entry, dict):
            errors.append(f"reporter {reporter_id} registry entry must be an object")
            continue
        last_sequence = entry.get("last_sequence", 0)
        if isinstance(last_sequence, bool) or not isinstance(last_sequence, int) or last_sequence < 0:
            errors.append(f"reporter {reporter_id} last_sequence must be a non-negative int")
            continue
        expected_last_sequence = sequences.get(str(reporter_id), 0)
        if int(last_sequence) != expected_last_sequence:
            errors.append(f"reporter {reporter_id} last_sequence does not match replay")
    for query in queries:
        query_id = str(query.get("query_id"))
        expected_spent = query_reward_sums.get(query_id, 0)
        actual_spent = int(query.get("reward_spent_e8", 0))
        if actual_spent != expected_spent:
            errors.append(f"query {query_id} reward_spent_e8 does not match replay")
        if actual_spent > int(query.get("reward_budget_e8", 0)):
            errors.append(f"query {query_id} reward_spent_e8 exceeds reward_budget_e8")
    _verify_aggregates(home, reports, queries, errors)
    _verify_accepted_reads(home, queries, errors)
    _verify_authorization_bundles(home, errors, authorization_rows)
    _verify_disputes(home, reports, errors)
    _verify_stored_receipt_files(home, errors, authorization_rows)
    return not errors, errors, sequences, len(reports)


def cmd_verify_local_state(args: argparse.Namespace) -> int:
    home = _home(args)
    ok, errors, sequences, checked_reports = _verify_report_log(home)
    result = {
        "schema": SCHEMA,
        "ok": ok,
        "home": str(home),
        "checked_reports": checked_reports,
        "reporter_sequences": sequences,
        "errors": errors,
        "production_authority": False,
    }
    if args.out:
        _write_json(Path(args.out), result)
    _emit(result, json_out=args.json)
    return 0 if ok else 2


def _check_non_negative_int(payload: Mapping[str, Any], key: str, errors: list[str]) -> int:
    value = payload.get(key)
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        errors.append(f"{key} must be a non-negative int")
        return 0
    return int(value)


def _is_sha256_ref(value: Any) -> bool:
    if not isinstance(value, str) or not value.startswith("sha256:") or len(value) != 71:
        return False
    try:
        int(value.removeprefix("sha256:"), 16)
    except ValueError:
        return False
    return True


def _verify_report_receipt(payload: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    core = {
        key: payload[key]
        for key in (
            "schema",
            "query_id",
            "reporter_id",
            "source_id",
            "value_kind",
            "price_e8",
            "source_observed_epoch",
            "reported_epoch",
            "sequence",
            "reporter_state_hash",
            "source_state_hash",
        )
        if key in payload
    }
    for required in (
        "schema",
        "query_id",
        "reporter_id",
        "source_id",
        "value_kind",
        "price_e8",
        "source_observed_epoch",
        "reported_epoch",
        "sequence",
    ):
        if required not in core:
            errors.append(f"report missing {required}")
    signing_payload_hash, report_id = _report_hashes(core)
    if payload.get("signing_payload_hash") != signing_payload_hash:
        errors.append("report signing_payload_hash mismatch")
    if payload.get("report_id") != report_id:
        errors.append("report_id mismatch")
    if payload.get("value_kind") != "price_e8":
        errors.append("report value_kind must be price_e8")
    price_e8 = payload.get("price_e8")
    if isinstance(price_e8, bool) or not isinstance(price_e8, int) or price_e8 <= 0:
        errors.append("report price_e8 must be a positive int")
    reward_e8 = payload.get("reward_e8", 0)
    if isinstance(reward_e8, bool) or not isinstance(reward_e8, int) or reward_e8 < 0:
        errors.append("report reward_e8 must be a non-negative int")
    snapshot = payload.get("reporter_state_at_submit")
    if snapshot is not None and not isinstance(snapshot, dict):
        errors.append("reporter_state_at_submit must be an object when present")
    elif isinstance(snapshot, dict) and payload.get("reporter_state_hash") != _reporter_state_hash(snapshot):
        errors.append("reporter_state_hash mismatch")
    source_snapshot = payload.get("source_state_at_submit")
    if source_snapshot is not None:
        if not isinstance(source_snapshot, dict):
            errors.append("source_state_at_submit must be an object when present")
        elif source_snapshot.get("source_id") != payload.get("source_id"):
            errors.append("source_state_at_submit source_id mismatch")
    expected_source_state_hash = _source_state_hash(source_snapshot if isinstance(source_snapshot, Mapping) else None)
    if payload.get("source_state_hash") is not None and payload.get("source_state_hash") != expected_source_state_hash:
        errors.append("source_state_hash mismatch")
    return {
        "receipt_kind": "report",
        "expected_report_id": report_id,
        "expected_signing_payload_hash": signing_payload_hash,
    }


def _verify_aggregate_receipt(payload: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    body = dict(payload)
    aggregate_id = body.pop("aggregate_id", None)
    expected_aggregate_id = semantic_hash("zeno_oracle.aggregate.v1", body)
    if aggregate_id != expected_aggregate_id:
        errors.append("aggregate_id mismatch")
    included_report_ids = payload.get("included_report_ids")
    if not isinstance(included_report_ids, list) or not included_report_ids:
        errors.append("aggregate included_report_ids must be a non-empty list")
    elif len(set(str(item) for item in included_report_ids)) != len(included_report_ids):
        errors.append("aggregate included_report_ids must be distinct")
    source_ids = payload.get("included_source_ids")
    if not isinstance(source_ids, list) or not source_ids:
        errors.append("aggregate included_source_ids must be a non-empty list")
    elif len(set(str(item) for item in source_ids)) != len(source_ids):
        errors.append("aggregate included_source_ids must be distinct")
    for key in ("feed_registry_root", "query_policy_root", "source_registry_root", "reporter_registry_root"):
        if not _is_sha256_ref(payload.get(key)):
            errors.append(f"aggregate {key} must be a sha256 reference")
    reporter_count = _check_non_negative_int(payload, "reporter_count", errors)
    min_reporters = _check_non_negative_int(payload, "min_reporters", errors)
    if reporter_count < min_reporters:
        errors.append("aggregate reporter_count below min_reporters")
    _check_non_negative_int(payload, "value_e8", errors)
    _check_non_negative_int(payload, "confidence_e8", errors)
    _check_non_negative_int(payload, "deviation_bps", errors)
    return {
        "receipt_kind": "aggregate",
        "expected_aggregate_id": expected_aggregate_id,
    }


def _verify_accepted_read_receipt(payload: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    body = dict(payload)
    read_id = body.pop("read_id", None)
    expected_read_id = semantic_hash("zeno_oracle.accepted_read.v1", body)
    if read_id != expected_read_id:
        errors.append("read_id mismatch")
    for key in ("query_id", "value_e8", "observed_epoch"):
        if key not in payload:
            errors.append(f"accepted read missing {key}")
    expected_value_hash = oracle_value_hash(
        query_id=str(payload.get("query_id", "")),
        value_e8=int(payload.get("value_e8", 0)),
        observed_epoch=int(payload.get("observed_epoch", 0)),
    )
    if payload.get("value_hash") != expected_value_hash:
        errors.append("accepted read value_hash mismatch")
    try:
        _require_read_profile_evidence(payload.get("profile_id"), str(payload.get("evidence_class", "")))
    except SystemExit as exc:
        errors.append(f"accepted read {exc}")
    if int(payload.get("expires_at_epoch", 0)) < int(payload.get("observed_epoch", 0)):
        errors.append("accepted read expires before observed epoch")
    return {
        "receipt_kind": "accepted_read",
        "expected_read_id": expected_read_id,
        "expected_value_hash": expected_value_hash,
    }


def _verify_dispute_receipt(payload: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    dispute_id = payload.get("dispute_id")
    open_body = {
        "schema": "zeno_oracle.local_dispute.v1",
        "report_id": payload.get("report_id"),
        "reporter_id": payload.get("reporter_id"),
        "opened_epoch": payload.get("opened_epoch"),
        "bond_e8": payload.get("bond_e8"),
        "reason": payload.get("reason"),
        "status": "open",
    }
    expected_dispute_id = semantic_hash("zeno_oracle.dispute.v1", open_body)
    if dispute_id != expected_dispute_id:
        errors.append("dispute_id mismatch")
    status = payload.get("status")
    if status not in {"open", "upheld", "rejected"}:
        errors.append("dispute status must be open, upheld, or rejected")
    bond_e8 = payload.get("bond_e8")
    if isinstance(bond_e8, bool) or not isinstance(bond_e8, int) or bond_e8 <= 0:
        errors.append("dispute bond_e8 must be positive")
    slash_e8 = payload.get("slash_e8", 0)
    if isinstance(slash_e8, bool) or not isinstance(slash_e8, int) or slash_e8 < 0:
        errors.append("dispute slash_e8 must be a non-negative int")
    if status == "rejected" and slash_e8 != 0:
        errors.append("rejected dispute cannot carry slash_e8")
    return {
        "receipt_kind": "dispute",
        "expected_dispute_id": expected_dispute_id,
    }


def _verify_receipt_graph(payload: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    if payload.get("schema") != "zeno_oracle.receipt_graph.v1":
        errors.append("receipt graph schema must be zeno_oracle.receipt_graph.v1")
    for key in (
        "read_id",
        "aggregate_id",
        "value_hash",
        "report_leaf_root",
        "dispute_state_root",
        "feed_registry_root",
        "query_policy_root",
        "source_registry_root",
        "reporter_registry_root",
    ):
        if not _is_sha256_ref(payload.get(key)):
            errors.append(f"receipt graph {key} must be a sha256 reference")
    numeric_values: dict[str, int] = {}
    for key in (
        "value_e8",
        "confidence_e8",
        "deviation_bps",
        "observed_epoch",
        "expires_at_epoch",
        "reporter_count",
        "min_reporters",
        "source_count",
        "reporter_control_group_count",
    ):
        numeric_values[key] = _check_non_negative_int(payload, key, errors)
    if numeric_values["expires_at_epoch"] < numeric_values["observed_epoch"]:
        errors.append("receipt graph expires before observed epoch")

    included_reports = payload.get("included_report_ids")
    if not isinstance(included_reports, list) or not included_reports:
        errors.append("receipt graph included_report_ids must be a non-empty list")
        included_report_set: set[str] = set()
    else:
        included_report_set = {str(item) for item in included_reports}
        if len(included_report_set) != len(included_reports):
            errors.append("receipt graph included_report_ids must be distinct")
    included_sources = payload.get("included_source_ids")
    if not isinstance(included_sources, list) or not included_sources:
        errors.append("receipt graph included_source_ids must be a non-empty list")
    elif len({str(item) for item in included_sources}) != len(included_sources):
        errors.append("receipt graph included_source_ids must be distinct")

    report_leaf_commitments = payload.get("report_leaf_commitments")
    if not isinstance(report_leaf_commitments, list) or not report_leaf_commitments:
        errors.append("receipt graph report_leaf_commitments must be a non-empty list")
    else:
        leaf_report_ids: list[str] = []
        leaf_source_ids: list[str] = []
        for index, leaf in enumerate(report_leaf_commitments):
            if not isinstance(leaf, Mapping):
                errors.append(f"receipt graph report_leaf_commitments[{index}] must be an object")
                continue
            report_id = str(leaf.get("report_id", ""))
            source_id = str(leaf.get("source_id", ""))
            leaf_report_ids.append(report_id)
            leaf_source_ids.append(source_id)
            query_ids_raw = leaf.get("query_ids", [])
            if not isinstance(query_ids_raw, list):
                errors.append(f"receipt graph report leaf {report_id} query_ids must be a list")
                query_ids_raw = []
            reporter_snapshot = {
                "active": bool(leaf.get("active")),
                "bond_amount_e8": _check_non_negative_int(leaf, "bond_amount_e8", errors),
                "control_group_id": str(leaf.get("control_group_id", leaf.get("reporter_id", ""))),
                "query_ids": sorted(str(item) for item in query_ids_raw if isinstance(item, str)),
                "required_bond_e8": _check_non_negative_int(leaf, "required_bond_e8", errors),
                "slash_state": str(leaf.get("slash_state", "")),
            }
            if leaf.get("reporter_state_hash") != _reporter_state_hash(reporter_snapshot):
                errors.append(f"receipt graph report leaf {report_id} reporter_state_hash mismatch")
            source_snapshot = leaf.get("source_state_at_submit")
            if source_snapshot is not None and not isinstance(source_snapshot, Mapping):
                errors.append(f"receipt graph report leaf {report_id} source_state_at_submit must be an object")
                source_snapshot = None
            if isinstance(source_snapshot, Mapping):
                if source_snapshot.get("source_id") != source_id:
                    errors.append(f"receipt graph report leaf {report_id} source_state_at_submit source_id mismatch")
                for key in (
                    "source_control_group_id",
                    "venue_id",
                    "data_family_id",
                    "transport_id",
                    "assurance_class",
                ):
                    if not isinstance(source_snapshot.get(key), str) or not source_snapshot.get(key):
                        errors.append(f"receipt graph report leaf {report_id} source_state_at_submit missing {key}")
            if leaf.get("source_state_hash") != _source_state_hash(
                source_snapshot if isinstance(source_snapshot, Mapping) else None
            ):
                errors.append(f"receipt graph report leaf {report_id} source_state_hash mismatch")
        if leaf_report_ids != sorted(leaf_report_ids):
            errors.append("receipt graph report_leaf_commitments must be sorted by report_id")
        if set(leaf_report_ids) != included_report_set:
            errors.append("receipt graph report_leaf_commitments must match included_report_ids")
        if isinstance(included_sources, list) and {str(item) for item in included_sources} != set(leaf_source_ids):
            errors.append("receipt graph report_leaf_commitments must match included_source_ids")
        expected_report_leaf_root = semantic_hash(
            "zeno_oracle.report_leaf_root.v1",
            {"reports": report_leaf_commitments},
        )
        if payload.get("report_leaf_root") != expected_report_leaf_root:
            errors.append("receipt graph report_leaf_root mismatch")

    disputed_report_ids = payload.get("disputed_report_ids")
    if not isinstance(disputed_report_ids, list):
        errors.append("receipt graph disputed_report_ids must be a list")
    else:
        normalized_disputed = [str(item) for item in disputed_report_ids]
        if normalized_disputed != sorted(normalized_disputed):
            errors.append("receipt graph disputed_report_ids must be sorted")
        if len(set(normalized_disputed)) != len(normalized_disputed):
            errors.append("receipt graph disputed_report_ids must be distinct")
        if any(report_id not in included_report_set for report_id in normalized_disputed):
            errors.append("receipt graph disputed_report_ids must be included reports")

    body = dict(payload)
    receipt_graph_root = body.pop("receipt_graph_root", None)
    expected_receipt_graph_root = semantic_hash("zeno_oracle.receipt_graph.v1", body)
    if receipt_graph_root != expected_receipt_graph_root:
        errors.append("receipt_graph_root mismatch")
    return {
        "receipt_kind": "receipt_graph",
        "expected_receipt_graph_root": expected_receipt_graph_root,
    }


def _verify_reward_entry(payload: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    reward_entry_id = payload.get("reward_entry_id")
    body = dict(payload)
    body.pop("reward_entry_id", None)
    expected_reward_entry_id = semantic_hash("zeno_oracle.reward_ledger_entry.v1", body)
    if reward_entry_id != expected_reward_entry_id:
        errors.append("reward_entry_id mismatch")
    if not isinstance(payload.get("reporter_id"), str) or not payload.get("reporter_id"):
        errors.append("reward reporter_id must be a non-empty string")
    for key in (
        "pending_rewards_e8",
        "paid_rewards_e8",
        "accepted_report_count",
        "slash_debt_e8",
        "slashed_rewards_e8",
    ):
        _check_non_negative_int(payload, key, errors)
    return {
        "receipt_kind": "reward_ledger_entry",
        "expected_reward_entry_id": expected_reward_entry_id,
    }


def _verify_slash_settlement(payload: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    slash_settlement_id = payload.get("slash_settlement_id")
    body = dict(payload)
    body.pop("slash_settlement_id", None)
    expected_slash_settlement_id = semantic_hash("zeno_oracle.slash_settlement.v1", body)
    if slash_settlement_id != expected_slash_settlement_id:
        errors.append("slash_settlement_id mismatch")
    if not isinstance(payload.get("dispute_id"), str) or not payload.get("dispute_id"):
        errors.append("slash settlement dispute_id must be a non-empty string")
    if not isinstance(payload.get("reporter_id"), str) or not payload.get("reporter_id"):
        errors.append("slash settlement reporter_id must be a non-empty string")
    slash_e8 = _check_non_negative_int(payload, "slash_e8", errors)
    bond_slashed = _check_non_negative_int(payload, "bond_slashed_e8", errors)
    reward_slashed = _check_non_negative_int(payload, "pending_reward_slashed_e8", errors)
    slash_debt = _check_non_negative_int(payload, "slash_debt_e8", errors)
    _check_non_negative_int(payload, "resolved_epoch", errors)
    if bond_slashed + reward_slashed + slash_debt != slash_e8:
        errors.append("slash settlement components do not sum to slash_e8")
    return {
        "receipt_kind": "slash_settlement",
        "expected_slash_settlement_id": expected_slash_settlement_id,
    }


def _verify_oracle_authorization_bundle_receipt(
    payload: Mapping[str, Any],
    errors: list[str],
) -> dict[str, Any]:
    from tools.check_oracle_authorization_semantic_binding import check_authorization_payload

    auth = payload.get("authorization")
    runtime = payload.get("runtime_action")
    graph = payload.get("receipt_graph")
    if not isinstance(auth, Mapping):
        errors.append("authorization bundle authorization must be an object")
        auth = {}
    if not isinstance(runtime, Mapping):
        errors.append("authorization bundle runtime_action must be an object")
        runtime = {}
    if not isinstance(graph, Mapping):
        errors.append("authorization bundle receipt_graph must be an object")
        graph = {}

    semantic_payload: dict[str, Any] = {
        "authorization": auth,
        "runtime_action": runtime,
        "receipt_graph": graph,
    }
    economic_envelope = payload.get("economic_envelope")
    if economic_envelope is not None:
        semantic_payload["economic_envelope"] = economic_envelope
    try:
        semantic = check_authorization_payload(semantic_payload)
    except (TypeError, ValueError) as exc:
        semantic = {"typed_ok": False, "typed_errors": []}
        errors.append(f"authorization semantic check rejected: {exc}")
    errors.extend(str(error) for error in semantic.get("typed_errors", []))
    graph_details = _verify_receipt_graph(graph, errors)

    for root_key in (
        "feed_registry_root",
        "query_policy_root",
        "source_registry_root",
        "reporter_registry_root",
        "receipt_graph_root",
    ):
        if auth.get(root_key) != graph.get(root_key):
            errors.append(f"authorization bundle {root_key} does not match receipt_graph")
    for value_key, graph_key in (
        ("query_id", "query_id"),
        ("value_e8", "value_e8"),
        ("value_hash", "value_hash"),
        ("confidence_e8", "confidence_e8"),
        ("deviation_bps", "deviation_bps"),
        ("observed_epoch", "observed_epoch"),
        ("expires_at_epoch", "expires_at_epoch"),
        ("evidence_class", "read_evidence_class"),
    ):
        if auth.get(value_key) != graph.get(graph_key):
            errors.append(f"authorization bundle {value_key} does not match receipt_graph")

    expected_authorization_id = semantic_hash("zeno_oracle.oracle_authorization.v1", dict(auth))
    if payload.get("authorization_id") != expected_authorization_id:
        errors.append("authorization_id mismatch")
    return {
        "receipt_kind": "oracle_authorization_bundle",
        "authorization_id": payload.get("authorization_id"),
        "expected_authorization_id": expected_authorization_id,
        "expected_receipt_graph_root": graph_details.get("expected_receipt_graph_root"),
        "typed_ok": semantic.get("typed_ok") is True,
        "economic_envelope_ok": semantic.get("economic_envelope_ok") is True,
    }


def verify_standalone_receipt(payload: Mapping[str, Any]) -> dict[str, Any]:
    errors: list[str] = []
    if not isinstance(payload, Mapping):
        return {
            "schema": "zeno_oracle.receipt_check.v1",
            "ok": False,
            "receipt_kind": "unknown",
            "errors": ["payload root must be an object"],
            "production_authority": False,
        }
    schema = payload.get("schema")
    details: dict[str, Any]
    if schema == "zeno_oracle.report.v1":
        details = _verify_report_receipt(payload, errors)
    elif schema == "zeno_oracle.aggregate.v1":
        details = _verify_aggregate_receipt(payload, errors)
    elif schema == "zeno_oracle.accepted_read.v1":
        details = _verify_accepted_read_receipt(payload, errors)
    elif schema == "zeno_oracle.local_dispute.v1":
        details = _verify_dispute_receipt(payload, errors)
    elif schema == "zeno_oracle.receipt_graph.v1":
        details = _verify_receipt_graph(payload, errors)
    elif schema == "zeno_oracle.reward_ledger_entry.v1":
        details = _verify_reward_entry(payload, errors)
    elif schema == "zeno_oracle.slash_settlement.v1":
        details = _verify_slash_settlement(payload, errors)
    elif schema == "zeno_oracle.oracle_authorization_bundle.v1":
        details = _verify_oracle_authorization_bundle_receipt(payload, errors)
    else:
        details = {"receipt_kind": "unknown"}
        errors.append(f"unsupported receipt schema: {schema}")
    return {
        "schema": "zeno_oracle.receipt_check.v1",
        "ok": not errors,
        **details,
        "errors": errors,
        "production_authority": False,
    }


def cmd_verify_receipt(args: argparse.Namespace) -> int:
    payload = _load_json(Path(args.payload))
    result = verify_standalone_receipt(payload)
    if args.out:
        _write_json(Path(args.out), result)
    _emit(result, json_out=args.json)
    return 0 if result.get("ok") is True else 2


def cmd_verify_authorization(args: argparse.Namespace) -> int:
    from tools.check_oracle_authorization_semantic_binding import check_authorization_payload

    payload = _load_json(Path(args.payload))
    if not isinstance(payload, Mapping):
        raise SystemExit("payload root must be an object")
    result = check_authorization_payload(payload)
    if args.out:
        _write_json(Path(args.out), result)
    _emit(result, json_out=args.json)
    return 0 if result.get("typed_ok") is True else 2


def cmd_verify_evidence(args: argparse.Namespace) -> int:
    checker = ROOT / "internal/zeno_oracle/tools/check_oracle_mvp_evidence.py"
    if not checker.exists():
        raise SystemExit("internal Oracle MVP evidence checker is not available in this checkout")
    cmd = [sys.executable, str(checker)]
    if args.skip_lean:
        cmd.append("--skip-lean")
    proc = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if args.json:
        print(
            json.dumps(
                {
                    "schema": SCHEMA,
                    "ok": proc.returncode == 0,
                    "returncode": proc.returncode,
                    "stdout": proc.stdout,
                    "stderr": proc.stderr,
                },
                sort_keys=True,
                indent=2,
            )
        )
    else:
        print(proc.stdout, end="")
        if proc.stderr:
            print(proc.stderr, file=sys.stderr, end="")
    return proc.returncode


def _authority_profile_path(home: Path) -> Path:
    return home / "authority" / "production_authority_profile.json"


def _oracle_authority_status(home: Path) -> dict[str, Any]:
    profile_path = _authority_profile_path(home)
    if not profile_path.exists():
        status = evaluate_oracle_authority_profile_v1(None)
    else:
        try:
            payload = _load_json(profile_path)
        except Exception as exc:
            status = evaluate_oracle_authority_profile_v1(None)
            status["readiness_gaps"] = [f"oracle production authority profile unreadable: {exc}"]
        else:
            status = evaluate_oracle_authority_profile_v1(payload if isinstance(payload, Mapping) else None)
    status["profile_path"] = str(profile_path)
    return status


def _oracle_authority_exercise_report(home: Path, body: Mapping[str, Any]) -> dict[str, Any]:
    authority_status = _oracle_authority_status(home)
    profile_path = _authority_profile_path(home)
    profile: Mapping[str, Any] | None = None
    if profile_path.exists():
        payload = _load_json(profile_path)
        if isinstance(payload, Mapping):
            profile = payload
    exercise = build_oracle_authority_exercise_v1(
        chain_id=str(body.get("chain_id") or authority_status.get("chain_id") or ""),
        authority_id=str(body.get("authority_id") or authority_status.get("authority_id") or ""),
        target_network=str(body.get("target_network") or "local"),
        current_epoch=int(body.get("current_epoch", 0)),
        operator_service_url=str(body.get("operator_service_url") or ""),
        query_id=str(body.get("query_id") or ""),
        report_id=str(body.get("report_id") or ""),
        aggregate_id=str(body.get("aggregate_id") or ""),
        read_id=str(body.get("read_id") or ""),
        authorization_id=str(body.get("authorization_id") or ""),
        reward_receipt_id=str(body.get("reward_receipt_id") or ""),
        public_broadcast_reference=body.get("public_broadcast_reference"),
        public_settlement_reference=body.get("public_settlement_reference"),
    )
    exercise_status = evaluate_oracle_authority_exercise_v1(
        profile,
        exercise,
        expected_chain_id=str(authority_status.get("chain_id") or "") or None,
    )
    return {
        "schema": "zeno_oracle.api_authority_exercise.v1",
        "ok": bool(exercise_status.get("ok") is True),
        "status": exercise_status.get("status"),
        "authority_exercise": exercise,
        "authority_exercise_status": exercise_status,
        "authority_status": authority_status,
        "production_authority": bool(authority_status.get("production_authority") is True),
    }


def _load_json_mapping(path: Path, *, name: str) -> Mapping[str, Any]:
    payload = _load_json(path)
    if not isinstance(payload, Mapping):
        raise ValueError(f"{name} must decode to a JSON object")
    return payload


def _parse_authority_signer_private_key(raw: str) -> tuple[str, str, str]:
    parts = str(raw).split(":", 2)
    if len(parts) != 3 or not all(parts):
        raise ValueError("--signer-private-key must be signer_id:key_id:0x32-byte-hex")
    return parts[0], parts[1], parts[2]


def cmd_authority_status(args: argparse.Namespace) -> int:
    home = _home(args)
    status = _oracle_authority_status(home)
    if args.out:
        _write_json(Path(args.out), status)
    _emit(status, json_out=args.json)
    return 0 if status.get("production_authority") is True else 2


def cmd_authority_provision_profile(args: argparse.Namespace) -> int:
    home = _home(args)
    key_manager = _load_json_mapping(Path(args.key_manager), name="key_manager")
    signer_registry = _load_json_mapping(Path(args.signer_registry), name="signer_registry")
    profile = build_oracle_authority_profile_v1(
        authority_id=str(args.authority_id),
        chain_id=str(args.chain_id),
        stage=str(args.stage),
        enabled=not bool(args.disabled),
        key_manager=key_manager,
        signer_registry=signer_registry,
        wallet_ux={
            "external_signer_required": not bool(args.skip_external_signer_required),
            "key_manager_required": not bool(args.skip_key_manager_required),
            "device_approval_required": not bool(args.skip_device_approval_required),
        },
        proof_profile={
            "zk_or_proof_required": not bool(args.skip_zk_or_proof_required),
            "oracle_receipt_replay_required": not bool(args.skip_oracle_receipt_replay_required),
            "runtime_proof_profile": str(args.runtime_proof_profile),
        },
    )
    signature_envelopes: list[Mapping[str, Any]] = []
    for index, envelope_path in enumerate(args.signature_envelope or []):
        signature_envelopes.append(_load_json_mapping(Path(envelope_path), name=f"signature_envelope[{index}]"))
    for raw_key in args.signer_private_key or []:
        signer_id, key_id, private_key_hex = _parse_authority_signer_private_key(str(raw_key))
        signature_envelopes.append(
            build_bls_signed_artifact_envelope_v0(
                payload_kind="oracle_authority_profile",
                payload_hash=str(profile["authority_hash"]),
                signer_id=signer_id,
                key_id=key_id,
                private_key_hex=private_key_hex,
            )
        )
    if signature_envelopes:
        profile = {**profile, "signature_envelopes": [dict(envelope) for envelope in signature_envelopes]}
    status = evaluate_oracle_authority_profile_v1(profile)
    out_path = Path(args.out) if args.out else _authority_profile_path(home)
    if out_path.exists() and not args.force:
        raise SystemExit(f"{out_path} already exists; pass --force to overwrite")
    _write_json(out_path, profile)
    status["profile_path"] = str(out_path)
    report = {
        "schema": SCHEMA,
        "ok": status.get("production_authority") is True,
        "status": "accepted" if status.get("production_authority") is True else "blocked",
        "profile_path": str(out_path),
        "authority_profile": profile,
        "authority_status": status,
        "production_authority": bool(status.get("production_authority") is True),
    }
    _emit(report, json_out=args.json)
    return 0 if report["ok"] else 2


def cmd_health(args: argparse.Namespace) -> int:
    home = _home(args)
    authority_status = _oracle_authority_status(home)
    checks = {
        "home_exists": home.exists(),
        "config_exists": (home / "config.toml").exists(),
        "identity_exists": _key_path(home).exists(),
        "internal_evidence_checker_available": (
            ROOT / "internal/zeno_oracle/tools/check_oracle_mvp_evidence.py"
        ).exists(),
    }
    _emit(
        {
            "schema": SCHEMA,
            "ok": all(checks.values()),
            "home": str(home),
            "checks": checks,
            "authority_status": authority_status,
            "production_authority": bool(authority_status.get("production_authority") is True),
        },
        json_out=args.json,
    )
    return 0 if all(checks.values()) else 2


def _safe_verify_report_log(home: Path) -> dict[str, Any]:
    try:
        ok, errors, sequences, checked_reports = _verify_report_log(home)
    except SystemExit as exc:
        return {
            "ok": False,
            "checked_reports": 0,
            "reporter_sequences": {},
            "errors": [f"replay raised: {exc}"],
        }
    except Exception as exc:
        return {
            "ok": False,
            "checked_reports": 0,
            "reporter_sequences": {},
            "errors": [f"replay raised: {exc}"],
        }
    return {
        "ok": ok,
        "checked_reports": checked_reports,
        "reporter_sequences": sequences,
        "errors": errors,
    }


def _iter_receipt_dir(home: Path, kind: str) -> list[dict[str, Any]]:
    receipt_dir = home / "receipts" / kind
    if not receipt_dir.exists():
        return []
    receipts: list[dict[str, Any]] = []
    for path in sorted(receipt_dir.glob("*.json")):
        try:
            payload = _load_json(path)
        except Exception:
            continue
        if isinstance(payload, dict):
            receipts.append(payload)
    return receipts


def _dashboard_snapshot(home: Path, *, now_epoch: int, recent_limit: int = 50) -> dict[str, Any]:
    authority_status = _oracle_authority_status(home)
    query_registry = _load_query_registry(home)
    queries = _registry_queries(query_registry)
    reporters = [
        dict(entry)
        for _reporter_id, entry in sorted(_registry_reporters(_load_reporter_registry(home)).items())
        if isinstance(entry, dict)
    ]
    sources = [
        dict(entry)
        for _source_id, entry in sorted(_source_entries(_load_source_registry(home)).items())
        if isinstance(entry, dict)
    ]
    disputes = _sorted_disputes(_load_disputes(home))
    rewards = [
        dict(entry)
        for _reporter_id, entry in sorted(_reward_reporters(_load_rewards(home)).items())
        if isinstance(entry, dict)
    ]
    reports = _iter_jsonl(_reports_log_path(home))
    aggregates = _iter_jsonl(_aggregates_log_path(home))
    reads = _iter_jsonl(_reads_log_path(home))
    authorizations = _authorization_rows(home)
    reward_receipts = _iter_receipt_dir(home, "rewards")
    slash_receipts = _iter_receipt_dir(home, "slashes")
    replay = _safe_verify_report_log(home)
    feed_statuses = [_query_status(home, query, now_epoch) for query in queries if query.get("query_id")]
    critical_reads = [read for read in reads if _is_critical_profile(read.get("profile_id"))]
    o3_plus_reads = [
        read
        for read in reads
        if EVIDENCE_RANK.get(str(read.get("evidence_class", "O0")), 0) >= EVIDENCE_RANK["O3"]
    ]
    open_disputes = [entry for entry in disputes if entry.get("status") == "open"]
    upheld_disputes = [entry for entry in disputes if entry.get("status") == "upheld"]
    active_reporters = [entry for entry in reporters if entry.get("active") is True]
    active_sources = [entry for entry in sources if entry.get("active") is True]
    total_pending_rewards = sum(int(entry.get("pending_rewards_e8", 0)) for entry in rewards)
    total_paid_rewards = sum(int(entry.get("paid_rewards_e8", 0)) for entry in rewards)
    total_slashes = sum(int(entry.get("total_slashed_e8", 0)) for entry in reporters)
    summary = {
        "query_count": len(queries),
        "feed_status_count": len(feed_statuses),
        "active_feed_count": sum(1 for query in queries if query.get("status") == "active"),
        "reporter_count": len(reporters),
        "active_reporter_count": len(active_reporters),
        "source_count": len(sources),
        "active_source_count": len(active_sources),
        "report_count": len(reports),
        "aggregate_count": len(aggregates),
        "accepted_read_count": len(reads),
        "critical_read_count": len(critical_reads),
        "o3_plus_read_count": len(o3_plus_reads),
        "authorization_count": len(authorizations),
        "open_dispute_count": len(open_disputes),
        "upheld_dispute_count": len(upheld_disputes),
        "pending_rewards_e8": total_pending_rewards,
        "paid_rewards_e8": total_paid_rewards,
        "total_slashed_e8": total_slashes,
        "replay_ok": replay["ok"],
    }
    return {
        "schema": "zeno_oracle.dashboard_snapshot.v1",
        "ok": bool(replay["ok"]),
        "home": str(home),
        "now_epoch": int(now_epoch),
        "summary": summary,
        "feed_statuses": feed_statuses,
        "queries": queries,
        "reporters": reporters,
        "sources": sources,
        "disputes": disputes,
        "rewards": rewards,
        "recent_reports": reports[-recent_limit:],
        "recent_aggregates": aggregates[-recent_limit:],
        "recent_accepted_reads": reads[-recent_limit:],
        "recent_authorizations": authorizations[-recent_limit:],
        "recent_reward_receipts": reward_receipts[-recent_limit:],
        "recent_slash_receipts": slash_receipts[-recent_limit:],
        "replay": replay,
        "authority_status": authority_status,
        "production_authority": bool(authority_status.get("production_authority") is True),
    }


def _stored_receipt_by_id(home: Path, receipt_id: str) -> tuple[str, dict[str, Any]] | None:
    candidate_id = str(receipt_id).strip()
    if not candidate_id:
        return None
    for kind in ("reports", "aggregates", "reads", "authorizations", "rewards", "slashes"):
        path = home / "receipts" / kind / f"{candidate_id.replace(':', '_')}.json"
        if path.exists():
            if kind == "authorizations":
                payload = _load_canonical_authorization_receipt(home, path)
            else:
                payload = _load_json(path)
            if isinstance(payload, dict):
                return kind, payload

    log_sources = (
        ("report", _iter_jsonl(_reports_log_path(home)), "report_id"),
        ("aggregate", _iter_jsonl(_aggregates_log_path(home)), "aggregate_id"),
        ("accepted_read", _iter_jsonl(_reads_log_path(home)), "read_id"),
        ("authorization", _authorization_rows(home), "authorization_id"),
    )
    for kind, rows, id_key in log_sources:
        for row in rows:
            if row.get(id_key) == candidate_id:
                return kind, row

    dispute = _dispute_entries(_load_disputes(home)).get(candidate_id)
    if isinstance(dispute, dict):
        return "dispute", dispute
    return None


def _dashboard_endpoint_payload(
    home: Path,
    path: str,
    *,
    now_epoch: int,
    query_params: Mapping[str, list[str]] | None = None,
) -> tuple[int, dict[str, Any]]:
    if path == "/api/oracle/verify-receipt":
        authority_status = _oracle_authority_status(home)
        production_authority = bool(authority_status.get("production_authority") is True)
        params = query_params or {}
        receipt_id = params.get("id", [""])[0]
        found = _stored_receipt_by_id(home, receipt_id)
        if found is None:
            return (
                404,
                {
                    "schema": "zeno_oracle.api_receipt_verify.v1",
                    "ok": False,
                    "error": "receipt_not_found",
                    "receipt_id": receipt_id,
                    "authority_status": authority_status,
                    "production_authority": production_authority,
                },
            )
        receipt_kind, receipt = found
        check = verify_standalone_receipt(receipt)
        return (
            200 if check.get("ok") is True else 400,
            {
                "schema": "zeno_oracle.api_receipt_verify.v1",
                "ok": check.get("ok") is True,
                "receipt_id": receipt_id,
                "stored_receipt_kind": receipt_kind,
                "receipt_check": check,
                "receipt": receipt,
                "authority_status": authority_status,
                "production_authority": production_authority,
            },
        )

    if path == "/api/oracle/authority":
        return 200, _oracle_authority_status(home)

    snapshot = _dashboard_snapshot(home, now_epoch=now_epoch)
    authority_status = snapshot["authority_status"]
    production_authority = bool(snapshot.get("production_authority") is True)
    routes: dict[str, Any] = {
        "/api/oracle/health": {
            "schema": "zeno_oracle.api_health.v1",
            "ok": True,
            "home": str(home),
            "replay_ok": snapshot["replay"]["ok"],
            "authority_status": authority_status,
            "production_authority": production_authority,
        },
        "/api/oracle/dashboard": snapshot,
        "/api/oracle/feeds": {
            "schema": "zeno_oracle.api_feeds.v1",
            "ok": True,
            "count": len(snapshot["feed_statuses"]),
            "feed_statuses": snapshot["feed_statuses"],
            "production_authority": production_authority,
        },
        "/api/oracle/queries": {
            "schema": "zeno_oracle.api_queries.v1",
            "ok": True,
            "count": len(snapshot["queries"]),
            "queries": snapshot["queries"],
            "production_authority": production_authority,
        },
        "/api/oracle/reporters": {
            "schema": "zeno_oracle.api_reporters.v1",
            "ok": True,
            "count": len(snapshot["reporters"]),
            "reporters": snapshot["reporters"],
            "production_authority": production_authority,
        },
        "/api/oracle/sources": {
            "schema": "zeno_oracle.api_sources.v1",
            "ok": True,
            "count": len(snapshot["sources"]),
            "sources": snapshot["sources"],
            "production_authority": production_authority,
        },
        "/api/oracle/disputes": {
            "schema": "zeno_oracle.api_disputes.v1",
            "ok": True,
            "count": len(snapshot["disputes"]),
            "disputes": snapshot["disputes"],
            "production_authority": production_authority,
        },
        "/api/oracle/rewards": {
            "schema": "zeno_oracle.api_rewards.v1",
            "ok": True,
            "count": len(snapshot["rewards"]),
            "rewards": snapshot["rewards"],
            "production_authority": production_authority,
        },
        "/api/oracle/aggregates": {
            "schema": "zeno_oracle.api_aggregates.v1",
            "ok": True,
            "count": len(snapshot["recent_aggregates"]),
            "aggregates": snapshot["recent_aggregates"],
            "production_authority": production_authority,
        },
        "/api/oracle/accepted-reads": {
            "schema": "zeno_oracle.api_accepted_reads.v1",
            "ok": True,
            "count": len(snapshot["recent_accepted_reads"]),
            "accepted_reads": snapshot["recent_accepted_reads"],
            "production_authority": production_authority,
        },
        "/api/oracle/authorizations": {
            "schema": "zeno_oracle.api_authorizations.v1",
            "ok": True,
            "count": len(snapshot["recent_authorizations"]),
            "authorizations": snapshot["recent_authorizations"],
            "production_authority": production_authority,
        },
        "/api/oracle/replay": {
            "schema": "zeno_oracle.api_replay.v1",
            "ok": snapshot["replay"]["ok"],
            **snapshot["replay"],
            "production_authority": production_authority,
        },
    }
    if path in routes:
        return 200, routes[path]
    return (
        404,
        {
            "schema": "zeno_oracle.api_error.v1",
            "ok": False,
            "error": "not_found",
            "path": path,
            "available_paths": sorted([*routes, "/api/oracle/authority", "/api/oracle/verify-receipt"]),
            "production_authority": False,
        },
    )


def _api_command_error(message: str) -> tuple[int, dict[str, Any]]:
    return (
        400,
        {
            "schema": "zeno_oracle.api_command_error.v1",
            "ok": False,
            "error": message,
            "production_authority": False,
        },
    )


def _command_json(func: Any, namespace: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    stdout = io.StringIO()
    try:
        with contextlib.redirect_stdout(stdout):
            rc = int(func(namespace))
    except (SystemExit, argparse.ArgumentTypeError, ValueError, TypeError) as exc:
        return _api_command_error(str(exc))
    text = stdout.getvalue().strip()
    if not text:
        payload: dict[str, Any] = {"schema": SCHEMA, "ok": rc == 0, "production_authority": False}
    else:
        try:
            payload = _strict_json_loads(text)
        except json.JSONDecodeError:
            payload = {
                "schema": "zeno_oracle.api_command_result.v1",
                "ok": rc == 0,
                "stdout": text,
                "production_authority": False,
            }
    return (200 if rc == 0 else 400, payload)


def _list_payload(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, list):
        return [str(item) for item in value]
    return [str(value)]


def _write_endpoint_payload(home: Path, path: str, body: Mapping[str, Any]) -> tuple[int, dict[str, Any]]:
    if path == "/api/oracle/authority/exercise/evaluate":
        payload = _oracle_authority_exercise_report(home, body)
        return (200 if payload.get("ok") is True else 400, payload)
    if path == "/api/oracle/identity/create":
        return _command_json(
            cmd_identity_create,
            argparse.Namespace(home=str(home), force=bool(body.get("force", False)), json=True),
        )
    if path == "/api/oracle/reporter/register":
        return _command_json(
            cmd_reporter_register,
            argparse.Namespace(
                home=str(home),
                display_name=str(body.get("display_name", "local reporter")),
                control_group_id=body.get("control_group_id"),
                query_id=_list_payload(body.get("query_ids", body.get("query_id"))),
                required_bond_e8=int(body.get("required_bond_e8", DEFAULT_REQUIRED_BOND_E8)),
                bond_asset=str(body.get("bond_asset", "ZORACLE")),
                epoch=body.get("epoch"),
                force=bool(body.get("force", False)),
                json=True,
            ),
        )
    if path == "/api/oracle/reporter/bond":
        return _command_json(
            cmd_reporter_bond,
            argparse.Namespace(
                home=str(home),
                amount_e8=str(body.get("amount_e8", "")),
                asset=str(body.get("asset", "ZORACLE")),
                json=True,
            ),
        )
    if path == "/api/oracle/query/register":
        return _command_json(
            cmd_query_register,
            argparse.Namespace(
                home=str(home),
                query_type=str(body.get("query_type", "spot_price")),
                base_asset=str(body.get("base_asset", "")),
                quote_asset=str(body.get("quote_asset", "")),
                feed_id=body.get("feed_id"),
                asset_class=str(body.get("asset_class", "crypto")),
                jurisdiction=str(body.get("jurisdiction", "global")),
                market_hours_policy_id=str(body.get("market_hours_policy_id", "always-open-v1")),
                valuation_policy_id=str(body.get("valuation_policy_id", "spot-observed-v1")),
                scale=int(body.get("scale", 100_000_000)),
                evidence_floor=str(body.get("evidence_floor", "O3")),
                freshness_window_epochs=int(body.get("freshness_window_epochs", 3)),
                min_reporters=int(body.get("min_reporters", 3)),
                max_deviation_bps=int(body.get("max_deviation_bps", 100)),
                high_uncertainty_confidence_e8=int(body.get("high_uncertainty_confidence_e8", 1_000_000)),
                source_policy_id=str(body.get("source_policy_id", "source-policy:declared-diverse-v1")),
                report_reward_e8=int(body.get("report_reward_e8", DEFAULT_REPORT_REWARD_E8)),
                reward_budget_e8=int(body.get("reward_budget_e8", 0)),
                dispute_bond_e8=int(body.get("dispute_bond_e8", DEFAULT_DISPUTE_BOND_E8)),
                default_slash_e8=int(body.get("default_slash_e8", DEFAULT_SLASH_E8)),
                query_id=body.get("query_id"),
                force=bool(body.get("force", False)),
                json=True,
            ),
        )
    if path == "/api/oracle/query/fund":
        return _command_json(
            cmd_query_fund,
            argparse.Namespace(
                home=str(home),
                query_id=str(body.get("query_id", "")),
                amount_e8=str(body.get("amount_e8", "")),
                json=True,
            ),
        )
    if path == "/api/oracle/source/register":
        return _command_json(
            cmd_source_register,
            argparse.Namespace(
                home=str(home),
                source_id=str(body.get("source_id", "")),
                source_kind=str(body.get("source_kind", "manual")),
                operator_id=body.get("operator_id"),
                control_group_id=body.get("control_group_id"),
                venue_id=body.get("venue_id"),
                data_family_id=str(body.get("data_family_id", "price:spot")),
                transport_id=str(body.get("transport_id", "transport:manual")),
                jurisdiction=str(body.get("jurisdiction", "global")),
                asset_class=_list_payload(body.get("asset_classes", body.get("asset_class"))),
                query_id=_list_payload(body.get("query_ids", body.get("query_id"))),
                assurance_class=str(body.get("assurance_class", "S1")),
                epoch=body.get("epoch"),
                force=bool(body.get("force", False)),
                json=True,
            ),
        )
    if path == "/api/oracle/rewards/pay":
        return _command_json(
            cmd_rewards_pay,
            argparse.Namespace(
                home=str(home),
                reporter_id=body.get("reporter_id"),
                amount_e8=body.get("amount_e8"),
                json=True,
            ),
        )
    if path == "/api/oracle/dispute/open":
        return _command_json(
            cmd_dispute_open,
            argparse.Namespace(
                home=str(home),
                report_id=str(body.get("report_id", "")),
                reporter_id=str(body.get("reporter_id", "")),
                bond_e8=str(body.get("bond_e8", DEFAULT_DISPUTE_BOND_E8)),
                reason=str(body.get("reason", "local-api-dispute")),
                epoch=body.get("epoch"),
                dispute_id=body.get("dispute_id"),
                force=bool(body.get("force", False)),
                json=True,
            ),
        )
    if path == "/api/oracle/dispute/resolve":
        return _command_json(
            cmd_dispute_resolve,
            argparse.Namespace(
                home=str(home),
                dispute_id=str(body.get("dispute_id", "")),
                outcome=str(body.get("outcome", "")),
                slash_e8=body.get("slash_e8"),
                epoch=body.get("epoch"),
                force=bool(body.get("force", False)),
                json=True,
            ),
        )
    if path == "/api/oracle/aggregate/build":
        return _command_json(
            cmd_aggregate_build,
            argparse.Namespace(
                home=str(home),
                query_id=str(body.get("query_id", "")),
                epoch=body.get("epoch"),
                json=True,
            ),
        )
    if path == "/api/oracle/read/accept":
        return _command_json(
            cmd_read_accept,
            argparse.Namespace(
                home=str(home),
                aggregate_id=str(body.get("aggregate_id", "")),
                consumer_module=str(body.get("consumer_module", "zenodex.zusd")),
                profile_id=str(body.get("profile_id", "critical-zusd-v1")),
                json=True,
            ),
        )
    if path in {
        "/api/oracle/authorization/build",
        "/api/oracle/authorization/build-exact",
    }:
        exact_runtime_required = path.endswith("/build-exact")
        if exact_runtime_required:
            if type(body) is not dict:
                return _api_command_error("exact authorization request must be an exact object")
            if any(type(key) is not str for key in body):
                return _api_command_error(
                    "exact authorization request field names must be exact strings"
                )
            allowed_exact_fields = {
                "read_id",
                "runtime_action",
                "expected_receipt_graph_root",
                "min_evidence_class",
                "economic_envelope",
            }
            unknown_fields = sorted(set(body) - allowed_exact_fields)
            if unknown_fields:
                return _api_command_error(
                    "exact authorization request has unknown fields: "
                    + ", ".join(unknown_fields)
                )
            if "economic_envelope" not in body:
                return _api_command_error(
                    "economic_envelope is required for exact authorization build"
                )
        return _command_json(
            cmd_authorization_build,
            argparse.Namespace(
                home=str(home),
                read_id=str(body.get("read_id", "")),
                action_kind=str(body.get("action_kind", "")),
                action_id=str(body.get("action_id", "")),
                action_facts_hash=str(body.get("action_facts_hash", "")),
                pre_state_hash=str(body.get("pre_state_hash", "")),
                now_epoch=body.get("now_epoch"),
                runtime_action=body.get("runtime_action"),
                require_runtime_action=exact_runtime_required,
                expected_receipt_graph_root=body.get("expected_receipt_graph_root"),
                require_expected_receipt_graph_root=exact_runtime_required,
                min_evidence_class=str(body.get("min_evidence_class", "O3")),
                economic_envelope_id=str(body.get("economic_envelope_id", "econ:local-dev-v1")),
                economic_envelope=body.get("economic_envelope"),
                require_economic_envelope=exact_runtime_required,
                json=True,
            ),
        )
    if path == "/api/oracle/report/submit":
        return _command_json(
            cmd_report_submit,
            argparse.Namespace(
                home=str(home),
                query_id=str(body.get("query_id", "")),
                price_e8=str(body.get("price_e8", "")),
                source_observed_epoch=str(body.get("source_observed_epoch", "")),
                reported_epoch=body.get("reported_epoch"),
                source_id=str(body.get("source_id", "source:manual")),
                reward_e8=body.get("reward_e8"),
                out=None,
                json=True,
            ),
        )
    return (
        404,
        {
            "schema": "zeno_oracle.api_error.v1",
            "ok": False,
            "error": "not_found",
            "path": path,
            "available_write_paths": [
                "/api/oracle/identity/create",
                "/api/oracle/reporter/register",
                "/api/oracle/reporter/bond",
                "/api/oracle/query/register",
                "/api/oracle/query/fund",
                "/api/oracle/source/register",
                "/api/oracle/rewards/pay",
                "/api/oracle/dispute/open",
                "/api/oracle/dispute/resolve",
                "/api/oracle/aggregate/build",
                "/api/oracle/read/accept",
                "/api/oracle/authorization/build",
                "/api/oracle/authorization/build-exact",
                "/api/oracle/report/submit",
            ],
            "production_authority": False,
        },
    )


def cmd_dashboard_snapshot(args: argparse.Namespace) -> int:
    home = _home(args)
    now_epoch = int(args.now_epoch if args.now_epoch is not None else time.time())
    result = _dashboard_snapshot(home, now_epoch=now_epoch)
    if args.out:
        _write_json(Path(args.out), result)
    _emit(result, json_out=args.json)
    return 0 if result.get("ok") is True else 2


def cmd_serve(args: argparse.Namespace) -> int:
    from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
    from urllib.parse import parse_qs, urlparse

    home = _home(args)
    host = str(args.host)
    port = int(args.port)
    state_lock = threading.RLock()

    class OracleHandler(BaseHTTPRequestHandler):
        server_version = "ZenoOracleLocal/0.1"

        def log_message(self, format: str, *format_args: object) -> None:
            if args.quiet:
                return
            super().log_message(format, *format_args)

        def _send_json(self, status: int, payload: Mapping[str, Any]) -> None:
            body = json.dumps(payload, sort_keys=True, indent=2).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("Access-Control-Allow-Origin", args.cors_origin)
            self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
            self.send_header("Access-Control-Allow-Headers", "Content-Type")
            self.end_headers()
            self.wfile.write(body)

        def do_OPTIONS(self) -> None:
            self._send_json(200, {"schema": "zeno_oracle.api_options.v1", "ok": True})

        def do_GET(self) -> None:
            parsed = urlparse(self.path)
            now_epoch = int(args.now_epoch if args.now_epoch is not None else time.time())
            try:
                with state_lock:
                    status, payload = _dashboard_endpoint_payload(
                        home,
                        parsed.path,
                        now_epoch=now_epoch,
                        query_params=parse_qs(parsed.query),
                    )
            except Exception as exc:
                status, payload = (
                    500,
                    {
                        "schema": "zeno_oracle.api_error.v1",
                        "ok": False,
                        "error": f"internal_error: {exc}",
                        "production_authority": False,
                    },
                )
            self._send_json(status, payload)

        def do_POST(self) -> None:
            parsed = urlparse(self.path)
            if not args.allow_writes:
                self._send_json(
                    403,
                    {
                        "schema": "zeno_oracle.api_error.v1",
                        "ok": False,
                        "error": "write_api_disabled",
                        "hint": "restart zenodex-oracle serve with --allow-writes for local operator writes",
                        "production_authority": False,
                    },
                )
                return
            try:
                content_length = int(self.headers.get("Content-Length", "0"))
            except ValueError:
                content_length = 0
            if content_length <= 0 or content_length > 65_536:
                self._send_json(
                    400,
                    {
                        "schema": "zeno_oracle.api_error.v1",
                        "ok": False,
                        "error": "invalid_content_length",
                        "production_authority": False,
                    },
                )
                return
            try:
                body = _strict_json_loads(
                    self.rfile.read(content_length).decode("utf-8")
                )
            except Exception as exc:
                self._send_json(
                    400,
                    {
                        "schema": "zeno_oracle.api_error.v1",
                        "ok": False,
                        "error": f"invalid_json: {exc}",
                        "production_authority": False,
                    },
                )
                return
            if not isinstance(body, Mapping):
                self._send_json(
                    400,
                    {
                        "schema": "zeno_oracle.api_error.v1",
                        "ok": False,
                        "error": "request body must be a JSON object",
                        "production_authority": False,
                    },
                )
                return
            try:
                with state_lock:
                    status, payload = _write_endpoint_payload(home, parsed.path, body)
            except Exception as exc:
                status, payload = (
                    500,
                    {
                        "schema": "zeno_oracle.api_error.v1",
                        "ok": False,
                        "error": f"internal_error: {exc}",
                        "production_authority": False,
                    },
                )
            self._send_json(status, payload)

    server = ThreadingHTTPServer((host, port), OracleHandler)
    actual_port = int(server.server_address[1])
    authority_status = _oracle_authority_status(home)
    ready = {
        "schema": SCHEMA,
        "ok": True,
        "home": str(home),
        "url": f"http://{host}:{actual_port}",
        "paths": [
            "/api/oracle/health",
            "/api/oracle/authority",
            "/api/oracle/dashboard",
            "/api/oracle/feeds",
            "/api/oracle/reporters",
            "/api/oracle/sources",
            "/api/oracle/disputes",
            "/api/oracle/rewards",
            "/api/oracle/aggregates",
            "/api/oracle/accepted-reads",
            "/api/oracle/authorizations",
            "/api/oracle/replay",
        ],
        "write_paths_enabled": bool(args.allow_writes),
        "write_paths": [
            "/api/oracle/authority/exercise/evaluate",
            "/api/oracle/identity/create",
            "/api/oracle/reporter/register",
            "/api/oracle/reporter/bond",
            "/api/oracle/query/register",
            "/api/oracle/query/fund",
            "/api/oracle/source/register",
            "/api/oracle/rewards/pay",
            "/api/oracle/dispute/open",
            "/api/oracle/dispute/resolve",
            "/api/oracle/aggregate/build",
            "/api/oracle/read/accept",
            "/api/oracle/authorization/build",
            "/api/oracle/authorization/build-exact",
            "/api/oracle/report/submit",
        ] if args.allow_writes else [],
        "authority_status": authority_status,
        "production_authority": bool(authority_status.get("production_authority") is True),
    }
    print(json.dumps(ready, sort_keys=True), flush=True)
    try:
        if args.once:
            with contextlib.suppress(Exception):
                server.handle_request()
        else:
            server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="zenodex-oracle")
    parser.add_argument("--json", action="store_true", help="emit JSON output")
    sub = parser.add_subparsers(dest="cmd", required=True)

    version = sub.add_parser("version", help="show version/build information")
    version.set_defaults(func=cmd_version)

    init = sub.add_parser("init", help="create local Oracle home/config directories")
    init.add_argument("--home", default=str(DEFAULT_HOME))
    init.add_argument("--force", action="store_true")
    init.set_defaults(func=cmd_init)

    identity = sub.add_parser("identity", help="manage local reporter identity")
    identity_sub = identity.add_subparsers(dest="identity_cmd", required=True)
    identity_create = identity_sub.add_parser("create", help="create a local dev reporter identity")
    identity_create.add_argument("--home", default=str(DEFAULT_HOME))
    identity_create.add_argument("--force", action="store_true")
    identity_create.set_defaults(func=cmd_identity_create)
    identity_show = identity_sub.add_parser("show", help="show public reporter identity")
    identity_show.add_argument("--home", default=str(DEFAULT_HOME))
    identity_show.set_defaults(func=cmd_identity_show)

    reporter = sub.add_parser("reporter", help="manage local reporter registry state")
    reporter_sub = reporter.add_subparsers(dest="reporter_cmd", required=True)
    reporter_register = reporter_sub.add_parser("register", help="register the local identity as a reporter")
    reporter_register.add_argument("--home", default=str(DEFAULT_HOME))
    reporter_register.add_argument("--display-name", default="local reporter")
    reporter_register.add_argument("--control-group-id")
    reporter_register.add_argument("--query-id", action="append", default=[])
    reporter_register.add_argument("--required-bond-e8", type=int, default=DEFAULT_REQUIRED_BOND_E8)
    reporter_register.add_argument("--bond-asset", default="ZORACLE")
    reporter_register.add_argument("--epoch", type=int)
    reporter_register.add_argument("--force", action="store_true")
    reporter_register.set_defaults(func=cmd_reporter_register)
    reporter_bond = reporter_sub.add_parser("bond", help="add local reporter bond")
    reporter_bond.add_argument("--home", default=str(DEFAULT_HOME))
    reporter_bond.add_argument("--amount-e8", required=True)
    reporter_bond.add_argument("--asset", default="ZORACLE")
    reporter_bond.set_defaults(func=cmd_reporter_bond)
    reporter_show = reporter_sub.add_parser("show", help="show local reporter registry entry")
    reporter_show.add_argument("--home", default=str(DEFAULT_HOME))
    reporter_show.add_argument("--reporter-id")
    reporter_show.set_defaults(func=cmd_reporter_show)
    reporter_list = reporter_sub.add_parser("list", help="list local reporter registry entries")
    reporter_list.add_argument("--home", default=str(DEFAULT_HOME))
    reporter_list.add_argument("--active-only", action="store_true")
    reporter_list.add_argument("--query-id")
    reporter_list.set_defaults(func=cmd_reporter_list)
    reporter_deactivate = reporter_sub.add_parser("deactivate", help="deactivate a local reporter")
    reporter_deactivate.add_argument("--home", default=str(DEFAULT_HOME))
    reporter_deactivate.add_argument("--reporter-id")
    reporter_deactivate.add_argument("--epoch", type=int)
    reporter_deactivate.set_defaults(func=cmd_reporter_deactivate)

    source = sub.add_parser("source", help="manage local source registry state")
    source_sub = source.add_subparsers(dest="source_cmd", required=True)
    source_register = source_sub.add_parser("register", help="register a local oracle data source")
    source_register.add_argument("--home", default=str(DEFAULT_HOME))
    source_register.add_argument("--source-id", required=True)
    source_register.add_argument("--source-kind", choices=SOURCE_KINDS, default="manual")
    source_register.add_argument("--operator-id")
    source_register.add_argument("--control-group-id")
    source_register.add_argument("--venue-id")
    source_register.add_argument("--data-family-id", default="price:spot")
    source_register.add_argument("--transport-id", default="transport:manual")
    source_register.add_argument("--jurisdiction", default="global")
    source_register.add_argument("--asset-class", choices=ASSET_CLASSES, action="append", default=[])
    source_register.add_argument("--query-id", action="append", default=[])
    source_register.add_argument("--assurance-class", choices=SOURCE_ASSURANCE_CLASSES, default="S1")
    source_register.add_argument("--epoch", type=int)
    source_register.add_argument("--force", action="store_true")
    source_register.set_defaults(func=cmd_source_register)
    source_list = source_sub.add_parser("list", help="list local source registry entries")
    source_list.add_argument("--home", default=str(DEFAULT_HOME))
    source_list.add_argument("--active-only", action="store_true")
    source_list.add_argument("--asset-class", choices=ASSET_CLASSES)
    source_list.add_argument("--query-id")
    source_list.set_defaults(func=cmd_source_list)
    source_show = source_sub.add_parser("show", help="show one local source registry entry")
    source_show.add_argument("--home", default=str(DEFAULT_HOME))
    source_show.add_argument("--source-id", required=True)
    source_show.set_defaults(func=cmd_source_show)
    source_deactivate = source_sub.add_parser("deactivate", help="deactivate a local source")
    source_deactivate.add_argument("--home", default=str(DEFAULT_HOME))
    source_deactivate.add_argument("--source-id", required=True)
    source_deactivate.add_argument("--epoch", type=int)
    source_deactivate.set_defaults(func=cmd_source_deactivate)

    query = sub.add_parser("query", help="inspect query registries")
    query_sub = query.add_subparsers(dest="query_cmd", required=True)
    query_register = query_sub.add_parser("register", help="register a local spot-price query/feed")
    query_register.add_argument("--home", default=str(DEFAULT_HOME))
    query_register.add_argument(
        "--query-type",
        choices=("spot_price", "index_price", "nav_price", "settlement_price"),
        default="spot_price",
    )
    query_register.add_argument("--base-asset", required=True)
    query_register.add_argument("--quote-asset", required=True)
    query_register.add_argument("--feed-id")
    query_register.add_argument("--asset-class", choices=ASSET_CLASSES, default="crypto")
    query_register.add_argument("--jurisdiction", default="global")
    query_register.add_argument("--market-hours-policy-id", default="always-open-v1")
    query_register.add_argument("--valuation-policy-id", default="spot-observed-v1")
    query_register.add_argument("--scale", type=int, default=100_000_000)
    query_register.add_argument("--evidence-floor", default="O3")
    query_register.add_argument("--freshness-window-epochs", type=int, default=3)
    query_register.add_argument("--min-reporters", type=int, default=3)
    query_register.add_argument("--max-deviation-bps", type=int, default=100)
    query_register.add_argument("--high-uncertainty-confidence-e8", type=int, default=1_000_000)
    query_register.add_argument("--source-policy-id", default="source-policy:declared-diverse-v1")
    query_register.add_argument("--report-reward-e8", type=int, default=DEFAULT_REPORT_REWARD_E8)
    query_register.add_argument("--reward-budget-e8", type=int, default=0)
    query_register.add_argument("--dispute-bond-e8", type=int, default=DEFAULT_DISPUTE_BOND_E8)
    query_register.add_argument("--default-slash-e8", type=int, default=DEFAULT_SLASH_E8)
    query_register.add_argument("--query-id")
    query_register.add_argument("--force", action="store_true")
    query_register.set_defaults(func=cmd_query_register)
    query_fund = query_sub.add_parser("fund", help="add local reward budget to a query/feed")
    query_fund.add_argument("--home", default=str(DEFAULT_HOME))
    query_fund.add_argument("--query-id", required=True)
    query_fund.add_argument("--amount-e8", required=True)
    query_fund.set_defaults(func=cmd_query_fund)
    query_list = query_sub.add_parser("list", help="list query registry entries")
    query_list.add_argument("--home", default=str(DEFAULT_HOME))
    query_list.add_argument("--registry")
    query_list.set_defaults(func=cmd_query_list)
    query_show = query_sub.add_parser("show", help="show one query registry entry")
    query_show.add_argument("--home", default=str(DEFAULT_HOME))
    query_show.add_argument("--registry")
    query_show.add_argument("--query-id", required=True)
    query_show.set_defaults(func=cmd_query_show)
    query_status = query_sub.add_parser("status", help="show local feed freshness/dispute/uncertainty labels")
    query_status.add_argument("--home", default=str(DEFAULT_HOME))
    query_status.add_argument("--query-id")
    query_status.add_argument("--all", action="store_true")
    query_status.add_argument("--now-epoch", type=int)
    query_status.set_defaults(func=cmd_query_status)

    report = sub.add_parser("report", help="build local report artifacts")
    report_sub = report.add_subparsers(dest="report_cmd", required=True)
    dry_run = report_sub.add_parser("dry-run", help="build a deterministic unsigned report preview")
    dry_run.add_argument("--query-id", required=True)
    dry_run.add_argument("--price-e8", required=True)
    dry_run.add_argument("--source-observed-epoch", required=True)
    dry_run.add_argument("--reported-epoch", type=int)
    dry_run.add_argument("--reporter-id", required=True)
    dry_run.add_argument("--source-id", required=True)
    dry_run.add_argument("--out")
    dry_run.set_defaults(func=cmd_report_dry_run)
    submit = report_sub.add_parser("submit", help="submit a local signed report and update rewards")
    submit.add_argument("--home", default=str(DEFAULT_HOME))
    submit.add_argument("--query-id", required=True)
    submit.add_argument("--price-e8", required=True)
    submit.add_argument("--source-observed-epoch", required=True)
    submit.add_argument("--reported-epoch", type=int)
    submit.add_argument("--source-id", required=True)
    submit.add_argument("--reward-e8", type=int)
    submit.add_argument("--out")
    submit.set_defaults(func=cmd_report_submit)

    aggregate = sub.add_parser("aggregate", help="build local aggregate receipts")
    aggregate_sub = aggregate.add_subparsers(dest="aggregate_cmd", required=True)
    aggregate_build = aggregate_sub.add_parser("build", help="build a deterministic aggregate from local reports")
    aggregate_build.add_argument("--home", default=str(DEFAULT_HOME))
    aggregate_build.add_argument("--query-id", required=True)
    aggregate_build.add_argument("--epoch", type=int)
    aggregate_build.set_defaults(func=cmd_aggregate_build)

    read = sub.add_parser("read", help="build local accepted-read receipts")
    read_sub = read.add_subparsers(dest="read_cmd", required=True)
    read_accept = read_sub.add_parser("accept", help="accept a local aggregate for a consumer profile")
    read_accept.add_argument("--home", default=str(DEFAULT_HOME))
    read_accept.add_argument("--aggregate-id", required=True)
    read_accept.add_argument("--consumer-module", required=True)
    read_accept.add_argument("--profile-id", required=True)
    read_accept.set_defaults(func=cmd_read_accept)

    authorization = sub.add_parser("authorization", help="build typed OracleAuthorization bundles")
    authorization_sub = authorization.add_subparsers(dest="authorization_cmd", required=True)
    authorization_build = authorization_sub.add_parser(
        "build",
        help="bind an accepted read to exact runtime action facts",
    )
    authorization_build.add_argument("--home", default=str(DEFAULT_HOME))
    authorization_build.add_argument("--read-id", required=True)
    authorization_build.add_argument("--action-kind", required=True)
    authorization_build.add_argument("--action-id", required=True)
    authorization_build.add_argument("--action-facts-hash", required=True)
    authorization_build.add_argument("--pre-state-hash", required=True)
    authorization_build.add_argument("--now-epoch", type=int)
    authorization_build.add_argument("--min-evidence-class", default="O3")
    authorization_build.add_argument("--economic-envelope-id", default="econ:local-dev-v1")
    authorization_build.set_defaults(func=cmd_authorization_build)

    rewards = sub.add_parser("rewards", help="inspect local reporter rewards")
    rewards_sub = rewards.add_subparsers(dest="rewards_cmd", required=True)
    rewards_inspect = rewards_sub.add_parser("inspect", help="show pending and paid local rewards")
    rewards_inspect.add_argument("--home", default=str(DEFAULT_HOME))
    rewards_inspect.add_argument("--reporter-id")
    rewards_inspect.set_defaults(func=cmd_rewards_inspect)
    rewards_pay = rewards_sub.add_parser("pay", help="move pending local rewards into paid rewards")
    rewards_pay.add_argument("--home", default=str(DEFAULT_HOME))
    rewards_pay.add_argument("--reporter-id")
    rewards_pay.add_argument("--amount-e8", type=int)
    rewards_pay.set_defaults(func=cmd_rewards_pay)

    dispute = sub.add_parser("dispute", help="manage local report disputes and slashes")
    dispute_sub = dispute.add_subparsers(dest="dispute_cmd", required=True)
    dispute_open = dispute_sub.add_parser("open", help="open a local dispute against a report")
    dispute_open.add_argument("--home", default=str(DEFAULT_HOME))
    dispute_open.add_argument("--report-id", required=True)
    dispute_open.add_argument("--reporter-id", required=True)
    dispute_open.add_argument("--bond-e8", default=str(DEFAULT_DISPUTE_BOND_E8))
    dispute_open.add_argument("--reason", required=True)
    dispute_open.add_argument("--epoch", type=int)
    dispute_open.add_argument("--dispute-id")
    dispute_open.add_argument("--force", action="store_true")
    dispute_open.set_defaults(func=cmd_dispute_open)
    dispute_list = dispute_sub.add_parser("list", help="list local disputes")
    dispute_list.add_argument("--home", default=str(DEFAULT_HOME))
    dispute_list.add_argument("--status")
    dispute_list.add_argument("--reporter-id")
    dispute_list.set_defaults(func=cmd_dispute_list)
    dispute_show = dispute_sub.add_parser("show", help="show one local dispute")
    dispute_show.add_argument("--home", default=str(DEFAULT_HOME))
    dispute_show.add_argument("--dispute-id", required=True)
    dispute_show.set_defaults(func=cmd_dispute_show)
    dispute_resolve = dispute_sub.add_parser("resolve", help="resolve a local dispute")
    dispute_resolve.add_argument("--home", default=str(DEFAULT_HOME))
    dispute_resolve.add_argument("--dispute-id", required=True)
    dispute_resolve.add_argument("--outcome", choices=("upheld", "rejected"), required=True)
    dispute_resolve.add_argument("--slash-e8", type=int)
    dispute_resolve.add_argument("--epoch", type=int)
    dispute_resolve.add_argument("--force", action="store_true")
    dispute_resolve.set_defaults(func=cmd_dispute_resolve)

    verify = sub.add_parser("verify", help="run deterministic verifier surfaces")
    verify_sub = verify.add_subparsers(dest="verify_cmd", required=True)
    verify_auth = verify_sub.add_parser("authorization", help="verify typed OracleAuthorization binding")
    verify_auth.add_argument("payload")
    verify_auth.add_argument("--out")
    verify_auth.set_defaults(func=cmd_verify_authorization)
    verify_evidence = verify_sub.add_parser("evidence", help="run internal Oracle MVP evidence replay")
    verify_evidence.add_argument("--skip-lean", action="store_true")
    verify_evidence.set_defaults(func=cmd_verify_evidence)
    verify_local = verify_sub.add_parser("local-state", help="replay local reporter reports/rewards")
    verify_local.add_argument("--home", default=str(DEFAULT_HOME))
    verify_local.add_argument("--out")
    verify_local.set_defaults(func=cmd_verify_local_state)
    verify_receipt = verify_sub.add_parser("receipt", help="verify one standalone Oracle receipt JSON file")
    verify_receipt.add_argument("payload")
    verify_receipt.add_argument("--out")
    verify_receipt.set_defaults(func=cmd_verify_receipt)

    sample_bundle_parser = sub.add_parser(
        "sample-bundle",
        help="emit a minimal accepted public Oracle receipt bundle",
    )
    sample_bundle_parser.add_argument("--output", help="optional output path for the sample bundle JSON")
    sample_bundle_parser.set_defaults(func=cmd_sample_bundle)

    validator = sub.add_parser("validator", help="validator-oriented deterministic replay commands")
    validator_sub = validator.add_subparsers(dest="validator_cmd", required=True)
    validator_replay = validator_sub.add_parser("replay", help="replay local Oracle state")
    validator_replay.add_argument("--home", default=str(DEFAULT_HOME))
    validator_replay.add_argument("--out")
    validator_replay.set_defaults(func=cmd_verify_local_state)
    validator_auth = validator_sub.add_parser("authorization", help="verify typed OracleAuthorization binding")
    validator_auth.add_argument("payload")
    validator_auth.add_argument("--out")
    validator_auth.set_defaults(func=cmd_verify_authorization)
    validator_receipt = validator_sub.add_parser("receipt", help="verify one standalone Oracle receipt JSON file")
    validator_receipt.add_argument("payload")
    validator_receipt.add_argument("--out")
    validator_receipt.set_defaults(func=cmd_verify_receipt)
    validator_evidence = validator_sub.add_parser("evidence", help="run internal Oracle MVP evidence replay")
    validator_evidence.add_argument("--skip-lean", action="store_true")
    validator_evidence.set_defaults(func=cmd_verify_evidence)

    dashboard = sub.add_parser("dashboard", help="emit dashboard-oriented Oracle state snapshots")
    dashboard_sub = dashboard.add_subparsers(dest="dashboard_cmd", required=True)
    dashboard_snapshot = dashboard_sub.add_parser("snapshot", help="emit one local dashboard JSON snapshot")
    dashboard_snapshot.add_argument("--home", default=str(DEFAULT_HOME))
    dashboard_snapshot.add_argument("--now-epoch", type=int)
    dashboard_snapshot.add_argument("--out")
    dashboard_snapshot.set_defaults(func=cmd_dashboard_snapshot)

    authority = sub.add_parser("authority", help="inspect or provision Oracle production authority")
    authority_sub = authority.add_subparsers(dest="authority_cmd", required=True)
    authority_status = authority_sub.add_parser("status", help="show production-authority preflight status")
    authority_status.add_argument("--home", default=str(DEFAULT_HOME))
    authority_status.add_argument("--out")
    authority_status.set_defaults(func=cmd_authority_status)
    authority_provision = authority_sub.add_parser(
        "provision-profile",
        help="write authority/production_authority_profile.json from public key and signer policy files",
    )
    authority_provision.add_argument("--home", default=str(DEFAULT_HOME))
    authority_provision.add_argument("--authority-id", required=True)
    authority_provision.add_argument("--chain-id", required=True)
    authority_provision.add_argument("--stage", choices=("devnet", "testnet", "production"), default="production")
    authority_provision.add_argument("--disabled", action="store_true")
    authority_provision.add_argument("--key-manager", required=True)
    authority_provision.add_argument("--signer-registry", required=True)
    authority_provision.add_argument("--runtime-proof-profile", required=True)
    authority_provision.add_argument("--skip-external-signer-required", action="store_true")
    authority_provision.add_argument("--skip-key-manager-required", action="store_true")
    authority_provision.add_argument("--skip-device-approval-required", action="store_true")
    authority_provision.add_argument("--skip-zk-or-proof-required", action="store_true")
    authority_provision.add_argument("--skip-oracle-receipt-replay-required", action="store_true")
    authority_provision.add_argument(
        "--signature-envelope",
        action="append",
        help="prebuilt BLS signed-artifact envelope JSON over the authority profile hash",
    )
    authority_provision.add_argument(
        "--signer-private-key",
        action="append",
        help="build a BLS signature envelope as signer_id:key_id:0x32-byte-hex",
    )
    authority_provision.add_argument("--out")
    authority_provision.add_argument("--force", action="store_true")
    authority_provision.set_defaults(func=cmd_authority_provision_profile)

    serve = sub.add_parser("serve", help="serve local ZenoOracle dashboard JSON API")
    serve.add_argument("--home", default=str(DEFAULT_HOME))
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=8787)
    serve.add_argument("--now-epoch", type=int)
    serve.add_argument("--cors-origin", default="*")
    serve.add_argument("--allow-writes", action="store_true")
    serve.add_argument("--quiet", action="store_true")
    serve.add_argument("--once", action="store_true")
    serve.set_defaults(func=cmd_serve)

    health = sub.add_parser("health", help="check local Oracle CLI setup")
    health.add_argument("--home", default=str(DEFAULT_HOME))
    health.set_defaults(func=cmd_health)
    return parser


def _dispatch_public_receipt_bundle_cli(argv: Sequence[str]) -> int | None:
    args = list(argv)
    if not args:
        return None

    if args[0] == "sample-bundle":
        parser = argparse.ArgumentParser(prog="zenodex-oracle sample-bundle")
        parser.add_argument("--output", help="optional output path for the sample bundle JSON")
        return cmd_sample_bundle(parser.parse_args(args[1:]))

    if (
        args[0] == "verify"
        and len(args) > 1
        and args[1] not in RECEIPT_BUNDLE_VERIFY_SUBCOMMANDS
        and args[1] not in {"-h", "--help"}
    ):
        parser = argparse.ArgumentParser(prog="zenodex-oracle verify")
        parser.add_argument("bundle", help="path to a receipt bundle JSON file")
        parser.add_argument("--output", help="optional output path for the verifier result JSON")
        return cmd_verify_receipt_bundle(parser.parse_args(args[1:]))

    return None


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv = list(sys.argv[1:] if argv is None else argv)
    public_bundle_rc = _dispatch_public_receipt_bundle_cli(raw_argv)
    if public_bundle_rc is not None:
        return int(public_bundle_rc)
    parser = build_parser()
    args = parser.parse_args(raw_argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
