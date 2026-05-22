#!/usr/bin/env python3
"""Validate archived evidence for a fresh two-machine ZenoLedger run."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_v0 import hash_v0  # noqa: E402
from src.integration.zeno_ledger_watcher import (  # noqa: E402
    WATCHER_ATTESTATION_SCHEMA_V0,
    WATCHER_ATTESTATION_STATUS_V0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.two_machine_evidence_report.v0"
EVIDENCE_SCHEMA = "zenodex.zeno_ledger.two_machine_latest_main_evidence.v0"
_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
_ROOT_RE = re.compile(r"^0x[0-9a-f]{64}$")
_PYTHON_VERSION_RE = re.compile(r"^[0-9]+\.[0-9]+\.[0-9]+(?:[a-z0-9.+-]*)?$")


def validate_two_machine_evidence_v0(
    evidence: Any,
    *,
    expected_commit: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(evidence, "evidence", errors)
    if obj.get("schema") != EVIDENCE_SCHEMA:
        errors.append("schema mismatch")

    commit_sha = _str(obj.get("commit_sha"), "commit_sha", errors)
    latest_pushed_commit_sha = _str(
        obj.get("latest_pushed_commit_sha"),
        "latest_pushed_commit_sha",
        errors,
    )
    for name, value in (
        ("commit_sha", commit_sha),
        ("latest_pushed_commit_sha", latest_pushed_commit_sha),
    ):
        if value is not None and _COMMIT_RE.fullmatch(value) is None:
            errors.append(f"{name} must be lowercase 40-hex")
    if commit_sha is not None and latest_pushed_commit_sha is not None and commit_sha != latest_pushed_commit_sha:
        errors.append("commit_sha must equal latest_pushed_commit_sha")
    if expected_commit is not None:
        if _COMMIT_RE.fullmatch(expected_commit) is None:
            errors.append("expected_commit must be lowercase 40-hex")
        elif commit_sha != expected_commit:
            errors.append("commit_sha does not match expected_commit")

    network_config_hash = _root(obj.get("network_config_hash"), "network_config_hash", errors)
    feature_suite_hash = _root(obj.get("feature_suite_hash"), "feature_suite_hash", errors)
    common_header_hash = _root(obj.get("common_header_hash"), "common_header_hash", errors)

    machine_a = _machine(obj.get("machine_a"), "machine_a", errors)
    machine_b = _machine(obj.get("machine_b"), "machine_b", errors)
    tx_counts = _mapping(obj.get("tx_counts"), "tx_counts", errors)
    accepted_tx_count = _nonnegative_int(tx_counts.get("accepted"), "tx_counts.accepted", errors)
    rejected_tx_count = _nonnegative_int(tx_counts.get("rejected"), "tx_counts.rejected", errors)
    if accepted_tx_count is not None and accepted_tx_count == 0:
        errors.append("tx_counts.accepted must be positive")
    token_test = _mapping(obj.get("token_test_result"), "token_test_result", errors)
    if token_test.get("ok") is not True:
        errors.append("token_test_result.ok must be true")
    if token_test.get("status") != "accepted":
        errors.append("token_test_result.status must be accepted")

    watchers = _watcher_attestations(obj.get("watcher_attestations"), errors)
    watcher_ids = [str(watcher.get("watcher_id")) for watcher in watchers]
    if len(set(watcher_ids)) != len(watcher_ids):
        errors.append("watcher_attestations watcher_id values must be unique")
    if len(watchers) < 2:
        errors.append("watcher_attestations must contain at least two attestations")
    for watcher in watchers:
        if common_header_hash is not None and watcher.get("last_header_hash") != common_header_hash:
            errors.append("watcher_attestation last_header_hash must match common_header_hash")
    machine_ids: list[str] = []
    for label, machine in (("machine_a", machine_a), ("machine_b", machine_b)):
        if machine is None:
            continue
        machine_id = machine.get("machine_id")
        if isinstance(machine_id, str):
            machine_ids.append(machine_id)
        if commit_sha is not None and machine.get("commit_sha") != commit_sha:
            errors.append(f"{label}.commit_sha must match commit_sha")
        if network_config_hash is not None and machine.get("network_config_hash") != network_config_hash:
            errors.append(f"{label}.network_config_hash mismatch")
        if feature_suite_hash is not None and machine.get("feature_suite_hash") != feature_suite_hash:
            errors.append(f"{label}.feature_suite_hash mismatch")
        if common_header_hash is not None and machine.get("header_hash") != common_header_hash:
            errors.append(f"{label}.header_hash mismatch")
    if len(machine_ids) == 2:
        if machine_ids[0] == machine_ids[1]:
            errors.append("machine_a.machine_id and machine_b.machine_id must differ")
        missing_watchers = sorted(set(machine_ids) - set(watcher_ids))
        if missing_watchers:
            joined = ",".join(missing_watchers)
            errors.append(f"watcher_attestations missing machine watcher ids: {joined}")
    required_evidence_fields = {
        "commit_sha": commit_sha is not None,
        "latest_pushed_commit_sha": latest_pushed_commit_sha is not None,
        "machine_a_python_version": (
            machine_a is not None and machine_a.get("python_version") is not None
        ),
        "machine_b_python_version": (
            machine_b is not None and machine_b.get("python_version") is not None
        ),
        "network_config_hash": network_config_hash is not None,
        "feature_suite_hash": feature_suite_hash is not None,
        "common_header_hash": common_header_hash is not None,
        "accepted_tx_count": accepted_tx_count is not None,
        "rejected_tx_count": rejected_tx_count is not None,
        "token_test_result": (
            isinstance(token_test, Mapping)
            and token_test.get("ok") is True
            and token_test.get("status") == "accepted"
        ),
        "watcher_attestations": len(watchers) >= 2,
        "machine_watcher_attestations": (
            len(machine_ids) == 2 and set(machine_ids).issubset(set(watcher_ids))
        ),
    }

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "required_evidence_fields": required_evidence_fields,
        "commit_sha": commit_sha,
        "network_config_hash": network_config_hash,
        "feature_suite_hash": feature_suite_hash,
        "common_header_hash": common_header_hash,
        "accepted_tx_count": accepted_tx_count,
        "rejected_tx_count": rejected_tx_count,
        "watcher_count": len(watchers),
        "python_versions": {
            "machine_a": None if machine_a is None else machine_a.get("python_version"),
            "machine_b": None if machine_b is None else machine_b.get("python_version"),
        },
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _root(value: Any, name: str, errors: list[str]) -> str | None:
    parsed = _str(value, name, errors)
    if parsed is not None and _ROOT_RE.fullmatch(parsed) is None:
        errors.append(f"{name} must be lowercase 0x-prefixed sha256 hex")
    return parsed


def _nonnegative_int(value: Any, name: str, errors: list[str]) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        errors.append(f"{name} must be a non-negative int")
        return None
    return int(value)


def _machine(value: Any, name: str, errors: list[str]) -> Mapping[str, Any] | None:
    obj = _mapping(value, name, errors)
    if not obj:
        return None
    _str(obj.get("machine_id"), f"{name}.machine_id", errors)
    commit_sha = _str(obj.get("commit_sha"), f"{name}.commit_sha", errors)
    if commit_sha is not None and _COMMIT_RE.fullmatch(commit_sha) is None:
        errors.append(f"{name}.commit_sha must be lowercase 40-hex")
    python_version = _str(obj.get("python_version"), f"{name}.python_version", errors)
    if python_version is not None and _PYTHON_VERSION_RE.fullmatch(python_version) is None:
        errors.append(f"{name}.python_version must look like major.minor.patch")
    _root(obj.get("network_config_hash"), f"{name}.network_config_hash", errors)
    _root(obj.get("feature_suite_hash"), f"{name}.feature_suite_hash", errors)
    _root(obj.get("header_hash"), f"{name}.header_hash", errors)
    return obj


def _watcher_attestations(value: Any, errors: list[str]) -> list[Mapping[str, Any]]:
    if not isinstance(value, list):
        errors.append("watcher_attestations must be a list")
        return []
    watchers: list[Mapping[str, Any]] = []
    for index, item in enumerate(value):
        watcher = _mapping(item, f"watcher_attestations[{index}]", errors)
        if not watcher:
            continue
        if watcher.get("schema") != WATCHER_ATTESTATION_SCHEMA_V0:
            errors.append(f"watcher_attestations[{index}] schema mismatch")
        if watcher.get("status") != WATCHER_ATTESTATION_STATUS_V0:
            errors.append(f"watcher_attestations[{index}] status must be range_verified")
        attestation_hash = _root(
            watcher.get("attestation_hash"),
            f"watcher_attestations[{index}].attestation_hash",
            errors,
        )
        body = {key: raw for key, raw in watcher.items() if key != "attestation_hash"}
        if attestation_hash is not None and attestation_hash != hash_v0("watcher_attestation_v0", body):
            errors.append(f"watcher_attestations[{index}] attestation_hash mismatch")
        _str(watcher.get("watcher_id"), f"watcher_attestations[{index}].watcher_id", errors)
        _str(watcher.get("verifier_ref"), f"watcher_attestations[{index}].verifier_ref", errors)
        _nonnegative_int(
            watcher.get("observed_time_ms"),
            f"watcher_attestations[{index}].observed_time_ms",
            errors,
        )
        _root(watcher.get("last_header_hash"), f"watcher_attestations[{index}].last_header_hash", errors)
        _root(watcher.get("last_post_state_root"), f"watcher_attestations[{index}].last_post_state_root", errors)
        _root(watcher.get("last_app_hash"), f"watcher_attestations[{index}].last_app_hash", errors)
        _root(watcher.get("verify_report_hash"), f"watcher_attestations[{index}].verify_report_hash", errors)
        from_height = _nonnegative_int(
            watcher.get("from_height"),
            f"watcher_attestations[{index}].from_height",
            errors,
        )
        to_height = _nonnegative_int(
            watcher.get("to_height"),
            f"watcher_attestations[{index}].to_height",
            errors,
        )
        _checked_heights(
            watcher.get("checked_heights"),
            from_height=from_height,
            to_height=to_height,
            name=f"watcher_attestations[{index}].checked_heights",
            errors=errors,
        )
        watchers.append(watcher)
    return watchers


def _checked_heights(
    value: Any,
    *,
    from_height: int | None,
    to_height: int | None,
    name: str,
    errors: list[str],
) -> None:
    if not isinstance(value, list) or not value:
        errors.append(f"{name} must be a non-empty list")
        return
    parsed: list[int] = []
    for index, item in enumerate(value):
        height = _nonnegative_int(item, f"{name}[{index}]", errors)
        if height is None:
            continue
        if parsed and height != parsed[-1] + 1:
            errors.append(f"{name} must be contiguous")
        parsed.append(height)
    if from_height is not None and to_height is not None and to_height < from_height:
        errors.append("watcher_attestation to_height must be greater than or equal to from_height")
    if parsed:
        if from_height is not None and parsed[0] != from_height:
            errors.append(f"{name} first height must equal from_height")
        if to_height is not None and parsed[-1] != to_height:
            errors.append(f"{name} last height must equal to_height")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--expected-commit")
    args = parser.parse_args(argv)

    evidence = json.loads(args.evidence.read_text(encoding="utf-8"))
    report = validate_two_machine_evidence_v0(
        evidence,
        expected_commit=args.expected_commit,
    )
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
