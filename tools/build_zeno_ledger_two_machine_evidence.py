#!/usr/bin/env python3
"""Build and validate a two-machine ZenoLedger evidence archive."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zeno_ledger_two_machine_evidence import (  # noqa: E402
    EVIDENCE_SCHEMA,
    validate_two_machine_evidence_v0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.two_machine_evidence_build_report.v0"

_MISSING = object()
_MACHINE_FIELD_ALIASES: dict[str, tuple[str, ...]] = {
    "machine_id": ("machine_id", "node_id", "watcher_id"),
    "commit_sha": ("commit_sha", "git_commit_sha"),
    "python_version": ("python_version",),
    "network_config_hash": ("network_config_hash",),
    "feature_suite_hash": ("feature_suite_hash",),
    "header_hash": (
        "header_hash",
        "last_header_hash",
        "latest_header_hash",
        "local_tip.header_hash",
    ),
}


def load_json_object_v0(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def write_json_v0(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def normalize_machine_artifact_v0(artifact: Mapping[str, Any], *, name: str) -> dict[str, Any]:
    """Extract the compact machine evidence fields from a host artifact."""

    if not isinstance(artifact, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return {
        field: _pick_alias(artifact, aliases)
        for field, aliases in _MACHINE_FIELD_ALIASES.items()
    }


def assemble_two_machine_evidence_v0(
    *,
    machine_a_artifact: Mapping[str, Any],
    machine_b_artifact: Mapping[str, Any],
    token_test_result: Mapping[str, Any],
    watcher_attestations: list[Mapping[str, Any]],
    accepted_tx_count: int,
    rejected_tx_count: int,
    latest_pushed_commit_sha: str,
    commit_sha: str | None = None,
) -> dict[str, Any]:
    machine_a = normalize_machine_artifact_v0(machine_a_artifact, name="machine_a")
    machine_b = normalize_machine_artifact_v0(machine_b_artifact, name="machine_b")
    archive_commit = commit_sha if commit_sha is not None else machine_a["commit_sha"]
    return {
        "schema": EVIDENCE_SCHEMA,
        "commit_sha": archive_commit,
        "latest_pushed_commit_sha": latest_pushed_commit_sha,
        "network_config_hash": machine_a["network_config_hash"],
        "feature_suite_hash": machine_a["feature_suite_hash"],
        "common_header_hash": machine_a["header_hash"],
        "machine_a": machine_a,
        "machine_b": machine_b,
        "tx_counts": {
            "accepted": accepted_tx_count,
            "rejected": rejected_tx_count,
        },
        "token_test_result": dict(token_test_result),
        "watcher_attestations": [dict(attestation) for attestation in watcher_attestations],
    }


def _pick_alias(obj: Mapping[str, Any], aliases: tuple[str, ...]) -> Any:
    for alias in aliases:
        value = _get_alias(obj, alias)
        if value is not _MISSING:
            return value
    return None


def _get_alias(obj: Mapping[str, Any], alias: str) -> Any:
    current: Any = obj
    for part in alias.split("."):
        if not isinstance(current, Mapping) or part not in current:
            return _MISSING
        current = current[part]
    return current


def _load_watchers(paths: list[Path]) -> list[Mapping[str, Any]]:
    return [load_json_object_v0(path) for path in paths]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machine-a", required=True, type=Path)
    parser.add_argument("--machine-b", required=True, type=Path)
    parser.add_argument("--token-test-result", required=True, type=Path)
    parser.add_argument("--watcher-attestation", required=True, action="append", type=Path)
    parser.add_argument("--accepted-tx-count", required=True, type=int)
    parser.add_argument("--rejected-tx-count", required=True, type=int)
    parser.add_argument("--latest-pushed-commit-sha", required=True)
    parser.add_argument("--commit-sha")
    parser.add_argument("--expected-commit")
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)

    validation_report: dict[str, Any] | None = None
    try:
        evidence = assemble_two_machine_evidence_v0(
            machine_a_artifact=load_json_object_v0(args.machine_a),
            machine_b_artifact=load_json_object_v0(args.machine_b),
            token_test_result=load_json_object_v0(args.token_test_result),
            watcher_attestations=_load_watchers(args.watcher_attestation),
            accepted_tx_count=args.accepted_tx_count,
            rejected_tx_count=args.rejected_tx_count,
            latest_pushed_commit_sha=args.latest_pushed_commit_sha,
            commit_sha=args.commit_sha,
        )
        validation_report = validate_two_machine_evidence_v0(
            evidence,
            expected_commit=args.expected_commit,
        )
        if validation_report["ok"] is True:
            write_json_v0(args.out, evidence)
            report = {
                "schema": REPORT_SCHEMA,
                "ok": True,
                "status": "accepted",
                "output_path": str(args.out),
                "evidence_schema": EVIDENCE_SCHEMA,
                "commit_sha": validation_report["commit_sha"],
                "common_header_hash": validation_report["common_header_hash"],
                "watcher_count": validation_report["watcher_count"],
                "validation_report": validation_report,
            }
        else:
            report = {
                "schema": REPORT_SCHEMA,
                "ok": False,
                "status": "rejected",
                "errors": validation_report["errors"],
                "validation_report": validation_report,
            }
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
        if validation_report is not None:
            report["validation_report"] = validation_report
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
