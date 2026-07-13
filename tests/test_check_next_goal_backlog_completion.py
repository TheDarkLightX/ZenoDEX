from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tools.check_next_goal_backlog_completion import main, run_completion_audit
from tools.check_zeno_ledger_two_machine_evidence import EVIDENCE_SCHEMA

COMMIT = "a" * 40


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _watcher(watcher_id: str, *, last_header_hash: str) -> dict[str, object]:
    verify_report = {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "range_verified",
        "mode": "replay_bound",
        "authority_scope": "replay_bound_range_v0",
        "range_verified": True,
        "header_linkage_checked": True,
        "state_continuity_checked": True,
        "state_replay_checked": True,
        "receipt_replay_checked": True,
        "config_binding_checked": True,
        "replay_config_digest": _root("replay-config"),
        "errors": [],
        "checked_heights": [1, 2],
        "last_header_hash": last_header_hash,
        "last_post_state_root": _root("post"),
        "last_app_hash": _root("app"),
    }
    return build_watcher_attestation_v0(
        verify_report=verify_report,
        watcher_id=watcher_id,
        observed_time_ms=1_778_730_000_000,
        verifier_ref="pytest",
    )


def _evidence() -> dict[str, object]:
    network_config_hash = _root("network-config")
    feature_suite_hash = _root("feature-suite")
    common_header_hash = _root("common-header")
    return {
        "schema": EVIDENCE_SCHEMA,
        "commit_sha": COMMIT,
        "latest_pushed_commit_sha": COMMIT,
        "network_config_hash": network_config_hash,
        "feature_suite_hash": feature_suite_hash,
        "common_header_hash": common_header_hash,
        "machine_a": {
            "machine_id": "machine-a",
            "commit_sha": COMMIT,
            "python_version": "3.12.3",
            "network_config_hash": network_config_hash,
            "feature_suite_hash": feature_suite_hash,
            "header_hash": common_header_hash,
        },
        "machine_b": {
            "machine_id": "machine-b",
            "commit_sha": COMMIT,
            "python_version": "3.12.3",
            "network_config_hash": network_config_hash,
            "feature_suite_hash": feature_suite_hash,
            "header_hash": common_header_hash,
        },
        "tx_counts": {
            "accepted": 3,
            "rejected": 1,
        },
        "token_test_result": {
            "ok": True,
            "status": "accepted",
            "asset": "tZENO",
        },
        "watcher_attestations": [
            _watcher("machine-a", last_header_hash=common_header_hash),
            _watcher("machine-b", last_header_hash=common_header_hash),
        ],
    }


def _write_evidence(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _item(report: dict[str, Any], item_id: str) -> dict[str, Any]:
    by_id = {item["item_id"]: item for item in report["items"]}
    return cast(dict[str, Any], by_id[item_id])


def _requirement(item: dict[str, Any], requirement_id: str) -> dict[str, Any]:
    by_id = {req["requirement_id"]: req for req in item["requirements"]}
    return cast(dict[str, Any], by_id[requirement_id])


def test_completion_audit_rejects_without_two_machine_archive() -> None:
    report = run_completion_audit(
        latest_pushed_commit_sha=COMMIT,
        two_machine_evidence_path=None,
        run_supporting_gates=False,
    )
    item = _item(report, "fresh_two_machine_latest_main_run")

    assert report["status"] == "rejected"
    assert item["status"] == "rejected"
    assert "fresh_two_machine_latest_main_run.two_machine_evidence_archive_present" in report[
        "missing_requirements"
    ]
    assert "fresh_two_machine_latest_main_run.two_machine_evidence_archive_validates" in report[
        "missing_requirements"
    ]
    assert _requirement(item, "latest_pushed_commit_sha_supplied")["ok"] is True
    assert _requirement(item, "two_machine_evidence_archive_present")["status"] == "missing"


def test_completion_audit_accepts_two_machine_subgate_for_valid_archive(tmp_path: Path) -> None:
    evidence_path = tmp_path / "two-machine-evidence.json"
    _write_evidence(evidence_path, _evidence())

    report = run_completion_audit(
        latest_pushed_commit_sha=COMMIT,
        two_machine_evidence_path=evidence_path,
        run_supporting_gates=False,
    )
    item = _item(report, "fresh_two_machine_latest_main_run")
    validation_req = _requirement(item, "two_machine_evidence_archive_validates")

    assert item["status"] == "accepted"
    assert validation_req["ok"] is True
    assert validation_req["required_evidence_fields"] == {
        "accepted_tx_count": True,
        "common_header_hash": True,
        "commit_sha": True,
        "feature_suite_hash": True,
        "latest_pushed_commit_sha": True,
        "machine_a_python_version": True,
        "machine_b_python_version": True,
        "machine_watcher_attestations": True,
        "network_config_hash": True,
        "rejected_tx_count": True,
        "token_test_result": True,
        "watcher_attestations": True,
    }
    assert report["status"] == "rejected"
    assert any(
        missing.endswith(".production_boundary_checker_accepts")
        for missing in report["missing_requirements"]
    )


def test_completion_audit_rejects_archive_missing_required_field(tmp_path: Path) -> None:
    evidence = _evidence()
    machine_b = cast(dict[str, object], evidence["machine_b"])
    del machine_b["python_version"]
    evidence_path = tmp_path / "two-machine-evidence.json"
    _write_evidence(evidence_path, evidence)

    report = run_completion_audit(
        latest_pushed_commit_sha=COMMIT,
        two_machine_evidence_path=evidence_path,
        run_supporting_gates=False,
    )
    item = _item(report, "fresh_two_machine_latest_main_run")
    validation_req = _requirement(item, "two_machine_evidence_archive_validates")

    assert item["status"] == "rejected"
    assert validation_req["ok"] is False
    assert validation_req["required_evidence_fields"]["machine_b_python_version"] is False
    assert "required_evidence_fields false: machine_b_python_version" in validation_req["errors"]


def test_completion_audit_cli_rejects_invalid_latest_commit(capsys) -> None:
    code = main(["--latest-pushed-commit-sha", "abc"])
    report = json.loads(capsys.readouterr().out)

    assert code == 1
    assert report["schema"] == "zenodex.next_goal_backlog_completion_audit.v0"
    assert "fresh_two_machine_latest_main_run.latest_pushed_commit_sha_supplied" in report[
        "missing_requirements"
    ]
