from __future__ import annotations

import json
from typing import Any, cast

from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tools.check_zeno_ledger_two_machine_evidence import (
    EVIDENCE_SCHEMA,
    main,
    validate_two_machine_evidence_v0,
)

COMMIT = "a" * 40


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _watcher(watcher_id: str, *, last_header_hash: str) -> dict[str, object]:
    verify_report = {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "accepted",
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


def _attestations(evidence: dict[str, object]) -> list[dict[str, Any]]:
    return cast(list[dict[str, Any]], evidence["watcher_attestations"])


def _rehash_watcher(watcher: dict[str, Any]) -> None:
    body = {key: value for key, value in watcher.items() if key != "attestation_hash"}
    watcher["attestation_hash"] = hash_v0("watcher_attestation_v0", body)


def _machine(evidence: dict[str, object], label: str) -> dict[str, Any]:
    return cast(dict[str, Any], evidence[label])


def test_two_machine_evidence_accepts_complete_archive() -> None:
    report = validate_two_machine_evidence_v0(_evidence(), expected_commit=COMMIT)

    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert report["accepted_tx_count"] == 3
    assert report["rejected_tx_count"] == 1
    assert report["watcher_count"] == 2
    assert report["python_versions"] == {
        "machine_a": "3.12.3",
        "machine_b": "3.12.3",
    }
    assert report["required_evidence_fields"] == {
        "commit_sha": True,
        "latest_pushed_commit_sha": True,
        "machine_a_python_version": True,
        "machine_b_python_version": True,
        "network_config_hash": True,
        "feature_suite_hash": True,
        "common_header_hash": True,
        "accepted_tx_count": True,
        "rejected_tx_count": True,
        "token_test_result": True,
        "watcher_attestations": True,
        "machine_watcher_attestations": True,
    }


def test_two_machine_evidence_rejects_commit_mismatch() -> None:
    evidence = _evidence()
    evidence["latest_pushed_commit_sha"] = "b" * 40

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "commit_sha must equal latest_pushed_commit_sha" in report["errors"]


def test_two_machine_evidence_rejects_machine_commit_mismatch() -> None:
    evidence = _evidence()
    _machine(evidence, "machine_b")["commit_sha"] = "b" * 40

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "machine_b.commit_sha must match commit_sha" in report["errors"]


def test_two_machine_evidence_rejects_malformed_machine_python_version() -> None:
    evidence = _evidence()
    _machine(evidence, "machine_a")["python_version"] = "python-local"

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "machine_a.python_version must look like major.minor.patch" in report["errors"]


def test_two_machine_evidence_rejects_watcher_hash_tampering() -> None:
    evidence = _evidence()
    _attestations(evidence)[0]["last_app_hash"] = _root("tampered-app")

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "watcher_attestations[0] attestation_hash mismatch" in report["errors"]


def test_two_machine_evidence_rejects_watcher_header_mismatch() -> None:
    evidence = _evidence()
    evidence["common_header_hash"] = _root("different-common-header")

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "watcher_attestation last_header_hash must match common_header_hash" in report["errors"]


def test_two_machine_evidence_rejects_inverted_watcher_range_with_matching_hash() -> None:
    evidence = _evidence()
    watcher = _attestations(evidence)[0]
    watcher["from_height"] = 3
    watcher["to_height"] = 2
    watcher["checked_heights"] = [3, 2]
    _rehash_watcher(watcher)

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "watcher_attestation to_height must be greater than or equal to from_height" in report["errors"]


def test_two_machine_evidence_rejects_watcher_height_gap_with_matching_hash() -> None:
    evidence = _evidence()
    watcher = _attestations(evidence)[0]
    watcher["from_height"] = 1
    watcher["to_height"] = 3
    watcher["checked_heights"] = [1, 3]
    _rehash_watcher(watcher)

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "watcher_attestations[0].checked_heights must be contiguous" in report["errors"]


def test_two_machine_evidence_rejects_zero_accepted_transactions() -> None:
    evidence = _evidence()
    tx_counts = cast(dict[str, int], evidence["tx_counts"])
    tx_counts["accepted"] = 0

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "tx_counts.accepted must be positive" in report["errors"]


def test_two_machine_evidence_rejects_duplicate_machine_identity() -> None:
    evidence = _evidence()
    _machine(evidence, "machine_b")["machine_id"] = "machine-a"

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "machine_a.machine_id and machine_b.machine_id must differ" in report["errors"]


def test_two_machine_evidence_rejects_missing_machine_watcher_id() -> None:
    evidence = _evidence()
    _machine(evidence, "machine_b")["machine_id"] = "machine-c"

    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert report["ok"] is False
    assert "watcher_attestations missing machine watcher ids: machine-c" in report["errors"]


def test_two_machine_evidence_cli_emits_rejection_for_non_object(
    tmp_path,
    capsys,
) -> None:
    evidence_path = tmp_path / "two-machine-evidence.json"
    evidence_path.write_text(json.dumps(["not", "an", "object"]), encoding="utf-8")

    code = main([str(evidence_path), "--expected-commit", COMMIT])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 1
    assert report["ok"] is False
    assert "evidence must be an object" in report["errors"]
