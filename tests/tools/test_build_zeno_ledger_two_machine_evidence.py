from __future__ import annotations

import json
from pathlib import Path

from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tools.build_zeno_ledger_two_machine_evidence import (
    assemble_two_machine_evidence_v0,
    main,
)
from tools.check_zeno_ledger_two_machine_evidence import (
    EVIDENCE_SCHEMA,
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


def _machine(
    machine_id: str,
    *,
    network_config_hash: str,
    feature_suite_hash: str,
    header_hash: str,
) -> dict[str, object]:
    return {
        "machine_id": machine_id,
        "commit_sha": COMMIT,
        "python_version": "3.12.3",
        "network_config_hash": network_config_hash,
        "feature_suite_hash": feature_suite_hash,
        "header_hash": header_hash,
    }


def _write(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def test_assemble_two_machine_evidence_accepts_status_aliases() -> None:
    network_config_hash = _root("network-config")
    feature_suite_hash = _root("feature-suite")
    common_header_hash = _root("common-header")
    machine_a = {
        "node_id": "machine-a",
        "commit_sha": COMMIT,
        "python_version": "3.12.3",
        "network_config_hash": network_config_hash,
        "feature_suite_hash": feature_suite_hash,
        "last_header_hash": common_header_hash,
    }
    machine_b = _machine(
        "machine-b",
        network_config_hash=network_config_hash,
        feature_suite_hash=feature_suite_hash,
        header_hash=common_header_hash,
    )

    evidence = assemble_two_machine_evidence_v0(
        machine_a_artifact=machine_a,
        machine_b_artifact=machine_b,
        token_test_result={"ok": True, "status": "accepted", "asset": "tZENO"},
        watcher_attestations=[
            _watcher("machine-a", last_header_hash=common_header_hash),
            _watcher("machine-b", last_header_hash=common_header_hash),
        ],
        accepted_tx_count=3,
        rejected_tx_count=1,
        latest_pushed_commit_sha=COMMIT,
    )
    report = validate_two_machine_evidence_v0(evidence, expected_commit=COMMIT)

    assert evidence["schema"] == EVIDENCE_SCHEMA
    assert report["ok"] is True
    assert evidence["machine_a"]["machine_id"] == "machine-a"
    assert evidence["machine_a"]["header_hash"] == common_header_hash


def test_builder_cli_writes_validated_archive(tmp_path, capsys) -> None:
    network_config_hash = _root("network-config")
    feature_suite_hash = _root("feature-suite")
    common_header_hash = _root("common-header")
    machine_a_path = tmp_path / "machine-a.json"
    machine_b_path = tmp_path / "machine-b.json"
    token_path = tmp_path / "token.json"
    watcher_a_path = tmp_path / "watcher-a.json"
    watcher_b_path = tmp_path / "watcher-b.json"
    out_path = tmp_path / "two-machine-evidence.json"
    _write(
        machine_a_path,
        _machine(
            "machine-a",
            network_config_hash=network_config_hash,
            feature_suite_hash=feature_suite_hash,
            header_hash=common_header_hash,
        ),
    )
    _write(
        machine_b_path,
        _machine(
            "machine-b",
            network_config_hash=network_config_hash,
            feature_suite_hash=feature_suite_hash,
            header_hash=common_header_hash,
        ),
    )
    _write(token_path, {"ok": True, "status": "accepted", "asset": "tZENO"})
    _write(watcher_a_path, _watcher("machine-a", last_header_hash=common_header_hash))
    _write(watcher_b_path, _watcher("machine-b", last_header_hash=common_header_hash))

    code = main(
        [
            "--machine-a",
            str(machine_a_path),
            "--machine-b",
            str(machine_b_path),
            "--token-test-result",
            str(token_path),
            "--watcher-attestation",
            str(watcher_a_path),
            "--watcher-attestation",
            str(watcher_b_path),
            "--accepted-tx-count",
            "3",
            "--rejected-tx-count",
            "1",
            "--latest-pushed-commit-sha",
            COMMIT,
            "--expected-commit",
            COMMIT,
            "--out",
            str(out_path),
        ]
    )
    build_report = json.loads(capsys.readouterr().out)
    evidence = json.loads(out_path.read_text(encoding="utf-8"))

    assert code == 0
    assert build_report["ok"] is True
    assert build_report["validation_report"]["ok"] is True
    assert evidence["schema"] == EVIDENCE_SCHEMA


def test_builder_cli_rejects_mismatched_machine_header_without_writing(tmp_path, capsys) -> None:
    network_config_hash = _root("network-config")
    feature_suite_hash = _root("feature-suite")
    common_header_hash = _root("common-header")
    machine_a_path = tmp_path / "machine-a.json"
    machine_b_path = tmp_path / "machine-b.json"
    token_path = tmp_path / "token.json"
    watcher_a_path = tmp_path / "watcher-a.json"
    watcher_b_path = tmp_path / "watcher-b.json"
    out_path = tmp_path / "two-machine-evidence.json"
    _write(
        machine_a_path,
        _machine(
            "machine-a",
            network_config_hash=network_config_hash,
            feature_suite_hash=feature_suite_hash,
            header_hash=common_header_hash,
        ),
    )
    _write(
        machine_b_path,
        _machine(
            "machine-b",
            network_config_hash=network_config_hash,
            feature_suite_hash=feature_suite_hash,
            header_hash=_root("different-header"),
        ),
    )
    _write(token_path, {"ok": True, "status": "accepted", "asset": "tZENO"})
    _write(watcher_a_path, _watcher("machine-a", last_header_hash=common_header_hash))
    _write(watcher_b_path, _watcher("machine-b", last_header_hash=common_header_hash))

    code = main(
        [
            "--machine-a",
            str(machine_a_path),
            "--machine-b",
            str(machine_b_path),
            "--token-test-result",
            str(token_path),
            "--watcher-attestation",
            str(watcher_a_path),
            "--watcher-attestation",
            str(watcher_b_path),
            "--accepted-tx-count",
            "3",
            "--rejected-tx-count",
            "1",
            "--latest-pushed-commit-sha",
            COMMIT,
            "--expected-commit",
            COMMIT,
            "--out",
            str(out_path),
        ]
    )
    build_report = json.loads(capsys.readouterr().out)

    assert code == 1
    assert out_path.exists() is False
    assert build_report["ok"] is False
    assert "machine_b.header_hash mismatch" in build_report["errors"]
