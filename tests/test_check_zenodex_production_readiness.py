from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tools.check_zenodex_production_readiness import (
    RELEASE_GATE_REPORT_SCHEMA,
    REQUIRED_RELEASE_GATE_CHECKS,
    build_readiness_status,
    main,
)

COMMIT = "b" * 40


def _write_json(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _root(label: str) -> str:
    return hash_v0("production_readiness_test_root", {"label": label})


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


def _write_two_machine_evidence(path: Path) -> None:
    network_config_hash = _root("network-config")
    feature_suite_hash = _root("feature-suite")
    common_header_hash = _root("common-header")
    _write_json(
        path,
        {
            "schema": "zenodex.zeno_ledger.two_machine_latest_main_evidence.v0",
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
            "tx_counts": {"accepted": 3, "rejected": 1},
            "token_test_result": {"ok": True, "status": "accepted", "asset": "tZENO"},
            "watcher_attestations": [
                _watcher("machine-a", last_header_hash=common_header_hash),
                _watcher("machine-b", last_header_hash=common_header_hash),
            ],
        },
    )


def _valid_release_smoke() -> dict[str, Any]:
    return {
        "schema": "zenodex.local_testnet.release_flow_smoke_report.v1",
        "ok": True,
        "checks": {
            "faucet_tagrs": {"ok": True},
            "zusd_collateral_deposit": {"ok": True},
            "zusd_minted_from_collateral": {"ok": True},
            "perps_collateral_deposit": {"ok": True},
            "perps_long_short_open": {"ok": True},
            "perps_settlement_cycle": {"ok": True},
            "spot_swap_tagrs_tzdex": {"ok": True},
            "status_and_header_agreement": {"ok": True},
        },
    }


def _write_public_testnet_manifest(path: Path) -> None:
    root = path.parent
    _write_json(root / "local.json", {"ok": True})
    acceptance = {
        "ok": True,
        "status": "accepted",
        "network_config_hash": "0xabc",
        "common_header_match": True,
        "live_observed": True,
    }
    _write_json(root / "external.json", acceptance)
    _write_json(root / "second.json", acceptance)
    _write_json(
        root / "phone.json",
        {
            "ok": True,
            "checks": {
                "public_ui_https_loaded": True,
                "status_page_loaded": True,
                "token_list_loaded": True,
            },
        },
    )
    _write_json(root / "release.json", _valid_release_smoke())
    (root / "residual.md").write_text(
        "fake-value public testnet. no production value. no mainnet custody. session-stable Quick Tunnel URL.\n",
        encoding="utf-8",
    )
    _write_json(
        path,
        {
            "schema": "zenodex.public_testnet_v0_1_16.evidence_manifest.v1",
            "public_config_url": "https://sample.trycloudflare.com/public_network_config.json",
            "public_config_url_posture": "session_stable_quick_tunnel",
            "stable_public_config_url": False,
            "artifacts": {
                "local_full_stack_smoke_report": "local.json",
                "external_laptop_acceptance_report": "external.json",
                "second_clean_follower_report": "second.json",
                "phone_browser_validation_report": "phone.json",
                "release_flow_transaction_smoke_report": "release.json",
                "residual_limits_statement": "residual.md",
            },
        },
    )


def _lane(report: dict[str, Any], lane_id: str) -> dict[str, Any]:
    for lane in report["lanes"]:
        if lane["lane_id"] == lane_id:
            return lane
    raise AssertionError(f"missing lane {lane_id}")


def test_missing_external_artifacts_block_without_usage_error(tmp_path: Path) -> None:
    report = build_readiness_status(
        public_testnet_manifest=tmp_path / "missing-public" / "manifest.json",
        two_machine_evidence=tmp_path / "missing-two-machine.json",
        release_gate_report=tmp_path / "missing-release.json",
        expected_commit=COMMIT,
        run_internal_gates=False,
    )

    assert report["production_ready"] is False
    assert report["production_security_claim"] is False
    assert report["status"] == "blocked"
    assert "public_testnet_v0_1_16_evidence" in report["blocked_lanes"]
    public_lane = _lane(report, "public_testnet_v0_1_16_evidence")
    assert public_lane["status"] == "blocked"
    assert "usage:" not in " ".join(public_lane["blockers"]).lower()
    assert public_lane["replay_command"].startswith(
        "python3 tools/check_public_testnet_v0_1_16_evidence.py"
    )
    assert _lane(report, "zeno_ledger_two_machine_latest_main_evidence")["status"] == "blocked"
    assert _lane(report, "full_release_gate_artifact")["status"] == "blocked"


def test_external_evidence_lanes_accept_valid_archives_but_internal_skips_block(
    tmp_path: Path,
) -> None:
    public_manifest = tmp_path / "public" / "manifest.json"
    two_machine = tmp_path / "two_machine.json"
    release_gate = tmp_path / "prod_gate_report.json"
    _write_public_testnet_manifest(public_manifest)
    _write_two_machine_evidence(two_machine)
    _write_json(
        release_gate,
        {
            "schema": RELEASE_GATE_REPORT_SCHEMA,
            "ok": True,
            "command": "bash tools/prod_gate.sh",
            "commit_sha": COMMIT,
            "completed_at": "2026-06-12T00:00:00Z",
            "check_results": {
                check_id: {"ok": True}
                for check_id in REQUIRED_RELEASE_GATE_CHECKS
            },
        },
    )

    report = build_readiness_status(
        public_testnet_manifest=public_manifest,
        two_machine_evidence=two_machine,
        release_gate_report=release_gate,
        expected_commit=COMMIT,
        run_internal_gates=False,
    )

    assert _lane(report, "public_testnet_v0_1_16_evidence")["ok"] is True
    assert _lane(report, "zeno_ledger_two_machine_latest_main_evidence")["ok"] is True
    assert _lane(report, "full_release_gate_artifact")["ok"] is True
    assert report["production_ready"] is False
    assert "autogovnext_node_apply_path" in report["blocked_lanes"]


def test_release_gate_report_rejects_bare_ok_true(tmp_path: Path) -> None:
    release_gate = tmp_path / "prod_gate_report.json"
    _write_json(release_gate, {"ok": True})

    report = build_readiness_status(
        public_testnet_manifest=tmp_path / "missing-public.json",
        two_machine_evidence=tmp_path / "missing-two-machine.json",
        release_gate_report=release_gate,
        expected_commit=COMMIT,
        run_internal_gates=False,
    )

    lane = _lane(report, "full_release_gate_artifact")
    assert lane["ok"] is False
    assert lane["status"] == "rejected"
    assert f"schema must be {RELEASE_GATE_REPORT_SCHEMA}" in lane["errors"]
    assert "release-gate report command must be bash tools/prod_gate.sh" in lane["errors"]
    assert "release-gate report check_results must be an object" in lane["errors"]
    assert "release-gate check trivy_scan must have ok=true" in lane["errors"]


def test_cli_default_emits_blocked_json_not_argparse_usage(
    tmp_path: Path,
    capsys,
) -> None:
    code = main(
        [
            "--skip-internal",
            "--expected-commit",
            COMMIT,
            "--public-testnet-manifest",
            str(tmp_path / "missing-public.json"),
            "--two-machine-evidence",
            str(tmp_path / "missing-two-machine.json"),
            "--release-gate-report",
            str(tmp_path / "missing-release.json"),
        ]
    )
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 1
    assert report["production_ready"] is False
    assert report["status"] == "blocked"
    assert "usage:" not in out.lower()
