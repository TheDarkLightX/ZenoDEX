from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tests.test_zeno_sdk_browser_bundle import _write_fixture_files
from tools.build_zeno_sdk_browser_bundle import build_browser_bundle_from_files
from tools.check_public_testnet_v0_1_16_evidence import (
    EVIDENCE_SCHEMA,
    main,
    validate_public_testnet_v0_1_16_evidence,
)
from tools.check_zeno_ledger_two_machine_evidence import EVIDENCE_SCHEMA as TWO_MACHINE_SCHEMA

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


def _two_machine_evidence() -> dict[str, object]:
    network_config_hash = _root("network-config")
    feature_suite_hash = _root("feature-suite")
    common_header_hash = _root("common-header")
    return {
        "schema": TWO_MACHINE_SCHEMA,
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


def _browser_bundle(tmp_path: Path) -> dict[str, Any]:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    return build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )


def _evidence(tmp_path: Path) -> dict[str, object]:
    two_machine = _two_machine_evidence()
    network_config_hash = cast(str, two_machine["network_config_hash"])
    common_header_hash = cast(str, two_machine["common_header_hash"])
    bundle = _browser_bundle(tmp_path)
    return {
        "schema": EVIDENCE_SCHEMA,
        "release_version": "v0.1.16",
        "network_config_url": "https://seed.example.test/zeno-ledger-public-testnet/public_network_config.json",
        "network_config_hash": network_config_hash,
        "stable_public_config_url": True,
        "two_machine_evidence": two_machine,
        "clean_machine_join": {
            "ok": True,
            "joined_from_config_url": True,
            "bundle_hashes_verified": True,
            "seed_peer_check_ok": True,
            "served_status": True,
            "network_config_hash": network_config_hash,
        },
        "second_clean_machine": {
            "ok": True,
            "network_config_hash": network_config_hash,
            "common_header_hash": common_header_hash,
        },
        "phone_or_browser_client": {
            "ok": True,
            "mode": "checkpoint_bundle",
            "browser_checkpoint_bundle": bundle,
            "browser_report": {
                "ok": True,
                "bundle_hash": bundle["bundle_hash"],
                "checkpoint_hash": bundle["verification_summary"]["checkpoint_hash"],
                "browser_range_replay_verified": True,
            },
            "backend_bearer_tokens_exposed": False,
        },
        "residual_limits": [
            "designated_writer_testnet",
            "fake_tokens_only",
            "no_production_value",
            "open_p2p_gossip_later",
        ],
    }


def test_public_testnet_v0_1_16_evidence_accepts_complete_checkpoint_bundle_path(tmp_path: Path) -> None:
    report = validate_public_testnet_v0_1_16_evidence(_evidence(tmp_path))

    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert all(report["required_evidence_fields"].values())


def test_public_testnet_v0_1_16_evidence_rejects_non_https_public_config(tmp_path: Path) -> None:
    evidence = _evidence(tmp_path)
    evidence["network_config_url"] = "http://seed.example.test/public_network_config.json"

    report = validate_public_testnet_v0_1_16_evidence(evidence)

    assert report["ok"] is False
    assert "network_config_url must use https" in report["errors"]


def test_public_testnet_v0_1_16_evidence_rejects_exposed_browser_bearer_token(tmp_path: Path) -> None:
    evidence = _evidence(tmp_path)
    phone = cast(dict[str, object], evidence["phone_or_browser_client"])
    phone["backend_bearer_tokens_exposed"] = True

    report = validate_public_testnet_v0_1_16_evidence(evidence)

    assert report["ok"] is False
    assert "phone_or_browser_client.backend_bearer_tokens_exposed must be false" in report["errors"]


def test_public_testnet_v0_1_16_evidence_rejects_second_machine_header_mismatch(tmp_path: Path) -> None:
    evidence = _evidence(tmp_path)
    second = cast(dict[str, object], evidence["second_clean_machine"])
    second["common_header_hash"] = _root("different-common-header")

    report = validate_public_testnet_v0_1_16_evidence(evidence)

    assert report["ok"] is False
    assert "second_clean_machine.common_header_hash mismatch" in report["errors"]


def test_public_testnet_v0_1_16_evidence_cli_accepts_fixture(tmp_path: Path, capsys) -> None:
    path = tmp_path / "public-testnet-evidence.json"
    path.write_text(json.dumps(_evidence(tmp_path), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    code = main([str(path)])
    out = json.loads(capsys.readouterr().out)

    assert code == 0
    assert out["ok"] is True
