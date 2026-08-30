from __future__ import annotations

import json
from pathlib import Path

from tools.check_public_testnet_v0_1_16_evidence import check_evidence_manifest


def _write_json(path: Path, obj: object) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _valid_release_smoke() -> dict[str, object]:
    checks = {
        "faucet_tagrs": {"ok": True},
        "zusd_collateral_deposit": {"ok": True},
        "zusd_minted_from_collateral": {"ok": True},
        "perps_collateral_deposit": {"ok": True},
        "perps_long_short_open": {"ok": True},
        "perps_settlement_cycle": {"ok": True},
        "spot_swap_tagrs_tzdex": {"ok": True},
        "status_and_header_agreement": {"ok": True},
    }
    return {"schema": "zenodex.local_testnet.release_flow_smoke_report.v1", "ok": True, "checks": checks}


def _write_valid_fixture(tmp_path: Path, *, posture: str = "session_stable_quick_tunnel") -> Path:
    _write_json(tmp_path / "local.json", {"ok": True})
    acceptance = {
        "ok": True,
        "status": "accepted",
        "network_config_hash": "0xabc",
        "common_header_match": True,
        "live_observed": True,
        "local_tip": {"live": True, "height": 8, "header_hash": "0x123"},
        "peer_tip": {"live": True, "height": 8, "header_hash": "0x123"},
    }
    _write_json(tmp_path / "external.json", acceptance)
    _write_json(tmp_path / "second.json", acceptance)
    _write_json(
        tmp_path / "phone.json",
        {
            "ok": True,
            "checks": {
                "public_ui_https_loaded": True,
                "status_page_loaded": True,
                "token_list_loaded": True,
            },
        },
    )
    _write_json(tmp_path / "release.json", _valid_release_smoke())
    residual = (
        "fake-value public testnet. no production value. moves no mainnet assets. "
        "session-stable Quick Tunnel URL."
    )
    (tmp_path / "residual.md").write_text(residual + "\n", encoding="utf-8")
    public_url = (
        "https://sample.trycloudflare.com/public_network_config.json"
        if posture == "session_stable_quick_tunnel"
        else "https://testnet.example.com/public_network_config.json"
    )
    manifest = {
        "schema": "zenodex.public_testnet_v0_1_16.evidence_manifest.v1",
        "public_config_url": public_url,
        "public_config_url_posture": posture,
        "stable_public_config_url": posture == "stable_named_url",
        "artifacts": {
            "local_full_stack_smoke_report": "local.json",
            "external_laptop_acceptance_report": "external.json",
            "second_clean_follower_report": "second.json",
            "phone_browser_validation_report": "phone.json",
            "release_flow_transaction_smoke_report": "release.json",
            "residual_limits_statement": "residual.md",
        },
    }
    path = tmp_path / "manifest.json"
    _write_json(path, manifest)
    return path


def test_valid_quick_tunnel_history_cannot_authorize_current_release(tmp_path: Path) -> None:
    report = check_evidence_manifest(_write_valid_fixture(tmp_path))
    assert report["historical_evidence_valid"] is True, report["errors"]
    assert report["current_release_eligible"] is False
    assert report["ok"] is False
    assert report["authority"] == "NONE"
    assert report["vm_gates_closed"] == []


def test_valid_named_url_history_cannot_authorize_current_release(tmp_path: Path) -> None:
    report = check_evidence_manifest(_write_valid_fixture(tmp_path, posture="stable_named_url"))
    assert report["historical_evidence_valid"] is True, report["errors"]
    assert report["current_release_eligible"] is False
    assert report["ok"] is False


def test_caller_claimed_current_bindings_cannot_override_local_quarantine(tmp_path: Path) -> None:
    manifest_path = _write_valid_fixture(tmp_path)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest.update(
        {
            "current_profile_id": "caller-forged-active-profile",
            "current_release_eligible": True,
            "source_commit": "f" * 40,
            "quarantine_registry_hash": "f" * 64,
            "manifest_hash": "f" * 64,
        }
    )
    _write_json(manifest_path, manifest)

    report = check_evidence_manifest(manifest_path)

    assert report["historical_evidence_valid"] is True
    assert report["current_profile_id"] == "local-testnet-retired-bridge-quarantine-v2"
    assert report["current_release_eligible"] is False
    assert report["status"] == "blocked_current_profile"


def test_rejects_quick_tunnel_marked_stable(tmp_path: Path) -> None:
    manifest_path = _write_valid_fixture(tmp_path)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["stable_public_config_url"] = True
    _write_json(manifest_path, manifest)

    report = check_evidence_manifest(manifest_path)

    assert report["ok"] is False
    assert any("stable_public_config_url" in err for err in report["errors"])


def test_rejects_missing_release_flow_check(tmp_path: Path) -> None:
    manifest_path = _write_valid_fixture(tmp_path)
    release_path = tmp_path / "release.json"
    release = json.loads(release_path.read_text(encoding="utf-8"))
    release["checks"].pop("spot_swap_tagrs_tzdex")
    _write_json(release_path, release)

    report = check_evidence_manifest(manifest_path)

    assert report["ok"] is False
    assert any("spot_swap_tagrs_tzdex" in err for err in report["errors"])


def test_rejects_phone_report_without_status_page(tmp_path: Path) -> None:
    manifest_path = _write_valid_fixture(tmp_path)
    phone_path = tmp_path / "phone.json"
    phone = json.loads(phone_path.read_text(encoding="utf-8"))
    phone["checks"]["status_page_loaded"] = False
    _write_json(phone_path, phone)

    report = check_evidence_manifest(manifest_path)

    assert report["ok"] is False
    assert any("status page" in err for err in report["errors"])


def test_rejects_acceptance_without_live_tip(tmp_path: Path) -> None:
    manifest_path = _write_valid_fixture(tmp_path)
    second_path = tmp_path / "second.json"
    second = json.loads(second_path.read_text(encoding="utf-8"))
    second["live_observed"] = False
    second["local_tip"] = {"live": False, "height": 5}
    second["peer_tip"] = {"live": False, "height": 5}
    _write_json(second_path, second)

    report = check_evidence_manifest(manifest_path)

    assert report["ok"] is False
    assert any("live follower and seed tips" in err for err in report["errors"])
