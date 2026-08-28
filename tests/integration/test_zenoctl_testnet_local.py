"""Unit tests for `zenoctl testnet local` orchestration (no Docker required).

Verifies:
  - CLI dispatch shape (sub-commands present, required args enforced)
  - Manifest schema (build/save/load round-trip; validation rejects bad inputs)
  - Nginx template render (path split correct; tokens injected only in writer/
    stdlib blocks; nginx $variables preserved)
  - Token leakage guards (no literal token in manifest or runtime config)
  - Loopback-only enforcement in compose overlay
  - Port collision detection
  - Fixture determinism for same out-dir + chain-id
  - Compose image refs match the existing multimachine compose file
"""

from __future__ import annotations

import argparse
import ast
import json
import os
import socket
import subprocess
import sys
from contextlib import closing
from pathlib import Path
from types import SimpleNamespace
from typing import Callable, Mapping

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
COMPOSE_OVERLAY = REPO_ROOT / "docker-compose.local-testnet.yml"
COMPOSE_MULTIMACHINE = REPO_ROOT / "docker-compose.multimachine.yml"
NGINX_TEMPLATE = REPO_ROOT / ".docker" / "nginx.local-testnet.conf.template"


# ---------------------------------------------------------------------------
# Manifest schema
# ---------------------------------------------------------------------------


def _valid_manifest_kwargs(out_dir: Path) -> dict:
    return dict(
        out_dir=out_dir,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        ports={"ui": 18080},
        service_urls={
            "ui": "http://127.0.0.1:18080",
            "stdlib_api": "compose://zenodex-api:8000",
            "writer": "compose://zeno-ledger-writer:8787",
            "oracle": "compose://zenodex-oracle:9100",
            "tau": "compose://tau-local:65432",
        },
        image_refs={
            "operator_tools": "zenodex/operator-tools:local",
            "tau_local": "zenodex/tau-local:local-testnet",
        },
        enabled_lanes=["DEX_API_ENABLED"],
        fixture_paths={
            "key_bundle": str(out_dir / "secrets" / "keys.json"),
            "oracle_authority_profile": str(out_dir / "fixtures" / "oracle_authority_profile.json"),
            "perps_wallet_authority_profile": str(out_dir / "fixtures" / "perps_wallet_authority_profile.json"),
            "autotrader_supervisor_profile": str(out_dir / "fixtures" / "autotrader_supervisor_profile.json"),
            "guardian_quorum": str(out_dir / "fixtures" / "guardians.json"),
            "perps_wallet_recovery_exercise": str(out_dir / "fixtures" / "perps_wallet_recovery_exercise.json"),
            "perps_wallet_rotation_exercise": str(out_dir / "fixtures" / "perps_wallet_rotation_exercise.json"),
            "perps_wallet_device_approval_exercise": str(out_dir / "fixtures" / "perps_wallet_device_approval_exercise.json"),
            "perps_wallet_signer_device_integration": str(out_dir / "fixtures" / "perps_wallet_signer_device_integration.json"),
            "perps_wallet_signer_prompt_capture": str(out_dir / "fixtures" / "perps_wallet_signer_prompt_capture.json"),
            "perps_wallet_signer_execution_exercise": str(out_dir / "fixtures" / "perps_wallet_signer_execution_exercise.json"),
            "perps_wallet_encrypted_sss_backup": str(out_dir / "fixtures" / "perps_wallet_encrypted_sss_backup.json"),
            "perps_wallet_encrypted_sss_recipient_keys": str(out_dir / "fixtures" / "perps_wallet_encrypted_sss_recipient_keys.json"),
        },
        ledger_bundle_manifest=str(out_dir / "ledger" / "public_testnet_manifest.json"),
        writer_token="writer-secret-abc",
        stdlib_token="stdlib-secret-xyz",
        created_at_ms=1_700_000_000_000,
    )


def test_manifest_build_validate_roundtrip(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    assert mf.validate_manifest(body) == []
    assert body["schema"] == mf.SCHEMA_V2
    assert body["compose_project"].startswith("zenodex-local-testnet-")
    assert body["writer_token_sha256"].startswith("sha256:")
    assert body["stdlib_token_sha256"].startswith("sha256:")
    assert body["zk_mode_requested"] == "auto-strict"
    assert body["zk_mode_effective"] == "open"
    assert body["zk_required"] is False
    assert body["proof_verifier_kind"] == "disabled"
    assert body["production_security_claim"] is False
    assert body["rendered_paths"]["nginx_conf"].startswith("/")
    assert body["rendered_paths"]["runtime_config"].startswith("/")
    assert body["host_paths"]["fixtures_dir"].startswith("/")
    assert body["host_paths"]["secrets_dir"].startswith("/")
    assert body["host_paths"]["oracle_home_dir"].startswith("/")
    assert body["host_paths"]["reports_dir"].startswith("/")
    assert "writer-secret-abc" not in json.dumps(body, sort_keys=True), "raw token must not be in manifest"


def test_manifest_save_load_roundtrip(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    path = tmp_path / "manifest.json"
    mf.save_manifest(body, path)
    assert path.is_file()
    loaded = mf.load_manifest(path)
    assert loaded == body


def test_force_up_can_load_stale_manifest_for_reset(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["fixture_paths"].pop("perps_wallet_encrypted_sss_backup")
    path = tmp_path / mf.MANIFEST_FILENAME
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with pytest.raises(ValueError):
        lc._load_manifest_if_present(path)

    loaded = lc._load_manifest_if_present(path, allow_invalid=True)
    assert loaded is not None
    assert loaded["compose_project"] == body["compose_project"]


def test_manifest_rejects_bad_schema(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["schema"] = "wrong"
    errors = mf.validate_manifest(body)
    assert any("schema" in e for e in errors)


def test_manifest_rejects_quarantined_autotrader_lane(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("AUTOTRADER_LIVE_API_ENABLED")

    errors = mf.validate_manifest(body)

    assert errors == [
        "enabled_lanes contains unmountable lanes: ['AUTOTRADER_LIVE_API_ENABLED']"
    ]
    path = tmp_path / mf.MANIFEST_FILENAME
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with pytest.raises(ValueError, match="unmountable lanes"):
        lc._load_manifest_if_present(path)
    assert lc._load_manifest_if_present(path, allow_invalid=True) is not None


def test_manifest_rejects_quarantined_zusd_tau_wallet_lane(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("ZUSD_TAU_WALLET_API_ENABLED")

    assert mf.validate_manifest(body) == [
        "enabled_lanes contains unmountable lanes: ['ZUSD_TAU_WALLET_API_ENABLED']"
    ]
    path = tmp_path / mf.MANIFEST_FILENAME
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with pytest.raises(ValueError, match="unmountable lanes"):
        lc._load_manifest_if_present(path)
    assert lc._load_manifest_if_present(path, allow_invalid=True) is not None


@pytest.mark.parametrize(
    "lane",
    ("PERPS_WALLET_API_ENABLED", "ZUSD_MONETARY_WALLET_API_ENABLED"),
)
def test_manifest_rejects_retired_tau_value_lanes(tmp_path: Path, lane: str) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append(lane)

    assert mf.validate_manifest(body) == [
        f"enabled_lanes contains unmountable lanes: [{lane!r}]"
    ]


@pytest.mark.parametrize(
    ("operation", "expected_code"),
    (
        ("up", 2),
        ("down", 0),
        ("status", 2),
        ("smoke", 2),
        ("release_smoke", 2),
        ("public_up", 2),
        ("logs", 2),
        ("reset", 2),
    ),
)
def test_identity_bound_retired_route_manifest_is_quiesced_before_lifecycle(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    operation: str,
    expected_code: int,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].extend(
        ["PERPS_WALLET_API_ENABLED", "ZUSD_MONETARY_WALLET_API_ENABLED"]
    )
    path = tmp_path / mf.MANIFEST_FILENAME
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    calls: list[dict[str, object]] = []

    monkeypatch.setattr(lc.cm, "detect_engine", lambda _name: object())
    monkeypatch.setattr(lc.cm, "compose_down", lambda **kwargs: calls.append(kwargs))
    monkeypatch.setattr(lc.shutil, "rmtree", lambda *_args, **_kwargs: None)

    if operation == "up":
        code = lc.cmd_up(lc.UpOptions(out_dir=tmp_path))
    elif operation == "down":
        code = lc.cmd_down(lc.DownOptions(out_dir=tmp_path))
    elif operation == "status":
        code = lc.cmd_status(lc.StatusOptions(out_dir=tmp_path, as_json=True))
    elif operation == "smoke":
        code = lc.cmd_smoke(lc.SmokeOptions(out_dir=tmp_path, browser="off"))
    elif operation == "release_smoke":
        code = lc.cmd_release_smoke(lc.ReleaseSmokeOptions(out_dir=tmp_path))
    elif operation == "public_up":
        code = lc.cmd_public_up(lc.PublicUpOptions(out_dir=tmp_path))
    elif operation == "logs":
        code = lc.cmd_logs(lc.LogsOptions(out_dir=tmp_path))
    elif operation == "reset":
        code = lc.cmd_reset(lc.ResetOptions(out_dir=tmp_path))
    else:
        raise AssertionError(operation)

    assert code == expected_code
    assert len(calls) == 1
    assert calls[0]["project_name"] == mf.compose_project_name(tmp_path)
    assert calls[0]["compose_files"] == [lc.COMPOSE_FILE]
    assert calls[0]["remove_volumes"] is (operation == "reset")


def test_foreign_retired_route_manifest_cannot_stop_an_unrelated_project(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("PERPS_WALLET_API_ENABLED")
    body["compose_project"] = "zenodex-local-testnet-v2-" + ("0" * 32)
    path = tmp_path / mf.MANIFEST_FILENAME
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    effects: list[str] = []

    def record_engine_detection(_name: str) -> object:
        effects.append("engine")
        return object()

    monkeypatch.setattr(
        lc.cm,
        "detect_engine",
        record_engine_detection,
    )

    with pytest.raises(ValueError, match="unsafe identity binding"):
        lc.cmd_down(lc.DownOptions(out_dir=tmp_path))

    assert effects == []


def test_force_up_quiesces_and_removes_retired_route_state_before_rebuild(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("PERPS_WALLET_API_ENABLED")
    manifest_path = tmp_path / mf.MANIFEST_FILENAME
    manifest_path.write_text(
        json.dumps(body, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    calls: list[dict[str, object]] = []

    monkeypatch.setattr(lc.cm, "detect_engine", lambda _name: object())
    monkeypatch.setattr(lc.cm, "compose_down", lambda **kwargs: calls.append(kwargs))

    def stop_before_rebuild(_repo_root: Path) -> None:
        raise RuntimeError("rebuild preflight reached")

    monkeypatch.setattr(lc.cm, "check_external_tau_testnet_present", stop_before_rebuild)

    with pytest.raises(RuntimeError, match="rebuild preflight reached"):
        lc.cmd_up(lc.UpOptions(out_dir=tmp_path, force=True, ui_port=18081))

    assert len(calls) == 1
    assert calls[0]["project_name"] == mf.compose_project_name(tmp_path)
    assert calls[0]["remove_volumes"] is True
    assert tmp_path.is_dir()
    assert not manifest_path.exists()


def test_force_up_quiesces_then_refuses_stale_tunnel_origin_port_rebind(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("PERPS_WALLET_API_ENABLED")
    manifest_path = tmp_path / mf.MANIFEST_FILENAME
    manifest_path.write_text(
        json.dumps(body, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    calls: list[dict[str, object]] = []
    preflight: list[str] = []

    monkeypatch.setattr(lc.cm, "detect_engine", lambda _name: object())
    monkeypatch.setattr(lc.cm, "compose_down", lambda **kwargs: calls.append(kwargs))
    monkeypatch.setattr(
        lc.cm,
        "check_external_tau_testnet_present",
        lambda _repo_root: preflight.append("rebuild"),
    )

    code = lc.cmd_up(lc.UpOptions(out_dir=tmp_path, force=True, ui_port=18080))

    assert code == 2
    assert len(calls) == 1
    assert calls[0]["project_name"] == mf.compose_project_name(tmp_path)
    assert calls[0]["remove_volumes"] is False
    assert manifest_path.is_file()
    assert preflight == []


def test_reset_preserves_retired_origin_identity_until_fresh_port_rebuild(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("ZUSD_MONETARY_WALLET_API_ENABLED")
    manifest_path = tmp_path / mf.MANIFEST_FILENAME
    manifest_path.write_text(
        json.dumps(body, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    calls: list[dict[str, object]] = []

    monkeypatch.setattr(lc.cm, "detect_engine", lambda _name: object())
    monkeypatch.setattr(lc.cm, "compose_down", lambda **kwargs: calls.append(kwargs))

    code = lc.cmd_reset(lc.ResetOptions(out_dir=tmp_path))

    assert code == 2
    assert len(calls) == 1
    assert calls[0]["remove_volumes"] is True
    assert manifest_path.is_file()


def test_force_up_rejects_malformed_retired_origin_identity_after_quiescence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("PERPS_WALLET_API_ENABLED")
    body["ports"]["ui"] = True
    manifest_path = tmp_path / mf.MANIFEST_FILENAME
    manifest_path.write_text(
        json.dumps(body, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    calls: list[dict[str, object]] = []
    preflight: list[str] = []

    monkeypatch.setattr(lc.cm, "detect_engine", lambda _name: object())
    monkeypatch.setattr(lc.cm, "compose_down", lambda **kwargs: calls.append(kwargs))
    monkeypatch.setattr(
        lc.cm,
        "check_external_tau_testnet_present",
        lambda _repo_root: preflight.append("rebuild"),
    )

    code = lc.cmd_up(lc.UpOptions(out_dir=tmp_path, force=True, ui_port=18080))

    assert code == 2
    assert len(calls) == 1
    assert calls[0]["remove_volumes"] is False
    assert manifest_path.is_file()
    assert preflight == []


def test_manifest_mountable_lane_registry_excludes_retired_tau_routes() -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    assert mf.LOCAL_TESTNET_MOUNTABLE_LANES == (
        "DEX_API_ENABLED",
        "CONFIDENTIAL_ATTESTATION_API_ENABLED",
    )


def test_lifecycle_source_has_no_retired_tau_route_reachability() -> None:
    source = (REPO_ROOT / "tools/zenoctl_testnet_local/lifecycle.py").read_text(
        encoding="utf-8"
    )
    module = ast.parse(source)
    functions = {
        node.name: node
        for node in module.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }

    cmd_up_calls = {
        node.func.id
        for node in ast.walk(functions["cmd_up"])
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    assert "_seed_api_state" not in cmd_up_calls

    for function_name in (
        "_collect_lane_readiness",
        "_run_feature_smoke",
        "_browser_smoke_cases",
    ):
        strings = {
            node.value
            for node in ast.walk(functions[function_name])
            if isinstance(node, ast.Constant) and isinstance(node.value, str)
        }
        assert all("/api/perps/wallet" not in value for value in strings)
        assert all("/api/zusd/monetary" not in value for value in strings)

    release_calls = {
        node.func.id
        for node in ast.walk(functions["cmd_release_smoke"])
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    assert release_calls.isdisjoint(
        {
            "_load_manifest_if_present",
            "_runtime_env_for_existing_manifest",
            "_write_json",
        }
    )


def test_release_smoke_rejects_before_manifest_or_runtime_effects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []
    monkeypatch.setattr(
        lc,
        "_load_manifest_if_present",
        lambda *_args, **_kwargs: events.append("manifest"),
    )

    rc = lc.cmd_release_smoke(lc.ReleaseSmokeOptions(out_dir=tmp_path))

    assert rc == 2
    assert events == []
    report = json.loads(capsys.readouterr().out)
    assert report == {
        "schema": "zenodex.local_testnet.release_flow_smoke_report.v1",
        "ok": False,
        "status": "blocked_current_profile",
        "rejection_code": "LOCAL_RELEASE_SMOKE_REQUIRES_QUARANTINED_ROUTES",
        "current_profile_id": "local-testnet-retired-bridge-quarantine-v1",
        "current_release_eligible": False,
        "authority": "NONE",
        "vm_gates_closed": [],
        "release_blocker": (
            "current profile quarantines stream-8 perps, stream-9 zUSD wallet, "
            "and stream-11 zUSD monetary routes; retained testnet artifacts "
            "cannot authorize a current release"
        ),
        "quarantined_routes": [
            "PERPS_WALLET_API_ENABLED",
            "ZUSD_TAU_WALLET_API_ENABLED",
            "ZUSD_MONETARY_WALLET_API_ENABLED",
        ],
        "value_movement_authority": "NONE",
        "checks": {},
    }
    assert not (tmp_path / "reports").exists()


def test_manifest_force_reset_rejects_invalid_identity_binding(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["enabled_lanes"].append("AUTOTRADER_LIVE_API_ENABLED")
    expected_project = mf.compose_project_name(tmp_path)
    wrong_project = "zenodex-local-testnet-v2-" + ("0" * 32)
    if wrong_project == expected_project:
        wrong_project = "zenodex-local-testnet-v2-" + ("1" * 32)
    body["compose_project"] = wrong_project
    path = tmp_path / mf.MANIFEST_FILENAME
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    assert mf.validate_manifest(body) == [
        "compose_project does not match the project derived from out_dir: "
        f"expected {expected_project!r}, got {wrong_project!r}",
        "enabled_lanes contains unmountable lanes: ['AUTOTRADER_LIVE_API_ENABLED']",
    ]
    with pytest.raises(ValueError, match="manifest has unsafe identity binding"):
        lc._load_manifest_if_present(path, allow_invalid=True)


def test_manifest_loader_rejects_valid_manifest_relocated_to_another_out_dir(
    tmp_path: Path,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    selected_out_dir = tmp_path / "selected"
    other_out_dir = tmp_path / "other"
    body = mf.build_manifest(**_valid_manifest_kwargs(other_out_dir))
    path = selected_out_dir / mf.MANIFEST_FILENAME
    path.parent.mkdir(parents=True)
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    assert mf.validate_manifest(body) == []
    with pytest.raises(ValueError, match="manifest has unsafe identity binding"):
        lc._load_manifest_if_present(path)
    with pytest.raises(ValueError, match="manifest has unsafe identity binding"):
        lc._load_manifest_if_present(path, allow_invalid=True)


def test_compose_project_identity_separates_known_legacy_collision() -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    left = Path("/tmp/zenodex-compose-id-collision-37513")
    right = Path("/tmp/zenodex-compose-id-collision-41442")

    assert mf.legacy_compose_project_name(left) == mf.legacy_compose_project_name(right)
    assert mf.compose_project_name(left) != mf.compose_project_name(right)
    assert mf.compose_project_name(left).startswith("zenodex-local-testnet-v2-")
    assert len(mf.compose_project_name(left).rsplit("-", 1)[1]) == 32


def test_force_reset_classifies_and_refuses_collision_prone_legacy_project(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    legacy_project = mf.legacy_compose_project_name(tmp_path)
    body["compose_project"] = legacy_project
    path = tmp_path / mf.MANIFEST_FILENAME
    path.write_text(json.dumps(body, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    engine_called = False

    with pytest.raises(ValueError, match="manifest validation failed"):
        lc._load_manifest_if_present(path)
    loaded = lc._load_manifest_if_present(path, allow_invalid=True)

    def detect_engine(_name: str) -> object:
        nonlocal engine_called
        engine_called = True
        return object()

    monkeypatch.setattr(lc.cm, "detect_engine", detect_engine)

    with pytest.raises(ValueError, match="legacy 32-bit Compose identity"):
        lc._reset_stack(paths=paths, engine_name="auto", manifest=loaded)
    assert engine_called is False


def test_force_reset_uses_derived_identity_and_safe_paths(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["host_paths"]["fixtures_dir"] = "/untrusted/fixtures"
    captured: dict[str, object] = {}

    monkeypatch.setattr(lc.cm, "detect_engine", lambda _name: object())
    monkeypatch.setattr(lc.cm, "compose_down", lambda **kwargs: captured.update(kwargs))
    monkeypatch.setattr(lc.shutil, "rmtree", lambda *_args, **_kwargs: None)

    lc._reset_stack(paths=paths, engine_name="auto", manifest=body)

    assert captured["project_name"] == mf.compose_project_name(paths.out_dir)
    env = captured["env"]
    assert isinstance(env, dict)
    assert env["FIXTURES_DIR"] == str(paths.fixtures_dir)


def test_manifest_rejects_missing_keys(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    del body["service_urls"]
    errors = mf.validate_manifest(body)
    assert any("service_urls" in e for e in errors)


def test_manifest_rejects_malformed_writer_token_hash(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["writer_token_sha256"] = "writer-secret"
    errors = mf.validate_manifest(body)
    assert any("writer_token_sha256" in e for e in errors)


def test_manifest_rejects_invalid_port(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["ports"]["ui"] = 99_999
    errors = mf.validate_manifest(body)
    assert any("ports[ui]" in e for e in errors)


def test_manifest_rejects_auto_strict_as_effective_zk_mode(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["zk_mode_effective"] = "auto-strict"
    errors = mf.validate_manifest(body)
    assert any("zk_mode_effective" in e for e in errors)


def test_manifest_rejects_local_production_security_claim(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["production_security_claim"] = True
    errors = mf.validate_manifest(body)
    assert any("production_security_claim must be false" in e for e in errors)


def test_manifest_rejects_strict_without_required_zk_inputs(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(
        **_valid_manifest_kwargs(tmp_path),
        zk_posture={
            "zk_mode_requested": "strict",
            "zk_mode_effective": "strict",
            "zk_required": False,
            "zk_fallback_reason": None,
            "proof_verifier_kind": "disabled",
            "proof_artifact_hashes": {},
            "production_security_claim": False,
        },
    )

    errors = mf.validate_manifest(body)

    assert "strict zk mode requires zk_required=true" in errors
    assert "strict zk mode requires proof_verifier_kind=subprocess" in errors
    assert "strict zk mode requires verifier and circuit artifact hashes" in errors


def test_writer_token_sha256_is_stable() -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    a = mf.writer_token_sha256("hello-token")
    b = mf.writer_token_sha256("hello-token")
    assert a == b
    c = mf.writer_token_sha256("different")
    assert a != c


def test_zk_auto_strict_uses_bundled_local_wrapper_when_no_verifier_env(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    for name in (
        "TAU_DEX_PROOF_VERIFIER_CMD_JSON",
        "TAU_DEX_PROOF_VERIFIER_TIMEOUT_S",
        "TAU_DEX_PROOF_VERIFIER_MAX_PROOF_BYTES",
        "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
        "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
        "TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE",
        "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_FILE",
        "TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP",
    ):
        monkeypatch.delenv(name, raising=False)
    posture = lc._resolve_zk_posture("auto-strict")
    assert posture["ok"] is True
    assert posture["zk_mode_requested"] == "auto-strict"
    assert posture["zk_mode_effective"] == "strict"
    assert posture["zk_required"] is True
    assert posture["zk_fallback_reason"] is None
    assert posture["proof_verifier_kind"] == "subprocess"
    assert posture["proof_artifact_hashes"] == {
        "verifier": "sha256:" + "33" * 32,
        "circuit": "sha256:" + "44" * 32,
    }
    assert posture["production_security_claim"] is False


def test_zk_strict_rejects_explicit_incomplete_verifier_config(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps([sys.executable, "-c", "print()"]))
    monkeypatch.delenv("TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON", raising=False)
    monkeypatch.delenv("TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON", raising=False)
    monkeypatch.delenv("TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE", raising=False)
    monkeypatch.delenv("TAU_DEX_PROOF_CIRCUIT_ARTIFACT_FILE", raising=False)
    posture = lc._resolve_zk_posture("strict")
    assert posture["ok"] is False
    assert posture["zk_required"] is True
    assert "proof verifier artifact hash unavailable" in posture["zk_fallback_reason"]
    assert "proof circuit artifact hash unavailable" in posture["zk_fallback_reason"]


def test_zk_strict_accepts_subprocess_verifier_and_artifacts(monkeypatch: pytest.MonkeyPatch) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps([sys.executable, "-c", "print()"]))
    monkeypatch.setenv(
        "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
        json.dumps({"artifact_id": "verifier", "artifact_hash": "sha256:" + "11" * 32}),
    )
    monkeypatch.setenv(
        "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps({"artifact_id": "circuit", "artifact_hash": "0x" + "22" * 32, "proof_system": "risc0"}),
    )
    posture = lc._resolve_zk_posture("strict")
    assert posture["ok"] is True
    assert posture["zk_mode_effective"] == "strict"
    assert posture["zk_required"] is True
    assert posture["proof_verifier_kind"] == "subprocess"
    assert posture["proof_artifact_hashes"] == {
        "verifier": "sha256:" + "11" * 32,
        "circuit": "0x" + "22" * 32,
    }
    assert posture["production_security_claim"] is False


def test_zk_strict_rejects_relative_verifier_without_path_lookup(monkeypatch: pytest.MonkeyPatch) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps(["python3", "-c", "print()"]))
    monkeypatch.setenv(
        "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
        json.dumps({"artifact_id": "verifier", "artifact_hash": "sha256:" + "11" * 32}),
    )
    monkeypatch.setenv(
        "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps({"artifact_id": "circuit", "artifact_hash": "0x" + "22" * 32, "proof_system": "risc0"}),
    )
    monkeypatch.delenv("TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP", raising=False)

    posture = lc._resolve_zk_posture("strict")

    assert posture["ok"] is False
    assert "absolute executable path" in posture["zk_fallback_reason"]


def test_zk_strict_env_gap_rejects_manifest_artifact_mismatch(monkeypatch: pytest.MonkeyPatch) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps([sys.executable, "-c", "print()"]))
    monkeypatch.setenv(
        "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
        json.dumps({"artifact_id": "verifier", "artifact_hash": "sha256:" + "11" * 32}),
    )
    monkeypatch.setenv(
        "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps({"artifact_id": "circuit", "artifact_hash": "0x" + "22" * 32, "proof_system": "risc0"}),
    )

    gap = lc._strict_zk_env_gap(
        expected={
            "proof_verifier_kind": "subprocess",
            "proof_artifact_hashes": {
                "verifier": "sha256:" + "aa" * 32,
                "circuit": "0x" + "22" * 32,
            },
        }
    )

    assert gap == "current proof artifact hashes do not match manifest"


def test_zk_strict_requires_complete_artifact_metadata(monkeypatch: pytest.MonkeyPatch) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps([sys.executable, "-c", "print()"]))
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON", json.dumps({"artifact_hash": "sha256:" + "11" * 32}))
    monkeypatch.setenv(
        "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
        json.dumps({"artifact_id": "circuit", "artifact_hash": "0x" + "22" * 32}),
    )

    posture = lc._resolve_zk_posture("strict")

    assert posture["ok"] is False
    assert "proof verifier artifact artifact_id missing or invalid" in posture["zk_fallback_reason"]
    assert "proof circuit artifact proof_system missing or invalid" in posture["zk_fallback_reason"]


def test_zk_artifact_file_must_be_json_metadata(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    artifact_path = tmp_path / "artifact.txt"
    artifact_path.write_text(json.dumps({"artifact_hash": "sha256:" + "11" * 32}), encoding="utf-8")
    monkeypatch.delenv("TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON", raising=False)
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE", str(artifact_path))

    artifact_hash, error = lc._artifact_hash_from_env(
        json_name="TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
        file_name="TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE",
        label="proof verifier artifact",
    )

    assert artifact_hash is None
    assert error == "proof verifier artifact file must be JSON metadata"


def test_existing_manifest_rejects_requested_zk_mode_change(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    manifest = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    gap = lc._existing_manifest_zk_request_gap(
        opts=lc.UpOptions(out_dir=tmp_path, zk_mode="strict"),
        manifest=manifest,
    )

    assert gap is not None
    assert "use --force to recreate with --zk-mode strict" in gap


def test_browser_smoke_cases_omit_quarantined_value_routes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from urllib.parse import parse_qs, urlsplit

    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setattr(
        lc,
        "_build_signed_live_swap_payload",
        lambda **_: {"signature": "sig", "nonce": 7, "deadline": 123},
    )
    roles = {
        "alice": {"public_key": "alice-pub", "privkey_hex": "0x01"},
        "bob": {"public_key": "bob-pub", "privkey_hex": "0x02"},
        "oracle_authority": {"public_key": "oracle-pub", "privkey_hex": "0x03"},
    }

    cases = lc._browser_smoke_cases(
        ui_base="http://127.0.0.1:18080",
        roles=roles,
        chain_id="chain",
    )
    by_name = {str(item["name"]): item for item in cases}

    spot_query = parse_qs(urlsplit(str(by_name["spot_swap_ui"]["url"])).query)
    assert "zkProofJson" not in spot_query
    assert set(by_name) == {"spot_swap_ui", "oracle_ui", "confidential_ui"}
    assert "autotrader_ui" not in by_name
    assert "zusd_wallet_ui" not in by_name
    assert "zusd_monetary_ui" not in by_name
    assert "zusd_quick_mint_ui" not in by_name
    assert "perps_wallet_ui" not in by_name


# ---------------------------------------------------------------------------
# Fixture determinism
# ---------------------------------------------------------------------------


def test_fixture_seed_is_deterministic_per_out_dir(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    s1 = fx.derive_seed(out_dir=tmp_path, chain_id="zeno-ledger-localtest-v0")
    s2 = fx.derive_seed(out_dir=tmp_path, chain_id="zeno-ledger-localtest-v0")
    assert s1 == s2

    s3 = fx.derive_seed(out_dir=tmp_path, chain_id="other-chain")
    assert s1 != s3, "chain_id change must rotate seed"


def test_fixture_role_keys_are_distinct() -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    seed = b"\xab" * 32
    keys = {role: fx.derive_role_privkey(seed, role) for role in fx.KEY_ROLES}
    assert len(set(keys.values())) == len(fx.KEY_ROLES)


def test_fixture_writer_token_is_not_a_role_key() -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    seed = b"\xab" * 32
    token_hex = fx.derive_writer_token(seed)
    token_bytes = bytes.fromhex(token_hex)
    for role in fx.KEY_ROLES:
        assert token_bytes != fx.derive_role_privkey(seed, role)


def test_fixture_bundle_writes_expected_files(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    for path in (
        bundle.key_bundle,
        bundle.role_pubkeys,
        bundle.oracle_authority_profile,
        bundle.perps_wallet_authority_profile,
        bundle.autotrader_supervisor_profile,
        bundle.guardian_quorum,
        bundle.perps_wallet_recovery_exercise,
        bundle.perps_wallet_rotation_exercise,
        bundle.perps_wallet_device_approval_exercise,
        bundle.perps_wallet_signer_device_integration,
        bundle.perps_wallet_signer_prompt_capture,
        bundle.perps_wallet_signer_execution_exercise,
        bundle.perps_wallet_encrypted_sss_backup,
        bundle.perps_wallet_encrypted_sss_recipient_keys,
    ):
        assert path.is_file(), f"missing fixture file: {path}"

    doc = json.loads(bundle.key_bundle.read_text(encoding="utf-8"))
    assert doc["schema"] == "zenodex.local_testnet.key_bundle.v0"
    assert set(doc["roles"].keys()) == set(fx.KEY_ROLES)
    public_doc = json.loads(bundle.role_pubkeys.read_text(encoding="utf-8"))
    assert public_doc["schema"] == "zenodex.local_testnet.role_pubkeys.v0"
    assert set(public_doc["roles"].keys()) == set(fx.KEY_ROLES)
    assert all("privkey_hex" not in material for material in public_doc["roles"].values())
    assert bundle.key_bundle.parent == tmp_path.resolve() / "secrets"
    assert not (tmp_path / "fixtures" / "keys.json").exists()


def test_fixture_bundle_writes_key_material_with_owner_only_mode(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    if os.name == "nt":
        pytest.skip("chmod mode bits are not reliable on Windows")
    for path in (
        bundle.key_bundle,
        bundle.oracle_authority_profile,
        bundle.perps_wallet_authority_profile,
        bundle.autotrader_supervisor_profile,
        bundle.guardian_quorum,
        bundle.perps_wallet_recovery_exercise,
        bundle.perps_wallet_rotation_exercise,
        bundle.perps_wallet_device_approval_exercise,
        bundle.perps_wallet_signer_device_integration,
        bundle.perps_wallet_signer_prompt_capture,
        bundle.perps_wallet_signer_execution_exercise,
        bundle.perps_wallet_encrypted_sss_backup,
        bundle.perps_wallet_encrypted_sss_recipient_keys,
    ):
        mode = path.stat().st_mode & 0o777
        assert mode == 0o600, f"{path} must be 0600, got {oct(mode)}"
    assert bundle.role_pubkeys.stat().st_mode & 0o777 == 0o644


def test_fixture_bundle_is_byte_identical_across_reruns(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx
    import hashlib

    common_kwargs = dict(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    b1 = fx.generate_fixture_bundle(**common_kwargs)
    b2 = fx.generate_fixture_bundle(**common_kwargs)
    assert hashlib.sha256(b1.key_bundle.read_bytes()).hexdigest() == hashlib.sha256(
        b2.key_bundle.read_bytes()
    ).hexdigest()
    assert hashlib.sha256(b1.perps_wallet_encrypted_sss_backup.read_bytes()).hexdigest() == hashlib.sha256(
        b2.perps_wallet_encrypted_sss_backup.read_bytes()
    ).hexdigest()


def test_fixture_profiles_pass_live_authority_evaluators(tmp_path: Path) -> None:
    from src.integration.autotrader_supervisor_profile import evaluate_autotrader_supervisor_profile_v1
    from src.integration.perps_wallet_authority import (
        evaluate_perps_wallet_authority_profile_v1,
        evaluate_perps_wallet_device_approval_exercise_v1,
        evaluate_perps_wallet_hardware_custody_v1,
        evaluate_perps_wallet_recovery_exercise_v1,
        evaluate_perps_wallet_rotation_exercise_v1,
        evaluate_perps_wallet_signer_ceremony_v1,
        evaluate_perps_wallet_signer_device_integration_v1,
        evaluate_perps_wallet_signer_execution_exercise_v1,
        evaluate_perps_wallet_signer_prompt_capture_v1,
    )
    from src.integration.perps_wallet_encrypted_sss_backup import (
        evaluate_perps_wallet_encrypted_sss_backup_v1,
        recipient_root_keys_from_fixture_v1,
    )
    from src.integration.zeno_oracle_authority import evaluate_oracle_authority_profile_v1
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )

    oracle_profile = json.loads(bundle.oracle_authority_profile.read_text(encoding="utf-8"))
    oracle_status = evaluate_oracle_authority_profile_v1(oracle_profile)
    assert oracle_status["ok"] is True, oracle_status["readiness_gaps"]

    perps_profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    perps_status = evaluate_perps_wallet_authority_profile_v1(
        perps_profile,
        expected_chain_id=chain_id,
    )
    assert perps_status["ok"] is True, perps_status["readiness_gaps"]
    recovery = evaluate_perps_wallet_recovery_exercise_v1(
        perps_profile,
        json.loads(bundle.perps_wallet_recovery_exercise.read_text(encoding="utf-8")),
        expected_chain_id=chain_id,
    )
    rotation = evaluate_perps_wallet_rotation_exercise_v1(
        perps_profile,
        json.loads(bundle.perps_wallet_rotation_exercise.read_text(encoding="utf-8")),
        expected_chain_id=chain_id,
    )
    device_approval = evaluate_perps_wallet_device_approval_exercise_v1(
        perps_profile,
        json.loads(bundle.perps_wallet_device_approval_exercise.read_text(encoding="utf-8")),
        expected_chain_id=chain_id,
    )
    signer_device = evaluate_perps_wallet_signer_device_integration_v1(
        perps_profile,
        json.loads(bundle.perps_wallet_signer_device_integration.read_text(encoding="utf-8")),
        expected_chain_id=chain_id,
    )
    signer_prompt = evaluate_perps_wallet_signer_prompt_capture_v1(
        perps_profile,
        json.loads(bundle.perps_wallet_signer_prompt_capture.read_text(encoding="utf-8")),
        expected_chain_id=chain_id,
    )
    signer_execution = evaluate_perps_wallet_signer_execution_exercise_v1(
        perps_profile,
        json.loads(bundle.perps_wallet_signer_execution_exercise.read_text(encoding="utf-8")),
        expected_chain_id=chain_id,
    )
    signer_ceremony = evaluate_perps_wallet_signer_ceremony_v1(
        wallet_authority_hash=perps_profile["wallet_authority_hash"],
        device_approval_status=device_approval,
        signer_device_status=signer_device,
        signer_prompt_capture_status=signer_prompt,
        signer_execution_status=signer_execution,
    )
    hardware_custody = evaluate_perps_wallet_hardware_custody_v1(
        wallet_authority_hash=perps_profile["wallet_authority_hash"],
        device_approval_status=device_approval,
        signer_device_status=signer_device,
        signer_prompt_capture_status=signer_prompt,
        signer_execution_status=signer_execution,
        signer_ceremony_status=signer_ceremony,
    )
    encrypted_sss_backup = evaluate_perps_wallet_encrypted_sss_backup_v1(
        perps_profile,
        json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8")),
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys_from_fixture_v1(
            json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
        ),
    )
    assert recovery["recovery_exercise_ready"] is True, recovery["errors"]
    assert rotation["rotation_exercise_ready"] is True, rotation["errors"]
    assert device_approval["device_approval_ready"] is True, device_approval["errors"]
    assert signer_device["signer_device_ready"] is True, signer_device["errors"]
    assert signer_prompt["signer_prompt_capture_ready"] is True, signer_prompt["errors"]
    assert signer_execution["signer_execution_ready"] is True, signer_execution["errors"]
    assert signer_ceremony["signer_ceremony_ready"] is True, signer_ceremony["errors"]
    assert hardware_custody["hardware_custody_ready"] is True, hardware_custody["errors"]
    assert hardware_custody["production_hardware_custody_ready"] is False
    assert hardware_custody["custody_evidence_mode"] == "local_fixture"
    assert encrypted_sss_backup["encrypted_sss_backup_ready"] is True, encrypted_sss_backup["errors"]
    assert encrypted_sss_backup["threshold"] == 3
    assert set(encrypted_sss_backup["storage_provider_kinds"]) >= {"recovery_email", "cloud_drive", "offline_export"}
    assert encrypted_sss_backup["provider_delivery_ready"] is True
    assert encrypted_sss_backup["live_provider_delivery_ready"] is False
    assert encrypted_sss_backup["delivery_modes"] == ["local_fixture"]
    assert encrypted_sss_backup["external_audit_ready"] is False

    autotrader_profile = json.loads(bundle.autotrader_supervisor_profile.read_text(encoding="utf-8"))
    autotrader_status = evaluate_autotrader_supervisor_profile_v1(
        autotrader_profile,
        expected_chain_id=chain_id,
    )
    assert autotrader_status["ok"] is True, autotrader_status["readiness_gaps"]


def test_encrypted_sss_shamir_recovery_and_duplicate_rejection() -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import (
        recover_secret_shamir_gf256,
        split_secret_shamir_gf256,
    )

    secret = bytes(range(32))
    shares = split_secret_shamir_gf256(
        secret,
        threshold=3,
        share_count=5,
        coefficient_seed=b"local-testnet-sss-unit-seed",
    )
    assert recover_secret_shamir_gf256(shares[:3]) == secret
    assert recover_secret_shamir_gf256([shares[0], shares[2], shares[4]]) == secret
    assert recover_secret_shamir_gf256(shares[:2]) != secret
    with pytest.raises(ValueError, match="duplicate share"):
        recover_secret_shamir_gf256([shares[0], shares[0], shares[2]])


def test_encrypted_sss_backup_evaluator_rejects_tampered_envelope(tmp_path: Path) -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import (
        evaluate_perps_wallet_encrypted_sss_backup_v1,
        recipient_root_keys_from_fixture_v1,
    )
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    recipient_root_keys = recipient_root_keys_from_fixture_v1(
        json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
    )
    assert evaluate_perps_wallet_encrypted_sss_backup_v1(
        profile,
        backup,
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys,
    )["encrypted_sss_backup_ready"] is True

    backup["envelopes"][0]["ciphertext_b64"] = backup["envelopes"][0]["ciphertext_b64"][:-4] + "AAAA"
    tampered = evaluate_perps_wallet_encrypted_sss_backup_v1(
        profile,
        backup,
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys,
    )
    assert tampered["encrypted_sss_backup_ready"] is False
    assert "encrypted SSS backup hash mismatch" in tampered["errors"]


def test_encrypted_sss_backup_evaluator_replays_recovery_after_rehashed_tamper(tmp_path: Path) -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import (
        evaluate_perps_wallet_encrypted_sss_backup_v1,
        perps_wallet_encrypted_sss_backup_hash_v1,
        perps_wallet_encrypted_sss_delivery_hash_v1,
        perps_wallet_encrypted_sss_envelope_hash_v1,
        recipient_root_keys_from_fixture_v1,
    )
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    recipient_root_keys = recipient_root_keys_from_fixture_v1(
        json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
    )
    envelope = backup["envelopes"][0]
    envelope["ciphertext_b64"] = envelope["ciphertext_b64"][:-4] + "AAAA"
    envelope["envelope_hash"] = perps_wallet_encrypted_sss_envelope_hash_v1(envelope)
    for delivery in backup["delivery_evidence"]:
        if delivery["envelope_id"] == envelope["envelope_id"]:
            delivery["envelope_hash"] = envelope["envelope_hash"]
            delivery["delivery_hash"] = perps_wallet_encrypted_sss_delivery_hash_v1(delivery)
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)

    tampered = evaluate_perps_wallet_encrypted_sss_backup_v1(
        profile,
        backup,
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys,
    )
    assert tampered["encrypted_sss_backup_ready"] is False
    assert any("encrypted SSS replay decrypt failed" in err for err in tampered["errors"])


def test_encrypted_sss_public_fields_do_not_recover_key_from_one_share(tmp_path: Path) -> None:
    import hashlib

    from src.integration.perps_wallet_encrypted_sss_backup import (
        _decrypt_share_envelope,
        _derive_coefficient,
        _gf_mul,
        recipient_root_keys_from_fixture_v1,
    )
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    recipient_root_keys = recipient_root_keys_from_fixture_v1(
        json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
    )
    envelope = backup["envelopes"][0]
    share = _decrypt_share_envelope(
        backup_id=backup["backup_id"],
        wallet_authority_hash=backup["wallet_authority_hash"],
        envelope=envelope,
        recipient_root_key=recipient_root_keys[envelope["recipient_id"]],
    )

    public_seed = hashlib.blake2b(
        b"zenodex-localtest-sss-coefficients-v1|"
        + backup["wallet_authority_hash"].encode("utf-8")
        + b"|"
        + backup["subject_key_id"].encode("utf-8"),
        digest_size=32,
    ).digest()
    x = int(envelope["x"])
    x2 = _gf_mul(x, x)
    guessed_secret = bytes(
        y
        ^ _gf_mul(_derive_coefficient(public_seed, byte_index=index, degree=1), x)
        ^ _gf_mul(_derive_coefficient(public_seed, byte_index=index, degree=2), x2)
        for index, y in enumerate(share)
    )
    subject_public_key = next(
        item["public_key"]
        for item in profile["key_manager"]["key_refs"]
        if item["key_id"] == backup["subject_key_id"]
    )
    try:
        guessed_public_key = "0x" + bls_pubkey_hex_from_privkey(guessed_secret)
    except ValueError:
        guessed_public_key = None
    assert guessed_public_key != subject_public_key


def test_encrypted_sss_backup_requires_trusted_replay_keys(tmp_path: Path) -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import evaluate_perps_wallet_encrypted_sss_backup_v1
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))

    blocked = evaluate_perps_wallet_encrypted_sss_backup_v1(profile, backup, expected_chain_id=chain_id)
    assert blocked["encrypted_sss_backup_ready"] is False
    assert "encrypted SSS trusted recipient replay keys are missing" in blocked["errors"]


def test_encrypted_sss_backup_requires_delivery_receipts(tmp_path: Path) -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import (
        evaluate_perps_wallet_encrypted_sss_backup_v1,
    )
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    backup.pop("delivery_evidence")

    blocked = evaluate_perps_wallet_encrypted_sss_backup_v1(profile, backup, expected_chain_id=chain_id)
    assert blocked["encrypted_sss_backup_ready"] is False
    assert "delivery_evidence must be a list" in blocked["errors"]


def test_encrypted_sss_backup_accepts_live_delivery_receipts(tmp_path: Path) -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import (
        build_perps_wallet_encrypted_sss_live_delivery_receipt_v1,
        evaluate_perps_wallet_encrypted_sss_backup_v1,
        perps_wallet_encrypted_sss_backup_hash_v1,
        recipient_root_keys_from_fixture_v1,
    )
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    receipt_by_kind = {
        "recovery_email": {"delivery_mode": "smtp", "smtp_message_id": "smtp:msg-1"},
        "cloud_drive": {"delivery_mode": "dropbox", "provider_file_id": "dropbox:file-1", "provider_revision": "rev-a"},
        "offline_export": {"delivery_mode": "offline_export", "offline_export_manifest_hash": "0x" + "44" * 32},
    }
    backup["delivery_evidence"] = [
        build_perps_wallet_encrypted_sss_live_delivery_receipt_v1(
            envelope,
            delivered_at_epoch=15,
            receipt_reference=f"live-delivery:{index}",
            provider_response_hash="0x" + f"{index:064x}"[-64:],
            **receipt_by_kind[str(envelope["provider_kind"])],
        )
        for index, envelope in enumerate(backup["envelopes"], start=1)
    ]
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)

    ready = evaluate_perps_wallet_encrypted_sss_backup_v1(
        profile,
        backup,
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys_from_fixture_v1(
            json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
        ),
    )

    assert ready["encrypted_sss_backup_ready"] is True, ready["errors"]
    assert ready["provider_delivery_ready"] is True
    assert ready["live_provider_delivery_ready"] is True
    assert set(ready["delivery_modes"]) == {"smtp", "dropbox", "offline_export"}


def test_perps_wallet_api_has_no_local_provider_delivery_route(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.integration import perps_wallet_api
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    recipient_keys = json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("PERPS_WALLET_AUTHORITY_PROFILE_JSON", json.dumps(profile, sort_keys=True))
    monkeypatch.setenv("PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_JSON", json.dumps(recipient_keys, sort_keys=True))

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/encrypted-sss-backup/deliver-local",
        json.dumps({"chain_id": chain_id, "backup": backup}).encode("utf-8"),
    )

    assert status_code == 404, payload
    assert payload["ok"] is False
    assert payload["error"] == "not_found"


def test_perps_wallet_api_real_provider_delivery_fails_closed_without_provider_config(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.integration import perps_wallet_api
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    recipient_keys = json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("PERPS_WALLET_AUTHORITY_PROFILE_JSON", json.dumps(profile, sort_keys=True))
    monkeypatch.setenv("PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_JSON", json.dumps(recipient_keys, sort_keys=True))

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/encrypted-sss-backup/deliver",
        json.dumps({"chain_id": chain_id, "backup": backup}).encode("utf-8"),
    )

    assert status_code == 400, payload
    assert payload["ok"] is False
    assert str(payload["error"]).startswith("encrypted_sss_delivery_provider_not_configured:")
    assert "PERPS_WALLET_ENCRYPTED_SSS_SMTP_HOST" in payload["error"]
    assert "PERPS_WALLET_ENCRYPTED_SSS_DROPBOX_ACCESS_TOKEN" in payload["error"]
    assert "PERPS_WALLET_ENCRYPTED_SSS_BOX_ACCESS_TOKEN" in payload["error"]
    assert "PERPS_WALLET_ENCRYPTED_SSS_OFFLINE_EXPORT_DIR" in payload["error"]
    assert "backup" not in payload


def test_perps_wallet_api_real_provider_delivery_redacts_backup_material(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from src.integration import perps_wallet_api
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    recipient_keys = json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
    backup["envelopes"] = [item for item in backup["envelopes"] if item.get("provider_kind") == "offline_export"]
    export_dir = tmp_path / "sss-export"
    export_dir.mkdir()
    monkeypatch.setenv("TAU_DEX_CHAIN_ID", chain_id)
    monkeypatch.setenv("PERPS_WALLET_AUTHORITY_PROFILE_JSON", json.dumps(profile, sort_keys=True))
    monkeypatch.setenv("PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_JSON", json.dumps(recipient_keys, sort_keys=True))
    monkeypatch.setenv("PERPS_WALLET_ENCRYPTED_SSS_OFFLINE_EXPORT_DIR", str(export_dir))

    status_code, payload = perps_wallet_api.handle_perps_wallet_request(
        "POST",
        "/api/perps/wallet/encrypted-sss-backup/deliver",
        json.dumps({"chain_id": chain_id, "backup": backup}).encode("utf-8"),
    )

    assert status_code == 400, payload
    assert payload["ok"] is False
    assert payload["backup_redacted"] is True
    assert payload["backup_hash"] == payload["encrypted_sss_backup"]["backup_hash"]
    assert len(payload["delivery_evidence_hashes"]) == 1
    assert "backup" not in payload
    assert "ciphertext_b64" not in json.dumps(payload, sort_keys=True)
    assert list(export_dir.iterdir())


def test_encrypted_sss_live_delivery_receipt_requires_provider_evidence(tmp_path: Path) -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import (
        evaluate_perps_wallet_encrypted_sss_backup_v1,
        perps_wallet_encrypted_sss_backup_hash_v1,
        perps_wallet_encrypted_sss_delivery_hash_v1,
    )
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    delivery = backup["delivery_evidence"][0]
    delivery["delivery_mode"] = "smtp"
    delivery["receipt_reference"] = "smtp:missing-provider-message"
    delivery["delivery_hash"] = perps_wallet_encrypted_sss_delivery_hash_v1(delivery)
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)

    blocked = evaluate_perps_wallet_encrypted_sss_backup_v1(profile, backup, expected_chain_id=chain_id)

    assert blocked["encrypted_sss_backup_ready"] is False
    assert "encrypted SSS live delivery evidence provider_response_hash is invalid" in blocked["errors"]
    assert "encrypted SSS smtp delivery evidence missing smtp_message_id" in blocked["errors"]


def test_encrypted_sss_external_audit_evidence_is_signed_and_bound(tmp_path: Path) -> None:
    from src.integration.perps_wallet_encrypted_sss_backup import (
        PERPS_WALLET_ENCRYPTED_SSS_AUDIT_EVIDENCE_SCHEMA_V1,
        PERPS_WALLET_ENCRYPTED_SSS_AUDIT_PAYLOAD_KIND_V1,
        evaluate_perps_wallet_encrypted_sss_backup_v1,
        perps_wallet_encrypted_sss_audit_evidence_hash_v1,
        perps_wallet_encrypted_sss_audit_subject_hash_v1,
        perps_wallet_encrypted_sss_backup_hash_v1,
        recipient_root_keys_from_fixture_v1,
    )
    from src.integration.zeno_ledger_signature import (
        bls_public_key_hex_from_private_key_v0,
        build_bls_signed_artifact_envelope_v0,
    )
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )
    profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    backup = json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8"))
    auditor_private_key = "0x" + "09" * 32
    auditor_public_key = bls_public_key_hex_from_private_key_v0(auditor_private_key)
    backup["audit_status"] = "external-audit-completed"
    audit = {
        "schema": PERPS_WALLET_ENCRYPTED_SSS_AUDIT_EVIDENCE_SCHEMA_V1,
        "audit_id": "sss-audit-2026-05-local",
        "audit_required_for_production": True,
        "external_audit_ready": True,
        "audit_status": "external-audit-completed",
        "audit_subject_hash": perps_wallet_encrypted_sss_audit_subject_hash_v1(backup),
        "audit_report_hash": "0x" + "55" * 32,
        "wallet_authority_hash": backup["wallet_authority_hash"],
        "findings_status": "no-critical-open",
        "issued_at_epoch": 16,
        "auditor_id": "external-auditor-a",
        "auditor_public_key": auditor_public_key,
    }
    audit["audit_hash"] = perps_wallet_encrypted_sss_audit_evidence_hash_v1(audit)
    audit["signature_envelope"] = build_bls_signed_artifact_envelope_v0(
        payload_kind=PERPS_WALLET_ENCRYPTED_SSS_AUDIT_PAYLOAD_KIND_V1,
        payload_hash=audit["audit_hash"],
        signer_id="external-auditor-a",
        key_id="external-auditor-a-bls",
        private_key_hex=auditor_private_key,
    )
    backup["audit_evidence"] = audit
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)

    ready = evaluate_perps_wallet_encrypted_sss_backup_v1(
        profile,
        backup,
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys_from_fixture_v1(
            json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
        ),
    )

    assert ready["encrypted_sss_backup_ready"] is True, ready["errors"]
    assert ready["external_audit_ready"] is True

    backup["audit_evidence"]["audit_subject_hash"] = "0x" + "66" * 32
    backup["audit_evidence"]["audit_hash"] = perps_wallet_encrypted_sss_audit_evidence_hash_v1(
        backup["audit_evidence"]
    )
    backup["backup_hash"] = perps_wallet_encrypted_sss_backup_hash_v1(backup)
    blocked = evaluate_perps_wallet_encrypted_sss_backup_v1(
        profile,
        backup,
        expected_chain_id=chain_id,
        recipient_root_keys=recipient_root_keys_from_fixture_v1(
            json.loads(bundle.perps_wallet_encrypted_sss_recipient_keys.read_text(encoding="utf-8"))
        ),
    )
    assert blocked["encrypted_sss_backup_ready"] is False
    assert "encrypted SSS external audit evidence subject hash mismatch" in blocked["errors"]
    assert any("signature invalid" in error for error in blocked["errors"])


def test_encrypted_sss_backup_fixture_has_no_plaintext_share_material(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    rendered = bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8")
    forbidden = ("privkey_hex", "private_key", "raw_share", "share_plaintext", "plaintext_share_bytes")
    for needle in forbidden:
        assert needle not in rendered


def test_fixture_seed_and_random_are_mutually_exclusive(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    with pytest.raises(ValueError, match="mutually exclusive"):
        fx.generate_fixture_bundle(
            out_dir=tmp_path,
            chain_id="zeno-ledger-localtest-v0",
            network_id="zeno-ledger-localtest-v0",
            seed_override_hex="ab" * 32,
            use_random=True,
        )


def test_fixture_seed_override_rejects_bad_length(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    with pytest.raises(ValueError, match="32 bytes"):
        fx.generate_fixture_bundle(
            out_dir=tmp_path,
            chain_id="zeno-ledger-localtest-v0",
            network_id="zeno-ledger-localtest-v0",
            seed_override_hex="ab" * 16,
        )


def test_lifecycle_seed_resolution_default_matches_fixture_derivation(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx
    from tools.zenoctl_testnet_local import lifecycle as lc

    opts = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
    )
    assert lc._resolve_fixture_seed(opts) == fx.derive_seed(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
    )


def test_lifecycle_seed_resolution_uses_override(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    override = "ab" * 32
    opts = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        seed_override_hex=override,
    )
    assert lc._resolve_fixture_seed(opts) == bytes.fromhex(override)


def test_lifecycle_seed_resolution_validates_override(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    bad_len = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        seed_override_hex="ab" * 16,
    )
    with pytest.raises(ValueError, match="32 bytes"):
        lc._resolve_fixture_seed(bad_len)

    bad_hex = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        seed_override_hex="zz" * 32,
    )
    with pytest.raises(ValueError, match="valid hex"):
        lc._resolve_fixture_seed(bad_hex)


def test_lifecycle_seed_resolution_random_mode_uses_token_bytes(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setattr(lc.secrets, "token_bytes", lambda n: b"\x42" * n)
    opts = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        use_random_seed=True,
    )
    assert lc._resolve_fixture_seed(opts) == b"\x42" * 32


# ---------------------------------------------------------------------------
# Nginx render
# ---------------------------------------------------------------------------


def _nginx_inputs():
    from tools.zenoctl_testnet_local.nginx import NginxRenderInputs

    return NginxRenderInputs(
        writer_upstream="zeno-ledger-writer:8787",
        stdlib_upstream="zenodex-api:8000",
        oracle_upstream="zenodex-oracle:9100",
        writer_token="writer-secret-abc",
        stdlib_token="stdlib-secret-xyz",
    )


def test_nginx_template_renders_all_required_location_blocks() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    for block in ng.EXPECTED_LOCATION_BLOCKS:
        assert block in rendered, f"missing nginx location block: {block!r}"


def test_nginx_path_split_targets_correct_upstreams() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    # Spot read and mutation endpoints go to writer with URI passed through.
    assert "http://zeno-ledger-writer:8787/api/pools" in rendered
    assert "http://zeno-ledger-writer:8787/api/swap" in rendered
    assert "http://zeno-ledger-writer:8787/api/liquidity/create" in rendered
    assert "http://zeno-ledger-writer:8787/api/liquidity/add" in rendered
    assert "http://zeno-ledger-writer:8787/api/liquidity/remove" in rendered
    assert "http://zeno-ledger-writer:8787/faucet" in rendered
    assert "http://zeno-ledger-writer:8787/api/tokenomics/status" in rendered
    assert "http://zeno-ledger-writer:8787/tx" in rendered
    assert "http://zeno-ledger-writer:8787/public_network_config.json" in rendered
    assert "http://zeno-ledger-writer:8787/status" in rendered
    assert "http://zeno-ledger-writer:8787/features" in rendered
    assert "http://zeno-ledger-writer:8787/tokens" in rendered
    assert "http://zeno-ledger-writer:8787/network" in rendered
    assert "http://zeno-ledger-writer:8787/live" in rendered
    # /api/oracle/ → oracle. proxy_pass omits the trailing slash so the
    # full URI (/api/oracle/...) is preserved, matching the oracle
    # service's route table at tools/zenodex_oracle.py:/api/oracle/*.
    assert "proxy_pass http://zenodex-oracle:9100;" in rendered
    # /api/ (everything else) → stdlib API, also preserving the URI so
    # routes like /api/zusd/wallet/* reach src/integration/api_server.py.
    assert "proxy_pass http://zenodex-api:8000;" in rendered


def test_nginx_has_no_plaintext_fixture_key_api_route() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    assert "location = /api/local-testnet/fixture-key" not in rendered


def test_nginx_injects_bearer_tokens_for_writer_and_stdlib() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    assert 'Bearer writer-secret-abc' in rendered
    assert 'Bearer stdlib-secret-xyz' in rendered


def test_nginx_token_injected_routes_have_browser_request_guards() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    assert "map $http_origin $zenodex_origin_ok" in rendered
    assert 'map "$request_method:$http_content_type" $zenodex_write_content_type_ok' in rendered
    for block in ng.WRITER_MUTATION_LOCATION_BLOCKS:
        chunk = ng._extract_location_block(rendered, block)
        assert "if ($zenodex_origin_ok = 0) { return 403; }" in chunk
        assert "if ($zenodex_write_content_type_ok = 0) { return 415; }" in chunk
    stdlib_chunk = ng._extract_location_block(rendered, "location ^~ /api/ {")
    assert "if ($zenodex_origin_ok = 0) { return 403; }" in stdlib_chunk


def test_nginx_origin_guard_allows_cloudflare_quick_tunnel() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())

    assert "trycloudflare\\.com" in rendered


def test_nginx_does_not_inject_writer_token_into_oracle_block() -> None:
    """The oracle does not get a token injection; writer/stdlib do."""
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    # Slice out the oracle block. The template uses ^~ prefix to make
    # /api/oracle/ take precedence over the /api/ catch-all.
    oracle_idx = rendered.index("location ^~ /api/oracle/")
    next_block = rendered.find("location ^~ /api/", oracle_idx + 1)
    assert next_block > oracle_idx, "expected stdlib /api/ block after oracle block"
    oracle_chunk = rendered[oracle_idx:next_block]
    assert "Bearer" not in oracle_chunk, "oracle block must not inject Bearer"


def test_nginx_preserves_nginx_variables() -> None:
    """nginx variables like $binary_remote_addr must NOT be substituted by
    our template renderer."""
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    assert "$binary_remote_addr" in rendered
    assert "$remote_addr" in rendered
    assert "$host" in rendered


def test_nginx_listens_on_port_8080_only() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    # Single 'listen' directive inside the server{} block.
    assert "listen 8080;" in rendered
    # No 'listen 80' or arbitrary other ports leaked from a typo
    bad_listens = [
        line for line in rendered.splitlines()
        if line.strip().startswith("listen ") and "8080" not in line
    ]
    assert not bad_listens, f"unexpected listen directives: {bad_listens}"


def test_nginx_render_rejects_empty_token() -> None:
    from tools.zenoctl_testnet_local import nginx as ng
    import dataclasses

    with pytest.raises(ValueError, match="non-empty"):
        ng.render_nginx_conf(dataclasses.replace(_nginx_inputs(), writer_token=""))


def test_nginx_render_rejects_malformed_upstream() -> None:
    from tools.zenoctl_testnet_local import nginx as ng
    import dataclasses

    with pytest.raises(ValueError, match="host:port"):
        ng.render_nginx_conf(dataclasses.replace(_nginx_inputs(), writer_upstream="no-port"))


def test_runtime_config_has_no_tokens() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    runtime = ng.render_runtime_config(demo_mode=False)
    parsed = json.loads(runtime)
    assert parsed["demoMode"] is False
    assert parsed["allowDemoMode"] is False
    assert parsed["apiBase"] == ""
    assert parsed["zenoOracleApiBase"] == ""
    assert parsed["oracleApiBase"] == ""
    assert parsed["allowBrowserKeyGeneration"] is True
    assert parsed["allowDefaultExternalSigner"] is True
    assert parsed["uiSurfaceContractSchema"] == "zenodex.dex_ui.surface_contract.v1"
    assert parsed["uiSurfaceContractVersion"] == ng.ui_surface_contract_version()
    assert parsed["uiSurfaceContractHash"] == ng.ui_surface_contract_hash()
    assert parsed["defaultExternalSigner"] == {
        "schema": "zenodex/dex-ui/runtime-default-external-signer/v0",
        "signerSecurityProfile": "native-desktop-loopback-signer-v0",
        "connectUrl": "http://127.0.0.1:8799/public-receipt",
        "signTauTransactionPayloadUrl": "http://127.0.0.1:8799/sign-tau-transaction-payload",
        "signDexIntentForEngineUrl": "http://127.0.0.1:8799/sign-dex-intent",
    }
    # No bearer-token-like fields
    serialized = json.dumps(parsed, sort_keys=True)
    assert "Bearer" not in serialized
    assert "writer" not in serialized.lower()
    assert "token" not in serialized.lower()
    assert parsed["perpsWalletUiEnabled"] is False
    assert parsed["zusdTauWalletUiEnabled"] is False
    assert parsed["zusdMonetaryWalletUiEnabled"] is False


def test_runtime_config_rejects_overriding_builtin_keys() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    with pytest.raises(ValueError, match="conflicts"):
        ng.render_runtime_config(extra={"demoMode": True})
    with pytest.raises(ValueError, match="conflicts"):
        ng.render_runtime_config(extra={"allowDemoMode": True})
    with pytest.raises(ValueError, match="conflicts"):
        ng.render_runtime_config(extra={"allowBrowserKeyGeneration": False})
    with pytest.raises(ValueError, match="conflicts"):
        ng.render_runtime_config(extra={"defaultExternalSigner": {}})
    with pytest.raises(ValueError, match="conflicts"):
        ng.render_runtime_config(extra={"uiSurfaceContractVersion": "old-ui"})
    for field in (
        "perpsWalletUiEnabled",
        "zusdTauWalletUiEnabled",
        "zusdMonetaryWalletUiEnabled",
    ):
        with pytest.raises(ValueError, match="conflicts"):
            ng.render_runtime_config(extra={field: True})


def test_existing_runtime_config_refresh_updates_ui_contract(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import nginx as ng

    path = tmp_path / "zenodex-config.json"
    path.write_text(
        json.dumps(
            {
                "demoMode": True,
                "perpsWalletUiEnabled": True,
                "zusdTauWalletUiEnabled": True,
                "zusdMonetaryWalletUiEnabled": True,
                "uiSurfaceContractSchema": "zenodex.dex_ui.surface_contract.v1",
                "uiSurfaceContractVersion": "old-ui",
                "uiSurfaceContractHash": "sha256:stale",
            }
        ),
        encoding="utf-8",
    )

    lc._refresh_existing_runtime_config(path)
    parsed = json.loads(path.read_text(encoding="utf-8"))

    assert parsed["demoMode"] is False
    assert parsed["allowBrowserKeyGeneration"] is True
    assert parsed["perpsWalletUiEnabled"] is False
    assert parsed["zusdTauWalletUiEnabled"] is False
    assert parsed["zusdMonetaryWalletUiEnabled"] is False
    assert parsed["uiSurfaceContractSchema"] == "zenodex.dex_ui.surface_contract.v1"
    assert parsed["uiSurfaceContractVersion"] == ng.ui_surface_contract_version()
    assert parsed["uiSurfaceContractHash"] == ng.ui_surface_contract_hash()


def test_token_leak_guard_fires_when_token_present(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    leaky = tmp_path / "leaky.json"
    leaky.write_text(json.dumps({"oops": "writer-secret-abc"}))
    with pytest.raises(AssertionError, match="SECURITY"):
        ng.assert_no_token_in_file(leaky, "writer-secret-abc")


def test_token_leak_guard_silent_when_clean(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    clean = tmp_path / "clean.json"
    clean.write_text(json.dumps({"foo": "bar"}))
    ng.assert_no_token_in_file(clean, "writer-secret-abc")  # no raise


# ---------------------------------------------------------------------------
# Compose overlay
# ---------------------------------------------------------------------------


def _load_compose_overlay() -> dict:
    return yaml.safe_load(COMPOSE_OVERLAY.read_text(encoding="utf-8"))


def _load_multimachine() -> dict:
    return yaml.safe_load(COMPOSE_MULTIMACHINE.read_text(encoding="utf-8"))


def test_compose_overlay_has_all_expected_services() -> None:
    doc = _load_compose_overlay()
    expected = {
        "zeno-ledger-bootstrap",
        "zeno-ledger-writer",
        "zeno-ledger-forwarder",
        "zeno-ledger-readonly",
        "tau-local",
        "zenodex-oracle",
        "zenodex-api",
        "zenodex-nginx",
    }
    assert set(doc["services"].keys()) == expected


def test_compose_overlay_only_nginx_exposes_host_ports() -> None:
    doc = _load_compose_overlay()
    for name, svc in doc["services"].items():
        ports = svc.get("ports") or []
        if name == "zenodex-nginx":
            assert ports, "nginx must expose a port"
        else:
            assert not ports, f"service {name!r} must NOT expose host ports, got {ports}"


def test_compose_overlay_nginx_binds_loopback_only() -> None:
    doc = _load_compose_overlay()
    ports = doc["services"]["zenodex-nginx"].get("ports") or []
    assert ports, "nginx ports missing"
    for p in ports:
        # Each binding must include 127.0.0.1; reject 0.0.0.0 or implicit-any binds.
        assert "127.0.0.1" in p, f"nginx must bind loopback only, got {p!r}"


def test_compose_overlay_image_refs_match_multimachine() -> None:
    """The local-testnet overlay reuses Dockerfile.operator-tools (image
    `zenodex/operator-tools:local`). It must agree with the multimachine
    file on that image tag to avoid silent build drift."""
    overlay = _load_compose_overlay()
    multi = _load_multimachine()
    multi_writer_image = multi["services"]["zeno-ledger-writer"]["image"]
    overlay_writer_image = overlay["services"]["zeno-ledger-writer"]["image"]
    assert (
        overlay_writer_image == multi_writer_image
    ), f"image drift: overlay={overlay_writer_image} vs multimachine={multi_writer_image}"


def test_compose_overlay_api_command_respects_operator_tools_entrypoint() -> None:
    doc = _load_compose_overlay()
    command = doc["services"]["zenodex-api"]["command"]
    assert command[:2] == ["-m", "src.integration.api_server"]


def test_compose_overlay_api_does_not_enable_demo_or_fixture_shortcuts() -> None:
    doc = _load_compose_overlay()
    env = doc["services"]["zenodex-api"]["environment"]
    assert env.get("ALLOW_DEMO_TOKEN_AUTH") not in {"1", "true", True}
    assert "DEMO_API_TOKEN" not in env
    assert "ZENODEX_API_BEARER_TOKEN" in env
    assert env.get("LOCAL_TESTNET_ALLOW_PLAINTEXT_FIXTURE_KEYS") not in {"1", "true", True}
    assert env.get("LOCAL_TESTNET_FIXTURE_KEY_API_ENABLED") not in {"1", "true", True}
    assert "LOCAL_TESTNET_FIXTURE_KEY_BUNDLE_FILE" not in env
    assert env.get("PERPS_API_ENABLED") == "false"
    assert env.get("ZUSD_API_ENABLED") == "false"


def test_compose_overlay_bootstrap_service_has_writer_token_for_controller_runs() -> None:
    doc = _load_compose_overlay()
    service = doc["services"]["zeno-ledger-bootstrap"]
    env = service["environment"]
    assert "ZENO_LEDGER_WRITER_TOKEN" in env
    assert env["ZENO_LEDGER_TOKEN_SYMBOL"] == "${ZENO_LEDGER_TOKEN_SYMBOL:-ZDEX}"
    assert "/app/fixtures/role_pubkeys.json" in service["command"]
    assert "${FIXTURES_DIR:?FIXTURES_DIR must be set by the orchestrator}:/app/fixtures:ro" in service["volumes"]
    assert all("/app/local-secrets" not in volume for volume in service["volumes"])


def test_compose_overlay_readonly_authenticates_controller_rejection_probe() -> None:
    doc = _load_compose_overlay()
    service = doc["services"]["zeno-ledger-readonly"]
    command = service["command"]
    assert service["environment"] == doc["services"]["zeno-ledger-writer"]["environment"]
    assert "--write-auth-token-env" in command
    assert "ZENO_LEDGER_WRITER_TOKEN" in command
    assert "--min-lp-position-age-seconds" in command
    assert "${ZENO_LEDGER_MIN_LP_POSITION_AGE_SECONDS:-300}" in command
    assert "--lp-duration-risk-policy" in command
    assert "${ZENO_LEDGER_LP_DURATION_RISK_POLICY:-zeno-oracle}" in command
    assert "--enable-testnet-faucet" not in command
    assert "--enable-testnet-intake" not in command


def test_compose_overlay_tau_local_enables_balance_patch_for_local_state_bootstrap() -> None:
    doc = _load_compose_overlay()
    env = doc["services"]["tau-local"]["environment"]
    assert env["TAU_ENABLE_FAUCET"] == "1"
    assert env["TAU_DEX_FAUCET"] == "1"
    assert env["TAU_DEX_TOKEN_SYMBOL"] == "${ZENO_LEDGER_TOKEN_SYMBOL:-ZDEX}"
    assert env["TAU_DEX_ALLOW_MISSING_SETTLEMENT"] == "1"
    assert env["TAU_APP_BRIDGE_ALLOW_BALANCE_PATCH"] == "1"


def test_compose_overlay_quarantines_retired_perps_and_zusd_monetary_routes() -> None:
    doc = _load_compose_overlay()
    env = doc["services"]["zenodex-api"]["environment"]
    assert env["PERPS_WALLET_API_ENABLED"] == "false"
    assert env["PERPS_WALLET_ALLOW_LOCAL_SIGNING"] == "false"
    assert env["PERPS_WALLET_AUTO_MINE"] == "false"
    assert env["PERPS_WALLET_TESTNET_FAUCET_ENABLED"] == "false"
    assert env["ZUSD_MONETARY_WALLET_API_ENABLED"] == "false"
    assert env["ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING"] == "false"
    assert env["ZUSD_MONETARY_WALLET_AUTO_MINE"] == "false"


def test_quarantined_api_mount_has_no_retired_route_reconstitution_material() -> None:
    doc = _load_compose_overlay()
    service = doc["services"]["zenodex-api"]
    env = service["environment"]
    forbidden_environment = {
        "PERPS_WALLET_AUTHORITY_PROFILE_FILE",
        "PERPS_WALLET_RECOVERY_EXERCISE_FILE",
        "PERPS_WALLET_ROTATION_EXERCISE_FILE",
        "PERPS_WALLET_DEVICE_APPROVAL_EXERCISE_FILE",
        "PERPS_WALLET_SIGNER_DEVICE_INTEGRATION_FILE",
        "PERPS_WALLET_SIGNER_PROMPT_CAPTURE_FILE",
        "PERPS_WALLET_SIGNER_EXECUTION_EXERCISE_FILE",
        "PERPS_WALLET_ENCRYPTED_SSS_BACKUP_FILE",
        "PERPS_WALLET_ENCRYPTED_SSS_RECIPIENT_KEYS_FILE",
    }

    assert forbidden_environment.isdisjoint(env)
    assert all("/app/fixtures" not in str(volume) for volume in service.get("volumes", []))


def test_historical_donor_helpers_refuse_before_any_effect() -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    calls: tuple[tuple[Callable[..., object], dict[str, object]], ...] = (
        (
            lc._seed_api_state_historical_donor,
            {
                "engine": None,
                "project": "retired",
                "env": {},
                "roles": {},
                "chain_id": "retired",
                "tau_rpc_timeout_s": 1.0,
            },
        ),
        (
            lc._materialize_release_native_collateral_historical_donor,
            {
                "engine": None,
                "compose_project": "retired",
                "env": {},
                "roles": {},
                "amount_e8": 1,
            },
        ),
        (
            lc._run_release_flow_smoke_historical_donor,
            {
                "ui_base": "http://127.0.0.1:1",
                "paths": None,
                "manifest": {},
                "engine": None,
                "compose_project": "retired",
                "env": {},
            },
        ),
        (
            lc._run_cloudflare_quick_tunnel_historical_donor,
            {"opts": None, "paths": None, "manifest": {}},
        ),
        (
            lc._zusd_transfer_payload_historical_donor,
            {"ui_base": "http://127.0.0.1:1", "roles": {}, "deadline": 0},
        ),
        (
            lc._run_perps_wallet_cycle_smoke_historical_donor,
            {
                "ui_base": "http://127.0.0.1:1",
                "market_id": "retired",
                "roles": {},
                "deadline": 0,
            },
        ),
    )

    for helper, kwargs in calls:
        with pytest.raises(RuntimeError, match="retired Tau value routes"):
            helper(**kwargs)


def test_compose_overlay_autotrader_uses_persistent_execution_journal() -> None:
    doc = _load_compose_overlay()
    env = doc["services"]["zenodex-api"]["environment"]
    assert env["AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH"] == "/tmp/autotrader_execution_journal.jsonl"


def test_seed_api_state_rejects_current_profile_before_compose_effect(monkeypatch) -> None:
    from tools.zenoctl_testnet_local import compose as cm
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []

    def fake_compose_run(**kwargs):
        events.append("compose_run")
        raise AssertionError(f"quarantine must precede compose effect: {kwargs}")

    monkeypatch.setattr(lc.cm, "compose_run", fake_compose_run)
    roles = {
        "alice": {"public_key": "0x" + "11" * 48, "privkey_int": 123456789},
        "bob": {"public_key": "0x" + "22" * 48, "privkey_int": 987654321},
    }

    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        lc._seed_api_state(
            engine=cm.ComposeEngine(binary="docker"),
            project="zenodex-local-testnet-test",
            env={},
            roles=roles,
            chain_id="zeno-ledger-localtest-v0",
            tau_rpc_timeout_s=900.0,
        )

    assert events == []


def test_release_native_collateral_materializer_rejects_before_compose_effect(monkeypatch) -> None:
    from tools.zenoctl_testnet_local import compose as cm
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []

    def fake_compose_run(**kwargs):
        events.append("compose_run")
        raise AssertionError(f"quarantine must precede compose effect: {kwargs}")

    monkeypatch.setattr(lc.cm, "compose_run", fake_compose_run)
    roles = {
        "alice": {"public_key": "0x" + "11" * 48, "privkey_int": 111},
        "carol": {"public_key": "0x" + "33" * 48, "privkey_int": 333},
        "bob": {"public_key": "0x" + "22" * 48, "privkey_int": 222},
    }

    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        lc._materialize_release_native_collateral(
            engine=cm.ComposeEngine(binary="docker"),
            compose_project="zenodex-local-testnet-test",
            env={},
            roles=roles,
            amount_e8=1000,
        )

    assert events == []


def test_compose_overlay_requires_orchestrator_env() -> None:
    """The compose file must use `${VAR:?…}` to refuse running without
    orchestrator-provided env."""
    raw = COMPOSE_OVERLAY.read_text(encoding="utf-8")
    for required in (
        "ZENO_LEDGER_WRITER_TOKEN",
        "ZENODEX_API_BEARER_TOKEN",
        "RENDERED_NGINX_CONF_PATH",
        "RENDERED_RUNTIME_CONFIG_PATH",
        "FIXTURES_DIR",
        "ORACLE_HOME_DIR",
        "HOST_UID",
        "HOST_GID",
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY",
        "TAU_DEX_ORACLE_PUBKEY",
        "TAU_DEX_ZUSD_ORACLE_PUBKEY",
        "CONFIDENTIAL_APPROVED_MEASUREMENTS",
        "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON",
    ):
        assert f"{required}:?" in raw, f"compose overlay must require env {required!r}"


def test_compose_overlay_bind_mount_services_run_as_host_user() -> None:
    doc = _load_compose_overlay()
    expected = "${HOST_UID:?HOST_UID must be set by the orchestrator}:${HOST_GID:?HOST_GID must be set by the orchestrator}"
    for service in ("zenodex-oracle", "zenodex-api", "zenodex-nginx"):
        assert doc["services"][service]["user"] == expected


def test_compose_overlay_api_seeds_confidential_local_smoke_profile() -> None:
    """The confidential UI/API path should be testable in local mode."""
    doc = _load_compose_overlay()
    env = doc["services"]["zenodex-api"]["environment"]
    assert env["CONFIDENTIAL_ATTESTATION_API_ENABLED"] == "true"
    assert env["CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED"] == "true"
    assert "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON" in env
    assert "must be set by the orchestrator" in env["CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON"]
    assert "must be set by the orchestrator" in env["CONFIDENTIAL_APPROVED_MEASUREMENTS"]
    assert env["CONFIDENTIAL_OPERATOR_CONTACT"].startswith("https://")


def test_compose_overlay_ledger_nodes_receive_proof_mining_verifier_env() -> None:
    """Strict local proof-mining payouts must execute on the ledger nodes."""
    doc = _load_compose_overlay()
    services = doc["services"]
    for service_name in ("zeno-ledger-writer", "zeno-ledger-forwarder", "zeno-ledger-readonly"):
        env = services[service_name]["environment"]
        assert "TAU_DEX_CHAIN_ID" in env
        assert "TAU_DEX_TOKEN_SYMBOL" in env
        assert "TAU_DEX_PROOF_MINING_POOL_PUBKEY" in env
        assert "TAU_DEX_ALLOW_EXTERNAL_TOOLS" in env
        assert "TAU_DEX_CONSENSUS_MODE" in env
        assert "TAU_DEX_PROOF_VERIFIER_CMD_JSON" in env
        assert "TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP" in env


def test_lifecycle_compose_env_generates_nonplaceholder_confidential_fixture(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    roles = {
        "operator": {"public_key": "op-pub"},
        "oracle_authority": {"public_key": "oracle-pub"},
        "alice": {"public_key": "alice-pub"},
    }
    fixture = lc._new_confidential_local_fixture()
    env = lc._compose_env(
        paths=paths,
        ui_port=19108,
        chain_id="chain",
        network_id="network",
        writer_token="writer-token",
        stdlib_token="stdlib-token",
        roles=roles,
        zk_required=False,
        confidential_fixture=fixture,
    )

    measurement = env["CONFIDENTIAL_APPROVED_MEASUREMENTS"]
    assert measurement == fixture.measurement
    assert "aaaaaaaa" not in measurement
    assert "bbbbbbbb" not in measurement
    assert len(set(fixture.nitro_pcr0)) >= 4
    assert len(set(fixture.nitro_pcr8)) >= 4
    assert fixture.measurement in env["CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON"]
    assert env["TAU_DEX_PROOF_MINING_POOL_PUBKEY"] == "op-pub"


def test_lifecycle_compose_env_wires_proof_mining_to_active_rewards_pool(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    roles = {
        "operator": {"public_key": "op-pub"},
        "oracle_authority": {"public_key": "oracle-pub"},
        "alice": {"public_key": "alice-pub"},
        "guardian_2": {"public_key": "guardian-two-pub"},
    }

    env = lc._compose_env(
        paths=paths,
        ui_port=19108,
        chain_id="chain",
        network_id="network",
        writer_token="writer-token",
        stdlib_token="stdlib-token",
        roles=roles,
        zk_required=False,
    )

    assert env["TAU_DEX_PROOF_MINING_POOL_PUBKEY"] == "guardian-two-pub"


def test_lifecycle_compose_env_sets_local_external_tool_posture_for_strict_zk(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    for name in lc.GLOBAL_ZK_ENV_NAMES:
        monkeypatch.delenv(name, raising=False)

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    roles = {
        "operator": {"public_key": "op-pub"},
        "oracle_authority": {"public_key": "oracle-pub"},
        "alice": {"public_key": "alice-pub"},
        "guardian_2": {"public_key": "guardian-two-pub"},
    }

    env = lc._compose_env(
        paths=paths,
        ui_port=19108,
        chain_id="chain",
        network_id="network",
        writer_token="writer-token",
        stdlib_token="stdlib-token",
        roles=roles,
        zk_required=True,
    )

    assert env["TAU_DEX_ALLOW_EXTERNAL_TOOLS"] == "1"
    assert env["TAU_DEX_CONSENSUS_MODE"] == "0"
    assert "local_live_wrapper_echo_v1.py" in env["TAU_DEX_PROOF_VERIFIER_CMD_JSON"]
    assert env["TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP"] == "true"
    assert env["TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON"]
    assert env["TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON"]
    assert env["ZUSD_MONETARY_WALLET_PROOF_VERIFIER_CMD_JSON"] == env["TAU_DEX_PROOF_VERIFIER_CMD_JSON"]
    assert env["PERPS_WALLET_PROOF_VERIFIER_CMD_JSON"] == env["TAU_DEX_PROOF_VERIFIER_CMD_JSON"]


def test_local_oracle_write_smoke_checks_duplicate_rewards_and_dispute_escrow(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    calls: list[tuple[str, dict[str, object]]] = []

    def fake_post_json(url: str, payload: Mapping[str, object], *, timeout_s: float = 10.0) -> dict[str, object]:
        path = "/" + url.split("/", 3)[3]
        calls.append((path, dict(payload)))
        if path == "/api/oracle/identity/create":
            return {"status_code": 200, "ok": True, "reporter_id": "reporter:local-smoke"}
        if path in {
            "/api/oracle/query/register",
            "/api/oracle/query/fund",
            "/api/oracle/reporter/register",
            "/api/oracle/reporter/bond",
            "/api/oracle/source/register",
        }:
            return {"status_code": 200, "ok": True}
        if path == "/api/oracle/report/submit":
            if payload.get("reward_e8") == 999:
                return {
                    "status_code": 200,
                    "ok": True,
                    "report_id": "report:one",
                    "reward_e8": 0,
                    "original_reward_e8": 17,
                    "pending_rewards_e8": 17,
                    "idempotent_replay": True,
                }
            return {
                "status_code": 200,
                "ok": True,
                "report_id": "report:one",
                "reward_e8": 17,
                "pending_rewards_e8": 17,
            }
        if path == "/api/oracle/dispute/open":
            if payload.get("force") is True:
                return {
                    "status_code": 400,
                    "ok": False,
                    "error": "dispute bond exceeds available reporter bond",
                }
            if payload.get("reason") == "local-smoke-duplicate":
                return {
                    "status_code": 400,
                    "ok": False,
                    "error": "open dispute already exists for report_id: report:one",
                }
            return {
                "status_code": 200,
                "ok": True,
                "dispute_id": "dispute:one",
                "dispute": {"status": "open", "bond_escrow_status": "escrowed"},
            }
        if path == "/api/oracle/dispute/resolve":
            return {
                "status_code": 200,
                "ok": True,
                "dispute": {"status": "rejected", "bond_escrow_status": "slashed"},
            }
        if path == "/api/oracle/aggregate/build":
            return {"status_code": 200, "ok": True, "aggregate_id": "aggregate:one"}
        if path == "/api/oracle/read/accept":
            return {"status_code": 200, "ok": True, "read_id": "read:one"}
        if path == "/api/oracle/authorization/build":
            return {"status_code": 200, "ok": True, "authorization_id": "authorization:one"}
        if path == "/api/oracle/rewards/pay":
            return {
                "status_code": 200,
                "ok": True,
                "reward_receipt": {"reward_entry_id": "reward:one"},
            }
        raise AssertionError(f"unexpected oracle smoke path: {path}")

    monkeypatch.setattr(lc, "_post_json", fake_post_json)

    result = lc._run_oracle_write_smoke(ui_base="http://127.0.0.1:19108", run_id="unit")

    assert result["ok"] is True
    assert result["duplicate_report_idempotent"] is True
    assert result["dispute_id"] == "dispute:one"
    assert result["steps"]["report_duplicate_idempotency"]["idempotent_replay"] is True
    assert result["steps"]["dispute_duplicate_open_rejected"]["ok"] is True
    assert result["steps"]["dispute_overbond_rejected"]["ok"] is True
    assert any(path == "/api/oracle/dispute/resolve" for path, _payload in calls)


def test_operator_tools_image_copies_perps_reference_models() -> None:
    """Perps wallet submit paths import generated reference models at runtime."""
    raw = (REPO_ROOT / "Dockerfile.operator-tools").read_text(encoding="utf-8")
    for name in (
        "perp_epoch_clearinghouse_2p_v0_1_ref.py",
        "perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
        "perp_epoch_isolated_v2_ref.py",
        "perp_epoch_isolated_v3_ref.py",
    ):
        assert f"COPY generated/perp_python/{name}" in raw


def test_local_seed_advances_perps_epoch_for_first_ui_publish() -> None:
    raw = (REPO_ROOT / "tools/zenoctl_testnet_local/lifecycle.py").read_text(encoding="utf-8")
    assert 'report["steps"]["perps_advance_epoch"]' in raw
    assert '"action": "advance_epoch"' in raw
    assert "allow_empty_mempool=True" in raw


def test_perps_pre_publish_step_handles_reusable_smoke_states() -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    assert lc._perps_pre_publish_step({"now_epoch": 0, "clearing_price_epoch": 0}) == "advance"
    assert (
        lc._perps_pre_publish_step(
            {"now_epoch": 2, "clearing_price_epoch": 2, "oracle_last_update_epoch": 1}
        )
        == "settle_then_advance"
    )
    assert (
        lc._perps_pre_publish_step(
            {"now_epoch": 2, "clearing_price_epoch": 1, "oracle_last_update_epoch": 1}
        )
        == "none"
    )


def test_signed_live_swap_payload_binds_nonce_deadline_and_signature(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip("py_ecc.bls")
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
    from tools.zenoctl_testnet_local import lifecycle as lc

    pubkey = "0x" + bls_pubkey_hex_from_privkey(17)
    roles = {"alice": {"public_key": pubkey, "privkey_hex": "0x11", "privkey_int": 17}}
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32

    def fake_get_json(url: str, *, timeout_s: float = 5.0) -> dict[str, object]:
        assert "/api/pools?" in url
        return {
            "ok": True,
            "account_last_nonce": 4,
            "pools": [
                {
                    "pool_id": pool_id,
                    "token0": "tAGRS",
                    "token1": "tZDEX",
                    "asset0": asset0,
                    "asset1": asset1,
                    "account_balance0": 10,
                    "account_balance1": 10,
                }
            ],
        }

    monkeypatch.setattr(lc, "_safe_get_json", fake_get_json)

    payload, operation = lc._build_signed_live_swap_intent(
        ui_base="http://127.0.0.1:18080",
        roles=roles,
        chain_id="zeno-ledger-localtest-v0",
        sender_role="alice",
        amount_in=3,
        min_amount_out=1,
        deadline=12345,
    )

    assert payload["nonce"] == 5
    assert payload["deadline"] == 12345
    assert payload["signature"] == operation["signature"]
    assert operation["kind"] == "SWAP_EXACT_IN"
    assert operation["pool_id"] == pool_id
    assert operation["asset_in"] == asset0
    assert operation["asset_out"] == asset1
    assert str(operation["signature"]).startswith("0x")


def test_complex_grouped_transaction_smoke_rejects_replay_without_partial_mint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip("py_ecc.bls")
    from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
    from tools.zenoctl_testnet_local import lifecycle as lc

    pubkey = "0x" + bls_pubkey_hex_from_privkey(17)
    roles = {"alice": {"public_key": pubkey, "privkey_hex": "0x11", "privkey_int": 17}}
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    balance = {"value": 12}
    posted: list[dict[str, object]] = []

    def fake_get_json(url: str, *, timeout_s: float = 5.0) -> dict[str, object]:
        return {
            "ok": True,
            "account_last_nonce": 8,
            "pools": [
                {
                    "pool_id": pool_id,
                    "token0": "tAGRS",
                    "token1": "tZDEX",
                    "asset0": asset0,
                    "asset1": asset1,
                    "account_balance0": balance["value"],
                    "account_balance1": 20,
                }
            ],
        }

    def fake_post_json(url: str, payload: Mapping[str, object], *, timeout_s: float = 10.0) -> dict[str, object]:
        assert url.endswith("/tx")
        tx = payload["tx"]
        assert isinstance(tx, Mapping)
        operations = tx["operations"]
        assert isinstance(operations, Mapping)
        assert set(operations) == {"5"}
        swap_ops = operations["5"]
        assert isinstance(swap_ops, list)
        assert len(swap_ops) == 2
        assert [op["nonce"] for op in swap_ops if isinstance(op, Mapping)] == [9, 10]
        posted.append(dict(tx))
        if len(posted) == 1:
            balance["value"] = 14
            return {"ok": True, "tx_accepted": True, "height": 10, "receipt": {"accepted": True}}
        return {"ok": True, "tx_accepted": False, "height": 11, "receipt": {"accepted": False}}

    monkeypatch.setattr(lc, "_safe_get_json", fake_get_json)
    monkeypatch.setattr(lc, "_post_json", fake_post_json)

    report = lc._run_complex_grouped_transaction_smoke(
        ui_base="http://127.0.0.1:18080",
        roles=roles,
        chain_id="zeno-ledger-localtest-v0",
        deadline=12345,
        run_id="unit",
    )

    assert report["ok"] is True
    assert report["replay_rejected"] is True
    assert report["atomic_reject_preserved_balance"] is True
    assert len(posted) == 2
    assert posted[0]["tx_id"] != posted[1]["tx_id"]


# ---------------------------------------------------------------------------
# Port collision detection
# ---------------------------------------------------------------------------


def test_port_collision_raises_actionable_error() -> None:
    from tools.zenoctl_testnet_local import compose as cm

    listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)
    busy_port = listener.getsockname()[1]
    try:
        with pytest.raises(ValueError, match="is in use"):
            cm.check_host_port_free(busy_port)
    finally:
        listener.close()


def test_port_collision_check_accepts_free_port() -> None:
    from tools.zenoctl_testnet_local import compose as cm

    with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as s:
        s.bind(("127.0.0.1", 0))
        free_port = s.getsockname()[1]
    cm.check_host_port_free(free_port)  # no raise


def test_port_collision_check_accepts_recently_released_port() -> None:
    from tools.zenoctl_testnet_local import compose as cm

    # A completed TCP connection can leave kernel-managed TIME_WAIT state and
    # does not model release of a listener-only orchestration port. The
    # occupied-listener case is covered by the preceding collision test.
    listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)
    port = listener.getsockname()[1]
    listener.close()

    cm.check_host_port_free(port)  # no raise


def test_port_collision_rejects_out_of_range() -> None:
    from tools.zenoctl_testnet_local import compose as cm

    for bad in (0, -1, 65_536, 100_000):
        with pytest.raises(ValueError, match=r"out of range"):
            cm.check_host_port_free(bad)


# ---------------------------------------------------------------------------
# CLI shape
# ---------------------------------------------------------------------------


def _zenoctl(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "tools/zenoctl.py", *args],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def test_cli_testnet_local_help_lists_full_lifecycle_surface() -> None:
    result = _zenoctl("testnet", "local", "--help")
    assert result.returncode == 0, result.stderr
    for sub in ("up", "down", "status", "smoke", "release-smoke", "public-up", "public", "logs", "reset"):
        assert sub in result.stdout, f"missing subcommand: {sub}"


def test_cli_testnet_local_up_requires_out_dir() -> None:
    result = _zenoctl("testnet", "local", "up")
    assert result.returncode != 0
    assert "--out-dir" in result.stderr or "required" in result.stderr.lower()


def test_cli_testnet_local_up_help_documents_options() -> None:
    result = _zenoctl("testnet", "local", "up", "--help")
    assert result.returncode == 0, result.stderr
    for flag in ("--out-dir", "--chain-id", "--ui-port", "--engine", "--force", "--seed", "--random", "--zk-mode"):
        assert flag in result.stdout, f"missing flag in up help: {flag}"


def test_cli_testnet_local_smoke_help_documents_browser_options() -> None:
    result = _zenoctl("testnet", "local", "smoke", "--help")
    assert result.returncode == 0, result.stderr
    for flag in ("--out-dir", "--engine", "--browser", "--chrome-bin", "--browser-timeout"):
        assert flag in result.stdout, f"missing flag in smoke help: {flag}"


def test_cli_testnet_local_public_help_documents_point_and_click_options() -> None:
    result = _zenoctl("testnet", "local", "public", "--help")
    assert result.returncode == 0, result.stderr
    for flag in (
        "--out-dir",
        "--cloudflared-bin",
        "--tunnel-url",
        "--no-open",
        "--no-release-smoke",
        "--force",
    ):
        assert flag in result.stdout, f"missing flag in public help: {flag}"


def test_cli_testnet_local_public_up_help_is_refusal_only() -> None:
    result = _zenoctl("testnet", "local", "public-up", "--help")
    assert result.returncode == 0, result.stderr
    help_text = " ".join(result.stdout.split())
    for flag in ("--open", "--release-smoke", "--tunnel-url", "--cloudflared-bin"):
        assert flag in help_text, f"missing flag in public-up help: {flag}"
    assert "refuses before stack, browser, smoke, tunnel, or report effects" in help_text
    assert "never opens a browser" in help_text
    assert "never starts cloudflared" in help_text
    assert "does not run release smoke" in help_text
    assert "does not emit a host report" in help_text


def test_cli_public_defaults_to_point_and_click_posture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tools.zenoctl_testnet_local import cli
    from tools.zenoctl_testnet_local import lifecycle as lc

    captured: dict[str, lc.PublicUpOptions] = {}

    def fake_public_up(opts: lc.PublicUpOptions) -> int:
        captured["opts"] = opts
        return 0

    monkeypatch.setattr(lc, "cmd_public_up", fake_public_up)
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="testnet_command", required=True)
    cli.register_subparser(sub)
    args = parser.parse_args(["local", "public", "--out-dir", str(tmp_path), "--tunnel-url", "https://public.example"])

    assert args.func(args) == 0
    opts = captured["opts"]
    assert opts.out_dir == tmp_path
    assert opts.open_browser is True
    assert opts.release_smoke_before_tunnel is True
    assert opts.tunnel_url == "https://public.example"


def test_cli_existing_testnet_subcommands_still_present() -> None:
    """Adding `local` must not remove `init|up|evidence|verify-evidence`."""
    result = _zenoctl("testnet", "--help")
    assert result.returncode == 0
    for sub in ("init", "up", "evidence", "verify-evidence", "local"):
        assert sub in result.stdout, f"missing subcommand under testnet: {sub}"


def test_cli_rejects_malformed_seed_hex(tmp_path: Path) -> None:
    """--seed must be exactly 64 hex chars; clear error before any compose work."""
    # Wrong length
    result = _zenoctl(
        "testnet", "local", "up", "--out-dir", str(tmp_path), "--seed", "ab" * 16
    )
    assert result.returncode == 2
    assert "64 hex" in result.stderr.lower() or "64 hex" in result.stdout.lower()

    # Wrong charset
    result = _zenoctl(
        "testnet", "local", "up", "--out-dir", str(tmp_path), "--seed", "z" * 64
    )
    assert result.returncode == 2
    assert "hex" in result.stderr.lower() or "hex" in result.stdout.lower()


def test_cli_rejects_seed_and_random_together(tmp_path: Path) -> None:
    """argparse mutually-exclusive group must reject both flags."""
    result = _zenoctl(
        "testnet", "local", "up",
        "--out-dir", str(tmp_path),
        "--seed", "ab" * 32,
        "--random",
    )
    assert result.returncode != 0
    assert "not allowed" in result.stderr.lower() or "argument" in result.stderr.lower()


def test_public_up_rejects_current_profile_before_cloudflared_resolution(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    code = lc.cmd_public_up(
        lc.PublicUpOptions(
            out_dir=tmp_path,
            cloudflared_bin="definitely-missing-cloudflared-for-test",
        )
    )
    captured = capsys.readouterr()

    assert code == 2
    report = json.loads(captured.out)
    assert report["status"] == "blocked_current_profile"
    assert report["current_release_eligible"] is False
    assert report["authority"] == "NONE"
    assert report["vm_gates_closed"] == []
    assert captured.err == ""
    assert not (tmp_path / "local_testnet_manifest.json").exists()


def test_public_release_workflow_rejects_before_stack_or_tunnel_effects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []
    monkeypatch.setattr(lc, "cmd_up", lambda _opts: events.append("up"))
    monkeypatch.setattr(
        lc,
        "_resolve_cloudflared_runner",
        lambda *_args, **_kwargs: events.append("tunnel_lookup"),
    )

    code = lc.cmd_public_up(
        lc.PublicUpOptions(
            out_dir=tmp_path,
            tunnel_url="https://public.example",
            release_smoke_before_tunnel=True,
        )
    )

    assert code == 2
    assert events == []
    report = json.loads(capsys.readouterr().out)
    assert report["rejection_code"] == "LOCAL_RELEASE_SMOKE_REQUIRES_QUARANTINED_ROUTES"
    assert not (tmp_path / "reports").exists()


def test_public_up_without_release_smoke_flag_still_rejects_before_stack_or_tunnel_effects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []
    monkeypatch.setattr(lc, "cmd_up", lambda _opts: events.append("up"))
    monkeypatch.setattr(
        lc,
        "_resolve_cloudflared_runner",
        lambda *_args, **_kwargs: events.append("tunnel_lookup"),
    )

    code = lc.cmd_public_up(
        lc.PublicUpOptions(
            out_dir=tmp_path,
            tunnel_url="https://public.example",
            release_smoke_before_tunnel=False,
        )
    )

    assert code == 2
    assert events == []
    report = json.loads(capsys.readouterr().out)
    assert report["status"] == "blocked_current_profile"
    assert report["current_profile_id"] == "local-testnet-retired-bridge-quarantine-v1"
    assert report["current_release_eligible"] is False
    assert report["authority"] == "NONE"
    assert report["vm_gates_closed"] == []
    assert not (tmp_path / "reports").exists()


def test_release_flow_helper_rejects_current_profile_before_file_or_network_effect(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange.
    from tools.zenoctl_testnet_local import compose as cm
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []

    def record_read(*_args: object, **_kwargs: object) -> dict[str, object]:
        events.append("read")
        return {}

    monkeypatch.setattr(
        lc,
        "_load_json_file",
        record_read,
    )
    paths = lc.mf.ManifestPaths.from_out_dir(tmp_path)

    # Act.
    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        lc._run_release_flow_smoke(
            ui_base="http://127.0.0.1:18080",
            paths=paths,
            manifest={"fixture_paths": {"key_bundle": str(tmp_path / "keys.json")}},
            engine=cm.ComposeEngine(binary="docker"),
            compose_project="zenodex-local-testnet-test",
            env={},
        )

    # Assert.
    assert events == []


def test_perps_cycle_helper_rejects_current_profile_before_network_effect(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange.
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []

    def record_post(*_args: object, **_kwargs: object) -> dict[str, object]:
        events.append("post")
        return {}

    monkeypatch.setattr(
        lc,
        "_post_json",
        record_post,
    )

    # Act.
    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        lc._run_perps_wallet_cycle_smoke(
            ui_base="http://127.0.0.1:18080",
            market_id="perp:retired",
            roles={},
            deadline=0,
        )

    # Assert.
    assert events == []


def test_quick_tunnel_helper_rejects_current_profile_before_runner_or_process_effect(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange.
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []
    monkeypatch.setattr(
        lc,
        "_resolve_cloudflared_runner",
        lambda *_args, **_kwargs: events.append("runner_lookup"),
    )
    paths = lc.mf.ManifestPaths.from_out_dir(tmp_path)

    # Act.
    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        lc._run_cloudflare_quick_tunnel(
            opts=lc.PublicUpOptions(out_dir=tmp_path),
            paths=paths,
            manifest={"service_urls": {"ui": "http://127.0.0.1:18080"}},
        )

    # Assert.
    assert events == []


def test_zusd_transfer_payload_rejects_current_profile_before_role_or_network_effect(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange.
    from tools.zenoctl_testnet_local import lifecycle as lc

    events: list[str] = []
    monkeypatch.setattr(
        lc,
        "_post_json",
        lambda *_args, **_kwargs: events.append("post_json"),
    )

    # Act.
    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        lc._zusd_transfer_payload(ui_base="http://127.0.0.1:1", roles={}, deadline=0)

    # Assert.
    assert events == []


def test_public_host_report_direct_call_cannot_probe_or_emit_accepted_release_claim(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    paths = lc.mf.ManifestPaths.from_out_dir(tmp_path)
    effects: list[str] = []
    monkeypatch.setattr(
        lc,
        "_safe_get_json",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("blocked profile must not probe a host")
        ),
    )
    monkeypatch.setattr(
        lc,
        "_write_json",
        lambda *_args, **_kwargs: effects.append("write_json"),
    )

    report = lc._write_public_host_report(
        paths=paths,
        manifest={"service_urls": {"ui": "http://127.0.0.1:18080"}},
        public_url="https://public.example",
        source="test",
    )

    assert report["ok"] is False
    assert report["status"] == "blocked_current_profile"
    assert report["current_release_eligible"] is False
    assert report["authority"] == "NONE"
    assert report["vm_gates_closed"] == []
    assert effects == []
    assert not paths.reports_dir.exists()


def test_public_host_summary_cannot_describe_blocked_profile_as_ready() -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    summary = lc._public_host_summary(
        {
            "ok": False,
            "status": "blocked_current_profile",
            "current_profile_id": "local-testnet-retired-bridge-quarantine-v1",
        }
    )

    assert "unavailable" in summary
    assert "ready" not in summary
    assert "Authority: NONE" in summary


def test_default_cloudflared_uses_container_runtime_when_binary_missing(monkeypatch: pytest.MonkeyPatch) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    def fake_which(name: str) -> str | None:
        if name == "docker":
            return "/usr/bin/docker"
        return None

    monkeypatch.setattr(lc.shutil, "which", fake_which)

    runner = lc._resolve_cloudflared_runner("cloudflared", engine="auto")
    assert runner == ("container", "/usr/bin/docker")

    command, source = lc._cloudflared_command(runner, "http://127.0.0.1:18080")
    assert source == "cloudflare_quick_tunnel_docker_container"
    assert command[:5] == ["/usr/bin/docker", "run", "--rm", "--network", "host"]
    assert "cloudflare/cloudflared:latest" in command
    assert command[-2:] == ["--url", "http://127.0.0.1:18080"]


def test_cli_reset_requires_force(tmp_path: Path) -> None:
    """`reset` is destructive (removes compose volumes + out-dir). Without
    --force it must refuse with exit code 2 and a clear message — no
    docker invocation, no rmtree."""
    sentinel = tmp_path / "sentinel.txt"
    sentinel.write_text("keep me", encoding="utf-8")
    result = _zenoctl("testnet", "local", "reset", "--out-dir", str(tmp_path))
    assert result.returncode == 2, result.stderr
    assert "force" in result.stderr.lower(), result.stderr
    # The sentinel must still be on disk: refusing --force must not touch the dir.
    assert sentinel.read_text(encoding="utf-8") == "keep me"


# ---------------------------------------------------------------------------
# Destructive-path safety guards
# ---------------------------------------------------------------------------


def test_reset_refuses_filesystem_root() -> None:
    """A typo like `--out-dir /` must not be able to wipe the host."""
    from tools.zenoctl_testnet_local import lifecycle as lc

    with pytest.raises(ValueError, match="refusing destructive"):
        lc._refuse_unsafe_reset_target(Path("/"))


def test_reset_refuses_user_home_itself() -> None:
    """Refuse to rmtree the user's home directory itself."""
    from tools.zenoctl_testnet_local import lifecycle as lc

    with pytest.raises(ValueError, match="home directory"):
        lc._refuse_unsafe_reset_target(Path.home())


def test_reset_refuses_system_directories() -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    for sysdir in ("/etc", "/usr", "/var", "/opt", "/root", "/home", "/bin", "/sbin"):
        with pytest.raises(ValueError, match="refusing destructive"):
            lc._refuse_unsafe_reset_target(Path(sysdir))


def test_reset_allows_dedicated_out_dirs(tmp_path: Path) -> None:
    """Tmp paths and user-chosen subdirectories must be allowed."""
    from tools.zenoctl_testnet_local import lifecycle as lc

    lc._refuse_unsafe_reset_target(tmp_path)
    lc._refuse_unsafe_reset_target(Path.home() / "zen-local-testnet")


def test_reset_refuses_dir_without_manifest_when_dir_has_unrelated_files(tmp_path: Path) -> None:
    """If the out-dir has no manifest AND contains files we didn't create,
    refuse the reset — the user likely pointed at a populated dir by mistake."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    unrelated = tmp_path / "my_real_data.txt"
    unrelated.write_text("important user data", encoding="utf-8")
    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    with pytest.raises(ValueError, match="unrelated entries"):
        lc._reset_stack(paths=paths, engine_name="auto", manifest=None)
    assert unrelated.exists(), "guard must not have deleted the file"


# ---------------------------------------------------------------------------
# Lifecycle env helper (down / status compose-env contract)
# ---------------------------------------------------------------------------


def test_lifecycle_env_for_compose_returns_all_required_vars(tmp_path: Path) -> None:
    """`down` and `status` invoke compose, which interpolates ${VAR:?...}.
    The env helper must set every var the overlay requires, so compose
    operations on an existing stack don't fail with "VAR not set"."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    env = lc._lifecycle_env_for_compose(body, paths)
    for required in (
        "ZENO_LEDGER_WRITER_TOKEN",
        "ZENODEX_API_BEARER_TOKEN",
        "RENDERED_NGINX_CONF_PATH",
        "RENDERED_RUNTIME_CONFIG_PATH",
        "FIXTURES_DIR",
        "ORACLE_HOME_DIR",
        "HOST_UID",
        "HOST_GID",
        "UI_PORT",
        "CHAIN_ID",
        "NETWORK_ID",
        "ZENO_LEDGER_TOKEN_SYMBOL",
        "TAU_DEX_REQUIRE_LIVE_ZK_PROOF",
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY",
        "TAU_DEX_ORACLE_PUBKEY",
        "TAU_DEX_ZUSD_ORACLE_PUBKEY",
        "CONFIDENTIAL_APPROVED_MEASUREMENTS",
        "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON",
    ):
        assert env.get(required), f"compose env missing required var: {required}"


def test_lifecycle_env_does_not_leak_real_tokens(tmp_path: Path) -> None:
    """The down/status env uses placeholders, never the real bearer token."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    env = lc._lifecycle_env_for_compose(body, paths)
    # Manifest input used 'writer-secret-abc' as the raw token; the env
    # must NOT carry that value into compose.
    assert env["ZENO_LEDGER_WRITER_TOKEN"] != "writer-secret-abc"


def test_key_management_authority_readiness_gates_tokenomics(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    manifest = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    wallet_authority = {
        "ok": True,
        "status": "ready",
        "production_wallet_authority": True,
        "readiness_gaps": [],
        "authority_id": "perps-wallet-authority-v1",
        "wallet_authority_hash": "0x" + "aa" * 32,
        "signer_registry_hash": "0x" + "bb" * 32,
        "key_manager_hash": "0x" + "cc" * 32,
        "active_signer_count": 2,
        "threshold": 2,
        "recoverable_active_key_count": 2,
        "recovery_exercise": {"recovery_exercise_ready": True},
        "rotation_exercise": {"rotation_exercise_ready": True},
        "device_approval_exercise": {"device_approval_ready": True},
        "signer_ceremony": {"signer_ceremony_ready": True},
        "hardware_custody": {"hardware_custody_ready": True},
        "encrypted_sss_backup": {
            "encrypted_sss_backup_ready": True,
            "threshold": 3,
            "share_count": 5,
            "storage_provider_kinds": ["cloud_drive", "offline_export", "recovery_email"],
            "provider_delivery_ready": True,
            "recovery_drill_ready": True,
            "replay_recovery_ready": True,
            "subject_public_key_matches": True,
            "hostile_share_tests_ready": True,
            "replay_hostile_tests_ready": True,
            "raw_material_absent": True,
        },
    }
    ready = lc._key_management_authority_readiness(
        manifest=manifest,
        lanes={"perps_wallet": {"status": {"wallet_authority": wallet_authority}}},
    )
    assert ready["tokenomics_authority_ready"] is True
    assert ready["rejection_code"] is None
    assert ready["production_security_claim"] is False
    assert ready["production_authority_ready"] is False
    assert ready["production_checks"]["local_tokenomics_authority_ready"] is True
    assert ready["production_checks"]["strict_zk_ready"] is False
    assert ready["production_checks"]["live_provider_delivery_ready"] is False
    assert ready["production_checks"]["external_audit_ready"] is False
    assert ready["secret_sharing"]["sss_implemented"] is True
    assert ready["checks"]["encrypted_sss_backup_ready"] is True

    blocked_authority = {**wallet_authority, "signer_ceremony": {"signer_ceremony_ready": False}}
    blocked = lc._key_management_authority_readiness(
        manifest=manifest,
        lanes={"perps_wallet": {"status": {"wallet_authority": blocked_authority}}},
    )
    assert blocked["tokenomics_authority_ready"] is False
    assert blocked["rejection_code"] == "TOKENOMICS_AUTHORITY_NOT_READY"
    assert "signer ceremony is not ready" in blocked["readiness_gaps"]

    missing_sss = {**wallet_authority}
    missing_sss.pop("encrypted_sss_backup")
    sss_blocked = lc._key_management_authority_readiness(
        manifest=manifest,
        lanes={"perps_wallet": {"status": {"wallet_authority": missing_sss}}},
    )
    assert sss_blocked["tokenomics_authority_ready"] is False
    assert "encrypted SSS backup is not ready" in sss_blocked["readiness_gaps"]


def test_key_management_readiness_rejects_public_private_key_fields(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    manifest = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    wallet_authority = {
        "production_wallet_authority": True,
        "readiness_gaps": [],
        "active_signer_count": 1,
        "threshold": 1,
        "recoverable_active_key_count": 1,
        "recovery_exercise": {"recovery_exercise_ready": True},
        "rotation_exercise": {"rotation_exercise_ready": True},
        "device_approval_exercise": {"device_approval_ready": True},
        "signer_ceremony": {"signer_ceremony_ready": True},
        "hardware_custody": {"hardware_custody_ready": True},
        "encrypted_sss_backup": {"encrypted_sss_backup_ready": True},
        "private_key_hex": "0x" + "00" * 32,
    }
    report = lc._key_management_authority_readiness(
        manifest=manifest,
        lanes={"perps_wallet": {"status": {"wallet_authority": wallet_authority}}},
    )
    assert report["tokenomics_authority_ready"] is False
    assert "raw private-key field detected in public status or manifest" in report["readiness_gaps"]


def test_key_management_readiness_allows_secret_absence_status_fields(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    manifest = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    wallet_authority = {
        "ok": True,
        "status": "ready",
        "production_wallet_authority": True,
        "readiness_gaps": [],
        "authority_id": "perps-wallet-authority-v1",
        "wallet_authority_hash": "0x" + "aa" * 32,
        "signer_registry_hash": "0x" + "bb" * 32,
        "key_manager_hash": "0x" + "cc" * 32,
        "active_signer_count": 1,
        "threshold": 1,
        "recoverable_active_key_count": 1,
        "recovery_exercise": {"recovery_exercise_ready": True},
        "rotation_exercise": {"rotation_exercise_ready": True},
        "device_approval_exercise": {"device_approval_ready": True},
        "signer_ceremony": {"signer_ceremony_ready": True},
        "hardware_custody": {
            "hardware_custody_ready": True,
            "no_raw_private_key_exposure": True,
        },
        "encrypted_sss_backup": {
            "encrypted_sss_backup_ready": True,
            "provider_delivery_ready": True,
            "replay_recovery_ready": True,
            "subject_public_key_matches": True,
            "replay_hostile_tests_ready": True,
            "raw_material_absent": True,
        },
    }
    report = lc._key_management_authority_readiness(
        manifest=manifest,
        lanes={"perps_wallet": {"status": {"wallet_authority": wallet_authority}}},
    )
    assert report["tokenomics_authority_ready"] is True
    assert report["checks"]["no_raw_private_key_fields"] is True


def test_lane_readiness_keeps_stack_ready_when_only_tokenomics_gate_blocks(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    manifest = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    wallet_authority = {
        "ok": True,
        "status": "ready",
        "production_wallet_authority": True,
        "readiness_gaps": [],
        "authority_id": "perps-wallet-authority-v1",
        "wallet_authority_hash": "0x" + "aa" * 32,
        "signer_registry_hash": "0x" + "bb" * 32,
        "key_manager_hash": "0x" + "cc" * 32,
        "active_signer_count": 1,
        "threshold": 1,
        "recoverable_active_key_count": 1,
        "recovery_exercise": {"recovery_exercise_ready": True},
        "rotation_exercise": {"rotation_exercise_ready": True},
        "device_approval_exercise": {"device_approval_ready": True},
        "signer_ceremony": {"signer_ceremony_ready": False},
        "hardware_custody": {"hardware_custody_ready": True},
    }

    requested_urls: list[str] = []

    def fake_get_json(url: str, **_: object) -> dict:
        requested_urls.append(url)
        if url.endswith("/api/pools"):
            return {"ok": True, "pools": [{"pool_id": "spot-a"}]}
        if url.endswith("/api/zusd/wallet/status"):
            return {"ok": True, "status": {"node_reachable": True}}
        if url.endswith("/api/zusd/monetary/status"):
            return {"ok": True, "status": {"node_reachable": True, "monetary_state_present": True}}
        if url.endswith("/api/perps/wallet/status"):
            return {
                "ok": True,
                "status": {
                    "node_reachable": True,
                    "market_count": 1,
                    "wallet_authority": wallet_authority,
                    "oracle_authority": {"ok": True},
                },
            }
        if url.endswith("/api/strategy/autotrader/status"):
            return {"ok": True, "status": {"supervisor": {"ok": True}}}
        if url.endswith("/api/oracle/health"):
            return {"ok": True}
        if url.endswith("/api/oracle/dashboard"):
            return {"ok": True}
        if url.endswith("/api/confidential/status"):
            return {"ok": True}
        raise AssertionError(f"unexpected URL: {url}")

    monkeypatch.setattr(lc, "_safe_get_json", fake_get_json)

    report = lc._collect_lane_readiness(ui_base="http://127.0.0.1:18080", manifest=manifest)

    assert report["ok"] is True
    assert "key_management_authority" not in report["checks"]
    assert report["key_management_authority"]["tokenomics_authority_ready"] is False
    assert report["tokenomics_lane"] == {
        "enabled": False,
        "rejection_code": "TOKENOMICS_AUTHORITY_NOT_READY",
    }
    assert all("/api/strategy/autotrader/" not in url for url in requested_urls)
    assert all("/api/zusd/wallet/" not in url for url in requested_urls)
    assert all("/api/zusd/monetary/" not in url for url in requested_urls)
    assert all("/api/perps/wallet/" not in url for url in requested_urls)


def test_feature_smoke_omits_quarantined_autotrader_and_zusd_tau_wallet_lanes(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    roles = {
        "alice": {
            "public_key": "0x" + ("11" * 48),
            "privkey_int": 1,
        }
    }
    posted_urls: list[str] = []

    def fake_load(_path: Path, *, label: str) -> dict:
        if label == "key bundle":
            return {"roles": roles}
        raise AssertionError(label)

    def fake_post(url: str, _payload: object) -> dict:
        posted_urls.append(url)
        return {"ok": True}

    monkeypatch.setattr(lc, "_load_json_file", fake_load)
    monkeypatch.setattr(lc, "_role_materials", lambda _bundle: roles)
    monkeypatch.setattr(lc, "_post_json", fake_post)
    monkeypatch.setattr(lc, "_smoke_run_id", lambda: "run-1")
    monkeypatch.setattr(lc, "_build_signed_live_swap_payload", lambda **_kwargs: {})
    monkeypatch.setattr(lc, "_run_complex_grouped_transaction_smoke", lambda **_kwargs: {"ok": True})
    monkeypatch.setattr(lc, "_run_oracle_write_smoke", lambda **_kwargs: {"ok": True})
    monkeypatch.setattr(lc, "_confidential_local_fixture_from_manifest", lambda **_kwargs: object())
    monkeypatch.setattr(lc, "_confidential_runtime_payload", lambda **_kwargs: {})

    report = lc._run_feature_smoke(
        ui_base="http://127.0.0.1:18080",
        paths=SimpleNamespace(reports_dir=tmp_path),
        manifest={
            "chain_id": "chain",
            "fixture_paths": {"key_bundle": str(tmp_path / "keys.json")},
            "zk_required": False,
        },
    )

    assert report["ok"] is True
    assert "autotrader_live_prepare" not in report["checks"]
    assert all("/api/strategy/autotrader/" not in url for url in posted_urls)
    assert "zusd_wallet_transfer" not in report["checks"]
    assert all("/api/zusd/wallet/" not in url for url in posted_urls)
    assert "zusd_monetary_advance_epoch" not in report["checks"]
    assert "perps_publish_clearing_price" not in report["checks"]
    assert all("/api/zusd/monetary/" not in url for url in posted_urls)
    assert all("/api/perps/wallet/" not in url for url in posted_urls)


def test_runtime_env_for_existing_manifest_recovers_tokens_and_roles(tmp_path: Path) -> None:
    """Restarting an existing stack must recover the live compose env from
    saved local artifacts. The manifest stores token hashes, not raw tokens."""
    from tools.zenoctl_testnet_local import fixtures as fx
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf
    from tools.zenoctl_testnet_local import nginx as ng

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    writer_token = "writer-secret-abc"
    stdlib_token = "stdlib-secret-xyz"
    rendered = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token=writer_token,
            stdlib_token=stdlib_token,
        )
    )
    ng.write_rendered_conf(rendered, out_path=paths.rendered_nginx)

    body = mf.build_manifest(
        **{
            **_valid_manifest_kwargs(tmp_path),
            "fixture_paths": bundle.as_manifest_paths(),
            "writer_token": writer_token,
        }
    )
    env = lc._runtime_env_for_existing_manifest(manifest=body, paths=paths)
    role_pubkeys = json.loads(bundle.role_pubkeys.read_text(encoding="utf-8"))

    assert env["ZENO_LEDGER_WRITER_TOKEN"] == writer_token
    assert env["ZENODEX_API_BEARER_TOKEN"] == stdlib_token
    assert env["TAU_DEX_REQUIRE_LIVE_ZK_PROOF"] == "false"
    assert env["UI_PORT"] == "18080"
    assert env["CHAIN_ID"] == "zeno-ledger-localtest-v0"
    assert env["TAU_DEX_TOKEN_OPERATOR_PUBKEY"]
    assert env["TAU_DEX_ORACLE_PUBKEY"]
    assert env["TAU_DEX_ZUSD_ORACLE_PUBKEY"]
    assert env["TAU_DEX_PROOF_MINING_POOL_PUBKEY"] == role_pubkeys["roles"]["guardian_2"]["public_key"]


def test_runtime_env_for_existing_manifest_rejects_writer_hash_mismatch(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf
    from tools.zenoctl_testnet_local import nginx as ng

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    rendered = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token="rendered-writer-token",
            stdlib_token="stdlib-secret-xyz",
        )
    )
    ng.write_rendered_conf(rendered, out_path=paths.rendered_nginx)

    body = mf.build_manifest(
        **{
            **_valid_manifest_kwargs(tmp_path),
            "fixture_paths": bundle.as_manifest_paths(),
            "writer_token": "different-manifest-token",
        }
    )
    with pytest.raises(ValueError, match="writer_token_sha256"):
        lc._runtime_env_for_existing_manifest(manifest=body, paths=paths)


def test_runtime_env_for_existing_manifest_rejects_stdlib_hash_mismatch(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf
    from tools.zenoctl_testnet_local import nginx as ng

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    rendered = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token="writer-secret-abc",
            stdlib_token="rendered-stdlib-token",
        )
    )
    ng.write_rendered_conf(rendered, out_path=paths.rendered_nginx)

    body = mf.build_manifest(
        **{
            **_valid_manifest_kwargs(tmp_path),
            "fixture_paths": bundle.as_manifest_paths(),
            "stdlib_token": "different-stdlib-token",
        }
    )
    with pytest.raises(ValueError, match="stdlib_token_sha256"):
        lc._runtime_env_for_existing_manifest(manifest=body, paths=paths)


def test_cmd_up_restarts_existing_manifest_without_force(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    """A stopped stack with a valid manifest should be restartable without
    destroying fixtures or forcing a fresh network."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    mf.save_manifest(body, paths.manifest_path)

    calls: list[str] = []

    class Engine:
        binary = "docker"

    def fake_compose_up(**kwargs):
        calls.append("compose_up")
        assert kwargs["project_name"] == body["compose_project"]
        assert kwargs["env"]["ZENO_LEDGER_WRITER_TOKEN"] == "writer-secret-abc"

    monkeypatch.setattr(lc.cm, "detect_engine", lambda engine: Engine())
    monkeypatch.setattr(
        lc,
        "_runtime_env_for_existing_manifest",
        lambda *, manifest, paths: {
            "ZENO_LEDGER_WRITER_TOKEN": "writer-secret-abc",
            "ZENODEX_API_BEARER_TOKEN": "stdlib-secret-xyz",
            "UI_PORT": "18080",
            "CHAIN_ID": "zeno-ledger-localtest-v0",
            "NETWORK_ID": "zeno-ledger-localtest-v0",
            "TAU_DEX_REQUIRE_LIVE_ZK_PROOF": "false",
            "RENDERED_NGINX_CONF_PATH": str(paths.rendered_nginx),
            "RENDERED_RUNTIME_CONFIG_PATH": str(paths.rendered_runtime_config),
            "FIXTURES_DIR": str(paths.fixtures_dir),
            "ORACLE_HOME_DIR": str(paths.oracle_home_dir),
            "HOST_UID": "1000",
            "HOST_GID": "1000",
            "TAU_DEX_TOKEN_OPERATOR_PUBKEY": "operator",
            "TAU_DEX_ORACLE_PUBKEY": "oracle",
            "TAU_DEX_ZUSD_ORACLE_PUBKEY": "zusd",
        },
    )
    monkeypatch.setattr(lc.cm, "compose_up", fake_compose_up)
    monkeypatch.setattr(lc, "_wait_for_base_services", lambda **kwargs: None)
    monkeypatch.setattr(lc, "_collect_lane_readiness", lambda **kwargs: {"ok": True, "lanes": {}})
    monkeypatch.setattr(lc, "_summary_text", lambda manifest: "")

    rc = lc.cmd_up(lc.UpOptions(out_dir=tmp_path))
    assert rc == 0
    assert calls == ["compose_up"]


def test_wait_for_lane_readiness_retries_until_ready(monkeypatch: pytest.MonkeyPatch) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    reports = [
        {"ok": False, "checks": {"spot": False}, "lanes": {}},
        {"ok": True, "checks": {"spot": True}, "lanes": {}},
    ]
    sleeps: list[float] = []

    monkeypatch.setattr(lc, "_collect_lane_readiness", lambda *, ui_base: reports.pop(0))
    monkeypatch.setattr(lc.time, "sleep", lambda seconds: sleeps.append(seconds))
    monkeypatch.setattr(lc.time, "monotonic", lambda: 0.0)

    result = lc._wait_for_lane_readiness(ui_base="http://127.0.0.1:18080", timeout_s=10)
    assert result["ok"] is True
    assert sleeps == [1.0]


def test_compose_overlay_zenodex_nginx_has_build_block() -> None:
    """zenodex:local must be buildable from the local-testnet overlay alone
    (so `compose up` doesn't fail with `image not found` on a fresh host)."""
    doc = _load_compose_overlay()
    nginx_svc = doc["services"]["zenodex-nginx"]
    assert "build" in nginx_svc, "zenodex-nginx must declare a build block"
    assert nginx_svc["build"].get("dockerfile") == "Dockerfile"
