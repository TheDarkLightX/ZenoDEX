#!/usr/bin/env python3
"""Check public fake-value testnet v0.1.16 evidence."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import urlparse

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.integration.local_route_quarantine import (  # noqa: E402
    CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1,
    CURRENT_LOCAL_OPERATOR_RELEASE_BLOCKER_V1,
)

SCHEMA = "zenodex.public_testnet_v0_1_16.evidence_manifest.v1"
REPORT_SCHEMA = "zenodex.public_testnet_v0_1_16.evidence_check_report.v1"
CURRENT_PROFILE_ID = CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1
CURRENT_RELEASE_BLOCKER = CURRENT_LOCAL_OPERATOR_RELEASE_BLOCKER_V1

REQUIRED_ARTIFACTS = (
    "local_full_stack_smoke_report",
    "external_laptop_acceptance_report",
    "second_clean_follower_report",
    "phone_browser_validation_report",
    "release_flow_transaction_smoke_report",
    "residual_limits_statement",
)

REQUIRED_RELEASE_CHECKS = (
    "faucet_tagrs",
    "zusd_collateral_deposit",
    "zusd_minted_from_collateral",
    "perps_collateral_deposit",
    "perps_long_short_open",
    "spot_swap_tagrs_tzdex",
    "status_and_header_agreement",
)


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _artifact_path(manifest_path: Path, raw: object) -> Path:
    if not isinstance(raw, str) or not raw.strip():
        raise ValueError("artifact path must be a non-empty string")
    path = Path(raw)
    return path if path.is_absolute() else manifest_path.parent / path


def _json_ok(obj: Mapping[str, Any]) -> bool:
    return obj.get("ok") is True or obj.get("status") == "accepted"


def _host(url: str) -> str:
    return str(urlparse(url).hostname or "").lower()


def _https_url(url: object) -> bool:
    return isinstance(url, str) and urlparse(url).scheme == "https" and bool(urlparse(url).netloc)


def _check_public_config_posture(manifest: Mapping[str, Any], errors: list[str]) -> None:
    public_url = manifest.get("public_config_url") or manifest.get("public_network_config_url")
    if not _https_url(public_url):
        errors.append("public_config_url must be an HTTPS URL")
        return
    posture = manifest.get("public_config_url_posture")
    stable_flag = manifest.get("stable_public_config_url")
    host = _host(str(public_url))
    if posture == "session_stable_quick_tunnel":
        if stable_flag is True:
            errors.append("stable_public_config_url must not be true for Quick Tunnel posture")
        if not host.endswith(".trycloudflare.com"):
            errors.append("session_stable_quick_tunnel requires a trycloudflare.com public_config_url")
    elif posture == "stable_named_url":
        if stable_flag is not True:
            errors.append("stable_named_url requires stable_public_config_url=true")
        if host.endswith(".trycloudflare.com"):
            errors.append("stable_named_url must not use trycloudflare.com")
    else:
        errors.append("public_config_url_posture must be stable_named_url or session_stable_quick_tunnel")


def _check_local_smoke(path: Path, errors: list[str]) -> None:
    obj = _load_json(path)
    if obj.get("ok") is not True:
        errors.append("local_full_stack_smoke_report must have ok=true")


def _check_acceptance_report(path: Path, label: str, errors: list[str]) -> None:
    obj = _load_json(path)
    if not _json_ok(obj):
        errors.append(f"{label} must be accepted")
    if obj.get("common_header_match") is not True:
        errors.append(f"{label} common_header_match must be true")
    if not isinstance(obj.get("network_config_hash"), str) or not str(obj.get("network_config_hash")).strip():
        errors.append(f"{label} network_config_hash must be a non-empty string")
    local_tip_raw = obj.get("local_tip")
    peer_tip_raw = obj.get("peer_tip")
    local_tip: Mapping[str, Any] = local_tip_raw if isinstance(local_tip_raw, Mapping) else {}
    peer_tip: Mapping[str, Any] = peer_tip_raw if isinstance(peer_tip_raw, Mapping) else {}
    live_observed = (
        obj.get("live_observed") is True
        or (local_tip.get("live") is True and peer_tip.get("live") is True)
    )
    if not live_observed:
        errors.append(f"{label} must observe live follower and seed tips")


def _check_phone_browser(path: Path, errors: list[str]) -> None:
    obj = _load_json(path)
    checks_raw = obj.get("checks")
    checks: Mapping[str, Any] = checks_raw if isinstance(checks_raw, Mapping) else {}
    loaded = (
        obj.get("public_ui_https_loaded") is True
        or obj.get("phone_browser_loaded") is True
        or checks.get("public_ui_https_loaded") is True
        or checks.get("ui_https_loaded") is True
    )
    status_loaded = obj.get("status_page_loaded") is True or checks.get("status_page_loaded") is True
    tokens_loaded = obj.get("token_list_loaded") is True or checks.get("token_list_loaded") is True
    if obj.get("ok") is not True or not loaded:
        errors.append("phone_browser_validation_report must prove HTTPS UI load")
    if not status_loaded:
        errors.append("phone_browser_validation_report must prove status page load")
    if not tokens_loaded:
        errors.append("phone_browser_validation_report must prove token list load")


def _check_release_flow(path: Path, errors: list[str]) -> None:
    obj = _load_json(path)
    if obj.get("ok") is not True:
        errors.append("release_flow_transaction_smoke_report must have ok=true")
    checks = obj.get("checks")
    if not isinstance(checks, Mapping):
        errors.append("release_flow_transaction_smoke_report checks must be an object")
        return
    for name in REQUIRED_RELEASE_CHECKS:
        item = checks.get(name)
        if not isinstance(item, Mapping) or item.get("ok") is not True:
            errors.append(f"release flow check {name} must have ok=true")
    perps_settled = checks.get("perps_settlement_cycle") or checks.get("perps_settled")
    if not isinstance(perps_settled, Mapping) or perps_settled.get("ok") is not True:
        errors.append("release flow must include accepted perps settlement cycle")


def _check_residual_limits(path: Path, posture: str, errors: list[str]) -> None:
    text = path.read_text(encoding="utf-8").strip()
    lowered = text.lower()
    if not text:
        errors.append("residual_limits_statement must be non-empty")
        return
    for phrase in ("fake-value", "no production value", "moves no mainnet assets"):
        if phrase not in lowered:
            errors.append(f"residual_limits_statement must mention {phrase}")
    if posture == "session_stable_quick_tunnel" and "session-stable" not in lowered:
        errors.append("residual_limits_statement must mention session-stable Quick Tunnel URL")


def check_evidence_manifest(manifest_path: Path) -> dict[str, Any]:
    errors: list[str] = []
    manifest = _load_json(manifest_path)
    if manifest.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA}")
    _check_public_config_posture(manifest, errors)
    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, Mapping):
        errors.append("artifacts must be an object")
        artifacts = {}

    resolved: dict[str, str] = {}
    for key in REQUIRED_ARTIFACTS:
        raw = artifacts.get(key)
        try:
            path = _artifact_path(manifest_path, raw)
        except Exception as exc:
            errors.append(f"{key}: {exc}")
            continue
        resolved[key] = str(path)
        if not path.is_file():
            errors.append(f"{key} missing: {path}")
            continue
        try:
            if key == "local_full_stack_smoke_report":
                _check_local_smoke(path, errors)
            elif key == "external_laptop_acceptance_report":
                _check_acceptance_report(path, key, errors)
            elif key == "second_clean_follower_report":
                _check_acceptance_report(path, key, errors)
            elif key == "phone_browser_validation_report":
                _check_phone_browser(path, errors)
            elif key == "release_flow_transaction_smoke_report":
                _check_release_flow(path, errors)
            elif key == "residual_limits_statement":
                _check_residual_limits(path, str(manifest.get("public_config_url_posture") or ""), errors)
        except Exception as exc:
            errors.append(f"{key}: {type(exc).__name__}: {exc}")

    historical_evidence_valid = not errors
    current_errors = [*errors, CURRENT_RELEASE_BLOCKER]
    return {
        "schema": REPORT_SCHEMA,
        "ok": False,
        "status": "blocked_current_profile",
        "historical_evidence_valid": historical_evidence_valid,
        "historical_status": "accepted" if historical_evidence_valid else "rejected",
        "current_profile_id": CURRENT_PROFILE_ID,
        "current_release_eligible": False,
        "authority": "NONE",
        "vm_gates_closed": [],
        "manifest_path": str(manifest_path),
        "artifacts": resolved,
        "errors": current_errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args(argv)
    try:
        report = check_evidence_manifest(args.manifest)
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "manifest_path": str(args.manifest),
            "errors": [f"{type(exc).__name__}: {exc}"],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
