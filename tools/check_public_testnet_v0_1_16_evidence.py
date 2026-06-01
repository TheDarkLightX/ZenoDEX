#!/usr/bin/env python3
"""Validate the scoped public-testnet v0.1.16 release evidence bundle."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import parse_qsl, urlsplit

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_sdk_browser_bundle_v0 import (  # noqa: E402
    validate_browser_checkpoint_bundle_v0,
)
from tools.check_zeno_ledger_two_machine_evidence import (  # noqa: E402
    validate_two_machine_evidence_v0,
)

EVIDENCE_SCHEMA = "zenodex.public_testnet.v0_1_16.evidence.v0"
REPORT_SCHEMA = "zenodex.public_testnet.v0_1_16.evidence_report.v0"
_ROOT_RE = re.compile(r"^0x[0-9a-f]{64}$")
_SENSITIVE_QUERY_NAMES = ("auth", "bearer", "key", "password", "secret", "token")
_REQUIRED_RESIDUAL_LIMITS = {
    "designated_writer_testnet",
    "fake_tokens_only",
    "no_production_value",
    "open_p2p_gossip_later",
}


def validate_public_testnet_v0_1_16_evidence(evidence: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(evidence, "evidence", errors)
    _exact_keys(
        obj,
        {
            "schema",
            "release_version",
            "network_config_url",
            "network_config_hash",
            "stable_public_config_url",
            "two_machine_evidence",
            "clean_machine_join",
            "second_clean_machine",
            "phone_or_browser_client",
            "residual_limits",
        },
        "evidence",
        errors,
    )
    if obj.get("schema") != EVIDENCE_SCHEMA:
        errors.append("schema mismatch")
    if obj.get("release_version") != "v0.1.16":
        errors.append("release_version must be v0.1.16")

    network_config_url = _str(obj.get("network_config_url"), "network_config_url", errors)
    if network_config_url is not None:
        _url(
            network_config_url,
            name="network_config_url",
            require_https=True,
            errors=errors,
        )
    network_config_hash = _root(obj.get("network_config_hash"), "network_config_hash", errors)
    if obj.get("stable_public_config_url") is not True:
        errors.append("stable_public_config_url must be true")

    two_machine_report = validate_two_machine_evidence_v0(obj.get("two_machine_evidence"))
    if two_machine_report.get("ok") is not True:
        errors.append("two_machine_evidence rejected: " + "; ".join(two_machine_report.get("errors", [])))
    if network_config_hash is not None and two_machine_report.get("network_config_hash") != network_config_hash:
        errors.append("two_machine_evidence network_config_hash mismatch")
    common_header_hash = two_machine_report.get("common_header_hash")

    clean_ok = _validate_clean_machine_join(
        obj.get("clean_machine_join"),
        network_config_hash=network_config_hash,
        errors=errors,
    )
    second_ok = _validate_second_clean_machine(
        obj.get("second_clean_machine"),
        network_config_hash=network_config_hash,
        common_header_hash=common_header_hash,
        errors=errors,
    )
    browser_ok = _validate_phone_or_browser_client(obj.get("phone_or_browser_client"), errors)
    residual_ok = _validate_residual_limits(obj.get("residual_limits"), errors)

    required = {
        "stable_public_config_url": obj.get("stable_public_config_url") is True,
        "network_config_url_https": network_config_url is not None,
        "two_machine_evidence": two_machine_report.get("ok") is True,
        "clean_machine_join_from_url": clean_ok,
        "second_clean_machine_common_header": second_ok,
        "phone_or_browser_no_backend_tokens": browser_ok,
        "residual_limits": residual_ok,
    }
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "required_evidence_fields": required,
        "network_config_url": network_config_url,
        "network_config_hash": network_config_hash,
        "common_header_hash": common_header_hash,
    }


def _validate_clean_machine_join(
    value: Any,
    *,
    network_config_hash: str | None,
    errors: list[str],
) -> bool:
    obj = _mapping(value, "clean_machine_join", errors)
    _exact_keys(
        obj,
        {
            "ok",
            "joined_from_config_url",
            "bundle_hashes_verified",
            "seed_peer_check_ok",
            "served_status",
            "network_config_hash",
        },
        "clean_machine_join",
        errors,
    )
    for key in ("ok", "joined_from_config_url", "bundle_hashes_verified", "seed_peer_check_ok", "served_status"):
        if obj.get(key) is not True:
            errors.append(f"clean_machine_join.{key} must be true")
    observed_hash = _root(obj.get("network_config_hash"), "clean_machine_join.network_config_hash", errors)
    if network_config_hash is not None and observed_hash != network_config_hash:
        errors.append("clean_machine_join.network_config_hash mismatch")
    return (
        obj.get("ok") is True
        and obj.get("joined_from_config_url") is True
        and obj.get("bundle_hashes_verified") is True
        and obj.get("seed_peer_check_ok") is True
        and obj.get("served_status") is True
        and observed_hash == network_config_hash
    )


def _validate_second_clean_machine(
    value: Any,
    *,
    network_config_hash: str | None,
    common_header_hash: Any,
    errors: list[str],
) -> bool:
    obj = _mapping(value, "second_clean_machine", errors)
    _exact_keys(
        obj,
        {"ok", "network_config_hash", "common_header_hash"},
        "second_clean_machine",
        errors,
    )
    if obj.get("ok") is not True:
        errors.append("second_clean_machine.ok must be true")
    observed_network_hash = _root(
        obj.get("network_config_hash"),
        "second_clean_machine.network_config_hash",
        errors,
    )
    observed_header_hash = _root(
        obj.get("common_header_hash"),
        "second_clean_machine.common_header_hash",
        errors,
    )
    if network_config_hash is not None and observed_network_hash != network_config_hash:
        errors.append("second_clean_machine.network_config_hash mismatch")
    if isinstance(common_header_hash, str) and observed_header_hash != common_header_hash:
        errors.append("second_clean_machine.common_header_hash mismatch")
    return (
        obj.get("ok") is True
        and observed_network_hash == network_config_hash
        and isinstance(common_header_hash, str)
        and observed_header_hash == common_header_hash
    )


def _validate_phone_or_browser_client(value: Any, errors: list[str]) -> bool:
    obj = _mapping(value, "phone_or_browser_client", errors)
    mode = obj.get("mode")
    if mode == "public_https_ui":
        _exact_keys(
            obj,
            {"ok", "mode", "public_ui_url", "loaded_public_ui", "backend_bearer_tokens_exposed"},
            "phone_or_browser_client",
            errors,
        )
        public_ui_url = _str(obj.get("public_ui_url"), "phone_or_browser_client.public_ui_url", errors)
        if public_ui_url is not None:
            _url(public_ui_url, name="phone_or_browser_client.public_ui_url", require_https=True, errors=errors)
        if obj.get("loaded_public_ui") is not True:
            errors.append("phone_or_browser_client.loaded_public_ui must be true")
        return _common_phone_browser_checks(obj, errors) and obj.get("loaded_public_ui") is True
    if mode == "lan_or_vpn_ui":
        _exact_keys(
            obj,
            {"ok", "mode", "ui_url", "loaded_ui", "backend_bearer_tokens_exposed"},
            "phone_or_browser_client",
            errors,
        )
        ui_url = _str(obj.get("ui_url"), "phone_or_browser_client.ui_url", errors)
        if ui_url is not None:
            _url(ui_url, name="phone_or_browser_client.ui_url", require_https=False, errors=errors)
        if obj.get("loaded_ui") is not True:
            errors.append("phone_or_browser_client.loaded_ui must be true")
        return _common_phone_browser_checks(obj, errors) and obj.get("loaded_ui") is True
    if mode == "checkpoint_bundle":
        _exact_keys(
            obj,
            {
                "ok",
                "mode",
                "browser_checkpoint_bundle",
                "browser_report",
                "backend_bearer_tokens_exposed",
            },
            "phone_or_browser_client",
            errors,
        )
        bundle = _mapping(
            obj.get("browser_checkpoint_bundle"),
            "phone_or_browser_client.browser_checkpoint_bundle",
            errors,
        )
        browser_report = _mapping(
            obj.get("browser_report"),
            "phone_or_browser_client.browser_report",
            errors,
        )
        try:
            validate_browser_checkpoint_bundle_v0(bundle)
        except Exception as exc:  # noqa: BLE001 - convert validator detail into gate error
            errors.append(f"browser_checkpoint_bundle rejected: {exc}")
        if browser_report.get("ok") is not True:
            errors.append("phone_or_browser_client.browser_report.ok must be true")
        if browser_report.get("browser_range_replay_verified") is not True:
            errors.append("phone_or_browser_client.browser_report.browser_range_replay_verified must be true")
        if browser_report.get("bundle_hash") != bundle.get("bundle_hash"):
            errors.append("phone_or_browser_client.browser_report.bundle_hash mismatch")
        summary = _mapping(
            bundle.get("verification_summary"),
            "phone_or_browser_client.browser_checkpoint_bundle.verification_summary",
            errors,
        )
        if browser_report.get("checkpoint_hash") != summary.get("checkpoint_hash"):
            errors.append("phone_or_browser_client.browser_report.checkpoint_hash mismatch")
        return (
            _common_phone_browser_checks(obj, errors)
            and browser_report.get("ok") is True
            and browser_report.get("browser_range_replay_verified") is True
            and browser_report.get("bundle_hash") == bundle.get("bundle_hash")
            and browser_report.get("checkpoint_hash") == summary.get("checkpoint_hash")
        )
    errors.append("phone_or_browser_client.mode must be public_https_ui, lan_or_vpn_ui, or checkpoint_bundle")
    return False


def _common_phone_browser_checks(obj: Mapping[str, Any], errors: list[str]) -> bool:
    if obj.get("ok") is not True:
        errors.append("phone_or_browser_client.ok must be true")
    if obj.get("backend_bearer_tokens_exposed") is not False:
        errors.append("phone_or_browser_client.backend_bearer_tokens_exposed must be false")
    return obj.get("ok") is True and obj.get("backend_bearer_tokens_exposed") is False


def _validate_residual_limits(value: Any, errors: list[str]) -> bool:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        errors.append("residual_limits must be a list of strings")
        return False
    missing = sorted(_REQUIRED_RESIDUAL_LIMITS - set(value))
    if missing:
        errors.append("residual_limits missing: " + ",".join(missing))
    return not missing


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _exact_keys(value: Mapping[str, Any], expected: set[str], name: str, errors: list[str]) -> None:
    actual = set(value.keys())
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        if missing:
            errors.append(f"{name} missing keys: {','.join(missing)}")
        if extra:
            errors.append(f"{name} unknown keys: {','.join(extra)}")


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


def _url(value: str, *, name: str, require_https: bool, errors: list[str]) -> None:
    parsed = urlsplit(value)
    allowed_schemes = {"https"} if require_https else {"http", "https"}
    if parsed.scheme not in allowed_schemes:
        expected = "https" if require_https else "http or https"
        errors.append(f"{name} must use {expected}")
    if parsed.username is not None or parsed.password is not None:
        errors.append(f"{name} must not contain userinfo credentials")
    if parsed.netloc == "":
        errors.append(f"{name} must include a host")
    for key, _value in parse_qsl(parsed.query, keep_blank_values=True):
        lowered = key.lower()
        if any(marker in lowered for marker in _SENSITIVE_QUERY_NAMES):
            errors.append(f"{name} must not carry sensitive query parameter {key}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    raw = json.loads(args.evidence.read_text(encoding="utf-8"))
    report = validate_public_testnet_v0_1_16_evidence(raw)
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
