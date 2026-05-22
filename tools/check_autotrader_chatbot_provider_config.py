#!/usr/bin/env python3
"""Validate an AutoTrader chatbot local LLM provider config."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.autotrader_llm_provider import (  # noqa: E402
    AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
    build_autotrader_language_provider_from_config,
    load_autotrader_llm_provider_config_file,
)
from tools.evaluate_autotrader_chatbot_providers import build_report as build_eval_report  # noqa: E402

SCHEMA = "zenodex/agents/autotrader_chatbot_provider_config_check/v1"
_FORBIDDEN_SECRET_KEYS = {
    "api_key",
    "authorization",
    "bearer_token",
    "password",
    "secret",
    "token",
}


def build_report(config_path: Path, *, evaluate: bool = False) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    raw_text = config_path.read_text(encoding="utf-8")
    try:
        raw = json.loads(raw_text)
    except json.JSONDecodeError as exc:
        return {
            "schema": SCHEMA,
            "ok": False,
            "config_path": str(config_path),
            "error": f"json_decode_error:{exc.msg}",
            "checks": [],
        }
    _record(
        checks,
        "config.no_inline_secret_keys",
        not _contains_forbidden_secret_key(raw),
        "config must reference api_key_env instead of storing secrets",
    )
    try:
        config = load_autotrader_llm_provider_config_file(config_path)
    except Exception as exc:
        return {
            "schema": SCHEMA,
            "ok": False,
            "config_path": str(config_path),
            "error": str(exc),
            "check_count": len(checks),
            "passed_count": sum(1 for check in checks if bool(check["passed"])),
            "failed_count": sum(1 for check in checks if not bool(check["passed"])),
            "checks": checks,
        }
    metadata = config.to_metadata()
    _record(
        checks,
        "config.schema",
        metadata["schema"] == AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
        f"schema={metadata['schema']}",
    )
    _record(
        checks,
        "config.no_trade_authority_acknowledged",
        config.provider_kind == "deterministic" or config.user_acknowledges_no_trade_authority,
        f"provider_kind={config.provider_kind}",
    )
    _record(
        checks,
        "config.license_responsibility_acknowledged",
        config.provider_kind == "deterministic"
        or config.user_accepts_model_license_responsibility,
        f"license_label={config.license_label}",
    )
    _record(
        checks,
        "config.local_endpoint_risk_acknowledged",
        config.provider_kind == "deterministic" or config.user_accepts_local_endpoint_risk,
        f"allow_non_loopback={config.allow_non_loopback}",
    )
    _record(
        checks,
        "config.loopback_default",
        config.provider_kind == "deterministic" or not config.allow_non_loopback,
        "production default should keep local providers on loopback",
    )
    provider = build_autotrader_language_provider_from_config(config)
    _record(
        checks,
        "config.provider_builds",
        provider is not None or config.provider_kind == "deterministic",
        f"provider_kind={config.provider_kind}",
    )
    eval_report = None
    if evaluate:
        eval_report = build_eval_report(
            provider_label=config.provider_label,
            provider=provider,
            provider_config=config,
        )
        _record(
            checks,
            "evaluation.ok",
            bool(eval_report["ok"]),
            (
                f"passed={eval_report['passed_count']}/{eval_report['scenario_count']} "
                f"authority_violations={eval_report['metrics']['authority_violations']}"
            ),
        )
        _record(
            checks,
            "evaluation.no_authority_violations",
            eval_report["metrics"]["authority_violations"] == 0,
            f"authority_violations={eval_report['metrics']['authority_violations']}",
        )
        if config.provider_kind == "local_openai_compatible":
            _record(
                checks,
                "evaluation.local_provider_called",
                eval_report["metrics"]["provider_call_count"] > 0,
                f"provider_call_count={eval_report['metrics']['provider_call_count']}",
            )
            _record(
                checks,
                "evaluation.local_provider_schema_valid",
                eval_report["metrics"]["provider_schema_valid_count"] > 0,
                (
                    "provider_schema_valid_count="
                    f"{eval_report['metrics']['provider_schema_valid_count']}"
                ),
            )
            _record(
                checks,
                "evaluation.local_provider_no_fallback",
                eval_report["metrics"]["provider_fallback_count"] == 0,
                f"provider_fallback_count={eval_report['metrics']['provider_fallback_count']}",
            )
    ok = all(bool(check["passed"]) for check in checks)
    return {
        "schema": SCHEMA,
        "ok": ok,
        "config_path": str(config_path),
        "provider_config": metadata,
        "check_count": len(checks),
        "passed_count": sum(1 for check in checks if bool(check["passed"])),
        "failed_count": sum(1 for check in checks if not bool(check["passed"])),
        "checks": checks,
        "evaluation": eval_report,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--evaluate", action="store_true")
    args = parser.parse_args(argv)
    report = build_report(args.config, evaluate=args.evaluate)
    # codeql[py/clear-text-logging-sensitive-data] Config report exposes only metadata and validation status.
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def _contains_forbidden_secret_key(value: Any) -> bool:
    if isinstance(value, dict):
        for key, item in value.items():
            if str(key).lower() in _FORBIDDEN_SECRET_KEYS:
                return True
            if _contains_forbidden_secret_key(item):
                return True
    if isinstance(value, list):
        return any(_contains_forbidden_secret_key(item) for item in value)
    return False


def _record(checks: list[dict[str, Any]], check_id: str, passed: bool, detail: str) -> None:
    checks.append({"check_id": check_id, "passed": bool(passed), "detail": detail})


if __name__ == "__main__":
    raise SystemExit(main())
