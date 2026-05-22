#!/usr/bin/env python3
"""Aggregate production-readiness checks for the AutoTrader chatbot provider path."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_autotrader_chatbot_advisor import build_report as build_advisor_report  # noqa: E402
from tools.check_autotrader_chatbot_provider_config import (  # noqa: E402
    build_report as build_provider_config_report,
)
from tools.evaluate_autotrader_chatbot_providers import build_report as build_eval_report  # noqa: E402

SCHEMA = "zenodex/agents/autotrader_chatbot_production_readiness/v1"


def build_report(
    *,
    provider_config: Path | None = None,
    evaluate_provider_config: bool = False,
) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []
    advisor_report = build_advisor_report()
    deterministic_eval_report = build_eval_report(
        provider_label="deterministic",
        provider=None,
    )
    _record(
        checks,
        "advisor_promotion_check.ok",
        bool(advisor_report["ok"]),
        f"passed={advisor_report['passed_count']}/{advisor_report['check_count']}",
    )
    _record(
        checks,
        "advisor_promotion_check.local_openai_covered",
        _has_passed_check(advisor_report, "local_openai.valid_loopback_parse_hint_remains_advisory")
        and _has_passed_check(advisor_report, "local_openai.invalid_authority_hint_falls_back"),
        "loopback OpenAI-compatible valid and invalid provider paths are covered",
    )
    _record(
        checks,
        "deterministic_provider_eval.ok",
        bool(deterministic_eval_report["ok"]),
        (
            f"passed={deterministic_eval_report['passed_count']}/"
            f"{deterministic_eval_report['scenario_count']}"
        ),
    )
    _record(
        checks,
        "deterministic_provider_eval.no_authority_violations",
        deterministic_eval_report["metrics"]["authority_violations"] == 0,
        f"authority_violations={deterministic_eval_report['metrics']['authority_violations']}",
    )
    _record(
        checks,
        "deterministic_provider_eval.latency_and_rss_recorded",
        deterministic_eval_report["metrics"]["elapsed_ms_max"] >= 0.0
        and deterministic_eval_report["metrics"]["process_max_rss_kb"] > 0,
        (
            f"elapsed_ms_max={deterministic_eval_report['metrics']['elapsed_ms_max']:.6f} "
            f"rss_kb={deterministic_eval_report['metrics']['process_max_rss_kb']}"
        ),
    )
    config_report = None
    if provider_config is not None:
        config_report = build_provider_config_report(
            provider_config,
            evaluate=evaluate_provider_config,
        )
        _record(
            checks,
            "provider_config.ok",
            bool(config_report["ok"]),
            f"config_path={provider_config}",
        )
        _record(
            checks,
            "provider_config.no_inline_secrets",
            _has_passed_check(config_report, "config.no_inline_secret_keys"),
            "provider config must not store API key material",
        )
        _record(
            checks,
            "provider_config.no_trade_authority_acknowledged",
            _has_passed_check(config_report, "config.no_trade_authority_acknowledged"),
            "provider config records no-trade-authority acknowledgement",
        )
    ok = all(bool(check["passed"]) for check in checks)
    return {
        "schema": SCHEMA,
        "ok": ok,
        "check_count": len(checks),
        "passed_count": sum(1 for check in checks if bool(check["passed"])),
        "failed_count": sum(1 for check in checks if not bool(check["passed"])),
        "summary": {
            "advisor_checks": advisor_report["check_count"],
            "deterministic_eval_scenarios": deterministic_eval_report["scenario_count"],
            "deterministic_authority_violations": deterministic_eval_report["metrics"][
                "authority_violations"
            ],
            "deterministic_elapsed_ms_p95": deterministic_eval_report["metrics"][
                "elapsed_ms_p95"
            ],
            "provider_config_checked": provider_config is not None,
            "provider_config_evaluated": evaluate_provider_config,
        },
        "checks": checks,
        "advisor_report": advisor_report,
        "deterministic_eval_report": deterministic_eval_report,
        "provider_config_report": config_report,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider-config", type=Path)
    parser.add_argument("--evaluate-provider-config", action="store_true")
    args = parser.parse_args(argv)
    if args.evaluate_provider_config and args.provider_config is None:
        parser.error("--evaluate-provider-config requires --provider-config")
    report = build_report(
        provider_config=args.provider_config,
        evaluate_provider_config=args.evaluate_provider_config,
    )
    # codeql[py/clear-text-logging-sensitive-data] Provider config report redacts credential values.
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def _has_passed_check(report: dict[str, Any], check_id: str) -> bool:
    return any(
        check.get("check_id") == check_id and bool(check.get("passed"))
        for check in report.get("checks", [])
    )


def _record(checks: list[dict[str, Any]], check_id: str, passed: bool, detail: str) -> None:
    checks.append({"check_id": check_id, "passed": bool(passed), "detail": detail})


if __name__ == "__main__":
    raise SystemExit(main())
