#!/usr/bin/env python3
"""Validate breadth profiles for ZenoEnergy real replay evidence."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


PROFILE_SCHEMA = "zenodex/energy/replay_coverage_profile/v1"
PROFILE_CHECK_SCHEMA = "zenodex/energy/replay_coverage_profile_check/v1"
UPBA_REPORT_SCHEMA = "zenodex/energy/upba_real_replay_report/v1"
AUTOTRADER_REPORT_SCHEMA = "zenodex/energy/autotrader_real_shadow_report/v1"

MIN_UPBA_POOL_COUNT = 3
MIN_UPBA_INTENT_SIZE_BUCKET_COUNT = 3
MIN_UPBA_CANDIDATE_FAMILY_COUNT = 4
MIN_UPBA_HARD_NEGATIVE_FAMILY_COUNT = 4
MIN_UPBA_MIN_BATCHES_PER_MARKET_DAY = 50

MIN_AUTOTRADER_STRATEGY_FAMILY_COUNT = 3
MIN_AUTOTRADER_GUARD_FAMILY_COUNT = 4
MIN_AUTOTRADER_DECISION_FAMILY_COUNT = 3
MIN_AUTOTRADER_MIN_CONTEXTS_PER_MARKET_DAY = 20


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--real-report", type=Path, required=True)
    parser.add_argument("--coverage-profile", type=Path, required=True)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args(argv)

    report = validate_replay_coverage_profile(
        real_report=_load_json(args.real_report),
        profile=_load_json(args.coverage_profile),
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report.get("ok") is True else 1


def validate_replay_coverage_profile(
    *,
    real_report: dict[str, Any],
    profile: dict[str, Any],
) -> dict[str, Any]:
    expected_type = _expected_profile_type(real_report)
    source_report_count = len(_source_reports(real_report))
    checks = [
        _check(
            "schema",
            profile.get("schema") == PROFILE_SCHEMA,
            "profile must use replay_coverage_profile/v1",
        ),
        _check(
            "profile_type",
            str(profile.get("profile_type", "")) == expected_type,
            "profile_type must match the real replay report schema",
        ),
        _check(
            "source_kind_match",
            str(profile.get("source_kind", "")) == str(real_report.get("source_kind", "")),
            "profile source_kind must match real report",
        ),
        _check(
            "source_descriptor_match",
            str(profile.get("source_descriptor", ""))
            == str(real_report.get("source_descriptor", "")),
            "profile source_descriptor must match real report",
        ),
        _check(
            "market_day_count_match",
            _pass_if(
                lambda: _json_int(profile.get("market_day_count"), name="profile.market_day_count")
                == _json_int(real_report.get("market_day_count"), name="real_report.market_day_count")
            ),
            "profile market_day_count must match real report",
        ),
        _check(
            "source_report_count_match",
            _pass_if(
                lambda: _json_int(profile.get("source_report_count"), name="profile.source_report_count")
                == source_report_count
                and source_report_count > 0
            ),
            "profile source_report_count must match at least one hashed source report",
        ),
    ]
    if expected_type == "upba":
        checks.extend(_upba_checks(profile, real_report))
    elif expected_type == "autotrader":
        checks.extend(_autotrader_checks(profile, real_report))
    else:
        checks.append(
            _check(
                "report_schema",
                False,
                "real report must be UPBA real replay or AutoTrader real shadow",
            )
        )

    ok = all(check["passed"] is True for check in checks)
    return {
        "schema": PROFILE_CHECK_SCHEMA,
        "ok": ok,
        "profile_schema": PROFILE_SCHEMA,
        "profile_type": expected_type,
        "source_kind": str(profile.get("source_kind", "")),
        "source_descriptor": str(profile.get("source_descriptor", "")),
        "market_day_count": _safe_int(profile.get("market_day_count")),
        "source_report_count": _safe_int(profile.get("source_report_count")),
        "check_count": len(checks),
        "failed_count": sum(1 for check in checks if check["passed"] is not True),
        "coverage": _coverage_summary(profile, expected_type),
        "thresholds": _thresholds(expected_type),
        "checks": checks,
        "negative_knowledge": (
            "The coverage profile is a deterministic breadth guard. It cannot prove "
            "that production traffic is representative or that collection custody was truthful."
        ),
    }


def coverage_profile_summary(check_report: dict[str, Any]) -> dict[str, Any]:
    market_day_count = _safe_int(check_report.get("market_day_count"), default=-1)
    source_report_count = _safe_int(check_report.get("source_report_count"), default=-1)
    failed_count = _safe_int(check_report.get("failed_count"), default=-1)
    return {
        "schema": PROFILE_CHECK_SCHEMA,
        "ok": check_report.get("ok") is True
        and market_day_count >= 0
        and source_report_count >= 0
        and failed_count == 0,
        "profile_type": str(check_report.get("profile_type", "")),
        "source_kind": str(check_report.get("source_kind", "")),
        "source_descriptor": str(check_report.get("source_descriptor", "")),
        "market_day_count": max(market_day_count, 0),
        "source_report_count": max(source_report_count, 0),
        "failed_count": max(failed_count, 0),
        "coverage": check_report.get("coverage", {}),
    }


def _upba_checks(
    profile: dict[str, Any],
    real_report: dict[str, Any],
) -> list[dict[str, object]]:
    return [
        _check(
            "upba_pool_count",
            _pass_if(lambda: _json_int(profile.get("pool_count"), name="profile.pool_count") >= MIN_UPBA_POOL_COUNT),
            "UPBA replay must cover multiple pools",
        ),
        _check(
            "upba_intent_size_bucket_count",
            _pass_if(
                lambda: _json_int(profile.get("intent_size_bucket_count"), name="profile.intent_size_bucket_count")
                >= MIN_UPBA_INTENT_SIZE_BUCKET_COUNT
            ),
            "UPBA replay must cover multiple intent-set size buckets",
        ),
        _check(
            "upba_candidate_family_count",
            _pass_if(
                lambda: _json_int(profile.get("candidate_family_count"), name="profile.candidate_family_count")
                >= MIN_UPBA_CANDIDATE_FAMILY_COUNT
            ),
            "UPBA replay must cover multiple candidate families",
        ),
        _check(
            "upba_hard_negative_family_count",
            _pass_if(
                lambda: _json_int(profile.get("hard_negative_family_count"), name="profile.hard_negative_family_count")
                >= MIN_UPBA_HARD_NEGATIVE_FAMILY_COUNT
            ),
            "UPBA replay must include hard negative families",
        ),
        _check(
            "upba_min_batches_per_market_day",
            _pass_if(
                lambda: _json_int(
                    profile.get("min_batches_per_market_day"),
                    name="profile.min_batches_per_market_day",
                )
                >= MIN_UPBA_MIN_BATCHES_PER_MARKET_DAY
            ),
            "UPBA replay must avoid a thin market-day tail",
        ),
        _check(
            "upba_profile_not_larger_than_report",
            _pass_if(
                lambda: _json_int(profile.get("batch_count", real_report.get("batch_count")), name="profile.batch_count")
                <= _json_int(real_report.get("batch_count"), name="real_report.batch_count")
            ),
            "profile batch_count cannot exceed real report batch_count",
        ),
    ]


def _autotrader_checks(
    profile: dict[str, Any],
    real_report: dict[str, Any],
) -> list[dict[str, object]]:
    return [
        _check(
            "autotrader_strategy_family_count",
            _pass_if(
                lambda: _json_int(profile.get("strategy_family_count"), name="profile.strategy_family_count")
                >= MIN_AUTOTRADER_STRATEGY_FAMILY_COUNT
            ),
            "AutoTrader replay must cover multiple strategy families",
        ),
        _check(
            "autotrader_guard_family_count",
            _pass_if(
                lambda: _json_int(profile.get("guard_family_count"), name="profile.guard_family_count")
                >= MIN_AUTOTRADER_GUARD_FAMILY_COUNT
            ),
            "AutoTrader replay must cover multiple guard families",
        ),
        _check(
            "autotrader_decision_family_count",
            _pass_if(
                lambda: _json_int(profile.get("decision_family_count"), name="profile.decision_family_count")
                >= MIN_AUTOTRADER_DECISION_FAMILY_COUNT
            ),
            "AutoTrader replay must cover multiple decision families",
        ),
        _check(
            "autotrader_min_contexts_per_market_day",
            _pass_if(
                lambda: _json_int(
                    profile.get("min_contexts_per_market_day"),
                    name="profile.min_contexts_per_market_day",
                )
                >= MIN_AUTOTRADER_MIN_CONTEXTS_PER_MARKET_DAY
            ),
            "AutoTrader replay must avoid a thin market-day tail",
        ),
        _check(
            "autotrader_profile_not_larger_than_report",
            _pass_if(
                lambda: _json_int(
                    profile.get("context_count", real_report.get("context_count")),
                    name="profile.context_count",
                )
                <= _json_int(real_report.get("context_count"), name="real_report.context_count")
            ),
            "profile context_count cannot exceed real report context_count",
        ),
    ]


def _expected_profile_type(real_report: dict[str, Any]) -> str:
    schema = str(real_report.get("schema", ""))
    if schema == UPBA_REPORT_SCHEMA:
        return "upba"
    if schema == AUTOTRADER_REPORT_SCHEMA:
        return "autotrader"
    return "unknown"


def _coverage_summary(profile: dict[str, Any], profile_type: str) -> dict[str, int]:
    keys: tuple[str, ...]
    if profile_type == "upba":
        keys = (
            "pool_count",
            "intent_size_bucket_count",
            "candidate_family_count",
            "hard_negative_family_count",
            "min_batches_per_market_day",
        )
    elif profile_type == "autotrader":
        keys = (
            "strategy_family_count",
            "guard_family_count",
            "decision_family_count",
            "min_contexts_per_market_day",
        )
    else:
        keys = ()
    return {key: _safe_int(profile.get(key)) for key in keys}


def _thresholds(profile_type: str) -> dict[str, int]:
    if profile_type == "upba":
        return {
            "min_pool_count": MIN_UPBA_POOL_COUNT,
            "min_intent_size_bucket_count": MIN_UPBA_INTENT_SIZE_BUCKET_COUNT,
            "min_candidate_family_count": MIN_UPBA_CANDIDATE_FAMILY_COUNT,
            "min_hard_negative_family_count": MIN_UPBA_HARD_NEGATIVE_FAMILY_COUNT,
            "min_batches_per_market_day": MIN_UPBA_MIN_BATCHES_PER_MARKET_DAY,
        }
    if profile_type == "autotrader":
        return {
            "min_strategy_family_count": MIN_AUTOTRADER_STRATEGY_FAMILY_COUNT,
            "min_guard_family_count": MIN_AUTOTRADER_GUARD_FAMILY_COUNT,
            "min_decision_family_count": MIN_AUTOTRADER_DECISION_FAMILY_COUNT,
            "min_contexts_per_market_day": MIN_AUTOTRADER_MIN_CONTEXTS_PER_MARKET_DAY,
        }
    return {}


def _source_reports(real_report: dict[str, Any]) -> list[dict[str, Any]]:
    reports = real_report.get("source_reports", [])
    if not isinstance(reports, list):
        return []
    return [item for item in reports if isinstance(item, dict)]


def _json_int(value: object, *, name: str) -> int:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    raise ValueError(f"{name} must be a JSON integer")


def _safe_int(value: object, *, default: int = 0) -> int:
    try:
        return _json_int(value, name="value")
    except ValueError:
        return default


def _pass_if(fn: Any) -> bool:
    try:
        return bool(fn())
    except ValueError:
        return False


def _check(check_id: str, passed: bool, detail: str) -> dict[str, object]:
    return {"check_id": check_id, "passed": bool(passed), "detail": detail}


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected JSON object")
    return payload


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Replay Coverage Profile Check",
        "",
        f"ok: {str(report['ok']).lower()}",
        f"profile_type: {report['profile_type']}",
        f"source_kind: {report['source_kind']}",
        f"source_descriptor: {report['source_descriptor']}",
        f"market_day_count: {report['market_day_count']}",
        f"source_report_count: {report['source_report_count']}",
        "",
        "| check | result | detail |",
        "| --- | --- | --- |",
    ]
    for check in report["checks"]:
        lines.append(
            f"| {check['check_id']} | "
            f"{'pass' if check['passed'] else 'fail'} | "
            f"{check['detail']} |"
        )
    lines.extend(["", str(report["negative_knowledge"]), ""])
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
