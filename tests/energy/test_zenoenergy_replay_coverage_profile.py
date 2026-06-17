from __future__ import annotations

import json
from pathlib import Path

from tools.check_zenoenergy_replay_coverage_profile import (
    coverage_profile_summary,
    main,
    validate_replay_coverage_profile,
)


def test_upba_coverage_profile_passes_breadth_thresholds() -> None:
    check = validate_replay_coverage_profile(
        real_report=_upba_real_report(),
        profile=_upba_coverage_profile(),
    )
    summary = coverage_profile_summary(check)

    assert check["schema"] == "zenodex/energy/replay_coverage_profile_check/v1"
    assert check["ok"] is True
    assert check["failed_count"] == 0
    assert summary["profile_type"] == "upba"
    assert summary["coverage"]["hard_negative_family_count"] == 4


def test_coverage_profile_summary_requires_strict_ok() -> None:
    summary = coverage_profile_summary(
        {
            "ok": "true",
            "profile_type": "upba",
            "source_kind": "production-shadow",
            "source_descriptor": "prod-shadow",
            "market_day_count": 1,
            "source_report_count": 1,
            "failed_count": 0,
            "coverage": {},
        }
    )

    assert summary["ok"] is False


def test_upba_coverage_profile_rejects_thin_hard_negatives() -> None:
    profile = _upba_coverage_profile()
    profile["hard_negative_family_count"] = 1

    check = validate_replay_coverage_profile(
        real_report=_upba_real_report(),
        profile=profile,
    )
    failed = {
        str(item["check_id"])
        for item in check["checks"]
        if not bool(item["passed"])
    }

    assert check["ok"] is False
    assert "upba_hard_negative_family_count" in failed


def test_autotrader_coverage_profile_passes_guard_breadth() -> None:
    check = validate_replay_coverage_profile(
        real_report=_autotrader_real_report(),
        profile=_autotrader_coverage_profile(),
    )

    assert check["ok"] is True
    assert check["profile_type"] == "autotrader"
    assert check["coverage"]["guard_family_count"] == 4


def test_autotrader_coverage_profile_rejects_source_mismatch() -> None:
    profile = _autotrader_coverage_profile()
    profile["source_descriptor"] = "prod-shadow:autotrader:wrong-window"

    check = validate_replay_coverage_profile(
        real_report=_autotrader_real_report(),
        profile=profile,
    )
    failed = {
        str(item["check_id"])
        for item in check["checks"]
        if not bool(item["passed"])
    }

    assert check["ok"] is False
    assert "source_descriptor_match" in failed


def test_cli_writes_coverage_profile_check(tmp_path: Path) -> None:
    real_report = tmp_path / "upba_real.json"
    profile = tmp_path / "coverage.json"
    output = tmp_path / "coverage_check.json"
    real_report.write_text(json.dumps(_upba_real_report()), encoding="utf-8")
    profile.write_text(json.dumps(_upba_coverage_profile()), encoding="utf-8")

    rc = main(
        [
            "--real-report",
            str(real_report),
            "--coverage-profile",
            str(profile),
            "--output-json",
            str(output),
        ]
    )

    payload = json.loads(output.read_text(encoding="utf-8"))
    assert rc == 0
    assert payload["ok"] is True
    assert payload["profile_type"] == "upba"


def _upba_real_report() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/upba_real_replay_report/v1",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
        "batch_count": 1_250,
        "candidate_count": 25_000,
        "market_day_count": 9,
        "source_reports": [{"schema": "zenodex/energy/upba_v2_benchmark_report/v1"}],
    }


def _autotrader_real_report() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/autotrader_real_shadow_report/v1",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:autotrader:2026-05-01..2026-05-09",
        "context_count": 700,
        "row_count": 7_500,
        "market_day_count": 9,
        "source_reports": [{"schema": "zenodex/energy/autotrader_shadow_bridge_report/v1"}],
    }


def _upba_coverage_profile() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_coverage_profile/v1",
        "profile_type": "upba",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
        "market_day_count": 9,
        "source_report_count": 1,
        "batch_count": 1_250,
        "pool_count": 4,
        "intent_size_bucket_count": 3,
        "candidate_family_count": 5,
        "hard_negative_family_count": 4,
        "min_batches_per_market_day": 75,
    }


def _autotrader_coverage_profile() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_coverage_profile/v1",
        "profile_type": "autotrader",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:autotrader:2026-05-01..2026-05-09",
        "market_day_count": 9,
        "source_report_count": 1,
        "context_count": 700,
        "strategy_family_count": 3,
        "guard_family_count": 4,
        "decision_family_count": 3,
        "min_contexts_per_market_day": 50,
    }
