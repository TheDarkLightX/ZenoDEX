from __future__ import annotations

import json
from pathlib import Path

from tools import check_zenoenergy_replay_coverage_profile as coverage_tool
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


def test_coverage_profile_summary_rejects_coerced_counts() -> None:
    summary = coverage_profile_summary(
        {
            "ok": True,
            "profile_type": "upba",
            "source_kind": "production-shadow",
            "source_descriptor": "prod-shadow",
            "market_day_count": "1",
            "source_report_count": True,
            "failed_count": "0",
            "coverage": {},
        }
    )

    assert summary["ok"] is False
    assert summary["market_day_count"] == 0
    assert summary["source_report_count"] == 0
    assert summary["failed_count"] == 0


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


def test_upba_coverage_profile_rejects_numeric_string_market_day_count() -> None:
    profile = _upba_coverage_profile()
    profile["market_day_count"] = "9"

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
    assert check["market_day_count"] == 0
    assert "market_day_count_match" in failed


def test_upba_coverage_profile_rejects_coerced_breadth_counts() -> None:
    profile = _upba_coverage_profile()
    profile["pool_count"] = "4"

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
    assert check["coverage"]["pool_count"] == 0
    assert "upba_pool_count" in failed


def test_upba_coverage_profile_rejects_coerced_real_report_counts() -> None:
    real_report = _upba_real_report()
    real_report["batch_count"] = "1250"

    check = validate_replay_coverage_profile(
        real_report=real_report,
        profile=_upba_coverage_profile(),
    )
    failed = {
        str(item["check_id"])
        for item in check["checks"]
        if not bool(item["passed"])
    }

    assert check["ok"] is False
    assert "upba_profile_not_larger_than_report" in failed


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


def test_autotrader_coverage_profile_rejects_coerced_context_count() -> None:
    profile = _autotrader_coverage_profile()
    profile["context_count"] = "700"

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
    assert "autotrader_profile_not_larger_than_report" in failed


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


def test_cli_rejects_truthy_string_coverage_ok(monkeypatch, tmp_path: Path) -> None:
    real_report = tmp_path / "upba_real.json"
    profile = tmp_path / "coverage.json"
    real_report.write_text(json.dumps(_upba_real_report()), encoding="utf-8")
    profile.write_text(json.dumps(_upba_coverage_profile()), encoding="utf-8")

    def fake_validate_replay_coverage_profile(*, real_report, profile):
        return {
            "schema": "zenodex/energy/replay_coverage_profile_check/v1",
            "ok": "true",
            "profile_type": "upba",
            "failed_count": 0,
        }

    monkeypatch.setattr(
        coverage_tool,
        "validate_replay_coverage_profile",
        fake_validate_replay_coverage_profile,
    )

    rc = main(["--real-report", str(real_report), "--coverage-profile", str(profile)])

    assert rc == 1


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
