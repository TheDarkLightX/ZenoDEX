from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import check_zenoenergy_replay_source_manifest as source_manifest_checker
from tools.check_zenoenergy_replay_source_manifest import (
    canonical_sha256,
    main,
    source_manifest_summary,
    validate_replay_source_manifest,
)


def test_manifest_check_accepts_clean_real_source() -> None:
    source = _source_report()
    report = validate_replay_source_manifest(
        manifest=_manifest(source_reports=[source]),
        source_reports=[source],
    )

    assert report["schema"] == "zenodex/energy/replay_source_manifest_check/v1"
    assert report["ok"] is True
    assert report["source_report_match_count"] == 1
    assert report["failed_count"] == 0


def test_manifest_check_rejects_fixture_descriptor() -> None:
    source = _source_report()
    manifest = _manifest(source_reports=[source])
    manifest["source_descriptor"] = "synthetic fixture replay"

    report = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source],
    )

    assert report["ok"] is False
    assert _check(report, "source_descriptor")["passed"] is False


def test_manifest_check_rejects_dirty_secret_scan() -> None:
    source = _source_report()
    manifest = _manifest(source_reports=[source])
    manifest["secret_scan"] = {
        "tool": "local-secret-scan-v1",
        "ok": False,
        "finding_count": 1,
    }

    report = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source],
    )

    assert report["ok"] is False
    assert _check(report, "secret_scan_clean")["passed"] is False


def test_manifest_check_rejects_truthy_string_attestations() -> None:
    source = _source_report()
    manifest = _manifest(source_reports=[source])
    manifest["deterministic_replay_ok"] = "true"
    manifest["no_live_secrets"] = "true"

    report = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source],
    )

    assert report["ok"] is False
    assert _check(report, "deterministic_replay_ok")["passed"] is False
    assert _check(report, "no_live_secrets")["passed"] is False


def test_manifest_check_rejects_truthy_string_secret_scan_ok() -> None:
    source = _source_report()
    manifest = _manifest(source_reports=[source])
    secret_scan = manifest["secret_scan"]
    assert isinstance(secret_scan, dict)
    secret_scan["ok"] = "true"

    report = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source],
    )

    assert report["ok"] is False
    assert _check(report, "secret_scan_clean")["passed"] is False


def test_manifest_check_rejects_numeric_string_market_day_count() -> None:
    source = _source_report()
    manifest = _manifest(source_reports=[source])
    manifest["market_day_count"] = "9"

    report = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source],
    )

    assert report["ok"] is False
    assert report["market_day_count"] == 0
    assert _check(report, "market_day_count")["passed"] is False


def test_manifest_check_rejects_numeric_string_secret_scan_count() -> None:
    source = _source_report()
    manifest = _manifest(source_reports=[source])
    secret_scan = manifest["secret_scan"]
    assert isinstance(secret_scan, dict)
    secret_scan["finding_count"] = "0"

    report = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source],
    )

    assert report["ok"] is False
    assert _check(report, "secret_scan_clean")["passed"] is False


def test_source_manifest_summary_requires_strict_ok() -> None:
    summary = source_manifest_summary(
        {
            "ok": "true",
            "manifest_id": "m",
            "source_kind": "production-shadow",
            "source_descriptor": "prod-shadow",
            "market_day_count": 1,
            "source_report_count": 1,
            "source_report_match_count": 1,
            "failed_count": 0,
        }
    )

    assert summary["ok"] is False


def test_source_manifest_summary_rejects_coerced_counts() -> None:
    summary = source_manifest_summary(
        {
            "ok": True,
            "manifest_id": "m",
            "source_kind": "production-shadow",
            "source_descriptor": "prod-shadow",
            "market_day_count": "1",
            "source_report_count": "1",
            "source_report_match_count": True,
            "failed_count": "0",
        }
    )

    assert summary["ok"] is False
    assert summary["market_day_count"] == 0
    assert summary["source_report_count"] == 0
    assert summary["source_report_match_count"] == 0
    assert summary["failed_count"] == 0


def test_manifest_check_rejects_source_report_hash_mismatch() -> None:
    source = _source_report()
    manifest = _manifest(source_reports=[dict(source)])
    source["sha256"] = "0" * 64

    report = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source],
    )

    assert report["ok"] is False
    assert _check(report, "source_reports_match")["passed"] is False


def test_manifest_check_cli_writes_report(tmp_path: Path) -> None:
    source_path = tmp_path / "source.json"
    manifest_path = tmp_path / "manifest.json"
    output_path = tmp_path / "check.json"
    source_payload = _source_payload()
    source_path.write_text(json.dumps(source_payload), encoding="utf-8")
    source = {
        "name": "upba-benchmark",
        "schema": source_payload["schema"],
        "sha256": canonical_sha256(source_payload),
    }
    manifest_path.write_text(json.dumps(_manifest(source_reports=[source])), encoding="utf-8")

    rc = main(
        [
            "--manifest",
            str(manifest_path),
            "--source-report",
            str(source_path),
            "--output-json",
            str(output_path),
        ]
    )

    payload = json.loads(output_path.read_text(encoding="utf-8"))
    assert rc == 0
    assert payload["ok"] is True
    assert payload["source_report_match_count"] == 1


def test_manifest_check_cli_rejects_truthy_non_bool_ok(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps({"schema": "ignored"}), encoding="utf-8")

    def forged_report(
        *,
        manifest: dict[str, object],
        source_reports: list[dict[str, object]] | None = None,
    ) -> dict[str, object]:
        return {
            "schema": "zenodex/energy/replay_source_manifest_check/v1",
            "ok": "true",
        }

    monkeypatch.setattr(source_manifest_checker, "validate_replay_source_manifest", forged_report)

    rc = main(["--manifest", str(manifest_path)])

    assert rc == 1


def _check(report: dict[str, object], check_id: str) -> dict[str, object]:
    checks = report["checks"]
    assert isinstance(checks, list)
    for check in checks:
        assert isinstance(check, dict)
        if check["check_id"] == check_id:
            return check
    raise AssertionError(f"missing check {check_id}")


def _source_payload() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/upba_v2_benchmark_report/v1",
        "batches": 1250,
        "modes": {},
    }


def _source_report() -> dict[str, object]:
    payload = _source_payload()
    return {
        "name": "upba-benchmark",
        "schema": payload["schema"],
        "sha256": canonical_sha256(payload),
    }


def _manifest(*, source_reports: list[dict[str, object]]) -> dict[str, object]:
    return {
        "schema": "zenodex/energy/replay_source_manifest/v1",
        "manifest_id": "prod-shadow-upba-20260501-20260509",
        "source_kind": "production-shadow",
        "source_descriptor": "prod-shadow:2026-05-01..2026-05-09",
        "market_day_count": 9,
        "deterministic_replay_ok": True,
        "no_live_secrets": True,
        "secret_scan": {
            "tool": "local-secret-scan-v1",
            "ok": True,
            "finding_count": 0,
        },
        "artifacts": source_reports,
        "operational_limits": [
            "external data custody is asserted by the operator replay pipeline",
        ],
    }
