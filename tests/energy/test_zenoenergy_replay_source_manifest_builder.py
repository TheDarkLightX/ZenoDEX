from __future__ import annotations

import json
from pathlib import Path

from tools.build_zenoenergy_replay_source_manifest import (
    build_replay_source_manifest,
    main,
    validate_manifest_against_named_reports,
)
from tools.check_zenoenergy_replay_source_manifest import canonical_sha256


def test_builds_manifest_with_canonical_source_report_hash(tmp_path: Path) -> None:
    source_path = tmp_path / "upba_benchmark.json"
    source_payload = _source_payload()
    source_path.write_text(json.dumps(source_payload), encoding="utf-8")

    manifest = build_replay_source_manifest(
        manifest_id="prod-shadow-upba-20260501-20260509",
        source_kind="production-shadow",
        source_descriptor="prod-shadow:2026-05-01..2026-05-09",
        market_day_count=9,
        source_reports=[("upba-benchmark", source_path)],
        deterministic_replay_ok=True,
        no_live_secrets=True,
        secret_scan_tool="local-secret-scan-v1",
        secret_scan_ok=True,
        secret_scan_finding_count=0,
        operator_notes=["private replay corpus retained outside git"],
    )
    check = validate_manifest_against_named_reports(
        manifest,
        [("upba-benchmark", source_path)],
    )

    assert manifest["schema"] == "zenodex/energy/replay_source_manifest/v1"
    assert manifest["builder"]["schema"] == "zenodex/energy/replay_source_manifest_builder/v1"
    assert manifest["artifacts"][0]["name"] == "upba-benchmark"
    assert manifest["artifacts"][0]["sha256"] == canonical_sha256(source_payload)
    assert check["ok"] is True
    assert check["source_report_match_count"] == 1


def test_builder_rejects_missing_source_report() -> None:
    try:
        build_replay_source_manifest(
            manifest_id="prod-shadow-upba-20260501-20260509",
            source_kind="production-shadow",
            source_descriptor="prod-shadow:2026-05-01..2026-05-09",
            market_day_count=9,
            source_reports=[],
            deterministic_replay_ok=True,
            no_live_secrets=True,
            secret_scan_tool="local-secret-scan-v1",
            secret_scan_ok=True,
            secret_scan_finding_count=0,
        )
    except ValueError as exc:
        assert "source-report" in str(exc)
    else:
        raise AssertionError("builder should reject missing source reports")


def test_cli_writes_manifest_and_check(tmp_path: Path) -> None:
    source_path = tmp_path / "upba_benchmark.json"
    manifest_path = tmp_path / "manifest.json"
    check_path = tmp_path / "manifest_check.json"
    markdown_path = tmp_path / "manifest.md"
    source_path.write_text(json.dumps(_source_payload()), encoding="utf-8")

    rc = main(
        [
            "--manifest-id",
            "prod-shadow-upba-20260501-20260509",
            "--source-kind",
            "production-shadow",
            "--source-descriptor",
            "prod-shadow:2026-05-01..2026-05-09",
            "--market-day-count",
            "9",
            "--source-report",
            f"upba-benchmark={source_path}",
            "--deterministic-replay-ok",
            "--no-live-secrets",
            "--secret-scan-tool",
            "local-secret-scan-v1",
            "--secret-scan-ok",
            "--secret-scan-finding-count",
            "0",
            "--output-json",
            str(manifest_path),
            "--output-check-json",
            str(check_path),
            "--output-markdown",
            str(markdown_path),
        ]
    )

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    check = json.loads(check_path.read_text(encoding="utf-8"))
    assert rc == 0
    assert manifest["manifest_id"] == "prod-shadow-upba-20260501-20260509"
    assert check["ok"] is True
    assert "ZenoEnergy Replay Source Manifest" in markdown_path.read_text(
        encoding="utf-8"
    )


def test_cli_fails_closed_without_clean_secret_scan(tmp_path: Path) -> None:
    source_path = tmp_path / "upba_benchmark.json"
    manifest_path = tmp_path / "manifest.json"
    source_path.write_text(json.dumps(_source_payload()), encoding="utf-8")

    rc = main(
        [
            "--manifest-id",
            "prod-shadow-upba-20260501-20260509",
            "--source-kind",
            "production-shadow",
            "--source-descriptor",
            "prod-shadow:2026-05-01..2026-05-09",
            "--market-day-count",
            "9",
            "--source-report",
            f"upba-benchmark={source_path}",
            "--deterministic-replay-ok",
            "--no-live-secrets",
            "--secret-scan-tool",
            "local-secret-scan-v1",
            "--secret-scan-finding-count",
            "1",
            "--output-json",
            str(manifest_path),
        ]
    )

    assert rc == 2
    assert not manifest_path.exists()


def _source_payload() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/upba_v2_benchmark_report/v1",
        "batches": 1250,
        "modes": {
            "hybrid": {"mean_verifier_calls": 1.7},
            "hand": {"mean_verifier_calls": 2.4},
        },
    }
