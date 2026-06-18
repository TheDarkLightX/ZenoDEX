from __future__ import annotations

import json
from pathlib import Path

from tools import check_zenoenergy_replay_secret_scan as secret_scan_tool
from tools.check_zenoenergy_replay_secret_scan import (
    SECRET_SCAN_SCHEMA,
    main,
    scan_replay_reports,
    secret_scan_manifest_fragment,
)


def test_secret_scan_accepts_clean_replay_report(tmp_path: Path) -> None:
    report_path = tmp_path / "upba_report.json"
    report_path.write_text(json.dumps(_clean_report()), encoding="utf-8")

    report = scan_replay_reports([report_path])
    fragment = secret_scan_manifest_fragment(report)

    assert report["schema"] == SECRET_SCAN_SCHEMA
    assert report["ok"] is True
    assert report["finding_count"] == 0
    assert fragment["ok"] is True
    assert fragment["finding_count"] == 0


def test_secret_scan_rejects_sensitive_json_key(tmp_path: Path) -> None:
    report_path = tmp_path / "autotrader_report.json"
    payload = _clean_report()
    payload["private_key"] = "0x" + "a" * 64
    report_path.write_text(json.dumps(payload), encoding="utf-8")

    report = scan_replay_reports([report_path])

    assert report["ok"] is False
    assert report["finding_count"] == 1
    assert report["findings"][0]["rule_id"] == "sensitive_json_key"
    assert report["findings"][0]["evidence"] == "priv..._key"


def test_secret_scan_manifest_fragment_requires_strict_ok() -> None:
    fragment = secret_scan_manifest_fragment(
        {
            "schema": SECRET_SCAN_SCHEMA,
            "tool": "local-secret-scan-v1",
            "ok": "true",
            "finding_count": 0,
            "source_report_count": 1,
        }
    )

    assert fragment["ok"] is False


def test_secret_scan_rejects_text_key_material(tmp_path: Path) -> None:
    report_path = tmp_path / "bad_report.json"
    report_path.write_text(
        json.dumps({"schema": "x", "note": "sk-" + "a" * 28}),
        encoding="utf-8",
    )

    report = scan_replay_reports([report_path])

    assert report["ok"] is False
    assert report["findings"][0]["rule_id"] == "openai_api_key"
    assert report["findings"][0]["evidence"].startswith("sk-a")


def test_secret_scan_cli_writes_report(tmp_path: Path) -> None:
    report_path = tmp_path / "upba_report.json"
    output_path = tmp_path / "secret_scan.json"
    markdown_path = tmp_path / "secret_scan.md"
    report_path.write_text(json.dumps(_clean_report()), encoding="utf-8")

    rc = main(
        [
            "--source-report",
            str(report_path),
            "--output-json",
            str(output_path),
            "--output-markdown",
            str(markdown_path),
        ]
    )

    payload = json.loads(output_path.read_text(encoding="utf-8"))
    assert rc == 0
    assert payload["ok"] is True
    assert "ZenoEnergy Replay Secret Scan" in markdown_path.read_text(encoding="utf-8")


def test_secret_scan_cli_returns_one_on_findings(tmp_path: Path) -> None:
    report_path = tmp_path / "bad_report.json"
    output_path = tmp_path / "secret_scan.json"
    report_path.write_text(
        json.dumps({"schema": "x", "aws": "AKIAABCDEFGHIJKLMNOP"}),
        encoding="utf-8",
    )

    rc = main(
        [
            "--source-report",
            str(report_path),
            "--output-json",
            str(output_path),
        ]
    )

    payload = json.loads(output_path.read_text(encoding="utf-8"))
    assert rc == 1
    assert payload["ok"] is False
    assert payload["finding_count"] == 1


def test_secret_scan_cli_rejects_truthy_string_ok(monkeypatch, tmp_path: Path) -> None:
    report_path = tmp_path / "upba_report.json"
    report_path.write_text(json.dumps(_clean_report()), encoding="utf-8")

    def fake_scan(_paths: list[Path]) -> dict[str, object]:
        return {
            "schema": SECRET_SCAN_SCHEMA,
            "tool": "tools/check_zenoenergy_replay_secret_scan.py",
            "ok": "true",
            "finding_count": 0,
            "source_report_count": 1,
        }

    monkeypatch.setattr(secret_scan_tool, "scan_replay_reports", fake_scan)

    rc = main(["--source-report", str(report_path)])

    assert rc == 1


def _clean_report() -> dict[str, object]:
    return {
        "schema": "zenodex/energy/upba_v2_benchmark_report/v1",
        "batches": 1250,
        "modes": {
            "hybrid": {"mean_verifier_calls": 1.7},
            "hand": {"mean_verifier_calls": 2.4},
        },
    }
