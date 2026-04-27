from __future__ import annotations

import json
from pathlib import Path

from tools.check_dex_ui_dependency_audit import audit_is_clean, main, severity_counts


def _payload(**counts: int) -> dict[str, object]:
    severities = {
        "info": 0,
        "low": 0,
        "moderate": 0,
        "high": 0,
        "critical": 0,
        "total": 0,
    }
    severities.update(counts)
    severities["total"] = sum(
        int(severities[severity])
        for severity in ("info", "low", "moderate", "high", "critical")
    )
    return {"metadata": {"vulnerabilities": severities}, "vulnerabilities": {}}


def test_accepts_clean_audit() -> None:
    ok, counts, total = audit_is_clean(_payload())
    assert ok is True
    assert total == 0
    assert counts == {"info": 0, "low": 0, "moderate": 0, "high": 0, "critical": 0}


def test_rejects_moderate_vulnerability() -> None:
    ok, counts, total = audit_is_clean(_payload(moderate=1))
    assert ok is False
    assert total == 1
    assert counts["moderate"] == 1


def test_rejects_npm_audit_error_payload() -> None:
    ok, _counts, _total = audit_is_clean({"error": {"summary": "registry unavailable"}})
    assert ok is False


def test_counts_v2_vulnerability_entries_when_metadata_absent() -> None:
    counts = severity_counts(
        {
            "vulnerabilities": {
                "vite": {"severity": "high"},
                "postcss": {"severity": "moderate"},
            }
        }
    )
    assert counts["high"] == 1
    assert counts["moderate"] == 1


def test_cli_rejects_dirty_audit(tmp_path: Path, capsys) -> None:  # type: ignore[no-untyped-def]
    report = tmp_path / "audit.json"
    report.write_text(json.dumps(_payload(high=1)), encoding="utf-8")
    assert main(["--audit-json", str(report)]) == 1
    captured = capsys.readouterr()
    assert '"high": 1' in captured.out
    assert "DEX UI dependency audit found vulnerabilities" in captured.err


def test_cli_accepts_clean_audit(tmp_path: Path, capsys) -> None:  # type: ignore[no-untyped-def]
    report = tmp_path / "audit.json"
    report.write_text(json.dumps(_payload()), encoding="utf-8")
    assert main(["--audit-json", str(report)]) == 0
    captured = capsys.readouterr()
    assert '"ok": true' in captured.out
