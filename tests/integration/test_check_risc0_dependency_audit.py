from __future__ import annotations

import json
from pathlib import Path

from tools.check_risc0_dependency_audit import audit_is_acceptable, main


def _payload(*vulns: str, warnings: tuple[str, ...] = ()) -> dict[str, object]:
    return {
        "vulnerabilities": {
            "found": bool(vulns),
            "count": len(vulns),
            "list": [{"advisory": {"id": advisory_id}} for advisory_id in vulns],
        },
        "warnings": {
            "unmaintained": [{"advisory": {"id": advisory_id}} for advisory_id in warnings],
        },
    }


def test_accepts_clean_audit() -> None:
    ok, vulns, warnings, unexpected = audit_is_acceptable(_payload())
    assert ok is True
    assert vulns == []
    assert warnings == []
    assert unexpected == []


def test_rejects_previous_risc0_tracing_vulnerability_by_default() -> None:
    ok, vulns, warnings, unexpected = audit_is_acceptable(
        _payload(
            "RUSTSEC-2025-0055",
            warnings=("RUSTSEC-2025-0141", "RUSTSEC-2024-0388"),
        )
    )
    assert ok is False
    assert vulns == ["RUSTSEC-2025-0055"]
    assert warnings == ["RUSTSEC-2024-0388", "RUSTSEC-2025-0141"]
    assert unexpected == ["RUSTSEC-2025-0055"]


def test_can_accept_explicit_temporary_allowlist_with_warnings() -> None:
    ok, vulns, warnings, unexpected = audit_is_acceptable(
        _payload(
            "RUSTSEC-2025-0055",
            warnings=("RUSTSEC-2025-0141", "RUSTSEC-2024-0388"),
        ),
        allowed_vulnerabilities=("RUSTSEC-2025-0055",),
    )
    assert ok is True
    assert vulns == ["RUSTSEC-2025-0055"]
    assert warnings == ["RUSTSEC-2024-0388", "RUSTSEC-2025-0141"]
    assert unexpected == []


def test_rejects_new_vulnerability() -> None:
    ok, vulns, _warnings, unexpected = audit_is_acceptable(
        _payload("RUSTSEC-2023-0071", "RUSTSEC-2025-0055")
    )
    assert ok is False
    assert vulns == ["RUSTSEC-2023-0071", "RUSTSEC-2025-0055"]
    assert unexpected == ["RUSTSEC-2023-0071", "RUSTSEC-2025-0055"]


def test_cli_rejects_new_vulnerability(tmp_path: Path, capsys) -> None:  # type: ignore[no-untyped-def]
    report = tmp_path / "audit.json"
    report.write_text(json.dumps(_payload("RUSTSEC-2023-0071")), encoding="utf-8")
    assert main(["--audit-json", str(report)]) == 1
    captured = capsys.readouterr()
    assert "RUSTSEC-2023-0071" in captured.out
    assert "RISC Zero dependency vulnerabilities found" in captured.err


def test_cli_accepts_explicit_temporary_allowlist(tmp_path: Path, capsys) -> None:  # type: ignore[no-untyped-def]
    report = tmp_path / "audit.json"
    report.write_text(json.dumps(_payload("RUSTSEC-2025-0055")), encoding="utf-8")
    assert main(["--audit-json", str(report), "--allow", "RUSTSEC-2025-0055"]) == 0
    captured = capsys.readouterr()
    assert '"ok": true' in captured.out
