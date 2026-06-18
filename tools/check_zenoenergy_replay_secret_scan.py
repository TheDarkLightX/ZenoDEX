#!/usr/bin/env python3
"""Deterministically scan ZenoEnergy replay reports for obvious live secrets."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


SECRET_SCAN_SCHEMA = "zenodex/energy/replay_secret_scan/v1"
SENSITIVE_KEYS = {
    "apikey",
    "accesstoken",
    "bearertoken",
    "mnemonic",
    "password",
    "privatekey",
    "refreshtoken",
    "secretkey",
    "seedphrase",
    "sessiontoken",
}
TEXT_RULES: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "private_key_pem",
        re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----"),
    ),
    (
        "aws_access_key_id",
        re.compile(r"\bAKIA[0-9A-Z]{16}\b"),
    ),
    (
        "openai_api_key",
        re.compile(r"\bsk-[A-Za-z0-9_-]{20,}\b"),
    ),
    (
        "github_token",
        re.compile(r"\bgh[pousr]_[A-Za-z0-9_]{20,}\b"),
    ),
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-report", type=Path, action="append", required=True)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args(argv)

    try:
        report = scan_replay_reports(args.source_report)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report.get("ok") is True else 1


def scan_replay_reports(paths: list[Path]) -> dict[str, Any]:
    if not paths:
        raise ValueError("at least one --source-report is required")

    findings: list[dict[str, Any]] = []
    source_reports = []
    for path in paths:
        if not path.exists():
            raise ValueError(f"source report does not exist: {path}")
        text = path.read_text(encoding="utf-8")
        source_reports.append(
            {
                "path": _display_path(path),
                "byte_count": len(text.encode("utf-8")),
            }
        )
        findings.extend(_scan_text(path, text))
        findings.extend(_scan_json_keys(path, text))

    return {
        "schema": SECRET_SCAN_SCHEMA,
        "ok": len(findings) == 0,
        "tool": "tools/check_zenoenergy_replay_secret_scan.py",
        "source_report_count": len(paths),
        "finding_count": len(findings),
        "findings": findings,
        "source_reports": source_reports,
        "negative_knowledge": (
            "This scanner catches obvious key material and sensitive JSON keys. "
            "It cannot prove privacy policy compliance or absence of all secrets."
        ),
    }


def secret_scan_manifest_fragment(report: dict[str, Any]) -> dict[str, Any]:
    if report.get("schema") != SECRET_SCAN_SCHEMA:
        raise ValueError("secret scan report must use replay_secret_scan/v1")
    return {
        "tool": str(report.get("tool", "")),
        "ok": report.get("ok") is True,
        "finding_count": int(report.get("finding_count", -1)),
        "schema": SECRET_SCAN_SCHEMA,
        "source_report_count": int(report.get("source_report_count", 0)),
    }


def _scan_text(path: Path, text: str) -> list[dict[str, Any]]:
    findings = []
    lines = text.splitlines()
    for rule_id, pattern in TEXT_RULES:
        for line_number, line in enumerate(lines, start=1):
            match = pattern.search(line)
            if match is None:
                continue
            findings.append(
                _finding(
                    path=path,
                    rule_id=rule_id,
                    location=f"line:{line_number}",
                    evidence=_redact(line[match.start() : match.end()]),
                )
            )
    return findings


def _scan_json_keys(path: Path, text: str) -> list[dict[str, Any]]:
    try:
        payload = json.loads(text)
    except json.JSONDecodeError:
        return []
    findings: list[dict[str, Any]] = []
    _walk_json(path, payload, "$", findings)
    return findings


def _walk_json(
    path: Path,
    value: Any,
    json_path: str,
    findings: list[dict[str, Any]],
) -> None:
    if isinstance(value, dict):
        for raw_key, child in value.items():
            key = str(raw_key)
            child_path = f"{json_path}.{key}"
            if _normalized_key(key) in SENSITIVE_KEYS and _has_nonempty_secret_value(child):
                findings.append(
                    _finding(
                        path=path,
                        rule_id="sensitive_json_key",
                        location=child_path,
                        evidence=key,
                    )
                )
            _walk_json(path, child, child_path, findings)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _walk_json(path, child, f"{json_path}[{index}]", findings)


def _has_nonempty_secret_value(value: Any) -> bool:
    if value is None:
        return False
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, dict)):
        return bool(value)
    return True


def _normalized_key(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", value.lower())


def _finding(*, path: Path, rule_id: str, location: str, evidence: str) -> dict[str, str]:
    return {
        "path": _display_path(path),
        "rule_id": rule_id,
        "location": location,
        "evidence": _redact(evidence),
    }


def _redact(value: str) -> str:
    if len(value) <= 8:
        return "***"
    return f"{value[:4]}...{value[-4:]}"


def _display_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(ROOT))
    except ValueError:
        return str(path)


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Replay Secret Scan",
        "",
        f"ok: {str(report['ok']).lower()}",
        f"source_report_count: {report['source_report_count']}",
        f"finding_count: {report['finding_count']}",
        "",
    ]
    if report["findings"]:
        lines.extend(["| path | rule | location | evidence |", "| --- | --- | --- | --- |"])
        for finding in report["findings"]:
            lines.append(
                f"| {finding['path']} | {finding['rule_id']} | "
                f"{finding['location']} | {finding['evidence']} |"
            )
    lines.extend(["", str(report["negative_knowledge"]), ""])
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
