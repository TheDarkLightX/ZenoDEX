#!/usr/bin/env python3
"""Validate replay source manifests for ZenoEnergy real evidence reports."""

from __future__ import annotations

import argparse
import json
import re
import sys
from hashlib import sha256
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


ALLOWED_SOURCE_KINDS = {"production-shadow", "historical-replay"}
FORBIDDEN_SOURCE_MARKERS = ("synthetic", "fixture", "built-in", "generated")
SHA256_RE = re.compile(r"^(sha256:)?[0-9a-f]{64}$")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--source-report", type=Path, action="append", default=[])
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args(argv)

    report = validate_replay_source_manifest(
        manifest=_load_json(args.manifest),
        source_reports=[_source_report(path) for path in args.source_report],
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if bool(report["ok"]) else 1


def validate_replay_source_manifest(
    *,
    manifest: dict[str, Any],
    source_reports: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    artifacts = _manifest_artifacts(manifest)
    source_reports = source_reports or []
    checks = [
        _check(
            "schema",
            manifest.get("schema") == "zenodex/energy/replay_source_manifest/v1",
            "manifest must use replay_source_manifest/v1",
        ),
        _check(
            "source_kind",
            str(manifest.get("source_kind")) in ALLOWED_SOURCE_KINDS,
            "source_kind must be production-shadow or historical-replay",
        ),
        _check(
            "source_descriptor",
            _non_fixture_descriptor(str(manifest.get("source_descriptor", ""))),
            "source_descriptor must avoid synthetic, fixture, built-in, and generated markers",
        ),
        _check(
            "market_day_count",
            int(manifest.get("market_day_count", 0)) > 0,
            "market_day_count must be positive",
        ),
        _check(
            "deterministic_replay_ok",
            bool(manifest.get("deterministic_replay_ok")) is True,
            "deterministic replay attestation must be true",
        ),
        _check(
            "no_live_secrets",
            bool(manifest.get("no_live_secrets")) is True,
            "no-live-secrets attestation must be true",
        ),
        _check(
            "secret_scan_clean",
            _secret_scan_clean(manifest),
            "secret scan must pass with zero findings",
        ),
        _check(
            "artifact_hashes",
            bool(artifacts) and all(_valid_artifact(item) for item in artifacts),
            "artifacts must include valid SHA-256 hashes and schemas",
        ),
        _check(
            "source_reports_match",
            _source_reports_match(artifacts, source_reports),
            "every supplied source report must match a manifest artifact hash",
        ),
    ]
    ok = all(bool(check["passed"]) for check in checks)
    return {
        "schema": "zenodex/energy/replay_source_manifest_check/v1",
        "ok": ok,
        "manifest_id": str(manifest.get("manifest_id", "")),
        "source_kind": str(manifest.get("source_kind", "")),
        "source_descriptor": str(manifest.get("source_descriptor", "")),
        "market_day_count": int(manifest.get("market_day_count", 0)),
        "deterministic_replay_ok": bool(manifest.get("deterministic_replay_ok")),
        "no_live_secrets": bool(manifest.get("no_live_secrets")),
        "artifact_count": len(artifacts),
        "source_report_count": len(source_reports),
        "source_report_match_count": _source_report_match_count(artifacts, source_reports),
        "check_count": len(checks),
        "failed_count": sum(1 for check in checks if not bool(check["passed"])),
        "checks": checks,
        "negative_knowledge": (
            "The manifest check binds source hashes and attestations. It cannot "
            "prove external custody or truthful collection by itself."
        ),
    }


def source_manifest_summary(check_report: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": "zenodex/energy/replay_source_manifest_check/v1",
        "ok": bool(check_report.get("ok")),
        "manifest_id": str(check_report.get("manifest_id", "")),
        "source_kind": str(check_report.get("source_kind", "")),
        "source_descriptor": str(check_report.get("source_descriptor", "")),
        "market_day_count": int(check_report.get("market_day_count", 0)),
        "source_report_count": int(check_report.get("source_report_count", 0)),
        "source_report_match_count": int(check_report.get("source_report_match_count", 0)),
        "failed_count": int(check_report.get("failed_count", 0)),
    }


def source_report_from_path(path: Path) -> dict[str, Any]:
    return _source_report(path)


def canonical_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return sha256(encoded).hexdigest()


def _source_report(path: Path) -> dict[str, Any]:
    payload = _load_json(path)
    return {
        "path": _display_path(path),
        "schema": payload.get("schema"),
        "sha256": canonical_sha256(payload),
    }


def _source_reports_match(
    artifacts: list[dict[str, Any]],
    source_reports: list[dict[str, Any]],
) -> bool:
    if not source_reports:
        return True
    return _source_report_match_count(artifacts, source_reports) == len(source_reports)


def _source_report_match_count(
    artifacts: list[dict[str, Any]],
    source_reports: list[dict[str, Any]],
) -> int:
    artifact_keys = {
        (_strip_sha_prefix(str(item.get("sha256", ""))), str(item.get("schema", "")))
        for item in artifacts
    }
    return sum(
        1
        for report in source_reports
        if (_strip_sha_prefix(str(report.get("sha256", ""))), str(report.get("schema", "")))
        in artifact_keys
    )


def _manifest_artifacts(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    artifacts = manifest.get("artifacts", [])
    if not isinstance(artifacts, list):
        return []
    return [item for item in artifacts if isinstance(item, dict)]


def _valid_artifact(item: dict[str, Any]) -> bool:
    return (
        bool(str(item.get("name", "")))
        and bool(str(item.get("schema", "")))
        and SHA256_RE.match(str(item.get("sha256", ""))) is not None
    )


def _secret_scan_clean(manifest: dict[str, Any]) -> bool:
    scan = manifest.get("secret_scan", {})
    if not isinstance(scan, dict):
        return False
    return bool(scan.get("ok")) is True and int(scan.get("finding_count", -1)) == 0


def _non_fixture_descriptor(value: str) -> bool:
    lowered = value.lower()
    return bool(value) and not any(marker in lowered for marker in FORBIDDEN_SOURCE_MARKERS)


def _strip_sha_prefix(value: str) -> str:
    return value.removeprefix("sha256:")


def _check(check_id: str, passed: bool, detail: str) -> dict[str, object]:
    return {"check_id": check_id, "passed": bool(passed), "detail": detail}


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected JSON object")
    return payload


def _display_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(ROOT))
    except ValueError:
        return str(path)


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Replay Source Manifest Check",
        "",
        f"ok: {str(report['ok']).lower()}",
        f"manifest_id: {report['manifest_id']}",
        f"source_kind: {report['source_kind']}",
        f"source_descriptor: {report['source_descriptor']}",
        f"market_day_count: {report['market_day_count']}",
        f"source_report_match_count: {report['source_report_match_count']}",
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
