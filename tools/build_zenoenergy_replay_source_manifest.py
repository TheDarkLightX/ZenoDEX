#!/usr/bin/env python3
"""Build and immediately validate a ZenoEnergy replay source manifest."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zenoenergy_replay_source_manifest import (  # noqa: E402
    ALLOWED_SOURCE_KINDS,
    source_report_from_path,
    validate_replay_source_manifest,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest-id", required=True)
    parser.add_argument("--source-kind", choices=sorted(ALLOWED_SOURCE_KINDS), required=True)
    parser.add_argument("--source-descriptor", required=True)
    parser.add_argument("--market-day-count", type=int, required=True)
    parser.add_argument(
        "--source-report",
        action="append",
        default=[],
        metavar="NAME=PATH",
        help="Replay report artifact to bind. May be repeated.",
    )
    parser.add_argument("--deterministic-replay-ok", action="store_true")
    parser.add_argument("--no-live-secrets", action="store_true")
    parser.add_argument("--secret-scan-tool", default="operator-secret-scan")
    parser.add_argument("--secret-scan-ok", action="store_true")
    parser.add_argument("--secret-scan-finding-count", type=int, default=0)
    parser.add_argument("--operator-note", action="append", default=[])
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-check-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args(argv)

    try:
        named_reports = [_parse_named_report(item) for item in args.source_report]
        manifest = build_replay_source_manifest(
            manifest_id=args.manifest_id,
            source_kind=args.source_kind,
            source_descriptor=args.source_descriptor,
            market_day_count=args.market_day_count,
            source_reports=named_reports,
            deterministic_replay_ok=bool(args.deterministic_replay_ok),
            no_live_secrets=bool(args.no_live_secrets),
            secret_scan_tool=args.secret_scan_tool,
            secret_scan_ok=bool(args.secret_scan_ok),
            secret_scan_finding_count=args.secret_scan_finding_count,
            operator_notes=args.operator_note,
        )
        check = validate_manifest_against_named_reports(manifest, named_reports)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if bool(check["ok"]) is not True:
        failed = ", ".join(
            str(item["check_id"])
            for item in check.get("checks", [])
            if not bool(item.get("passed"))
        )
        print(f"error: replay source manifest check failed: {failed}", file=sys.stderr)
        return 2

    encoded_manifest = json.dumps(manifest, indent=2, sort_keys=True)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(encoded_manifest + "\n", encoding="utf-8")
    if args.output_check_json is not None:
        args.output_check_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_check_json.write_text(
            json.dumps(check, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(manifest, check), encoding="utf-8")
    print(encoded_manifest)
    return 0


def build_replay_source_manifest(
    *,
    manifest_id: str,
    source_kind: str,
    source_descriptor: str,
    market_day_count: int,
    source_reports: list[tuple[str, Path]],
    deterministic_replay_ok: bool,
    no_live_secrets: bool,
    secret_scan_tool: str,
    secret_scan_ok: bool,
    secret_scan_finding_count: int,
    operator_notes: list[str] | None = None,
) -> dict[str, Any]:
    if not source_reports:
        raise ValueError("at least one --source-report NAME=PATH is required")
    if not manifest_id:
        raise ValueError("manifest_id is required")
    if secret_scan_finding_count < 0:
        raise ValueError("secret_scan_finding_count must be nonnegative")

    artifacts = []
    for name, path in source_reports:
        source_report = source_report_from_path(path)
        artifacts.append(
            {
                "name": name,
                "schema": source_report["schema"],
                "sha256": source_report["sha256"],
                "path": source_report["path"],
            }
        )

    return {
        "schema": "zenodex/energy/replay_source_manifest/v1",
        "manifest_id": manifest_id,
        "source_kind": source_kind,
        "source_descriptor": source_descriptor,
        "market_day_count": int(market_day_count),
        "deterministic_replay_ok": bool(deterministic_replay_ok),
        "no_live_secrets": bool(no_live_secrets),
        "secret_scan": {
            "tool": secret_scan_tool,
            "ok": bool(secret_scan_ok),
            "finding_count": int(secret_scan_finding_count),
        },
        "artifacts": artifacts,
        "operator_notes": operator_notes or [],
        "builder": {
            "schema": "zenodex/energy/replay_source_manifest_builder/v1",
            "tool": "tools/build_zenoenergy_replay_source_manifest.py",
            "checker": "tools/check_zenoenergy_replay_source_manifest.py",
        },
        "negative_knowledge": (
            "The builder computes source hashes and runs local schema checks. It "
            "does not prove external custody, truthful collection, or log completeness."
        ),
    }


def validate_manifest_against_named_reports(
    manifest: dict[str, Any],
    source_reports: list[tuple[str, Path]],
) -> dict[str, Any]:
    return validate_replay_source_manifest(
        manifest=manifest,
        source_reports=[source_report_from_path(path) for _, path in source_reports],
    )


def _parse_named_report(value: str) -> tuple[str, Path]:
    if "=" not in value:
        raise ValueError("--source-report must use NAME=PATH")
    name, raw_path = value.split("=", 1)
    if not name:
        raise ValueError("--source-report name must be nonempty")
    path = Path(raw_path)
    if not path.exists():
        raise ValueError(f"source report does not exist: {path}")
    return name, path


def _markdown_report(manifest: dict[str, Any], check: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Replay Source Manifest",
        "",
        f"manifest_id: {manifest['manifest_id']}",
        f"source_kind: {manifest['source_kind']}",
        f"source_descriptor: {manifest['source_descriptor']}",
        f"market_day_count: {manifest['market_day_count']}",
        f"check_ok: {str(check['ok']).lower()}",
        "",
        "| artifact | schema | sha256 |",
        "| --- | --- | --- |",
    ]
    for artifact in manifest["artifacts"]:
        lines.append(
            f"| {artifact['name']} | {artifact['schema']} | {artifact['sha256']} |"
        )
    lines.extend(
        [
            "",
            "This manifest is an input to the ZenoEnergy production evidence bundle.",
            "It records source hashes and attestations; it does not prove external custody.",
            "",
        ]
    )
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
