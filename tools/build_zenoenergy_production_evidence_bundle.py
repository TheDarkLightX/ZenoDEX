#!/usr/bin/env python3
"""Assemble a fail-closed ZenoEnergy production evidence bundle."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.build_zenoenergy_real_replay_report import (  # noqa: E402
    ALLOWED_SOURCE_KINDS,
    build_autotrader_real_shadow_report,
    build_upba_real_replay_report,
)
from tools.check_zenoenergy_production_promotion import (  # noqa: E402
    build_production_gate_report,
)
from tools.check_zenoenergy_replay_source_manifest import (  # noqa: E402
    source_manifest_summary,
    source_report_from_path,
    validate_replay_source_manifest,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--research-replay",
        type=Path,
        default=ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json",
    )
    parser.add_argument("--upba-benchmark-report", type=Path)
    parser.add_argument("--upba-learned-report", type=Path)
    parser.add_argument("--upba-hand-report", type=Path)
    parser.add_argument("--upba-source-manifest", type=Path, required=True)
    parser.add_argument(
        "--upba-source-kind",
        choices=sorted(ALLOWED_SOURCE_KINDS),
        required=True,
    )
    parser.add_argument("--upba-source-descriptor", required=True)
    parser.add_argument("--upba-market-day-count", type=int, required=True)
    parser.add_argument("--autotrader-shadow-bridge-report", type=Path, required=True)
    parser.add_argument("--autotrader-source-manifest", type=Path, required=True)
    parser.add_argument(
        "--autotrader-source-kind",
        choices=sorted(ALLOWED_SOURCE_KINDS),
        required=True,
    )
    parser.add_argument("--autotrader-source-descriptor", required=True)
    parser.add_argument("--autotrader-market-day-count", type=int, required=True)
    parser.add_argument("--deterministic-replay-ok", action="store_true")
    parser.add_argument("--no-live-secrets", action="store_true")
    parser.add_argument("--operator-release-enable", action="store_true")
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args(argv)

    try:
        bundle = _build_from_args(args)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    encoded = json.dumps(bundle, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(bundle), encoding="utf-8")
    print(encoded)
    return 0


def build_production_evidence_bundle(
    *,
    research_replay: dict[str, Any],
    upba_source_manifest: dict[str, Any],
    upba_source_reports: list[dict[str, Any]],
    upba_source_kind: str,
    upba_source_descriptor: str,
    upba_market_day_count: int,
    autotrader_shadow_bridge_report: dict[str, Any],
    autotrader_source_manifest: dict[str, Any],
    autotrader_source_reports: list[dict[str, Any]],
    autotrader_source_kind: str,
    autotrader_source_descriptor: str,
    autotrader_market_day_count: int,
    deterministic_replay_ok: bool,
    no_live_secrets: bool,
    operator_release_enabled: bool,
    upba_benchmark_report: dict[str, Any] | None = None,
    upba_learned_report: dict[str, Any] | None = None,
    upba_hand_report: dict[str, Any] | None = None,
    source_paths: dict[str, str | None] | None = None,
) -> dict[str, Any]:
    if upba_benchmark_report is not None and (
        upba_learned_report is not None or upba_hand_report is not None
    ):
        raise ValueError("use either UPBA benchmark input or learned/hand inputs, not both")
    if upba_benchmark_report is None and (
        upba_learned_report is None or upba_hand_report is None
    ):
        raise ValueError("UPBA bundle input requires benchmark or both learned and hand reports")

    upba_manifest_check = _require_passing_manifest_check(
        label="UPBA",
        manifest=upba_source_manifest,
        source_reports=upba_source_reports,
    )
    autotrader_manifest_check = _require_passing_manifest_check(
        label="AutoTrader",
        manifest=autotrader_source_manifest,
        source_reports=autotrader_source_reports,
    )

    upba_real_replay = build_upba_real_replay_report(
        benchmark_report=upba_benchmark_report,
        learned_report=upba_learned_report,
        hand_report=upba_hand_report,
        source_kind=upba_source_kind,
        source_descriptor=upba_source_descriptor,
        market_day_count=upba_market_day_count,
        deterministic_replay_ok=deterministic_replay_ok,
        no_live_secrets=no_live_secrets,
        source_reports=upba_source_reports,
        source_manifest_check=upba_manifest_check,
    )
    autotrader_real_shadow = build_autotrader_real_shadow_report(
        shadow_bridge_report=autotrader_shadow_bridge_report,
        source_kind=autotrader_source_kind,
        source_descriptor=autotrader_source_descriptor,
        market_day_count=autotrader_market_day_count,
        deterministic_replay_ok=deterministic_replay_ok,
        no_live_secrets=no_live_secrets,
        source_reports=autotrader_source_reports,
        source_manifest_check=autotrader_manifest_check,
    )
    gate = build_production_gate_report(
        research_replay=research_replay,
        upba_real_replay=upba_real_replay,
        autotrader_real_shadow=autotrader_real_shadow,
        operator_release_enabled=operator_release_enabled,
        source_paths=source_paths or {},
    )

    return {
        "schema": "zenodex/energy/production_evidence_bundle/v1",
        "decision": gate["decision"],
        "promotion_allowed": bool(gate["promotion_allowed"]),
        "scope": "advisory_ranking_only",
        "builder": {
            "schema": "zenodex/energy/production_evidence_bundle_builder/v1",
            "tool": "tools/build_zenoenergy_production_evidence_bundle.py",
            "gate_tool": "tools/check_zenoenergy_production_promotion.py",
            "real_report_tool": "tools/build_zenoenergy_real_replay_report.py",
            "source_manifest_tool": "tools/check_zenoenergy_replay_source_manifest.py",
        },
        "source_paths": source_paths or {},
        "source_manifest_checks": {
            "upba": source_manifest_summary(upba_manifest_check),
            "autotrader": source_manifest_summary(autotrader_manifest_check),
        },
        "reports": {
            "upba_real_replay": upba_real_replay,
            "autotrader_real_shadow": autotrader_real_shadow,
            "production_gate": gate,
        },
        "blocked_reasons": gate["blocked_reasons"],
        "safety_contract": gate["safety_contract"],
        "negative_knowledge": [
            "A passing bundle promotes advisory ranking only.",
            "The bundle assembles replay reports, source manifest checks, and the gate decision; it cannot prove external data custody by itself.",
            "The scorer remains outside settlement validity, policy validity, state roots, and deterministic acceptance predicates.",
        ],
    }


def _build_from_args(args: argparse.Namespace) -> dict[str, Any]:
    if args.upba_benchmark_report is not None and (
        args.upba_learned_report is not None or args.upba_hand_report is not None
    ):
        raise ValueError("use either --upba-benchmark-report or learned/hand reports, not both")
    if args.upba_benchmark_report is None and (
        args.upba_learned_report is None or args.upba_hand_report is None
    ):
        raise ValueError(
            "UPBA evidence requires --upba-benchmark-report or both "
            "--upba-learned-report and --upba-hand-report"
        )

    upba_paths = [
        path
        for path in (
            args.upba_benchmark_report,
            args.upba_learned_report,
            args.upba_hand_report,
        )
        if path is not None
    ]
    source_paths = {
        "research_replay": _display_path(args.research_replay),
        "upba_benchmark_report": _optional_display_path(args.upba_benchmark_report),
        "upba_learned_report": _optional_display_path(args.upba_learned_report),
        "upba_hand_report": _optional_display_path(args.upba_hand_report),
        "upba_source_manifest": _display_path(args.upba_source_manifest),
        "autotrader_shadow_bridge_report": _display_path(args.autotrader_shadow_bridge_report),
        "autotrader_source_manifest": _display_path(args.autotrader_source_manifest),
    }
    return build_production_evidence_bundle(
        research_replay=_load_json(args.research_replay),
        upba_benchmark_report=_load_json(args.upba_benchmark_report)
        if args.upba_benchmark_report is not None
        else None,
        upba_learned_report=_load_json(args.upba_learned_report)
        if args.upba_learned_report is not None
        else None,
        upba_hand_report=_load_json(args.upba_hand_report)
        if args.upba_hand_report is not None
        else None,
        upba_source_manifest=_load_json(args.upba_source_manifest),
        upba_source_reports=[source_report_from_path(path) for path in upba_paths],
        upba_source_kind=args.upba_source_kind,
        upba_source_descriptor=args.upba_source_descriptor,
        upba_market_day_count=args.upba_market_day_count,
        autotrader_shadow_bridge_report=_load_json(args.autotrader_shadow_bridge_report),
        autotrader_source_manifest=_load_json(args.autotrader_source_manifest),
        autotrader_source_reports=[
            source_report_from_path(args.autotrader_shadow_bridge_report)
        ],
        autotrader_source_kind=args.autotrader_source_kind,
        autotrader_source_descriptor=args.autotrader_source_descriptor,
        autotrader_market_day_count=args.autotrader_market_day_count,
        deterministic_replay_ok=bool(args.deterministic_replay_ok),
        no_live_secrets=bool(args.no_live_secrets),
        operator_release_enabled=bool(args.operator_release_enable),
        source_paths=source_paths,
    )


def _require_passing_manifest_check(
    *,
    label: str,
    manifest: dict[str, Any],
    source_reports: list[dict[str, Any]],
) -> dict[str, Any]:
    check = validate_replay_source_manifest(
        manifest=manifest,
        source_reports=source_reports,
    )
    if bool(check.get("ok")) is not True:
        failed = ", ".join(
            str(item["check_id"])
            for item in check.get("checks", [])
            if not bool(item.get("passed"))
        )
        raise ValueError(f"{label} source manifest check failed: {failed}")
    return check


def _markdown_report(bundle: dict[str, Any]) -> str:
    gate = bundle["reports"]["production_gate"]
    lines = [
        "# ZenoEnergy Production Evidence Bundle",
        "",
        f"decision: {bundle['decision']}",
        f"promotion_allowed: {str(bundle['promotion_allowed']).lower()}",
        f"scope: {bundle['scope']}",
        "",
        "```text",
        "ProductionEvidenceBundle :=",
        "  UPBARealReplayReport",
        "  and AutoTraderRealShadowReport",
        "  and ReplaySourceManifestChecks",
        "  and ProductionPromotionGate",
        "```",
        "",
        "The bundle is valid only for advisory ranking. Acceptance remains under",
        "the deterministic verifier and AutoTrader policy guards.",
        "",
        "| obligation | result | reason |",
        "| --- | --- | --- |",
    ]
    for obligation in gate["obligations"]:
        lines.append(
            f"| {obligation['id']} | "
            f"{'pass' if obligation['passed'] else 'block'} | "
            f"{obligation['reason']} |"
        )
    lines.extend(["", "## Source Manifest Checks", ""])
    for name, summary in bundle["source_manifest_checks"].items():
        lines.append(
            f"- {name}: ok={str(summary['ok']).lower()}, "
            f"source_report_match_count={summary['source_report_match_count']}"
        )
    lines.extend(["", "## Negative Knowledge", ""])
    for item in bundle["negative_knowledge"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected JSON object")
    return payload


def _optional_display_path(path: Path | None) -> str | None:
    return None if path is None else _display_path(path)


def _display_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(ROOT))
    except ValueError:
        return str(path)


if __name__ == "__main__":
    raise SystemExit(main())
