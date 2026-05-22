#!/usr/bin/env python3
"""Build real replay reports for the ZenoEnergy production promotion gate."""

from __future__ import annotations

import argparse
import json
import sys
from hashlib import sha256
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_zenoenergy_replay_source_manifest import (  # noqa: E402
    source_manifest_summary,
    source_report_from_path,
    validate_replay_source_manifest,
)
from tools.check_zenoenergy_replay_coverage_profile import (  # noqa: E402
    coverage_profile_summary,
    validate_replay_coverage_profile,
)


ALLOWED_SOURCE_KINDS = {"production-shadow", "historical-replay"}
FORBIDDEN_SOURCE_MARKERS = ("synthetic", "fixture", "built-in", "generated")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="report_type", required=True)

    upba = subparsers.add_parser(
        "upba",
        help="Build zenodex/energy/upba_real_replay_report/v1",
    )
    upba.add_argument("--benchmark-report", type=Path)
    upba.add_argument("--learned-report", type=Path)
    upba.add_argument("--hand-report", type=Path)
    _add_common_args(upba)

    autotrader = subparsers.add_parser(
        "autotrader",
        help="Build zenodex/energy/autotrader_real_shadow_report/v1",
    )
    autotrader.add_argument("--shadow-bridge-report", type=Path, required=True)
    _add_common_args(autotrader)

    args = parser.parse_args(argv)
    try:
        if args.report_type == "upba":
            report = _build_upba_from_args(args)
        else:
            report = _build_autotrader_from_args(args)
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
    return 0


def build_upba_real_replay_report(
    *,
    benchmark_report: dict[str, Any] | None = None,
    learned_report: dict[str, Any] | None = None,
    hand_report: dict[str, Any] | None = None,
    source_kind: str,
    source_descriptor: str,
    market_day_count: int,
    deterministic_replay_ok: bool,
    no_live_secrets: bool,
    source_reports: list[dict[str, Any]] | None = None,
    source_manifest_check: dict[str, Any] | None = None,
    coverage_profile: dict[str, Any] | None = None,
) -> dict[str, Any]:
    _validate_common_real_assertions(
        source_kind=source_kind,
        source_descriptor=source_descriptor,
        market_day_count=market_day_count,
        deterministic_replay_ok=deterministic_replay_ok,
        no_live_secrets=no_live_secrets,
    )
    _validate_source_manifest_check(
        source_manifest_check,
        source_kind=source_kind,
        source_descriptor=source_descriptor,
        market_day_count=market_day_count,
    )
    if benchmark_report is not None:
        learned, hand, top_level = _extract_upba_modes_from_benchmark(benchmark_report)
    else:
        if learned_report is None or hand_report is None:
            raise ValueError("UPBA report requires --benchmark-report or both learned and hand reports")
        learned, hand, top_level = _extract_upba_modes_from_evaluations(
            learned_report,
            hand_report,
        )

    batch_count = int(learned.get("batches", top_level.get("batches", 0)))
    candidate_count = _candidate_total(learned, batch_count=batch_count)
    invalid_accept_count = int(
        top_level.get(
            "invalid_accept_count",
            int(learned.get("invalid_accept_count", 0)) + int(hand.get("invalid_accept_count", 0)),
        )
    )
    permutation_violation_count = int(learned.get("permutation_violation_count", 0))

    report = {
        "schema": "zenodex/energy/upba_real_replay_report/v1",
        "source_kind": source_kind,
        "source_descriptor": source_descriptor,
        "batch_count": batch_count,
        "candidate_count": candidate_count,
        "market_day_count": int(market_day_count),
        "invalid_accept_count": invalid_accept_count,
        "permutation_violation_count": permutation_violation_count,
        "top_25_recall": _topk_metric(learned, k=25, objective=False),
        "top_25_objective_recall": _topk_metric(learned, k=25, objective=True),
        "learned_mean_verifier_calls": _mean_call_metric(learned, "verifier"),
        "hand_mean_verifier_calls": _mean_call_metric(hand, "verifier"),
        "deterministic_replay_ok": True,
        "no_live_secrets": True,
        "source_reports": source_reports or [],
        "builder": {
            "schema": "zenodex/energy/real_replay_report_builder/v1",
            "tool": "tools/build_zenoenergy_real_replay_report.py",
            "report_type": "upba",
            "performance_gate_delegated_to": "tools/check_zenoenergy_production_promotion.py",
        },
    }
    if source_manifest_check is not None:
        report["source_manifest"] = source_manifest_summary(source_manifest_check)
    _attach_coverage_profile(report, coverage_profile)
    return report


def build_autotrader_real_shadow_report(
    *,
    shadow_bridge_report: dict[str, Any],
    source_kind: str,
    source_descriptor: str,
    market_day_count: int,
    deterministic_replay_ok: bool,
    no_live_secrets: bool,
    source_reports: list[dict[str, Any]] | None = None,
    source_manifest_check: dict[str, Any] | None = None,
    coverage_profile: dict[str, Any] | None = None,
) -> dict[str, Any]:
    _validate_common_real_assertions(
        source_kind=source_kind,
        source_descriptor=source_descriptor,
        market_day_count=market_day_count,
        deterministic_replay_ok=deterministic_replay_ok,
        no_live_secrets=no_live_secrets,
    )
    _validate_source_manifest_check(
        source_manifest_check,
        source_kind=source_kind,
        source_descriptor=source_descriptor,
        market_day_count=market_day_count,
    )
    if shadow_bridge_report.get("schema") != "zenodex/energy/autotrader_shadow_bridge_report/v1":
        raise ValueError("AutoTrader input must use autotrader_shadow_bridge_report/v1")
    report_source = str(shadow_bridge_report.get("source", ""))
    if _looks_non_real_source(report_source):
        raise ValueError(f"AutoTrader shadow source is not production-grade: {report_source!r}")

    shadow = shadow_bridge_report.get("shadow", {})
    modes = shadow_bridge_report.get("modes", {})
    learned = _require_mode(modes, "hybrid")
    hand = _require_mode(modes, "hand")
    safety = shadow_bridge_report.get("safety", {})

    report = {
        "schema": "zenodex/energy/autotrader_real_shadow_report/v1",
        "source_kind": source_kind,
        "source_descriptor": source_descriptor,
        "source": report_source,
        "context_count": int(shadow.get("context_count", 0)),
        "row_count": int(shadow.get("row_count", 0)),
        "market_day_count": int(market_day_count),
        "invalid_accept_count_total": int(safety.get("invalid_accept_count_total", 0)),
        "top_25_recall": _topk_metric(learned, k=25, objective=False),
        "top_25_objective_recall": _topk_metric(learned, k=25, objective=True),
        "learned_mean_guard_calls": _mean_call_metric(learned, "guard"),
        "hand_mean_guard_calls": _mean_call_metric(hand, "guard"),
        "deterministic_replay_ok": True,
        "no_live_secrets": True,
        "policy_guards_authoritative": bool(safety.get("policy_guards_authoritative")),
        "scorer_authorizes_trade": bool(safety.get("scorer_authorizes_trade")),
        "model_output_in_state_root": bool(safety.get("model_output_in_state_root")),
        "source_reports": source_reports or [],
        "builder": {
            "schema": "zenodex/energy/real_replay_report_builder/v1",
            "tool": "tools/build_zenoenergy_real_replay_report.py",
            "report_type": "autotrader",
            "performance_gate_delegated_to": "tools/check_zenoenergy_production_promotion.py",
        },
    }
    if source_manifest_check is not None:
        report["source_manifest"] = source_manifest_summary(source_manifest_check)
    _attach_coverage_profile(report, coverage_profile)
    return report


def _add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--source-kind",
        choices=sorted(ALLOWED_SOURCE_KINDS),
        required=True,
    )
    parser.add_argument(
        "--source-descriptor",
        required=True,
        help="Human source description, for example prod-shadow:2026-05-01..2026-05-08",
    )
    parser.add_argument("--market-day-count", type=int, required=True)
    parser.add_argument("--deterministic-replay-ok", action="store_true")
    parser.add_argument("--no-live-secrets", action="store_true")
    parser.add_argument("--source-manifest", type=Path)
    parser.add_argument("--coverage-profile", type=Path)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)


def _build_upba_from_args(args: argparse.Namespace) -> dict[str, Any]:
    if args.benchmark_report is not None and (
        args.learned_report is not None or args.hand_report is not None
    ):
        raise ValueError("use either --benchmark-report or learned/hand reports, not both")
    if args.benchmark_report is None and (
        args.learned_report is None or args.hand_report is None
    ):
        raise ValueError("UPBA report requires --benchmark-report or both --learned-report and --hand-report")

    benchmark = _load_json(args.benchmark_report) if args.benchmark_report is not None else None
    learned = _load_json(args.learned_report) if args.learned_report is not None else None
    hand = _load_json(args.hand_report) if args.hand_report is not None else None
    source_reports = [
        _source_report(path)
        for path in (args.benchmark_report, args.learned_report, args.hand_report)
        if path is not None
    ]
    source_manifest_check = _source_manifest_check_from_args(args, source_reports)
    return build_upba_real_replay_report(
        benchmark_report=benchmark,
        learned_report=learned,
        hand_report=hand,
        source_kind=args.source_kind,
        source_descriptor=args.source_descriptor,
        market_day_count=args.market_day_count,
        deterministic_replay_ok=bool(args.deterministic_replay_ok),
        no_live_secrets=bool(args.no_live_secrets),
        source_reports=source_reports,
        source_manifest_check=source_manifest_check,
        coverage_profile=_load_json(args.coverage_profile)
        if args.coverage_profile is not None
        else None,
    )


def _build_autotrader_from_args(args: argparse.Namespace) -> dict[str, Any]:
    bridge = _load_json(args.shadow_bridge_report)
    return build_autotrader_real_shadow_report(
        shadow_bridge_report=bridge,
        source_kind=args.source_kind,
        source_descriptor=args.source_descriptor,
        market_day_count=args.market_day_count,
        deterministic_replay_ok=bool(args.deterministic_replay_ok),
        no_live_secrets=bool(args.no_live_secrets),
        source_reports=[_source_report(args.shadow_bridge_report)],
        source_manifest_check=_source_manifest_check_from_args(
            args,
            [source_report_from_path(args.shadow_bridge_report)],
        ),
        coverage_profile=_load_json(args.coverage_profile)
        if args.coverage_profile is not None
        else None,
    )


def _validate_common_real_assertions(
    *,
    source_kind: str,
    source_descriptor: str,
    market_day_count: int,
    deterministic_replay_ok: bool,
    no_live_secrets: bool,
) -> None:
    if source_kind not in ALLOWED_SOURCE_KINDS:
        raise ValueError(f"unsupported source_kind {source_kind!r}")
    if _looks_non_real_source(source_descriptor):
        raise ValueError(f"source_descriptor is not production-grade: {source_descriptor!r}")
    if int(market_day_count) <= 0:
        raise ValueError("market_day_count must be positive")
    if not deterministic_replay_ok:
        raise ValueError("--deterministic-replay-ok is required")
    if not no_live_secrets:
        raise ValueError("--no-live-secrets is required")


def _validate_source_manifest_check(
    check_report: dict[str, Any] | None,
    *,
    source_kind: str,
    source_descriptor: str,
    market_day_count: int,
) -> None:
    if check_report is None:
        return
    if check_report.get("schema") != "zenodex/energy/replay_source_manifest_check/v1":
        raise ValueError("source manifest check must use replay_source_manifest_check/v1")
    if bool(check_report.get("ok")) is not True:
        raise ValueError("source manifest check failed")
    if str(check_report.get("source_kind")) != source_kind:
        raise ValueError("source manifest source_kind does not match builder arguments")
    if str(check_report.get("source_descriptor")) != source_descriptor:
        raise ValueError("source manifest source_descriptor does not match builder arguments")
    if int(check_report.get("market_day_count", 0)) != int(market_day_count):
        raise ValueError("source manifest market_day_count does not match builder arguments")


def _attach_coverage_profile(
    report: dict[str, Any],
    coverage_profile: dict[str, Any] | None,
) -> None:
    if coverage_profile is None:
        return
    check_report = validate_replay_coverage_profile(
        real_report=report,
        profile=coverage_profile,
    )
    if bool(check_report.get("ok")) is not True:
        failed = ", ".join(
            str(item["check_id"])
            for item in check_report.get("checks", [])
            if not bool(item.get("passed"))
        )
        raise ValueError(f"coverage profile check failed: {failed}")
    report["coverage_profile"] = coverage_profile_summary(check_report)


def _source_manifest_check_from_args(
    args: argparse.Namespace,
    source_reports: list[dict[str, Any]],
) -> dict[str, Any] | None:
    if args.source_manifest is None:
        return None
    return validate_replay_source_manifest(
        manifest=_load_json(args.source_manifest),
        source_reports=source_reports,
    )


def _extract_upba_modes_from_benchmark(
    report: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    if report.get("schema") not in {
        "zenodex/energy/upba_v2_benchmark_report/v1",
        "zenodex/energy/upba_v2_topk_sweep/v1",
    }:
        raise ValueError("UPBA benchmark input must use benchmark_report/v1 or topk_sweep/v1")
    modes = report.get("modes", {})
    learned = _require_mode(modes, "hybrid") if "hybrid" in modes else _require_mode(modes, "learned")
    hand = _require_mode(modes, "hand")
    return learned, hand, report


def _extract_upba_modes_from_evaluations(
    learned_report: dict[str, Any],
    hand_report: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    if learned_report.get("schema") != "zenodex/energy/upba_v2_evaluation_report/v1":
        raise ValueError("learned UPBA input must use upba_v2_evaluation_report/v1")
    if hand_report.get("schema") != "zenodex/energy/upba_v2_evaluation_report/v1":
        raise ValueError("hand UPBA input must use upba_v2_evaluation_report/v1")
    if learned_report.get("mode") not in {"learned", "hybrid"}:
        raise ValueError("learned UPBA report mode must be learned or hybrid")
    if hand_report.get("mode") != "hand":
        raise ValueError("hand UPBA report mode must be hand")
    return learned_report, hand_report, {}


def _require_mode(modes: Any, mode: str) -> dict[str, Any]:
    if not isinstance(modes, dict) or mode not in modes or not isinstance(modes[mode], dict):
        raise ValueError(f"missing mode {mode!r}")
    return modes[mode]


def _candidate_total(mode: dict[str, Any], *, batch_count: int) -> int:
    if "candidate_count_total" in mode:
        return int(mode["candidate_count_total"])
    if "candidate_count_mean" in mode:
        return int(round(float(mode["candidate_count_mean"]) * batch_count))
    if "candidate_count" in mode:
        return int(round(float(mode["candidate_count"]) * batch_count))
    return 0


def _topk_metric(mode: dict[str, Any], *, k: int, objective: bool) -> float:
    key = f"top_{k}_{'objective_' if objective else ''}recall"
    if key in mode:
        return float(mode[key])
    nested_key = "objective_top_k_recall" if objective else "top_k_recall"
    top_k = mode.get("top_k", {})
    if isinstance(top_k, dict) and str(k) in top_k:
        return float(top_k[str(k)].get(nested_key, 0.0))
    return 0.0


def _mean_call_metric(mode: dict[str, Any], metric: str) -> float:
    direct = f"mean_{metric}_calls"
    if direct in mode:
        return float(mode[direct])
    position = "mean_winner_position"
    if position in mode:
        return float(mode[position])
    return 0.0


def _source_report(path: Path) -> dict[str, Any]:
    payload = _load_json(path)
    return {
        "path": _display_path(path),
        "schema": payload.get("schema"),
        "sha256": _canonical_sha256(payload),
    }


def _canonical_sha256(payload: dict[str, Any]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return sha256(encoded).hexdigest()


def _looks_non_real_source(value: str) -> bool:
    lowered = value.lower()
    return any(marker in lowered for marker in FORBIDDEN_SOURCE_MARKERS)


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
    report_type = "UPBA real replay" if "batch_count" in report else "AutoTrader real shadow"
    lines = [
        f"# ZenoEnergy {report_type} Report",
        "",
        f"schema: {report['schema']}",
        f"source_kind: {report['source_kind']}",
        f"source_descriptor: {report['source_descriptor']}",
        f"market_day_count: {report['market_day_count']}",
        f"deterministic_replay_ok: {str(report['deterministic_replay_ok']).lower()}",
        f"no_live_secrets: {str(report['no_live_secrets']).lower()}",
        "",
    ]
    if "batch_count" in report:
        lines.extend(
            [
                f"batch_count: {report['batch_count']}",
                f"candidate_count: {report['candidate_count']}",
                f"top_25_recall: {report['top_25_recall']}",
                f"learned_mean_verifier_calls: {report['learned_mean_verifier_calls']}",
                f"hand_mean_verifier_calls: {report['hand_mean_verifier_calls']}",
            ]
        )
    else:
        lines.extend(
            [
                f"context_count: {report['context_count']}",
                f"row_count: {report['row_count']}",
                f"top_25_recall: {report['top_25_recall']}",
                f"learned_mean_guard_calls: {report['learned_mean_guard_calls']}",
                f"hand_mean_guard_calls: {report['hand_mean_guard_calls']}",
            ]
        )
    lines.extend(
        [
            "",
            "This report is an input to the production promotion gate. The builder",
            "checks schemas and source assertions, then the gate applies coverage",
            "and performance thresholds.",
            "",
        ]
    )
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
