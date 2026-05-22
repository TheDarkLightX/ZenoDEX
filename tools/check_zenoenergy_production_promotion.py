#!/usr/bin/env python3
"""Fail-closed production promotion gate for ZenoEnergy advisory ranking."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.operator_report_output import print_operator_json  # noqa: E402


MIN_UPBA_REAL_BATCHES = 1_000
MIN_UPBA_REAL_CANDIDATES = 20_000
MIN_AUTOTRADER_REAL_CONTEXTS = 500
MIN_AUTOTRADER_REAL_ROWS = 5_000
MIN_REAL_MARKET_DAYS = 7
MIN_TOP25_RECALL = 0.99
MIN_UPBA_POOL_COUNT = 3
MIN_UPBA_INTENT_SIZE_BUCKET_COUNT = 3
MIN_UPBA_CANDIDATE_FAMILY_COUNT = 4
MIN_UPBA_HARD_NEGATIVE_FAMILY_COUNT = 4
MIN_AUTOTRADER_STRATEGY_FAMILY_COUNT = 3
MIN_AUTOTRADER_GUARD_FAMILY_COUNT = 4
MIN_AUTOTRADER_DECISION_FAMILY_COUNT = 3


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--research-replay",
        type=Path,
        default=ROOT / "data/upba_energy/zenoenergy_research_evidence_replay_receipt.json",
    )
    parser.add_argument("--upba-real-replay", type=Path)
    parser.add_argument("--autotrader-real-shadow", type=Path)
    parser.add_argument("--operator-release-enable", action="store_true")
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args(argv)

    report = build_production_gate_report(
        research_replay=_load_json(args.research_replay),
        upba_real_replay=_load_json(args.upba_real_replay)
        if args.upba_real_replay is not None
        else None,
        autotrader_real_shadow=_load_json(args.autotrader_real_shadow)
        if args.autotrader_real_shadow is not None
        else None,
        operator_release_enabled=bool(args.operator_release_enable),
        source_paths={
            "research_replay": _display_path(args.research_replay),
            "upba_real_replay": None
            if args.upba_real_replay is None
            else _display_path(args.upba_real_replay),
            "autotrader_real_shadow": None
            if args.autotrader_real_shadow is None
            else _display_path(args.autotrader_real_shadow),
        },
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print_operator_json(report)
    return 0 if report["decision"] != "invalid_evidence" else 1


def build_production_gate_report(
    *,
    research_replay: dict[str, Any],
    upba_real_replay: dict[str, Any] | None,
    autotrader_real_shadow: dict[str, Any] | None,
    operator_release_enabled: bool,
    source_paths: dict[str, str | None] | None = None,
) -> dict[str, Any]:
    obligations = [
        _research_replay_obligation(research_replay),
        _ranking_only_obligation(operator_release_enabled),
        _upba_real_replay_obligation(upba_real_replay),
        _autotrader_real_shadow_obligation(autotrader_real_shadow),
    ]
    all_passed = all(bool(item["passed"]) for item in obligations)
    decision = "allow_ranking_only" if all_passed else "blocked"
    return {
        "schema": "zenodex/energy/production_promotion_gate/v1",
        "decision": decision,
        "promotion_allowed": all_passed,
        "scope": "advisory_ranking_only",
        "operator_release_enabled": bool(operator_release_enabled),
        "source_paths": source_paths or {},
        "thresholds": {
            "min_upba_real_batches": MIN_UPBA_REAL_BATCHES,
            "min_upba_real_candidates": MIN_UPBA_REAL_CANDIDATES,
            "min_autotrader_real_contexts": MIN_AUTOTRADER_REAL_CONTEXTS,
            "min_autotrader_real_rows": MIN_AUTOTRADER_REAL_ROWS,
            "min_real_market_days": MIN_REAL_MARKET_DAYS,
            "min_top25_recall": MIN_TOP25_RECALL,
            "min_upba_pool_count": MIN_UPBA_POOL_COUNT,
            "min_upba_intent_size_bucket_count": MIN_UPBA_INTENT_SIZE_BUCKET_COUNT,
            "min_upba_candidate_family_count": MIN_UPBA_CANDIDATE_FAMILY_COUNT,
            "min_upba_hard_negative_family_count": MIN_UPBA_HARD_NEGATIVE_FAMILY_COUNT,
            "min_autotrader_strategy_family_count": MIN_AUTOTRADER_STRATEGY_FAMILY_COUNT,
            "min_autotrader_guard_family_count": MIN_AUTOTRADER_GUARD_FAMILY_COUNT,
            "min_autotrader_decision_family_count": MIN_AUTOTRADER_DECISION_FAMILY_COUNT,
        },
        "obligations": obligations,
        "blocked_reasons": [
            str(item["reason"]) for item in obligations if not bool(item["passed"])
        ],
        "safety_contract": {
            "verifier_authoritative": True,
            "policy_guards_authoritative": True,
            "scorer_authorizes_settlement_or_trade": False,
            "model_output_in_state_root": False,
            "deterministic_fallback_required": True,
        },
        "negative_knowledge": (
            "Current ZenoEnergy evidence remains research-grade until real UPBA "
            "replay and real AutoTrader shadow reports satisfy this gate."
        ),
    }


def _research_replay_obligation(report: dict[str, Any]) -> dict[str, Any]:
    summary = report.get("summary", {})
    fallback = summary.get("fallback_permutation_audit", {})
    autotrader = summary.get("autotrader_energy_hard_cross_seed", {})
    shadow = summary.get("autotrader_energy_shadow_bridge", {})
    passed = (
        report.get("schema") == "zenodex/energy/research_evidence_replay_receipt/v1"
        and bool(report.get("ok")) is True
        and int(report.get("failed_count", -1)) == 0
        and int(fallback.get("invalid_accept_count", -1)) == 0
        and int(autotrader.get("invalid_accept_count_total", -1)) == 0
        and int(shadow.get("invalid_accept_count_total", -1)) == 0
        and float(fallback.get("learned_top_10_recall", 0.0)) >= 1.0
        and int(fallback.get("learned_permutation_violation_count", -1)) == 0
    )
    return {
        "id": "research_replay_clean",
        "passed": passed,
        "reason": "research replay, fallback, and invalid-accept receipts must be clean",
        "observed": {
            "ok": bool(report.get("ok")),
            "failed_count": int(report.get("failed_count", -1)),
            "fallback_invalid_accept_count": fallback.get("invalid_accept_count"),
            "autotrader_invalid_accept_count_total": autotrader.get(
                "invalid_accept_count_total"
            ),
            "shadow_invalid_accept_count_total": shadow.get("invalid_accept_count_total"),
            "learned_top_10_recall": fallback.get("learned_top_10_recall"),
            "learned_permutation_violation_count": fallback.get(
                "learned_permutation_violation_count"
            ),
        },
    }


def _ranking_only_obligation(operator_release_enabled: bool) -> dict[str, Any]:
    return {
        "id": "operator_ranking_only_enable",
        "passed": bool(operator_release_enabled),
        "reason": "operator must explicitly enable advisory ranking-only promotion",
        "observed": {
            "operator_release_enabled": bool(operator_release_enabled),
            "scope": "advisory_ranking_only",
        },
    }


def _upba_real_replay_obligation(report: dict[str, Any] | None) -> dict[str, Any]:
    if report is None:
        return {
            "id": "upba_real_replay_coverage",
            "passed": False,
            "reason": "missing real UPBA replay report",
            "observed": {"present": False},
        }
    passed = (
        report.get("schema") == "zenodex/energy/upba_real_replay_report/v1"
        and str(report.get("source_kind")) in {"production-shadow", "historical-replay"}
        and bool(report.get("deterministic_replay_ok")) is True
        and bool(report.get("no_live_secrets")) is True
        and _source_manifest_check_ok(report)
        and _coverage_profile_check_ok(report, expected_type="upba")
        and int(report.get("batch_count", 0)) >= MIN_UPBA_REAL_BATCHES
        and int(report.get("candidate_count", 0)) >= MIN_UPBA_REAL_CANDIDATES
        and int(report.get("market_day_count", 0)) >= MIN_REAL_MARKET_DAYS
        and int(report.get("invalid_accept_count", -1)) == 0
        and int(report.get("permutation_violation_count", -1)) == 0
        and float(report.get("top_25_recall", 0.0)) >= MIN_TOP25_RECALL
        and float(report.get("learned_mean_verifier_calls", 10**9))
        < float(report.get("hand_mean_verifier_calls", -1.0))
    )
    return {
        "id": "upba_real_replay_coverage",
        "passed": passed,
        "reason": "real UPBA replay must be broad, deterministic, source-manifested, secret-free, safe, and beat hand energy",
        "observed": {
            "present": True,
            "schema": report.get("schema"),
            "source_kind": report.get("source_kind"),
            "batch_count": report.get("batch_count"),
            "candidate_count": report.get("candidate_count"),
            "market_day_count": report.get("market_day_count"),
            "invalid_accept_count": report.get("invalid_accept_count"),
            "permutation_violation_count": report.get("permutation_violation_count"),
            "top_25_recall": report.get("top_25_recall"),
            "learned_mean_verifier_calls": report.get("learned_mean_verifier_calls"),
            "hand_mean_verifier_calls": report.get("hand_mean_verifier_calls"),
            "deterministic_replay_ok": report.get("deterministic_replay_ok"),
            "no_live_secrets": report.get("no_live_secrets"),
            "source_manifest_ok": _source_manifest_check_ok(report),
            "coverage_profile_ok": _coverage_profile_check_ok(
                report,
                expected_type="upba",
            ),
        },
    }


def _autotrader_real_shadow_obligation(report: dict[str, Any] | None) -> dict[str, Any]:
    if report is None:
        return {
            "id": "autotrader_real_shadow_coverage",
            "passed": False,
            "reason": "missing real AutoTrader shadow report",
            "observed": {"present": False},
        }
    passed = (
        report.get("schema") == "zenodex/energy/autotrader_real_shadow_report/v1"
        and str(report.get("source_kind")) in {"production-shadow", "historical-replay"}
        and bool(report.get("deterministic_replay_ok")) is True
        and bool(report.get("no_live_secrets")) is True
        and _source_manifest_check_ok(report)
        and _coverage_profile_check_ok(report, expected_type="autotrader")
        and bool(report.get("policy_guards_authoritative")) is True
        and bool(report.get("scorer_authorizes_trade")) is False
        and bool(report.get("model_output_in_state_root")) is False
        and int(report.get("context_count", 0)) >= MIN_AUTOTRADER_REAL_CONTEXTS
        and int(report.get("row_count", 0)) >= MIN_AUTOTRADER_REAL_ROWS
        and int(report.get("market_day_count", 0)) >= MIN_REAL_MARKET_DAYS
        and int(report.get("invalid_accept_count_total", -1)) == 0
        and float(report.get("top_25_recall", 0.0)) >= MIN_TOP25_RECALL
        and float(report.get("learned_mean_guard_calls", 10**9))
        < float(report.get("hand_mean_guard_calls", -1.0))
    )
    return {
        "id": "autotrader_real_shadow_coverage",
        "passed": passed,
        "reason": "real AutoTrader shadow replay must be broad, deterministic, source-manifested, secret-free, safe, and beat hand energy",
        "observed": {
            "present": True,
            "schema": report.get("schema"),
            "source_kind": report.get("source_kind"),
            "context_count": report.get("context_count"),
            "row_count": report.get("row_count"),
            "market_day_count": report.get("market_day_count"),
            "invalid_accept_count_total": report.get("invalid_accept_count_total"),
            "top_25_recall": report.get("top_25_recall"),
            "learned_mean_guard_calls": report.get("learned_mean_guard_calls"),
            "hand_mean_guard_calls": report.get("hand_mean_guard_calls"),
            "deterministic_replay_ok": report.get("deterministic_replay_ok"),
            "no_live_secrets": report.get("no_live_secrets"),
            "source_manifest_ok": _source_manifest_check_ok(report),
            "coverage_profile_ok": _coverage_profile_check_ok(
                report,
                expected_type="autotrader",
            ),
            "policy_guards_authoritative": report.get("policy_guards_authoritative"),
            "scorer_authorizes_trade": report.get("scorer_authorizes_trade"),
            "model_output_in_state_root": report.get("model_output_in_state_root"),
        },
    }


def _source_manifest_check_ok(report: dict[str, Any]) -> bool:
    manifest = report.get("source_manifest", {})
    return (
        isinstance(manifest, dict)
        and manifest.get("schema")
        == "zenodex/energy/replay_source_manifest_check/v1"
        and bool(manifest.get("ok")) is True
        and int(manifest.get("failed_count", -1)) == 0
        and int(manifest.get("source_report_count", 0)) > 0
        and int(manifest.get("source_report_match_count", 0))
        == int(manifest.get("source_report_count", -1))
    )


def _coverage_profile_check_ok(
    report: dict[str, Any],
    *,
    expected_type: str,
) -> bool:
    profile = report.get("coverage_profile", {})
    return (
        isinstance(profile, dict)
        and profile.get("schema")
        == "zenodex/energy/replay_coverage_profile_check/v1"
        and bool(profile.get("ok")) is True
        and str(profile.get("profile_type")) == expected_type
        and str(profile.get("source_kind", "")) == str(report.get("source_kind", ""))
        and str(profile.get("source_descriptor", ""))
        == str(report.get("source_descriptor", ""))
        and int(profile.get("failed_count", -1)) == 0
        and int(profile.get("source_report_count", 0)) > 0
        and int(profile.get("market_day_count", 0))
        == int(report.get("market_day_count", -1))
    )


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Production Promotion Gate",
        "",
        f"decision: {report['decision']}",
        f"promotion_allowed: {str(report['promotion_allowed']).lower()}",
        f"scope: {report['scope']}",
        f"operator_release_enabled: {str(report['operator_release_enabled']).lower()}",
        "",
        "```text",
        "ProductionEligible :=",
        "  ResearchReplayClean",
        "  and RealUPBAReplayOK",
        "  and RealAutoTraderShadowOK",
        "  and OperatorRankingOnlyEnable",
        "```",
        "",
        "Promotion is restricted to advisory ranking. Deterministic verification",
        "and policy guards remain authoritative for acceptance.",
        "",
        "| obligation | result | reason |",
        "| --- | --- | --- |",
    ]
    for obligation in report["obligations"]:
        lines.append(
            f"| {obligation['id']} | "
            f"{'pass' if obligation['passed'] else 'block'} | "
            f"{obligation['reason']} |"
        )
    lines.extend(
        [
            "",
            "## Blocked Reasons",
            "",
        ]
    )
    for reason in report["blocked_reasons"]:
        lines.append(f"- {reason}")
    lines.extend(
        [
            "",
            "## Thresholds",
            "",
            "| threshold | value |",
            "| --- | ---: |",
        ]
    )
    for name, value in report["thresholds"].items():
        lines.append(f"| {name} | {value} |")
    lines.extend(
        [
            "",
            "## Required Real Reports",
            "",
            "`upba_real_replay` must use schema",
            "`zenodex/energy/upba_real_replay_report/v1` and include broad",
            "historical-replay or production-shadow coverage, zero invalid accepts,",
            "zero permutation violations, a passing replay source manifest, top-25",
            "recall above threshold, and lower mean verifier calls than hand energy.",
            "It must also carry a passing replay coverage profile check so a",
            "single narrow source cannot satisfy production breadth on aggregate",
            "counts alone.",
            "",
            "`autotrader_real_shadow` must use schema",
            "`zenodex/energy/autotrader_real_shadow_report/v1` and include broad",
            "historical-replay or production-shadow coverage, zero invalid accepts,",
            "a passing replay source manifest, authoritative policy guards, no",
            "state-root model output, top-25 recall above threshold, and lower mean",
            "guard calls than hand energy.",
            "It must carry a passing replay coverage profile check covering multiple",
            "strategy, guard, and decision families.",
            "",
            "## Report Builder",
            "",
            "Use `tools/build_zenoenergy_real_replay_report.py` to construct these",
            "report schemas from replay outputs. The builder validates source",
            "schemas, records canonical source report hashes, rejects obvious",
            "fixture or synthetic source descriptors, and requires deterministic",
            "replay plus no-live-secrets attestations.",
            "",
            "The builder is an evidence normalizer. It does not replace replay",
            "provenance, data-custody checks, secret-scrubbing proof, or the",
            "production promotion gate.",
            "",
        ]
    )
    return "\n".join(lines)


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


if __name__ == "__main__":
    raise SystemExit(main())
