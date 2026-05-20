#!/usr/bin/env python3
"""Fail-closed gate for allowing signed ZenoGraph material to influence ranking only."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.autotrader_risk_disclosure import (  # noqa: E402
    build_autotrader_risk_disclosure,
)
from src.kernels.python.zenograph_ranking_promotion_gate_v1_adapter import (  # noqa: E402
    check_zenograph_ranking_promotion_gate,
)

REQUIRED_BASELINE_CASE_COUNT = 20
REQUIRED_BASELINE_FAMILIES = (
    "aligned_neutral",
    "aligned_irrelevant",
    "governance_block",
    "oracle_stale_block",
    "slippage_limit_block",
)


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _require_mapping(payload: object, *, name: str) -> Mapping[str, object]:
    if not isinstance(payload, Mapping):
        raise ValueError(f"{name} must be a JSON object")
    return payload


def _infer_signed_input_only(report: Mapping[str, object]) -> bool:
    return report.get("input_kind") == "accepted_store_exports"


def _load_rate(report: Mapping[str, object], key: str) -> float:
    value = report.get(key, 0.0)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{key} must be numeric when present")
    return float(value)


def _minimum_case_count_met(report: Mapping[str, object]) -> bool:
    value = report.get("case_count", 0)
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError("case_count must be an integer when present")
    return int(value) >= REQUIRED_BASELINE_CASE_COUNT


def _required_family_coverage_met(report: Mapping[str, object]) -> bool:
    family_summary = report.get("family_summary")
    if not isinstance(family_summary, Mapping):
        return False
    return all(str(family) in family_summary for family in REQUIRED_BASELINE_FAMILIES)


def build_ranking_promotion_gate_report(
    *,
    source_report_path: Path,
    source_report: Mapping[str, object],
    signed_input_only: bool,
    operator_release_enabled: bool,
    ranking_only_mode: bool = True,
) -> dict[str, object]:
    submit_vs_block_rate = _load_rate(
        source_report, "controller_submit_vs_zenograph_block_rate"
    )
    block_vs_allow_rate = _load_rate(
        source_report, "controller_block_vs_zenograph_allow_rate"
    )
    selected_template_mismatch_rate = _load_rate(
        source_report, "selected_template_mismatch_rate"
    )
    disagreement_rate = _load_rate(source_report, "disagreement_rate")
    minimum_case_count_met = _minimum_case_count_met(source_report)
    required_family_coverage_met = _required_family_coverage_met(source_report)

    gate = check_zenograph_ranking_promotion_gate(
        signed_input_only=bool(signed_input_only),
        ranking_only_mode=bool(ranking_only_mode),
        minimum_case_count_met=minimum_case_count_met,
        required_family_coverage_met=required_family_coverage_met,
        submit_vs_block_zero=(submit_vs_block_rate == 0.0),
        block_vs_allow_zero=(block_vs_allow_rate == 0.0),
        operator_release_enabled=bool(operator_release_enabled),
    )

    return {
        "schema": "zenodex/zenograph-autotrader-ranking-promotion-gate-report/v1",
        "source_report_path": str(source_report_path),
        "source_report_schema": source_report.get("schema"),
        "risk_disclosure": build_autotrader_risk_disclosure(
            mode="shadow",
            requires_explicit_acknowledgement=False,
            user_acknowledged=False,
        ),
        "source_metrics": {
            "signed_input_only": bool(signed_input_only),
            "ranking_only_mode": bool(ranking_only_mode),
            "operator_release_enabled": bool(operator_release_enabled),
            "case_count": int(source_report.get("case_count", 0) or 0),
            "minimum_case_count_met": bool(minimum_case_count_met),
            "required_family_coverage_met": bool(required_family_coverage_met),
            "disagreement_rate": disagreement_rate,
            "controller_submit_vs_zenograph_block_rate": submit_vs_block_rate,
            "controller_block_vs_zenograph_allow_rate": block_vs_allow_rate,
            "selected_template_mismatch_rate": selected_template_mismatch_rate,
        },
        "promotion_contract": {
            "required_case_count": REQUIRED_BASELINE_CASE_COUNT,
            "required_families": list(REQUIRED_BASELINE_FAMILIES),
            "requires_zero_submit_vs_block_rate": True,
            "requires_zero_block_vs_allow_rate": True,
            "requires_signed_input_only": True,
            "requires_ranking_only_mode": True,
            "requires_operator_release_enabled": True,
        },
        "gate": gate.to_dict(),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=(
            "Advanced experimental automation governance tool. "
            "This only governs ranking influence, never execution."
        ),
    )
    parser.add_argument("--report-file", required=True, type=Path)
    parser.add_argument(
        "--signed-input-only",
        action="store_true",
        help="Override the signed-input inference and force signed_input_only=true.",
    )
    parser.add_argument(
        "--operator-release-enable",
        action="store_true",
        help="Explicit operator enable bit for ranking-only promotion.",
    )
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report_payload = _require_mapping(_load_json(args.report_file), name="report_file")
    signed_input_only = bool(args.signed_input_only) or _infer_signed_input_only(report_payload)
    gate_report = build_ranking_promotion_gate_report(
        source_report_path=args.report_file,
        source_report=report_payload,
        signed_input_only=signed_input_only,
        operator_release_enabled=bool(args.operator_release_enable),
    )
    text = json.dumps(
        gate_report,
        indent=2 if args.pretty else None,
        sort_keys=True,
    ) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
