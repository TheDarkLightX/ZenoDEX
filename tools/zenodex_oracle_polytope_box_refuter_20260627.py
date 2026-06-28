#!/usr/bin/env python3
"""Refute overbroad Cartesian-box promotion for oracle feasibility intervals."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

from zenodex_oracle_economic_security import sample_envelope, verify_economic_security_envelope  # noqa: E402
from zenodex_oracle_polytope_compiler_20260627 import compile_polytope  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_oracle_polytope_box_refuter_20260627"
REPORT_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_ORACLE_POLYTOPE_BOX_REFUTER_20260627.md"


@dataclass(frozen=True)
class BoxProbe:
    probe_id: str
    assignments: dict[str, int]
    expected_ok: bool
    rationale: str


def _interval_map(interval_report: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(row["field"]): dict(row) for row in interval_report["intervals"]}


def _inside_interval(intervals: Mapping[str, Mapping[str, Any]], field: str, value: int) -> bool:
    row = intervals[field]
    return int(row["lower"]) <= int(value) <= int(row["upper"])


def _probe_catalog(interval_report: Mapping[str, Any]) -> tuple[BoxProbe, ...]:
    intervals = _interval_map(interval_report)
    return (
        BoxProbe(
            probe_id="baseline_sample_accepts",
            assignments={},
            expected_ok=True,
            rationale="The sample envelope remains the positive control.",
        ),
        BoxProbe(
            probe_id="attack_margin_cartesian_counterexample",
            assignments={
                "max_extractable_value_e8": int(intervals["max_extractable_value_e8"]["upper"]),
                "required_attack_margin_bps": int(intervals["required_attack_margin_bps"]["upper"]),
            },
            expected_ok=False,
            rationale="Each field is inside its one-field interval, but together they require more attack cost than the fixed floor.",
        ),
        BoxProbe(
            probe_id="reporter_reward_cartesian_counterexample",
            assignments={
                "reporter_reward_per_report_e8": int(intervals["reporter_reward_per_report_e8"]["upper"]),
                "reporter_count": int(intervals["reporter_count"]["upper"]),
            },
            expected_ok=False,
            rationale="Each field is inside its one-field interval, but together they overspend the fixed reporter reward budget.",
        ),
        BoxProbe(
            probe_id="slash_coverage_cartesian_counterexample",
            assignments={
                "reporter_bond_required_e8": int(intervals["reporter_bond_required_e8"]["lower"]),
                "slash_fraction_bps": int(intervals["slash_fraction_bps"]["lower"]),
            },
            expected_ok=False,
            rationale="Each field is inside its one-field interval, but together the slash amount no longer covers cheat gain plus margin.",
        ),
        BoxProbe(
            probe_id="all_lower_bounds_control",
            assignments={field: int(row["lower"]) for field, row in intervals.items()},
            expected_ok=True,
            rationale="The lower-bound corner is a passing control for the sample's monotone one-field intervals.",
        ),
    )


def run_refuter() -> dict[str, Any]:
    interval_report = compile_polytope()
    intervals = _interval_map(interval_report)
    base = dict(sample_envelope())
    probe_rows: list[dict[str, Any]] = []
    for probe in _probe_catalog(interval_report):
        variant = dict(base)
        variant.update(probe.assignments)
        result = verify_economic_security_envelope(variant)
        actual_ok = result.status == "accepted"
        varied_fields_inside = {
            field: _inside_interval(intervals, field, value)
            for field, value in probe.assignments.items()
        }
        all_varied_fields_inside = all(varied_fields_inside.values())
        cartesian_counterexample = all_varied_fields_inside and not actual_ok and not probe.expected_ok
        probe_rows.append(
            {
                "probe_id": probe.probe_id,
                "assignments": dict(probe.assignments),
                "varied_fields_inside_one_field_intervals": varied_fields_inside,
                "all_varied_fields_inside_one_field_intervals": all_varied_fields_inside,
                "expected_ok": probe.expected_ok,
                "actual_ok": actual_ok,
                "probe_matches_expectation": actual_ok is probe.expected_ok,
                "cartesian_counterexample": cartesian_counterexample,
                "errors": list(result.errors),
                "rationale": probe.rationale,
            }
        )
    counterexamples = [row for row in probe_rows if row["cartesian_counterexample"]]
    return {
        "schema": "zenodex.oracle.polytope_box_refuter_report.v1",
        "ok": bool(counterexamples) and all(row["probe_matches_expectation"] for row in probe_rows),
        "cartesian_promotion_refuted": bool(counterexamples),
        "counterexample_count": len(counterexamples),
        "probe_count": len(probe_rows),
        "interval_source_ok": bool(interval_report["ok"]),
        "probes": probe_rows,
        "negative_knowledge": (
            "The one-field intervals are not a Cartesian product feasibility polytope. "
            "A coupled interval certificate must include cross-field inequalities or "
            "an exact verifier for the intended multi-field region."
        ),
        "non_claims": [
            "This refuter does not invalidate the one-field interval compiler.",
            "This refuter does not construct the maximal coupled feasible region.",
            "This refuter does not estimate MEV, challenge probability, or oracle truth.",
        ],
        "replay_command": "python3 tools/zenodex_oracle_polytope_box_refuter_20260627.py",
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# Zeno Oracle Polytope Box Refuter - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "This artifact refutes the broad claim that the one-field oracle intervals can be promoted directly to a Cartesian product box."
    )
    lines.append(
        f"Counterexamples found: `{report['counterexample_count']}` from `{report['probe_count']}` deterministic probes."
    )
    lines.append("")
    lines.append(report["negative_knowledge"])
    lines.append("")
    lines.append("Authority boundary: the pointwise verifier remains authoritative; this tool records negative knowledge for the research frontier.")
    lines.append("")
    lines.append("## Probes")
    lines.append("")
    lines.append("| probe | inside one-field intervals | verifier accepted | errors |")
    lines.append("| --- | --- | --- | --- |")
    for row in report["probes"]:
        errors = ", ".join(f"`{err}`" for err in row["errors"]) or "none"
        lines.append(
            f"| `{row['probe_id']}` | `{row['all_varied_fields_inside_one_field_intervals']}` | `{row['actual_ok']}` | {errors} |"
        )
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(str(report["replay_command"]))
    lines.append("```")
    lines.append("")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path, output_md: Path) -> dict[str, Any]:
    report = run_refuter()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(OUT_DIR / "report.json"))
    parser.add_argument("--output-md", default=str(REPORT_PATH))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "cartesian_promotion_refuted": report["cartesian_promotion_refuted"],
                "counterexample_count": report["counterexample_count"],
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
