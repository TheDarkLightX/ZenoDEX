#!/usr/bin/env python3
"""Replay a positive route-dominance certificate over a bounded exact-out domain."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
TOOLS_DIR = REPO_ROOT / "tools"
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(TOOLS_DIR))

from zenodex_route_dominance_frontier_refuter_20260627 import (  # noqa: E402
    ASSET_A,
    ASSET_B,
    HostPacket,
    _all_true_flags,
    _route_pools,
    _run_tau_steps,
    _tau_step_from_flags,
    enumerate_route_labels,
    run_refuter,
    verify_host_packet,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_route_dominance_positive_certificate_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_ROUTE_DOMINANCE_POSITIVE_CERTIFICATE_20260628.md"
TAU_SPEC_REL = "src/tau_specs/recommended/route_dominance_frontier_envelope_v1.tau"


def _positive_packet(amount_out: int) -> HostPacket:
    pools = _route_pools()
    labels = enumerate_route_labels(pools, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=amount_out)
    if not labels:
        raise ValueError(f"bounded route domain is empty for amount_out={amount_out}")
    best = labels[0]
    return HostPacket(
        case_id=f"positive_best_only_amount_out_{amount_out}",
        pools=pools,
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_out=int(amount_out),
        kept_route_ids=(best.route_id,),
        pruned_route_ids=tuple(label.route_id for label in labels[1:]),
        selected_route_id=best.route_id,
        declared_flags=_all_true_flags(),
        note="The full-domain best label is the only kept frontier label; all other labels are pruned with that kept dominator.",
    )


def _positive_cases() -> tuple[dict[str, Any], ...]:
    packets = tuple(_positive_packet(amount_out) for amount_out in (8, 16, 24, 42, 64))
    host_rows = [verify_host_packet(packet) for packet in packets]
    tau = _run_tau_steps([_tau_step_from_flags(row["computed_flags"]) for row in host_rows])
    cases: list[dict[str, Any]] = []
    for idx, packet in enumerate(packets):
        labels = host_rows[idx]["labels"]
        output = tau.get("case_outputs", [{}])[idx] if tau.get("case_outputs") else {}
        cases.append(
            {
                "case_id": packet.case_id,
                "amount_out": int(packet.amount_out),
                "host_ok": bool(host_rows[idx]["host_ok"]),
                "tau_accepts": output.get("o4") == 1,
                "route_label_count": int(host_rows[idx]["route_label_count"]),
                "kept_count": len(host_rows[idx]["kept_route_ids"]),
                "pruned_count": len(host_rows[idx]["pruned_route_ids"]),
                "selected_route_id": host_rows[idx]["selected_route_id"],
                "selected_amount_in": host_rows[idx]["selected_amount_in"],
                "best_full_route_id": host_rows[idx]["best_full_route_id"],
                "best_full_amount_in": host_rows[idx]["best_full_amount_in"],
                "computed_flags": host_rows[idx]["computed_flags"],
                "tau_output": output,
                "first_three_labels": labels[:3],
            }
        )
    return tuple(cases)


def _mutation_cases(base_flags: Mapping[str, int]) -> dict[str, Any]:
    cases = {
        "drop_dominator_reject": {**base_flags, "i4": 0},
        "drop_projection_cover_reject": {**base_flags, "i6": 0},
        "drop_quote_replay_reject": {**base_flags, "i7": 0},
        "drop_rounding_bound_reject": {**base_flags, "i8": 0},
        "drop_no_authority_reject": {**base_flags, "i11": 0},
        "inactive_safe": {**base_flags, "i1": 0},
    }
    expected_primary = {
        "drop_dominator_reject": 0,
        "drop_projection_cover_reject": 0,
        "drop_quote_replay_reject": 0,
        "drop_rounding_bound_reject": 0,
        "drop_no_authority_reject": 0,
        "inactive_safe": 0,
    }
    tau = _run_tau_steps([_tau_step_from_flags(flags) for flags in cases.values()])
    rows: list[dict[str, Any]] = []
    invalid_accepts = 0
    for idx, (case_id, flags) in enumerate(cases.items()):
        output = tau.get("case_outputs", [{}])[idx] if tau.get("case_outputs") else {}
        primary = int(output.get("o4", 0))
        expected = expected_primary[case_id]
        invalid_accepts += int(primary == 1 and expected == 0)
        rows.append(
            {
                "case_id": case_id,
                "ok": primary == expected and (case_id != "inactive_safe" or int(output.get("o5", 0)) == 1),
                "expected_o4": expected,
                "got_o4": primary,
                "got_o5": int(output.get("o5", 0)),
                "flags": dict(flags),
                "tau_output": output,
            }
        )
    return {
        "ok": tau.get("ok") is True and invalid_accepts == 0 and all(row["ok"] for row in rows),
        "invalid_accepts": invalid_accepts,
        "cases": rows,
        "tau": {key: value for key, value in tau.items() if key != "case_outputs"},
    }


def build_report() -> dict[str, Any]:
    positives = _positive_cases()
    base_flags = positives[0]["computed_flags"]
    mutations = _mutation_cases(base_flags)
    refuter = run_refuter()
    label_counts = [int(row["route_label_count"]) for row in positives]
    kept_counts = [int(row["kept_count"]) for row in positives]
    pruned_counts = [int(row["pruned_count"]) for row in positives]
    ok = bool(
        positives
        and all(row["host_ok"] and row["tau_accepts"] for row in positives)
        and mutations["ok"]
        and refuter["ok"]
        and refuter["false_declared_admit_count"] == 2
        and refuter["computed_false_admit_count"] == 0
        and all(kept == 1 for kept in kept_counts)
    )
    return {
        "schema": "zenodex.route_dominance_positive_certificate_report.v1",
        "date": "2026-06-28",
        "ok": ok,
        "breakthrough": {
            "name": "Route dominance positive certificate",
            "summary": "A bounded exact-out route-label domain admits a best-only dominance frontier when a host verifier proves every pruned route is dominated under the integer route key and Tau certifies the resulting proof-surface flags.",
            "authority_boundary": "Research certificate only. Tau has no settlement, quote, routing, oracle, liquidation, or state-root authority.",
        },
        "tau_spec": TAU_SPEC_REL,
        "positive_cases": positives,
        "mutation_cases": mutations,
        "prior_refuter": {
            "ok": refuter["ok"],
            "false_declared_admit_count": refuter["false_declared_admit_count"],
            "computed_false_admit_count": refuter["computed_false_admit_count"],
            "case_count": refuter["case_count"],
        },
        "metrics": {
            "case_count": len(positives),
            "min_route_label_count": min(label_counts),
            "max_route_label_count": max(label_counts),
            "total_route_label_count": sum(label_counts),
            "total_kept_count": sum(kept_counts),
            "total_pruned_count": sum(pruned_counts),
            "frontier_compression": f"{sum(label_counts)}:{sum(kept_counts)}",
        },
        "non_claims": [
            "This is a bounded direct, two-hop, and two-way split exact-out route-label certificate, not an all-route theorem.",
            "The positive certificate still depends on host-computed flags; untrusted declared Tau flags are unsafe, as shown by the prior refuter.",
            "The artifact compresses the positive certificate frontier; it does not claim to reduce route-label generation cost.",
            "Tau does not compute route quotes, dominance, projection cover, settlement, or runtime route selection.",
        ],
        "replay_command": "python3 tools/zenodex_route_dominance_positive_certificate_20260628.py",
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Route Dominance Positive Certificate - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(str(report["breakthrough"]["summary"]))
    lines.append("")
    lines.append(str(report["breakthrough"]["authority_boundary"]))
    lines.append("")
    lines.append(f"- Tau spec: `{report['tau_spec']}`")
    lines.append(f"- Positive cases: `{report['metrics']['case_count']}`")
    lines.append(f"- Route labels covered: `{report['metrics']['total_route_label_count']}`")
    lines.append(f"- Kept frontier labels: `{report['metrics']['total_kept_count']}`")
    lines.append(f"- Pruned labels with dominators: `{report['metrics']['total_pruned_count']}`")
    lines.append(f"- Frontier compression: `{report['metrics']['frontier_compression']}`")
    lines.append(f"- Mutation invalid accepts: `{report['mutation_cases']['invalid_accepts']}`")
    lines.append(f"- Prior forged-flag admits retained as negative knowledge: `{report['prior_refuter']['false_declared_admit_count']}`")
    lines.append("")
    lines.append("## Positive Certificates")
    lines.append("")
    lines.append("| case | labels | kept | pruned | selected route | amount in | Tau accepts |")
    lines.append("| --- | ---: | ---: | ---: | --- | ---: | --- |")
    for row in report["positive_cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['route_label_count']}` | `{row['kept_count']}` | `{row['pruned_count']}` | `{row['selected_route_id']}` | `{row['selected_amount_in']}` | `{row['tau_accepts']}` |"
        )
    lines.append("")
    lines.append("## Negative Controls")
    lines.append("")
    lines.append("| case | ok | o4 | o5 |")
    lines.append("| --- | --- | ---: | ---: |")
    for row in report["mutation_cases"]["cases"]:
        lines.append(f"| `{row['case_id']}` | `{row['ok']}` | `{row['got_o4']}` | `{row['got_o5']}` |")
    lines.append("")
    lines.append("The prior refuter remains attached: forged all-true Tau flags admit two bad route packets, while host-computed flags have zero false admits.")
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
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    parser.add_argument("--output-md", default=str(REPORT_MD))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
                "frontier_compression": report["metrics"]["frontier_compression"],
                "mutation_invalid_accepts": report["mutation_cases"]["invalid_accepts"],
                "prior_false_declared_admits": report["prior_refuter"]["false_declared_admit_count"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
