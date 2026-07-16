#!/usr/bin/env python3
"""Build the exact-rational critical-region dispatcher comparison report."""

from __future__ import annotations

import csv
import json
import subprocess
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"
RAW = GENERATED / "critical_region_dispatch.tsv"
PARITY = GENERATED / "critical_region_dispatch_parity.txt"
REPORT = GENERATED / "critical_region_dispatch_report.json"
METHODS = ("equal", "midpoint", "critical")
BUDGETS = (1, 2, 4, 6, 8, 16, 32)


def parse_bool(value: str) -> bool:
    if value == "true":
        return True
    if value == "false":
        return False
    raise ValueError(f"unexpected boolean: {value!r}")


def load_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with RAW.open(newline="", encoding="utf-8") as source:
        for raw in csv.DictReader(source, delimiter="\t"):
            row: dict[str, Any] = {
                "case_id": raw["case_id"],
                "family": raw["family"],
                "parameters": raw["parameters"],
                "n": int(raw["n"]),
                "degree": int(raw["degree"]),
                "expected": raw["expected"],
            }
            for method in METHODS:
                row[method] = {
                    "accepted": parse_bool(raw[f"{method}_accepted"]),
                    "pieces": int(raw[f"{method}_pieces"]),
                    "search_interval_checks": int(
                        raw[f"{method}_search_interval_checks"]
                    ),
                    "compiler_scalar_updates": int(
                        raw[f"{method}_compiler_scalar_updates"]
                    ),
                    "checker_scalar_reads": int(
                        raw[f"{method}_checker_scalar_reads"]
                    ),
                    "certificate_bytes": int(raw[f"{method}_certificate_bytes"]),
                    "critical_splits": int(raw[f"{method}_critical_splits"]),
                    "midpoint_splits": int(raw[f"{method}_midpoint_splits"]),
                    "min_coeff": raw[f"{method}_min_coeff"],
                }
            rows.append(row)
    return rows


def budget_curve(positive_rows: list[dict[str, Any]], method: str) -> dict[str, Any]:
    curve: dict[str, Any] = {}
    total = len(positive_rows)
    for budget in BUDGETS:
        accepted = sum(
            row[method]["accepted"] and row[method]["pieces"] <= budget
            for row in positive_rows
        )
        curve[str(budget)] = {"accepted": accepted, "unknown": total - accepted}
    return curve


def method_metrics(rows: list[dict[str, Any]], method: str) -> dict[str, Any]:
    positives = [row for row in rows if row["expected"] == "positive"]
    negatives = [row for row in rows if row["expected"] == "negative"]
    accepted = [row for row in positives if row[method]["accepted"]]
    histogram = Counter(row[method]["pieces"] for row in accepted)
    return {
        "positive_obligations": len(positives),
        "accepted_positive": len(accepted),
        "unknown_positive": len(positives) - len(accepted),
        "negative_controls": len(negatives),
        "false_accepts": sum(row[method]["accepted"] for row in negatives),
        "total_certificate_pieces": sum(row[method]["pieces"] for row in accepted),
        "max_certificate_pieces": max(row[method]["pieces"] for row in accepted),
        "piece_histogram": dict(sorted(histogram.items())),
        "total_certificate_bytes": sum(
            row[method]["certificate_bytes"] for row in accepted
        ),
        "total_checker_scalar_reads": sum(
            row[method]["checker_scalar_reads"] for row in accepted
        ),
        "total_search_interval_checks": sum(
            row[method]["search_interval_checks"] for row in rows
        ),
        "total_compiler_scalar_updates": sum(
            row[method]["compiler_scalar_updates"] for row in rows
        ),
        "budget_curve": budget_curve(positives, method),
    }


def relation(left: int, right: int) -> str:
    if left < right:
        return "lower"
    if left > right:
        return "higher"
    return "equal"


def compare_methods(
    positives: list[dict[str, Any]], candidate: str, baseline: str
) -> dict[str, Any]:
    paired = [
        row
        for row in positives
        if row[candidate]["accepted"] and row[baseline]["accepted"]
    ]
    piece_relations = Counter(
        relation(row[candidate]["pieces"], row[baseline]["pieces"]) for row in paired
    )
    byte_relations = Counter(
        relation(
            row[candidate]["certificate_bytes"], row[baseline]["certificate_bytes"]
        )
        for row in paired
    )
    candidate_pieces = sum(row[candidate]["pieces"] for row in paired)
    baseline_pieces = sum(row[baseline]["pieces"] for row in paired)
    candidate_bytes = sum(row[candidate]["certificate_bytes"] for row in paired)
    baseline_bytes = sum(row[baseline]["certificate_bytes"] for row in paired)
    return {
        "paired_cases": len(paired),
        "piece_relation_counts": dict(sorted(piece_relations.items())),
        "byte_relation_counts": dict(sorted(byte_relations.items())),
        "piece_savings": baseline_pieces - candidate_pieces,
        "piece_savings_bps": (baseline_pieces - candidate_pieces)
        * 10_000
        // baseline_pieces,
        "byte_savings": baseline_bytes - candidate_bytes,
        "byte_savings_bps": (baseline_bytes - candidate_bytes)
        * 10_000
        // baseline_bytes,
    }


def family_metrics(rows: list[dict[str, Any]]) -> dict[str, Any]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["expected"] == "positive":
            grouped[row["family"]].append(row)
    result: dict[str, Any] = {}
    for family, family_rows in sorted(grouped.items()):
        result[family] = {
            method: {
                "accepted": sum(row[method]["accepted"] for row in family_rows),
                "total_pieces": sum(row[method]["pieces"] for row in family_rows),
                "max_pieces": max(row[method]["pieces"] for row in family_rows),
                "total_bytes": sum(
                    row[method]["certificate_bytes"] for row in family_rows
                ),
            }
            for method in METHODS
        }
    return result


def build_report(rows: list[dict[str, Any]]) -> dict[str, Any]:
    positives = [row for row in rows if row["expected"] == "positive"]
    parity_checks = int(PARITY.read_text(encoding="utf-8").strip().split("=")[1])
    return {
        "schema": "math-object-innovation/v132/critical-region-dispatch-v1",
        "tier": "research_certificate_compiler",
        "authority": "none",
        "arithmetic": "Rational{BigInt}",
        "bounded_domain": {
            "positive_obligations": len(positives),
            "negative_controls": len(rows) - len(positives),
            "families": sorted({row["family"] for row in positives}),
            "max_leaves": 32,
            "equal_piece_candidates": [1, 2, 4, 8, 16, 32],
            "critical_landmark_grid_denominator": 64,
        },
        "acceptance_rule": (
            "Every emitted interval covers part of [0,1], the intervals form a "
            "complete partition, and every exact Bernstein coefficient is nonnegative."
        ),
        "backend_parity_checks": parity_checks,
        "method_metrics": {
            method: method_metrics(rows, method) for method in METHODS
        },
        "family_metrics": family_metrics(rows),
        "comparisons": {
            "midpoint_vs_equal": compare_methods(positives, "midpoint", "equal"),
            "critical_vs_equal": compare_methods(positives, "critical", "equal"),
            "critical_vs_midpoint": compare_methods(
                positives, "critical", "midpoint"
            ),
        },
        "selected_method": "midpoint_adaptive",
        "selection_reason": (
            "Midpoint adaptive refinement preserves all accepts and zero false "
            "accepts while minimizing total pieces, canonical certificate bytes, "
            "and compiler scalar updates on this bounded corpus."
        ),
        "negative_knowledge": [
            "Derivative sign-variation landmarks did not beat midpoint adaptive refinement on this corpus.",
            "Coefficient-interpolated critical splits were rejected because exact recursive denominators depend on coefficient height and caused severe arithmetic growth.",
            "The derivative heuristic is advisory only; ACCEPT uses the same Bernstein cover rule for every method.",
            "These measurements do not prove an asymptotic advantage or a general Jacobi/Gegenbauer theorem.",
        ],
        "rows": rows,
    }


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [
            "julia",
            "--startup-file=no",
            "critical_region_dispatch.jl",
            str(RAW),
            str(PARITY),
        ],
        cwd=ROOT,
        check=True,
    )
    report = build_report(load_rows())
    REPORT.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(report["method_metrics"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
