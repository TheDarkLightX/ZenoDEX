#!/usr/bin/env python3
"""Run the v188 Gasper-cone Jacobi Turan orientation scan."""

from __future__ import annotations

import csv
import json
import subprocess
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"
RAW = GENERATED / "raw.tsv"
REPORT = GENERATED / "report.json"


def parse_bool(value: str) -> bool:
    if value == "true":
        return True
    if value == "false":
        return False
    raise ValueError(f"unexpected boolean: {value!r}")


def load_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with RAW.open(newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            rows.append(
                {
                    "family": row["family"],
                    "anchor": row["anchor"],
                    "alpha": row["alpha"],
                    "beta": row["beta"],
                    "relation": row["relation"],
                    "n": int(row["n"]),
                    "degree": int(row["degree"]),
                    "best_pieces": int(row["best_pieces"]),
                    "accepted": parse_bool(row["accepted"]),
                    "min_coeff": row["min_coeff"],
                    "fail_piece": int(row["fail_piece"]),
                    "value_at_0": row["value_at_0"],
                    "value_at_1": row["value_at_1"],
                    "endpoint_falsified": parse_bool(row["endpoint_falsified"]),
                    "expected": row["expected"],
                }
            )
    return rows


def split_name(n: int) -> str:
    return "discovery" if 1 <= n <= 10 else "holdout"


def metrics(group_rows: list[dict[str, Any]]) -> dict[str, Any]:
    accepted = [row for row in group_rows if row["accepted"]]
    hist = Counter(row["best_pieces"] for row in accepted)
    return {
        "count": len(group_rows),
        "certified": len(accepted),
        "unknown": len(group_rows) - len(accepted),
        "endpoint_falsified": sum(1 for row in group_rows if row["endpoint_falsified"]),
        "max_pieces": max((row["best_pieces"] for row in accepted), default=0),
        "piece_histogram": dict(sorted(hist.items())),
    }


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    positives = [row for row in rows if row["expected"] == "positive_claim"]
    outside = [row for row in rows if row["expected"] == "outside_cone"]
    negatives = [row for row in rows if row["expected"] == "negative"]

    by_anchor: dict[str, list[dict[str, Any]]] = defaultdict(list)
    by_relation: dict[str, list[dict[str, Any]]] = defaultdict(list)
    by_param: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["expected"] != "negative":
            by_anchor[row["anchor"]].append(row)
            by_relation[row["relation"]].append(row)
            by_param[f"{row['alpha']},{row['beta']}"].append(row)

    split_metrics: dict[str, dict[str, int]] = {
        "discovery": {
            "positive_claim": 0,
            "positive_certified": 0,
            "outside_cone": 0,
            "outside_endpoint_falsified": 0,
            "max_pieces": 0,
        },
        "holdout": {
            "positive_claim": 0,
            "positive_certified": 0,
            "outside_cone": 0,
            "outside_endpoint_falsified": 0,
            "max_pieces": 0,
        },
    }
    for row in rows:
        if row["expected"] == "negative":
            continue
        split = split_name(row["n"])
        if row["expected"] == "positive_claim":
            split_metrics[split]["positive_claim"] += 1
            if row["accepted"]:
                split_metrics[split]["positive_certified"] += 1
                split_metrics[split]["max_pieces"] = max(
                    split_metrics[split]["max_pieces"], row["best_pieces"]
                )
        elif row["expected"] == "outside_cone":
            split_metrics[split]["outside_cone"] += 1
            if row["endpoint_falsified"]:
                split_metrics[split]["outside_endpoint_falsified"] += 1

    recognizer_rows = [row for row in rows if row["expected"] != "negative"]
    oriented = [row for row in recognizer_rows if row["anchor"] == "oriented"]
    right = [row for row in recognizer_rows if row["anchor"] == "right"]
    left = [row for row in recognizer_rows if row["anchor"] == "left"]
    wrong = [row for row in recognizer_rows if row["anchor"] == "wrong"]

    return {
        "schema": "math-object-innovation/v188",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": True,
        "strongest_claim": (
            "The v186 asymmetric Jacobi Turan failures are explained by a Gasper-cone orientation rule: "
            "right-endpoint normalization certifies the sampled beta >= alpha cone, left-endpoint normalization certifies the mirrored alpha >= beta cone, "
            "and choosing the cone-compatible endpoint certifies every sampled asymmetric Jacobi Turan obligation while the wrong strict endpoint is endpoint-falsified."
        ),
        "sigma": {
            "R": "shifted Jacobi Turan polynomials over exact rational coefficients",
            "alpha": "endpoint-normalized one-dimensional polynomial obligations on [0,1]",
            "Delta": [
                "alpha,beta are nonnegative rational samples",
                "n is bounded by the discovery and holdout grids",
                "Bernstein nonnegative coefficients are sufficient certificates",
            ],
            "G": "classify a corrected asymmetric Jacobi Turan recognizer after v186 falsified endpoint-max normalization",
            "Pi": [
                "exact endpoint counterexamples for outside-cone claims",
                "exact Bernstein certificates for in-cone positive claims",
                "negative controls remain fail-closed",
            ],
            "S": ["Julia Rational{BigInt}", "Bernstein certificate checker", "Morph tactic lookup", "DLMF/Gasper reference anchors"],
            "M": ["v186 endpoint falsifiers", "Gasper beta >= alpha cone reference", "mirror symmetry x -> 1-x and alpha <-> beta"],
        },
        "morph_moves": [
            {
                "tactic": "tao_use_symmetry_normalize",
                "semantic": "equivalence",
                "effect": "replace endpoint-max normalization with a cone-compatible endpoint anchor",
            },
            {
                "tactic": "local_decompose_and_symmetrize",
                "semantic": "reduction",
                "effect": "split right, left, oriented, and wrong-anchor obligations and check each separately",
            },
        ],
        "discovery_domain": {
            "params": sorted(by_param),
            "n": [1, 10],
            "piece_candidates": [1, 2, 4, 8, 16, 32, 64, 128],
        },
        "holdout_domain": {
            "params": sorted(by_param),
            "n": [11, 18],
            "piece_candidates": [1, 2, 4, 8, 16, 32, 64, 128],
        },
        "reference_sources": [
            "DLMF 18.14(ii), Turan-type inequalities for Jacobi polynomials",
            "Gasper/Szego Jacobi Turan parameter-cone references",
            "DLMF Chapter 18 Jacobi polynomial conventions",
        ],
        "summary": {
            "positive_claims": len(positives),
            "positive_certified": sum(1 for row in positives if row["accepted"]),
            "positive_unknown": sum(1 for row in positives if not row["accepted"]),
            "outside_cone_cases": len(outside),
            "outside_endpoint_falsified": sum(1 for row in outside if row["endpoint_falsified"]),
            "outside_accidentally_certified": sum(1 for row in outside if row["accepted"]),
            "negative_controls": len(negatives),
            "accepted_negative": sum(1 for row in negatives if row["accepted"]),
            "oriented_cases": len(oriented),
            "oriented_certified": sum(1 for row in oriented if row["accepted"]),
            "oriented_unknown": sum(1 for row in oriented if not row["accepted"]),
            "wrong_anchor_cases": len(wrong),
            "wrong_anchor_endpoint_falsified": sum(1 for row in wrong if row["endpoint_falsified"]),
            "right_cases": len(right),
            "right_certified": sum(1 for row in right if row["accepted"]),
            "left_cases": len(left),
            "left_certified": sum(1 for row in left if row["accepted"]),
            "max_pieces_positive": max((row["best_pieces"] for row in positives if row["accepted"]), default=0),
        },
        "split_metrics": split_metrics,
        "anchor_metrics": {anchor: metrics(group_rows) for anchor, group_rows in sorted(by_anchor.items())},
        "relation_metrics": {relation: metrics(group_rows) for relation, group_rows in sorted(by_relation.items())},
        "param_metrics": {param: metrics(group_rows) for param, group_rows in sorted(by_param.items())},
        "outside_cone_examples": outside[:20],
        "negative_controls": negatives,
        "rows_sample": rows[:40],
        "negative_knowledge": [
            "The strict wrong-endpoint Jacobi Turan recognizer is false in the bounded profile; failures are exact endpoint counterexamples.",
            "More Bernstein subdivision is not the fix for v186 Turan failures, because the failed cases are not nonnegative.",
            "The cone-compatible rule is a bounded recognizer and certificate generator here, not a standalone proof of Gasper's full theorem.",
        ],
        "next_frontier": [
            "Turn the oriented endpoint rule into a Tau/FIRE theorem recognizer that emits Bernstein certificates and rejects outside-cone formulas without falling into QE.",
            "Formalize the mirror equivalence: left-normalized (alpha,beta) at x=0 reduces to right-normalized (beta,alpha) at 1-x.",
            "Ask Aristotle/Lean for the generic endpoint-mirror lemma and keep the full Gasper theorem as an external reference-backed theorem target, not an assumed local proof.",
        ],
    }


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    subprocess.run(["julia", "run_cycle.jl", str(RAW)], cwd=ROOT, check=True)
    report = summarize(load_rows())
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
