#!/usr/bin/env python3
"""Run the v189 Jacobi Turan endpoint-obstruction formula scan."""

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
                    "anchor": row["anchor"],
                    "endpoint": row["endpoint"],
                    "alpha": row["alpha"],
                    "beta": row["beta"],
                    "relation": row["relation"],
                    "n": int(row["n"]),
                    "direct": row["direct"],
                    "closed": row["closed"],
                    "formula_match": parse_bool(row["formula_match"]),
                    "sign": row["sign"],
                    "cone_ok": parse_bool(row["cone_ok"]),
                }
            )
    return rows


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_anchor: dict[str, list[dict[str, Any]]] = defaultdict(list)
    by_relation: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_anchor[row["anchor"]].append(row)
        by_relation[row["relation"]].append(row)

    outside = [row for row in rows if not row["cone_ok"]]
    inside = [row for row in rows if row["cone_ok"]]
    strict_wrong = [row for row in outside if row["relation"] != "alpha_eq_beta"]

    def group_metrics(group_rows: list[dict[str, Any]]) -> dict[str, Any]:
        signs = Counter(row["sign"] for row in group_rows)
        return {
            "count": len(group_rows),
            "formula_matches": sum(1 for row in group_rows if row["formula_match"]),
            "signs": dict(sorted(signs.items())),
        }

    return {
        "schema": "math-object-innovation/v189",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": False,
        "strongest_claim": (
            "The Jacobi Turan wrong-endpoint obstruction has a closed endpoint formula: "
            "right-normalized Turan at x=0 has sign beta-alpha, and left-normalized Turan at x=1 has sign alpha-beta. "
            "The exact bounded scan found zero mismatches against direct endpoint evaluation."
        ),
        "formulae": {
            "right_left_endpoint": (
                "T_n^+(0) = (C(n+beta,n)/C(n+alpha,n))^2 "
                "* (beta-alpha)/((n+alpha+1)*(n+beta))"
            ),
            "left_right_endpoint": (
                "T_n^-(1) = (C(n+alpha,n)/C(n+beta,n))^2 "
                "* (alpha-beta)/((n+beta+1)*(n+alpha))"
            ),
            "where": "C(n+gamma,n) denotes binom(n+gamma,n), n >= 1",
        },
        "proof_sketch": [
            "For right normalization, the opposite endpoint value is r_n = C(n+beta,n)/C(n+alpha,n) up to the harmless Jacobi endpoint sign.",
            "The Turan endpoint is r_n^2 - r_{n-1}*r_{n+1}.",
            "The ratio r_{n+1}/r_n is (n+beta+1)/(n+alpha+1).",
            "Substituting adjacent ratios gives the displayed factor beta-alpha over a positive denominator.",
            "The left-normalized formula follows by the mirror swap alpha <-> beta and x -> 1-x.",
        ],
        "discovery_domain": {
            "alpha_beta_values": ["0", "1/3", "1/2", "2/3", "1", "3/2", "2", "3", "5"],
            "n": [1, 32],
        },
        "holdout_domain": {
            "alpha_beta_values": ["0", "1/3", "1/2", "2/3", "1", "3/2", "2", "3", "5"],
            "n": [33, 64],
        },
        "reference_sources": [
            "DLMF Chapter 18 Jacobi endpoint conventions",
            "DLMF 18.14(ii) Jacobi Turan-type inequality reference surface",
            "Gasper/Szego parameter-cone literature used as theorem-shape guidance",
        ],
        "summary": {
            "rows": len(rows),
            "formula_mismatches": sum(1 for row in rows if not row["formula_match"]),
            "inside_cone_rows": len(inside),
            "inside_nonnegative": sum(1 for row in inside if row["sign"] in {"positive", "zero"}),
            "outside_cone_rows": len(outside),
            "outside_negative": sum(1 for row in outside if row["sign"] == "negative"),
            "strict_wrong_rows": len(strict_wrong),
            "strict_wrong_negative": sum(1 for row in strict_wrong if row["sign"] == "negative"),
            "equal_parameter_zero": sum(1 for row in rows if row["relation"] == "alpha_eq_beta" and row["sign"] == "zero"),
        },
        "lean_promotion": {
            "artifact": "lean-mathlib/Proofs/JacobiTuranEndpointObstruction.lean",
            "receipt": "lean-mathlib/proof_receipts/jacobi_turan_endpoint_obstruction_v1.json",
            "checker_command": "lake env lean Proofs/JacobiTuranEndpointObstruction.lean",
            "closed_theorems": [
                "right_endpoint_obstruction_formula",
                "left_endpoint_obstruction_formula",
            ],
            "status": "checked_no_placeholders",
            "scope": "algebraic endpoint-ratio skeleton, not full Jacobi/Gasper positivity",
        },
        "anchor_metrics": {anchor: group_metrics(group_rows) for anchor, group_rows in sorted(by_anchor.items())},
        "relation_metrics": {relation: group_metrics(group_rows) for relation, group_rows in sorted(by_relation.items())},
        "negative_knowledge": [
            "A strict wrong endpoint cannot be fixed by a stronger interval certificate; the endpoint determinant is negative before any subdivision begins.",
            "The endpoint formula proves only the necessary cone obstruction, not full interval positivity inside the cone.",
            "The full Gasper theorem remains a separate proof/import target.",
        ],
        "next_frontier": [
            "Formalize the endpoint obstruction in Lean using generalized binomial/Pochhammer arithmetic.",
            "Use this as a cheap prefilter in the Jacobi Turan recognizer before invoking Bernstein certificates.",
            "Search for a similarly compact interior positivity certificate inside the cone.",
        ],
        "rows_sample": rows[:40],
    }


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    subprocess.run(["julia", "run_cycle.jl", str(RAW)], cwd=ROOT, check=True)
    report = summarize(load_rows())
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
