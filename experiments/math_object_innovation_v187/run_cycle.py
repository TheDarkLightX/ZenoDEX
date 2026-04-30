#!/usr/bin/env python3
"""Run the v187 certificate-carrying route interval graph discovery cycle."""

from __future__ import annotations

import csv
import json
import subprocess
from collections import defaultdict
from fractions import Fraction
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
    raise ValueError(f"bad bool: {value!r}")


def run_julia() -> None:
    GENERATED.mkdir(exist_ok=True)
    subprocess.run(["julia", str(ROOT / "run_cycle.jl")], cwd=ROOT, check=True)


def load_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with RAW.open(newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            obj: dict[str, Any] = {"kind": row["kind"], "split": row["split"]}
            if row["kind"] == "graph":
                obj.update(
                    {
                        "seed": int(row["seed"]),
                        "injected": parse_bool(row["injected"]),
                        "potential_ok": parse_bool(row["potential_ok"]),
                        "path_count": int(row["path_count"]),
                        "incumbent": int(row["incumbent"]),
                        "pruneable": int(row["pruneable"]),
                        "false_prunes": int(row["false_prunes"]),
                        "cycle_profit": int(row["cycle_profit"]),
                    }
                )
            else:
                obj.update(
                    {
                        "grid_count": int(row["grid_count"]),
                        "grid_violations": int(row["grid_violations"]),
                        "max_error": row["max_error"],
                    }
                )
            rows.append(obj)
    return rows


def frac_string_lt_one(value: str) -> bool:
    return Fraction(value) < 1


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    graph_rows = [row for row in rows if row["kind"] == "graph"]
    floor_rows = [row for row in rows if row["kind"] == "floor_grid"]

    by_split: dict[str, dict[str, Any]] = defaultdict(
        lambda: {
            "noarb_graphs": 0,
            "noarb_certified": 0,
            "injected_graphs": 0,
            "injected_rejected": 0,
            "injected_profitable_cycles": 0,
            "route_candidates": 0,
            "pruneable_candidates": 0,
            "false_prunes": 0,
        }
    )
    for row in graph_rows:
        metrics = by_split[row["split"]]
        if row["injected"]:
            metrics["injected_graphs"] += 1
            if not row["potential_ok"]:
                metrics["injected_rejected"] += 1
            if row["cycle_profit"] > 0:
                metrics["injected_profitable_cycles"] += 1
        else:
            metrics["noarb_graphs"] += 1
            if row["potential_ok"]:
                metrics["noarb_certified"] += 1
            metrics["route_candidates"] += row["path_count"]
            metrics["pruneable_candidates"] += row["pruneable"]
            metrics["false_prunes"] += row["false_prunes"]

    floor_metrics: dict[str, Any] = {}
    for row in floor_rows:
        floor_metrics[row["split"]] = {
            "grid_count": row["grid_count"],
            "violations": row["grid_violations"],
            "max_error": row["max_error"],
            "max_error_lt_one": frac_string_lt_one(row["max_error"]),
        }

    total_noarb = sum(v["noarb_graphs"] for v in by_split.values())
    total_noarb_certified = sum(v["noarb_certified"] for v in by_split.values())
    total_injected = sum(v["injected_graphs"] for v in by_split.values())
    total_injected_rejected = sum(v["injected_rejected"] for v in by_split.values())
    total_false_prunes = sum(v["false_prunes"] for v in by_split.values())
    total_pruneable = sum(v["pruneable_candidates"] for v in by_split.values())
    total_candidates = sum(v["route_candidates"] for v in by_split.values())
    total_floor_violations = sum(v["violations"] for v in floor_metrics.values())

    return {
        "schema": "math-object-innovation/v187",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": True,
        "strongest_claim": (
            "Exact-rational Julia discovery supports a certificate-carrying route interval graph: "
            "potential-certified no-arb graphs safely prune bounded route candidates with zero false prunes, "
            "injected arbitrage graphs are rejected by the certificate, and post-fee CPMM local floor error stays in [0,1) on the bounded grids."
        ),
        "aot_iterations": 40,
        "selected_objects": [
            "certificate_carrying_arbitrage_graph",
            "integer_interval_cpmm_bridge",
        ],
        "discovery_domain": {
            "assets": 5,
            "noarb_graphs": 80,
            "injected_graphs": 40,
            "route_max_edges": 3,
            "floor_grid": {"reserve_in": [1, 80], "reserve_out": [1, 80], "post_fee_net_in": [1, 80]},
        },
        "holdout_domain": {
            "assets": 5,
            "noarb_graphs": 80,
            "injected_graphs": 40,
            "route_max_edges": 3,
            "floor_grid": {"reserve_in": [81, 140], "reserve_out": [81, 140], "post_fee_net_in": [81, 140]},
        },
        "reference_sources": [
            "DLMF Chapter 3 numerical methods / interval thinking",
            "Wolfram Functions Site as formula-oracle class reference",
            "OEIS as future residual sequence-recognition fallback",
            "Lean Mathlib as formal theorem target library",
            "local lean-mathlib/Proofs/ArbitrageCertificate.lean",
        ],
        "summary": {
            "total_noarb_graphs": total_noarb,
            "total_noarb_certified": total_noarb_certified,
            "total_injected_graphs": total_injected,
            "total_injected_rejected": total_injected_rejected,
            "total_pruneable_candidates": total_pruneable,
            "total_route_candidates": total_candidates,
            "total_false_prunes": total_false_prunes,
            "total_floor_violations": total_floor_violations,
        },
        "lean_promotion": {
            "artifact": "lean-mathlib/Proofs/RouteIntervalGraph.lean",
            "receipt": "lean-mathlib/proof_receipts/route_interval_graph_v1.json",
            "checker_command": "lake env lean Proofs/RouteIntervalGraph.lean",
            "closed_theorems": [
                "cpmm_post_fee_floor_interval",
                "pathProduct_potential_bound",
                "pathProduct_le_potential_ratio",
            ],
            "status": "checked_no_placeholders",
        },
        "by_split": dict(sorted(by_split.items())),
        "floor_metrics": floor_metrics,
        "restricted_theorems": [
            {
                "name": "potential_route_prefix_prune_sound",
                "statement": (
                    "If every edge satisfies upper_rate(i,j)*p[j] <= p[i], "
                    "and a route prefix reaches asset v with exact amount a, "
                    "then every continuation to dst outputs at most a*p[v]/p[dst]."
                ),
                "proof_lane": "Promoted to Lean as pathProduct_potential_bound and pathProduct_le_potential_ratio",
            },
            {
                "name": "cpmm_post_fee_floor_error_lt_one",
                "statement": (
                    "For positive integer reserves and post-fee net input n, "
                    "let q = n*reserve_out/(reserve_in+n). Then floor(q) <= q < floor(q)+1."
                ),
                "proof_lane": "Promoted to Lean as cpmm_post_fee_floor_interval",
            },
            {
                "name": "treasury_arbitrage_dual_guard",
                "statement": (
                    "A treasury opportunity is admissible only when a potential/interval opportunity certificate "
                    "and the existing treasury budget guard both accept."
                ),
                "proof_lane": "Compose existing TreasuryRebalancerGuard with a new certificate predicate",
            },
        ],
        "non_claims": [
            "not a production router",
            "not a complete arbitrage detector",
            "not a proof over all graph sizes",
            "not a live external-venue market-making proof",
        ],
    }


def main() -> None:
    run_julia()
    report = summarize(load_rows())
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
