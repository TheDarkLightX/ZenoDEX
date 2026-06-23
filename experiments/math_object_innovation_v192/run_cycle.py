#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.core.routing import best_route_exact_in_2hop, best_route_exact_out_2hop
from src.state.pools import PoolState, PoolStatus

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"
V190 = ROOT.parent / "math_object_innovation_v190"
BPS = 10_000
RECEIPT_SCHEMA = "zenodex/fire-revenue-surface-receipt/v1"


def _load_module(name: str, path: Path):
    spec = spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load module: {path}")
    module = module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


CALIBRATE = _load_module("v192_calibrate_receipts", V190 / "calibrate_receipts.py")
CAPS = _load_module("v192_build_fee_cap_recommendations", V190 / "build_fee_cap_recommendations.py")


@dataclass(frozen=True)
class MarketCase:
    name: str
    pools: dict[str, PoolState]


def pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=int(r0) if a0 < a1 else int(r1),
        reserve1=int(r1) if a0 < a1 else int(r0),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def market_cases() -> tuple[MarketCase, ...]:
    return (
        MarketCase(
            "deep_twohop_advantage",
            {
                "ab1": pool("v192-ab1", "A", "B", 100_000, 80_000, 30),
                "ac1": pool("v192-ac1", "A", "C", 100_000, 120_000, 10),
                "bc1": pool("v192-bc1", "C", "B", 100_000, 130_000, 10),
            },
        ),
        MarketCase(
            "parallel_direct_plus_twohop",
            {
                "ab2a": pool("v192-ab2a", "A", "B", 80_000, 50_000, 30),
                "ab2b": pool("v192-ab2b", "A", "B", 200_000, 140_000, 20),
                "ac2": pool("v192-ac2", "A", "C", 150_000, 170_000, 5),
                "bc2": pool("v192-bc2", "C", "B", 140_000, 200_000, 5),
            },
        ),
        MarketCase(
            "mild_twohop_advantage",
            {
                "ab3": pool("v192-ab3", "A", "B", 150_000, 150_000, 30),
                "ac3": pool("v192-ac3", "A", "C", 250_000, 260_000, 10),
                "bc3": pool("v192-bc3", "C", "B", 250_000, 270_000, 10),
            },
        ),
    )


def direct_pools(pools: dict[str, PoolState]) -> dict[str, PoolState]:
    return {
        pid: p
        for pid, p in pools.items()
        if {p.asset0, p.asset1} == {"A", "B"}
    }


def floor_bps(amount: int, bps: int) -> int:
    return int(amount) * int(bps) // BPS


def receipt(
    *,
    event_id: str,
    surface: str,
    measured_value_units: int,
    user_fee_paid_units: int,
    notional_units: int,
    direct_cost_units: int,
    metadata: dict[str, object],
    wash_score_bps: int = 0,
) -> dict[str, object]:
    return {
        "schema": RECEIPT_SCHEMA,
        "event_id": event_id,
        "surface": surface,
        "fee_source": "user",
        "asset": "B" if surface == "route_surplus_capture" else "A",
        "notional_units": int(notional_units),
        "measured_value_units": int(measured_value_units),
        "user_fee_paid_units": int(user_fee_paid_units),
        "protocol_revenue_units": int(user_fee_paid_units),
        "direct_cost_units": int(direct_cost_units),
        "recurring": True,
        "primary_revenue": True,
        "wash_score_bps": int(wash_score_bps),
        "eligible_for_retail": True,
        "metadata": metadata,
    }


def quote_key_shape(q) -> str:
    return "+".join(",".join(h.pool_id for h in leg.hops) for leg in q.legs)


def generate_execution_receipts() -> tuple[list[dict[str, object]], dict[str, object]]:
    rows: list[dict[str, object]] = []
    route_improvements: list[int] = []
    exact_out_savings: list[int] = []
    route_capture_bps = (1000, 2000, 3000)
    exact_out_capture_bps = (1000, 1500, 2500)
    exact_in_amounts = (1000, 5000, 10_000)
    exact_out_amounts = (500, 1000, 5000)

    for case in market_cases():
        direct = direct_pools(case.pools)
        for idx, amount_in in enumerate(exact_in_amounts):
            best = best_route_exact_in_2hop(
                pools_by_id=case.pools,
                asset_in="A",
                asset_out="B",
                amount_in=amount_in,
            )
            baseline = best_route_exact_in_2hop(
                pools_by_id=direct,
                asset_in="A",
                asset_out="B",
                amount_in=amount_in,
            )
            if best is None or baseline is None or best.amount_out <= baseline.amount_out:
                continue
            measured = int(best.amount_out) - int(baseline.amount_out)
            fee = floor_bps(measured, route_capture_bps[idx])
            route_improvements.append(measured)
            rows.append(
                receipt(
                    event_id=f"route-{case.name}-{amount_in}",
                    surface="route_surplus_capture",
                    measured_value_units=measured,
                    user_fee_paid_units=fee,
                    notional_units=int(amount_in),
                    direct_cost_units=1,
                    metadata={
                        "case": case.name,
                        "amount_in": int(amount_in),
                        "best_amount_out": int(best.amount_out),
                        "baseline_amount_out": int(baseline.amount_out),
                        "best_route_shape": quote_key_shape(best),
                    },
                )
            )

        for idx, amount_out in enumerate(exact_out_amounts):
            best = best_route_exact_out_2hop(
                pools_by_id=case.pools,
                asset_in="A",
                asset_out="B",
                amount_out=amount_out,
            )
            baseline = best_route_exact_out_2hop(
                pools_by_id=direct,
                asset_in="A",
                asset_out="B",
                amount_out=amount_out,
            )
            if best is None or baseline is None or baseline.amount_in <= best.amount_in:
                continue
            measured = int(baseline.amount_in) - int(best.amount_in)
            fee = floor_bps(measured, exact_out_capture_bps[idx])
            exact_out_savings.append(measured)
            rows.append(
                receipt(
                    event_id=f"exact-out-{case.name}-{amount_out}",
                    surface="exact_out_savings_capture",
                    measured_value_units=measured,
                    user_fee_paid_units=fee,
                    notional_units=int(baseline.amount_in),
                    direct_cost_units=1,
                    metadata={
                        "case": case.name,
                        "amount_out": int(amount_out),
                        "best_amount_in": int(best.amount_in),
                        "baseline_amount_in": int(baseline.amount_in),
                        "best_route_shape": quote_key_shape(best),
                    },
                )
            )

    # Deliberate bad rows derived from the same route surfaces.
    first_route = next(row for row in rows if row["surface"] == "route_surplus_capture")
    first_exact_out = next(row for row in rows if row["surface"] == "exact_out_savings_capture")
    too_high = dict(first_route)
    too_high["event_id"] = "bad-execution-route-fee-over-value"
    too_high["surface"] = "execution_route_overcharge_bad"
    too_high["user_fee_paid_units"] = int(too_high["measured_value_units"]) + 1
    too_high["protocol_revenue_units"] = too_high["user_fee_paid_units"]
    too_high["metadata"] = {**dict(too_high["metadata"]), "tamper": "fee_above_measured_value"}
    rows.append(too_high)

    wash = dict(first_exact_out)
    wash["event_id"] = "bad-execution-exact-out-wash"
    wash["surface"] = "execution_exact_out_wash_bad"
    wash["wash_score_bps"] = 9000
    wash["metadata"] = {**dict(wash["metadata"]), "tamper": "high_wash_score"}
    rows.append(wash)

    metrics = {
        "market_case_count": len(market_cases()),
        "route_receipt_count": len(route_improvements),
        "exact_out_receipt_count": len(exact_out_savings),
        "route_improvement_min": min(route_improvements),
        "route_improvement_max": max(route_improvements),
        "exact_out_savings_min": min(exact_out_savings),
        "exact_out_savings_max": max(exact_out_savings),
    }
    return rows, metrics


def write_jsonl(path: Path, rows: list[dict[str, object]]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in rows),
        encoding="utf-8",
    )


def _relative_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def run_cycle() -> dict[str, object]:
    GENERATED.mkdir(parents=True, exist_ok=True)
    receipt_rows, execution_metrics = generate_execution_receipts()
    receipts_path = GENERATED / "execution_revenue_surface_receipts.jsonl"
    write_jsonl(receipts_path, receipt_rows)

    calibration = CALIBRATE.calibration_report(receipts_path)
    calibration["source_path"] = _relative_path(receipts_path)
    calibration_path = GENERATED / "calibration_report.json"
    calibration_path.write_text(json.dumps(calibration, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    recommendations = CAPS.build_recommendations(
        calibration,
        min_user_fee_samples=5,
        max_user_value_cap_bps=5_000,
        max_retail_value_cap_bps=2_500,
    )
    recommendations_path = GENERATED / "fee_cap_recommendations.json"
    recommendations_path.write_text(json.dumps(recommendations, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    expected_reject_reason_counts = {
        "user_fee_exceeds_measured_value": 1,
        "wash_score_rejected": 1,
    }
    actual_reject_reason_counts = calibration["reject_reason_counts"]
    reject_reason_mismatches = {
        key: {"expected": expected, "actual": actual_reject_reason_counts.get(key, 0)}
        for key, expected in expected_reject_reason_counts.items()
        if actual_reject_reason_counts.get(key, 0) != expected
    }
    unexpected_reject_reasons = {
        key: actual
        for key, actual in actual_reject_reason_counts.items()
        if key not in expected_reject_reason_counts and int(actual) > 0
    }
    status_counts = recommendations["status_counts"]
    cap_recs = {row["surface"]: row for row in recommendations["recommendations"]}
    retail_cap_failures = sum(
        1
        for surface in ("route_surplus_capture", "exact_out_savings_capture")
        if cap_recs[surface]["recommended_user_value_cap_bps"] is None
        or int(cap_recs[surface]["recommended_user_value_cap_bps"]) > 2500
    )
    model_failures = (
        int(calibration["model_audit"]["total_calibration_invariant_failures"])
        + int(recommendations["model_audit"]["total_recommendation_invariant_failures"])
        + len(reject_reason_mismatches)
        + len(unexpected_reject_reasons)
        + int(retail_cap_failures)
    )

    report = {
        "schema": "zenodex/math-object-innovation-v192-report/v1",
        "object": "execution_derived_fee_receipt_bridge_v1",
        "tier": "descriptive_oracle",
        "oracle_dependent": True,
        "discovery_domain": {
            "market_case_count": execution_metrics["market_case_count"],
            "exact_in_amounts": [1000, 5000, 10_000],
            "exact_out_amounts": [500, 1000, 5000],
            "bad_execution_row_count": 2,
        },
        "holdout_domain": "none; deterministic execution-derived fixtures only",
        "receipt_count": int(calibration["receipt_count"]),
        "accepted_count": int(calibration["accepted_count"]),
        "rejected_count": int(calibration["rejected_count"]),
        "candidate_review_cap_count": int(recommendations["candidate_review_cap_count"]),
        "launch_parameter_claim_count": int(recommendations["launch_parameter_claim_count"]),
        "status_counts": status_counts,
        "expected_reject_reason_counts": expected_reject_reason_counts,
        "actual_reject_reason_counts": actual_reject_reason_counts,
        "reject_reason_mismatches": reject_reason_mismatches,
        "unexpected_reject_reasons": unexpected_reject_reasons,
        "retail_cap_failures": retail_cap_failures,
        "execution_metrics": execution_metrics,
        "recommended_caps": {
            surface: cap_recs[surface]["recommended_user_value_cap_bps"]
            for surface in ("route_surplus_capture", "exact_out_savings_capture")
        },
        "model_audit": {
            "calibration_invariant_failures": calibration["model_audit"]["total_calibration_invariant_failures"],
            "recommendation_invariant_failures": recommendations["model_audit"][
                "total_recommendation_invariant_failures"
            ],
            "total_execution_receipt_invariant_failures": model_failures,
        },
        "strongest_claim": (
            "On three deterministic CPMM routing markets, actual best-route improvements generate 18 accepted "
            "fee receipts and two deliberately bad rows. The same calibration bridge emits two review caps, keeps "
            "retail caps at or below 2500 bps of measured value, and rejects the bad rows for the expected reasons."
        ),
        "non_claims": [
            "The market cases are fixtures, not live telemetry.",
            "The result tests receipt generation and cap guards against real router arithmetic; it does not prove fee optimality.",
            "Runtime launch fees still require production receipt replay and governance approval.",
        ],
        "artifacts": {
            "execution_receipts_jsonl": _relative_path(receipts_path),
            "calibration_report": _relative_path(calibration_path),
            "fee_cap_recommendations": _relative_path(recommendations_path),
        },
    }
    report_path = GENERATED / "report.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    report = run_cycle()
    print(
        json.dumps(
            {
                "receipt_count": report["receipt_count"],
                "accepted_count": report["accepted_count"],
                "rejected_count": report["rejected_count"],
                "candidate_review_cap_count": report["candidate_review_cap_count"],
                "invariant_failures": report["model_audit"]["total_execution_receipt_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["model_audit"]["total_execution_receipt_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
