#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from typing import Any

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


CALIBRATE = _load_module("v190_calibrate_receipts", V190 / "calibrate_receipts.py")
CAPS = _load_module("v190_build_fee_cap_recommendations", V190 / "build_fee_cap_recommendations.py")


def floor_bps(amount: int, bps: int) -> int:
    return int(amount) * int(bps) // BPS


def receipt(
    *,
    event_id: str,
    surface: str,
    fee_source: str,
    notional_units: int,
    measured_value_units: int,
    fee_bps_of_value: int = 0,
    protocol_revenue_units: int | None = None,
    direct_cost_units: int = 0,
    recurring: bool = True,
    primary_revenue: bool = True,
    wash_score_bps: int = 0,
    eligible_for_retail: bool = False,
    asset: str = "QUOTE",
) -> dict[str, object]:
    user_fee_paid_units = floor_bps(measured_value_units, fee_bps_of_value)
    if protocol_revenue_units is None:
        protocol_revenue_units = user_fee_paid_units
    return {
        "schema": RECEIPT_SCHEMA,
        "event_id": event_id,
        "surface": surface,
        "fee_source": fee_source,
        "asset": asset,
        "notional_units": int(notional_units),
        "measured_value_units": int(measured_value_units),
        "user_fee_paid_units": int(user_fee_paid_units),
        "protocol_revenue_units": int(protocol_revenue_units),
        "direct_cost_units": int(direct_cost_units),
        "recurring": bool(recurring),
        "primary_revenue": bool(primary_revenue),
        "wash_score_bps": int(wash_score_bps),
        "eligible_for_retail": bool(eligible_for_retail),
    }


def user_surface_rows() -> list[dict[str, object]]:
    profiles = [
        ("route_surplus_capture", True, [900, 1200, 1800], [1000, 1800, 2500], 15),
        ("exact_out_savings_capture", True, [500, 700, 1100], [1000, 2000, 2500], 12),
        ("cow_batch_solver_surplus", False, [900, 1500, 2100], [5000, 7000, 8000], 20),
        ("pro_certificate_api", False, [1000, 1400, 1800], [1500, 3000, 4000], 35),
        ("integrator_router_surface", False, [750, 900, 1250], [2000, 3000, 4500], 30),
        ("lp_loss_cover_premium", False, [500, 800, 1200], [5000, 6000, 7000], 50),
    ]
    rows: list[dict[str, object]] = []
    for surface, retail, values, fee_bps_values, cost in profiles:
        for idx, (value, fee_bps) in enumerate(zip(values, fee_bps_values), start=1):
            rows.append(
                receipt(
                    event_id=f"good-{surface}-{idx}",
                    surface=surface,
                    fee_source="user",
                    asset="OUT" if surface != "pro_certificate_api" else "NATIVE",
                    notional_units=100_000 + idx * 40_000,
                    measured_value_units=value,
                    fee_bps_of_value=fee_bps,
                    direct_cost_units=cost,
                    eligible_for_retail=retail,
                )
            )
    return rows


def internal_surface_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for idx, value in enumerate((700, 850, 1100), start=1):
        rows.append(
            receipt(
                event_id=f"good-treasury-mm-{idx}",
                surface="treasury_market_maker_bot",
                fee_source="protocol_surplus",
                notional_units=0,
                measured_value_units=value,
                protocol_revenue_units=value // 2,
                direct_cost_units=60,
                eligible_for_retail=False,
            )
        )
    for idx, value in enumerate((900, 1100, 1400), start=1):
        rows.append(
            receipt(
                event_id=f"good-arb-recapture-{idx}",
                surface="arbitrage_recapture_auction",
                fee_source="protocol_surplus",
                notional_units=0,
                measured_value_units=value,
                protocol_revenue_units=value // 2,
                direct_cost_units=50,
                eligible_for_retail=False,
            )
        )
    for idx, notional in enumerate((25_000, 50_000, 100_000), start=1):
        rows.append(
            receipt(
                event_id=f"good-staking-exit-{idx}",
                surface="staking_early_exit_penalty",
                fee_source="penalty",
                notional_units=notional,
                measured_value_units=0,
                fee_bps_of_value=0,
                protocol_revenue_units=notional // 200,
                direct_cost_units=0,
                recurring=False,
                primary_revenue=False,
                eligible_for_retail=False,
            )
        )
        rows[-1]["user_fee_paid_units"] = rows[-1]["protocol_revenue_units"]
    return rows


def bad_rows() -> list[dict[str, object]]:
    rows = [
        receipt(
            event_id="bad-extractive-user-fee",
            surface="extractive_notional_bad",
            fee_source="user",
            notional_units=100_000,
            measured_value_units=100,
            fee_bps_of_value=90_000,
            direct_cost_units=5,
            eligible_for_retail=True,
        ),
        receipt(
            event_id="bad-protocol-surplus-overcapture",
            surface="protocol_surplus_overcapture_bad",
            fee_source="protocol_surplus",
            notional_units=0,
            measured_value_units=400,
            protocol_revenue_units=600,
            direct_cost_units=10,
        ),
        receipt(
            event_id="bad-primary-penalty",
            surface="primary_penalty_bad",
            fee_source="penalty",
            notional_units=50_000,
            measured_value_units=0,
            protocol_revenue_units=250,
            recurring=False,
            primary_revenue=True,
        ),
        receipt(
            event_id="bad-wash-rebate",
            surface="wash_rebate_bad",
            fee_source="user",
            notional_units=100_000,
            measured_value_units=400,
            fee_bps_of_value=2500,
            direct_cost_units=5,
            wash_score_bps=9000,
            eligible_for_retail=True,
        ),
        receipt(
            event_id="bad-negative-net-primary",
            surface="primary_negative_net_bad",
            fee_source="user",
            notional_units=100_000,
            measured_value_units=500,
            fee_bps_of_value=1000,
            protocol_revenue_units=50,
            direct_cost_units=80,
            primary_revenue=True,
            eligible_for_retail=True,
        ),
    ]
    return rows


def stress_corpus() -> list[dict[str, object]]:
    return user_surface_rows() + internal_surface_rows() + bad_rows()


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


def _recommendation_map(recommendations: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(row["surface"]): row for row in recommendations["recommendations"]}


def run_cycle() -> dict[str, object]:
    GENERATED.mkdir(parents=True, exist_ok=True)
    corpus_path = GENERATED / "stress_revenue_surface_receipts.jsonl"
    rows = stress_corpus()
    write_jsonl(corpus_path, rows)

    calibration = CALIBRATE.calibration_report(corpus_path)
    calibration["source_path"] = _relative_path(corpus_path)
    calibration_path = GENERATED / "calibration_report.json"
    calibration_path.write_text(json.dumps(calibration, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    recommendations = CAPS.build_recommendations(
        calibration,
        min_user_fee_samples=3,
        max_user_value_cap_bps=5_000,
        max_retail_value_cap_bps=2_500,
    )
    recommendations_path = GENERATED / "fee_cap_recommendations.json"
    recommendations_path.write_text(json.dumps(recommendations, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    recs = _recommendation_map(recommendations)

    cap_clip_surfaces = sorted(
        surface
        for surface, row in recs.items()
        if row["recommended_user_value_cap_bps"] is not None
        and int(row["observed_p90_fee_bps_of_value"]) > int(row["recommended_user_value_cap_bps"])
    )
    retail_cap_failures = sum(
        1
        for row in recs.values()
        if int(row["retail_eligible_sample_count"]) > 0
        and row["recommended_user_value_cap_bps"] is not None
        and int(row["recommended_user_value_cap_bps"]) > 2_500
    )
    expected_reject_reason_counts = {
        "penalty_marked_primary": 1,
        "primary_surface_negative_net_revenue": 1,
        "protocol_revenue_exceeds_surplus": 1,
        "user_fee_exceeds_measured_value": 1,
        "wash_score_rejected": 1,
    }
    actual_reject_reason_counts = calibration["reject_reason_counts"]
    reject_reason_mismatches = {
        key: {"expected": expected, "actual": actual_reject_reason_counts.get(key, 0)}
        for key, expected in expected_reject_reason_counts.items()
        if actual_reject_reason_counts.get(key, 0) != expected
    }
    model_failures = (
        int(calibration["model_audit"]["total_calibration_invariant_failures"])
        + int(recommendations["model_audit"]["total_recommendation_invariant_failures"])
        + int(retail_cap_failures)
        + len(reject_reason_mismatches)
    )

    report = {
        "schema": "zenodex/math-object-innovation-v191-report/v1",
        "object": "fee_cap_calibration_stress_corpus_v1",
        "tier": "descriptive_oracle",
        "oracle_dependent": True,
        "discovery_domain": {
            "user_fee_surface_count": 6,
            "accepted_samples_per_user_fee_surface": 3,
            "protocol_surplus_surface_count": 2,
            "penalty_surface_count": 1,
            "bad_row_count": 5,
        },
        "holdout_domain": "none; this is a deterministic synthetic stress corpus, not market data",
        "receipt_count": int(calibration["receipt_count"]),
        "accepted_count": int(calibration["accepted_count"]),
        "rejected_count": int(calibration["rejected_count"]),
        "candidate_review_cap_count": int(recommendations["candidate_review_cap_count"]),
        "launch_parameter_claim_count": int(recommendations["launch_parameter_claim_count"]),
        "status_counts": recommendations["status_counts"],
        "expected_reject_reason_counts": expected_reject_reason_counts,
        "actual_reject_reason_counts": actual_reject_reason_counts,
        "reject_reason_mismatches": reject_reason_mismatches,
        "cap_clip_surfaces": cap_clip_surfaces,
        "retail_cap_failures": retail_cap_failures,
        "model_audit": {
            "calibration_invariant_failures": calibration["model_audit"]["total_calibration_invariant_failures"],
            "recommendation_invariant_failures": recommendations["model_audit"][
                "total_recommendation_invariant_failures"
            ],
            "total_stress_invariant_failures": model_failures,
        },
        "strongest_claim": (
            "A deterministic 32-row synthetic corpus with three accepted samples per user-paid surface exercises "
            "the receipt -> calibration -> fee-cap bridge: six review caps survive, five adversarial rows are "
            "rejected for the expected reasons, retail caps stay under 2500 bps of measured value, and no launch "
            "parameter claim is emitted."
        ),
        "non_claims": [
            "This is not production market calibration.",
            "The corpus proves bridge sensitivity on declared synthetic cases, not economic optimality.",
            "Runtime launch parameters still require real receipts, governance review, and on-chain guard alignment.",
        ],
        "artifacts": {
            "stress_receipts_jsonl": _relative_path(corpus_path),
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
                "invariant_failures": report["model_audit"]["total_stress_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["model_audit"]["total_stress_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
