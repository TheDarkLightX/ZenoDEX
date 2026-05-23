#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

BPS = 10_000
SCHEMA = "zenodex/fire-revenue-fee-cap-recommendations/v1"


def _require_report(obj: Any) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise ValueError("calibration report must be an object")
    if obj.get("schema") != "zenodex/fire-revenue-surface-calibration-report/v1":
        raise ValueError("bad calibration report schema")
    summaries = obj.get("surface_summaries")
    if not isinstance(summaries, dict):
        raise ValueError("calibration report missing surface_summaries")
    return obj


def _int(summary: dict[str, Any], key: str) -> int:
    value = summary.get(key, 0)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be int")
    return int(value)


def _source_count(summary: dict[str, Any], source: str) -> int:
    counts = summary.get("accepted_fee_source_counts", {})
    if not isinstance(counts, dict):
        return 0
    value = counts.get(source, 0)
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else 0


def _recommendation_for_surface(
    *,
    surface: str,
    summary: dict[str, Any],
    min_user_fee_samples: int,
    max_user_value_cap_bps: int,
    max_retail_value_cap_bps: int,
) -> dict[str, Any]:
    accepted_count = _int(summary, "accepted_count")
    user_sample_count = _source_count(summary, "user")
    protocol_surplus_count = _source_count(summary, "protocol_surplus")
    penalty_count = _source_count(summary, "penalty")
    retail_count = _int(summary, "accepted_retail_eligible_count")
    suggested_value_cap = _int(summary, "suggested_review_cap_bps_of_value")
    observed_notional_cap = _int(summary, "observed_p90_fee_bps_of_notional")

    is_retail_surface = retail_count > 0
    hard_value_cap = min(
        int(max_user_value_cap_bps),
        int(max_retail_value_cap_bps) if is_retail_surface else int(max_user_value_cap_bps),
    )
    candidate_value_cap = max(0, min(int(suggested_value_cap), int(hard_value_cap)))
    candidate_notional_cap = max(0, min(int(observed_notional_cap), BPS))

    if accepted_count <= 0:
        status = "rejected_only"
        recommended_value_cap_bps: int | None = None
        recommended_notional_cap_bps: int | None = None
        launch_parameter_claim = False
    elif penalty_count > 0:
        status = "penalty_not_primary_revenue"
        recommended_value_cap_bps = None
        recommended_notional_cap_bps = candidate_notional_cap
        launch_parameter_claim = False
    elif protocol_surplus_count > 0 and user_sample_count == 0:
        status = "protocol_surplus_internal_capture"
        recommended_value_cap_bps = None
        recommended_notional_cap_bps = None
        launch_parameter_claim = False
    elif user_sample_count < int(min_user_fee_samples):
        status = "insufficient_user_fee_evidence"
        recommended_value_cap_bps = None
        recommended_notional_cap_bps = candidate_notional_cap
        launch_parameter_claim = False
    else:
        status = "candidate_review_cap"
        recommended_value_cap_bps = candidate_value_cap
        recommended_notional_cap_bps = candidate_notional_cap
        launch_parameter_claim = False

    evidence_tier = (
        "rejected_fixture"
        if accepted_count <= 0
        else "fixture_singleton"
        if user_sample_count <= 1
        else "fixture_small_sample"
    )
    if user_sample_count >= int(min_user_fee_samples) and int(min_user_fee_samples) >= 5:
        evidence_tier = "empirical_min_sample"

    return {
        "surface": surface,
        "status": status,
        "evidence_tier": evidence_tier,
        "accepted_count": accepted_count,
        "accepted_user_fee_sample_count": user_sample_count,
        "accepted_protocol_surplus_sample_count": protocol_surplus_count,
        "accepted_penalty_sample_count": penalty_count,
        "retail_eligible_sample_count": retail_count,
        "observed_p90_fee_bps_of_value": _int(summary, "observed_p90_fee_bps_of_value"),
        "observed_p90_fee_bps_of_notional": observed_notional_cap,
        "hard_value_cap_bps": hard_value_cap,
        "recommended_user_value_cap_bps": recommended_value_cap_bps,
        "recommended_notional_cap_bps": recommended_notional_cap_bps,
        "launch_parameter_claim": launch_parameter_claim,
        "reason": _reason_for_status(status),
    }


def _reason_for_status(status: str) -> str:
    return {
        "candidate_review_cap": (
            "accepted user-paid value receipts exist; cap is review-only and clipped by hard user-value rails"
        ),
        "insufficient_user_fee_evidence": (
            "accepted user-paid receipts exist but are below the requested minimum sample count"
        ),
        "protocol_surplus_internal_capture": (
            "surface captures protocol-side surplus and does not define a user-paid fee cap"
        ),
        "penalty_not_primary_revenue": (
            "surface is a commitment penalty; it may bound behavior but is not primary launch revenue"
        ),
        "rejected_only": "all observed rows for this surface were rejected by calibration guards",
    }[status]


def build_recommendations(
    report: dict[str, Any],
    *,
    min_user_fee_samples: int,
    max_user_value_cap_bps: int,
    max_retail_value_cap_bps: int,
) -> dict[str, Any]:
    report = _require_report(report)
    if min_user_fee_samples < 1:
        raise ValueError("min_user_fee_samples must be positive")
    if not 0 <= max_retail_value_cap_bps <= max_user_value_cap_bps <= BPS:
        raise ValueError("invalid cap rails")

    summaries = report["surface_summaries"]
    recommendations = []
    for surface, summary in sorted(summaries.items()):
        if not isinstance(summary, dict):
            raise ValueError(f"surface summary must be object: {surface}")
        recommendations.append(
            _recommendation_for_surface(
                surface=str(surface),
                summary=summary,
                min_user_fee_samples=int(min_user_fee_samples),
                max_user_value_cap_bps=int(max_user_value_cap_bps),
                max_retail_value_cap_bps=int(max_retail_value_cap_bps),
            )
        )

    status_counts: dict[str, int] = {}
    cap_bound_failures = 0
    launch_claim_failures = 0
    for rec in recommendations:
        status = str(rec["status"])
        status_counts[status] = status_counts.get(status, 0) + 1
        value_cap = rec["recommended_user_value_cap_bps"]
        notional_cap = rec["recommended_notional_cap_bps"]
        if value_cap is not None and not 0 <= int(value_cap) <= int(rec["hard_value_cap_bps"]):
            cap_bound_failures += 1
        if notional_cap is not None and not 0 <= int(notional_cap) <= BPS:
            cap_bound_failures += 1
        if rec["launch_parameter_claim"]:
            launch_claim_failures += 1

    return {
        "schema": SCHEMA,
        "source_report_schema": report["schema"],
        "min_user_fee_samples": int(min_user_fee_samples),
        "max_user_value_cap_bps": int(max_user_value_cap_bps),
        "max_retail_value_cap_bps": int(max_retail_value_cap_bps),
        "surface_count": len(recommendations),
        "status_counts": status_counts,
        "candidate_review_cap_count": status_counts.get("candidate_review_cap", 0),
        "launch_parameter_claim_count": sum(1 for rec in recommendations if rec["launch_parameter_claim"]),
        "recommendations": recommendations,
        "model_audit": {
            "cap_bound_failures": cap_bound_failures,
            "launch_claim_failures": launch_claim_failures,
            "calibration_invariant_failures": report.get("model_audit", {}).get(
                "total_calibration_invariant_failures", 0
            ),
            "total_recommendation_invariant_failures": (
                cap_bound_failures
                + launch_claim_failures
                + int(report.get("model_audit", {}).get("total_calibration_invariant_failures", 0))
            ),
        },
        "strongest_claim": (
            "Accepted user-paid receipt surfaces can be converted into review-only fee caps bounded by measured "
            "user value and hard retail/pro caps; penalty and protocol-surplus surfaces are not launch fee caps."
        ),
        "non_claims": [
            "These are not production launch parameters.",
            "Fixture samples are not enough to claim market-calibrated caps.",
            "A launch parameter requires real corpus replay, governance review, and runtime guards.",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description="Build guarded FIRE fee-cap recommendations.")
    parser.add_argument(
        "--calibration-report",
        default=str(root / "generated" / "receipt_calibration_report.json"),
    )
    parser.add_argument(
        "--output",
        default=str(root / "generated" / "fee_cap_recommendations.json"),
    )
    parser.add_argument("--min-user-fee-samples", type=int, default=1)
    parser.add_argument("--max-user-value-cap-bps", type=int, default=5_000)
    parser.add_argument("--max-retail-value-cap-bps", type=int, default=2_500)
    args = parser.parse_args(argv)

    report = json.loads(Path(args.calibration_report).read_text(encoding="utf-8"))
    recommendations = build_recommendations(
        report,
        min_user_fee_samples=int(args.min_user_fee_samples),
        max_user_value_cap_bps=int(args.max_user_value_cap_bps),
        max_retail_value_cap_bps=int(args.max_retail_value_cap_bps),
    )
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(recommendations, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "surface_count": recommendations["surface_count"],
                "candidate_review_cap_count": recommendations["candidate_review_cap_count"],
                "invariant_failures": recommendations["model_audit"]["total_recommendation_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if recommendations["model_audit"]["total_recommendation_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
