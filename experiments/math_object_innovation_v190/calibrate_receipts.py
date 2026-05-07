#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

BPS = 10_000
SCHEMA = "zenodex/fire-revenue-surface-receipt/v1"
FEE_SOURCES = {"user", "protocol_surplus", "penalty"}
WASH_REJECT_BPS = 8_000


@dataclass(frozen=True)
class RevenueSurfaceReceipt:
    schema: str
    event_id: str
    surface: str
    fee_source: str
    asset: str
    notional_units: int
    measured_value_units: int
    user_fee_paid_units: int
    protocol_revenue_units: int
    direct_cost_units: int
    recurring: bool
    primary_revenue: bool
    wash_score_bps: int
    eligible_for_retail: bool


@dataclass(frozen=True)
class ReceiptEvaluation:
    receipt: RevenueSurfaceReceipt
    accepted: bool
    reject_reasons: tuple[str, ...]
    user_net_value_units: int
    net_protocol_revenue_units: int
    fee_bps_of_notional: int
    fee_bps_of_value: int
    protocol_revenue_bps_of_value: int


def floor_ratio_bps(num: int, den: int) -> int:
    if den <= 0:
        return 0
    return int(num) * BPS // int(den)


def percentile_floor(values: list[int], pct: int) -> int:
    if not values:
        return 0
    if pct <= 0:
        return min(values)
    if pct >= 100:
        return max(values)
    ordered = sorted(values)
    idx = (len(ordered) - 1) * pct // 100
    return int(ordered[idx])


def require_int(obj: dict[str, Any], key: str) -> int:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{key} must be int")
    if value < 0:
        raise ValueError(f"{key} must be non-negative")
    return int(value)


def require_bool(obj: dict[str, Any], key: str) -> bool:
    value = obj.get(key)
    if not isinstance(value, bool):
        raise ValueError(f"{key} must be bool")
    return bool(value)


def require_str(obj: dict[str, Any], key: str) -> str:
    value = obj.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{key} must be non-empty string")
    return value.strip()


def parse_receipt(obj: Any) -> RevenueSurfaceReceipt:
    if not isinstance(obj, dict):
        raise ValueError("receipt must be object")
    receipt = RevenueSurfaceReceipt(
        schema=require_str(obj, "schema"),
        event_id=require_str(obj, "event_id"),
        surface=require_str(obj, "surface"),
        fee_source=require_str(obj, "fee_source"),
        asset=require_str(obj, "asset"),
        notional_units=require_int(obj, "notional_units"),
        measured_value_units=require_int(obj, "measured_value_units"),
        user_fee_paid_units=require_int(obj, "user_fee_paid_units"),
        protocol_revenue_units=require_int(obj, "protocol_revenue_units"),
        direct_cost_units=require_int(obj, "direct_cost_units"),
        recurring=require_bool(obj, "recurring"),
        primary_revenue=require_bool(obj, "primary_revenue"),
        wash_score_bps=require_int(obj, "wash_score_bps"),
        eligible_for_retail=require_bool(obj, "eligible_for_retail"),
    )
    if receipt.schema != SCHEMA:
        raise ValueError("bad schema")
    if receipt.fee_source not in FEE_SOURCES:
        raise ValueError("bad fee_source")
    if receipt.wash_score_bps > BPS:
        raise ValueError("wash_score_bps out of range")
    return receipt


def evaluate_receipt(receipt: RevenueSurfaceReceipt) -> ReceiptEvaluation:
    reasons: list[str] = []
    if receipt.fee_source == "user" and receipt.user_fee_paid_units > receipt.measured_value_units:
        reasons.append("user_fee_exceeds_measured_value")
    if receipt.fee_source == "protocol_surplus" and receipt.protocol_revenue_units > receipt.measured_value_units:
        reasons.append("protocol_revenue_exceeds_surplus")
    if receipt.fee_source == "penalty" and receipt.primary_revenue:
        reasons.append("penalty_marked_primary")
    if receipt.wash_score_bps >= WASH_REJECT_BPS:
        reasons.append("wash_score_rejected")
    if receipt.protocol_revenue_units < receipt.direct_cost_units and receipt.primary_revenue:
        reasons.append("primary_surface_negative_net_revenue")

    user_net = int(receipt.measured_value_units) - int(receipt.user_fee_paid_units)
    net_protocol = int(receipt.protocol_revenue_units) - int(receipt.direct_cost_units)
    return ReceiptEvaluation(
        receipt=receipt,
        accepted=not reasons,
        reject_reasons=tuple(reasons),
        user_net_value_units=user_net,
        net_protocol_revenue_units=net_protocol,
        fee_bps_of_notional=floor_ratio_bps(receipt.user_fee_paid_units, receipt.notional_units),
        fee_bps_of_value=floor_ratio_bps(receipt.user_fee_paid_units, receipt.measured_value_units),
        protocol_revenue_bps_of_value=floor_ratio_bps(receipt.protocol_revenue_units, receipt.measured_value_units),
    )


def load_receipts(path: Path) -> tuple[list[RevenueSurfaceReceipt], list[dict[str, object]]]:
    receipts: list[RevenueSurfaceReceipt] = []
    malformed: list[dict[str, object]] = []
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not raw.strip():
            continue
        try:
            obj = json.loads(raw)
            receipts.append(parse_receipt(obj))
        except Exception as exc:  # malformed receipt rows are data, not process crashes.
            malformed.append({"line": lineno, "error": str(exc)})
    return receipts, malformed


def summarize_surface(evals: Iterable[ReceiptEvaluation]) -> dict[str, object]:
    rows = list(evals)
    accepted = [row for row in rows if row.accepted]
    fee_value_bps = [row.fee_bps_of_value for row in accepted if row.receipt.fee_source == "user"]
    fee_notional_bps = [row.fee_bps_of_notional for row in accepted if row.receipt.notional_units > 0]
    fee_source_counts = {source: 0 for source in sorted(FEE_SOURCES)}
    accepted_fee_source_counts = {source: 0 for source in sorted(FEE_SOURCES)}
    for row in rows:
        fee_source_counts[row.receipt.fee_source] += 1
    for row in accepted:
        accepted_fee_source_counts[row.receipt.fee_source] += 1
    return {
        "row_count": len(rows),
        "accepted_count": len(accepted),
        "rejected_count": len(rows) - len(accepted),
        "fee_source_counts": fee_source_counts,
        "accepted_fee_source_counts": accepted_fee_source_counts,
        "accepted_recurring_count": sum(1 for row in accepted if row.receipt.recurring),
        "accepted_primary_revenue_count": sum(1 for row in accepted if row.receipt.primary_revenue),
        "accepted_retail_eligible_count": sum(1 for row in accepted if row.receipt.eligible_for_retail),
        "accepted_wash_score_max_bps": max((row.receipt.wash_score_bps for row in accepted), default=0),
        "accepted_measured_value_units": sum(row.receipt.measured_value_units for row in accepted),
        "accepted_user_fee_paid_units": sum(row.receipt.user_fee_paid_units for row in accepted),
        "accepted_protocol_revenue_units": sum(row.receipt.protocol_revenue_units for row in accepted),
        "accepted_net_protocol_revenue_units": sum(row.net_protocol_revenue_units for row in accepted),
        "accepted_user_net_value_units": sum(row.user_net_value_units for row in accepted if row.receipt.fee_source == "user"),
        "observed_p50_fee_bps_of_value": percentile_floor(fee_value_bps, 50),
        "observed_p90_fee_bps_of_value": percentile_floor(fee_value_bps, 90),
        "observed_max_fee_bps_of_value": percentile_floor(fee_value_bps, 100),
        "observed_p90_fee_bps_of_notional": percentile_floor(fee_notional_bps, 90),
        "suggested_review_cap_bps_of_value": min(5_000, percentile_floor(fee_value_bps, 90)),
    }


def calibration_report(path: Path) -> dict[str, object]:
    receipts, malformed = load_receipts(path)
    evals = [evaluate_receipt(receipt) for receipt in receipts]
    accepted = [row for row in evals if row.accepted]
    rejected = [row for row in evals if not row.accepted]
    by_surface: dict[str, list[ReceiptEvaluation]] = defaultdict(list)
    for row in evals:
        by_surface[row.receipt.surface].append(row)

    primary_recurring_revenue = sum(
        row.receipt.protocol_revenue_units
        for row in accepted
        if row.receipt.primary_revenue and row.receipt.recurring
    )
    penalty_revenue = sum(row.receipt.protocol_revenue_units for row in accepted if row.receipt.fee_source == "penalty")
    gross_revenue = sum(row.receipt.protocol_revenue_units for row in accepted)
    no_worse_failures = sum(
        1
        for row in accepted
        if row.receipt.fee_source == "user" and row.user_net_value_units < 0
    )
    net_identity_failures = sum(
        1
        for row in accepted
        if row.net_protocol_revenue_units
        != row.receipt.protocol_revenue_units - row.receipt.direct_cost_units
    )

    reject_reason_counts: dict[str, int] = {}
    for row in rejected:
        for reason in row.reject_reasons:
            reject_reason_counts[reason] = reject_reason_counts.get(reason, 0) + 1

    report = {
        "schema": "zenodex/fire-revenue-surface-calibration-report/v1",
        "source_path": _display_path(path),
        "receipt_count": len(receipts),
        "malformed_count": len(malformed),
        "accepted_count": len(accepted),
        "rejected_count": len(rejected),
        "gross_protocol_revenue_units": gross_revenue,
        "net_protocol_revenue_units": sum(row.net_protocol_revenue_units for row in accepted),
        "primary_recurring_revenue_units": primary_recurring_revenue,
        "penalty_revenue_units": penalty_revenue,
        "primary_recurring_revenue_bps": floor_ratio_bps(primary_recurring_revenue, gross_revenue),
        "penalty_revenue_bps": floor_ratio_bps(penalty_revenue, gross_revenue),
        "reject_reason_counts": reject_reason_counts,
        "malformed_rows": malformed,
        "surface_summaries": {
            surface: summarize_surface(rows)
            for surface, rows in sorted(by_surface.items())
        },
        "model_audit": {
            "accepted_no_worse_failures": no_worse_failures,
            "accepted_net_identity_failures": net_identity_failures,
            "accepted_negative_gross_revenue_failures": sum(
                1 for row in accepted if row.receipt.protocol_revenue_units < 0
            ),
            "total_calibration_invariant_failures": (
                no_worse_failures
                + net_identity_failures
                + len(malformed)
            ),
        },
        "strongest_claim": (
            "This report converts receipt-backed fee events into empirical value-density caps and rejects rows "
            "where user fees exceed measured value, protocol surplus capture exceeds surplus, penalties are primary, "
            "wash score is too high, or primary revenue is negative net."
        ),
        "non_claims": [
            "This is calibration scaffolding, not live production telemetry.",
            "The sample receipts are fixtures, not market data.",
            "Observed caps should not be used as launch parameters without real corpus replay.",
        ],
    }
    return report


def _display_path(path: Path) -> str:
    root = Path(__file__).resolve().parent
    try:
        return str(path.resolve().relative_to(root))
    except ValueError:
        return str(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Calibrate FIRE revenue surfaces from JSONL receipts.")
    parser.add_argument(
        "receipt_jsonl",
        nargs="?",
        default=str(Path(__file__).resolve().parent / "sample_revenue_surface_receipts.jsonl"),
    )
    parser.add_argument(
        "--output",
        default=str(Path(__file__).resolve().parent / "generated" / "receipt_calibration_report.json"),
    )
    args = parser.parse_args(argv)

    report = calibration_report(Path(args.receipt_jsonl))
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("receipt_count", "accepted_count", "rejected_count")}, indent=2))
    return 0 if report["model_audit"]["total_calibration_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
