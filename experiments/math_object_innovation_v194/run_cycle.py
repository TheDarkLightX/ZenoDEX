#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"
EXPERIMENTS = ROOT.parent
MEET_ROWS_PATH = EXPERIMENTS / "math_object_innovation_v193" / "generated" / "meet_rows.json"


@dataclass(frozen=True)
class FeeLine:
    surface: str
    fee_bps: int


@dataclass(frozen=True)
class CandidateConfig:
    config_id: str
    claimed_evidence_compliant: bool
    fees: tuple[FeeLine, ...]
    overrides: tuple[dict[str, object], ...] = ()


def assumption_override(
    *,
    surface: str,
    assumption_change_id: str,
    recorded_meet_cap_bps: int | None,
    reason: str,
    approved_by_governance: bool = True,
    acknowledged_no_user_net_claim: bool = True,
) -> dict[str, object]:
    return {
        "surface": surface,
        "assumption_change_id": assumption_change_id,
        "recorded_meet_cap_bps": recorded_meet_cap_bps,
        "reason": reason,
        "approved_by_governance": approved_by_governance,
        "acknowledged_no_user_net_claim": acknowledged_no_user_net_claim,
    }


CONFIGS: tuple[CandidateConfig, ...] = (
    CandidateConfig(
        "conservative_review_config",
        True,
        (
            FeeLine("route_surplus_capture", 900),
            FeeLine("exact_out_savings_capture", 1000),
            FeeLine("pro_certificate_api", 1000),
        ),
    ),
    CandidateConfig(
        "at_meet_all_surfaces",
        True,
        (
            FeeLine("cow_batch_solver_surplus", 5000),
            FeeLine("exact_out_savings_capture", 2000),
            FeeLine("integrator_router_surface", 3000),
            FeeLine("lp_loss_cover_premium", 5000),
            FeeLine("pro_certificate_api", 3000),
            FeeLine("route_surplus_capture", 1800),
        ),
    ),
    CandidateConfig(
        "overcap_no_override_bad",
        False,
        (FeeLine("route_surplus_capture", 1801),),
    ),
    CandidateConfig(
        "overcap_claim_bad",
        True,
        (FeeLine("exact_out_savings_capture", 2001),),
    ),
    CandidateConfig(
        "valid_route_override_review",
        False,
        (FeeLine("route_surplus_capture", 2300),),
        (
            assumption_override(
                surface="route_surplus_capture",
                assumption_change_id="assumption-change/route-live-market-alpha",
                recorded_meet_cap_bps=1800,
                reason="live market launch assumption differs from fixture stress corpus",
            ),
        ),
    ),
    CandidateConfig(
        "invalid_override_missing_ack_bad",
        False,
        (FeeLine("pro_certificate_api", 3500),),
        (
            assumption_override(
                surface="pro_certificate_api",
                assumption_change_id="assumption-change/pro-api-alpha",
                recorded_meet_cap_bps=3000,
                reason="professional API pricing experiment",
                acknowledged_no_user_net_claim=False,
            ),
        ),
    ),
    CandidateConfig(
        "unknown_surface_no_override_bad",
        False,
        (FeeLine("staking_passive_yield", 100),),
    ),
    CandidateConfig(
        "unknown_surface_valid_override",
        False,
        (FeeLine("governance_court_fee", 100),),
        (
            assumption_override(
                surface="governance_court_fee",
                assumption_change_id="assumption-change/governance-court-fee-v0",
                recorded_meet_cap_bps=None,
                reason="new non-route surface has no v193 meet cap yet",
            ),
        ),
    ),
    CandidateConfig(
        "redundant_override_bad",
        False,
        (FeeLine("integrator_router_surface", 1000),),
        (
            assumption_override(
                surface="integrator_router_surface",
                assumption_change_id="assumption-change/redundant-integrator-test",
                recorded_meet_cap_bps=3000,
                reason="unneeded assumption change for a below-cap fee",
            ),
        ),
    ),
    CandidateConfig(
        "mixed_safe_and_override_review",
        False,
        (
            FeeLine("route_surplus_capture", 1000),
            FeeLine("exact_out_savings_capture", 2100),
        ),
        (
            assumption_override(
                surface="exact_out_savings_capture",
                assumption_change_id="assumption-change/exact-out-pro-alpha",
                recorded_meet_cap_bps=2000,
                reason="pro-only exact-out beta uses a separate assumption set",
            ),
        ),
    ),
)


def load_meet_caps() -> dict[str, int]:
    rows = json.loads(MEET_ROWS_PATH.read_text(encoding="utf-8"))
    if not isinstance(rows, list):
        raise ValueError("v193 meet_rows must be a list")
    caps: dict[str, int] = {}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("v193 meet row must be object")
        cap = row.get("meet_cap_bps")
        if cap is not None:
            caps[str(row["surface"])] = int(cap)
    return caps


def validate_override(override: object, *, surface: str, meet_cap_bps: int | None) -> list[str]:
    if not isinstance(override, dict):
        return ["override_not_object"]
    failures: list[str] = []
    if str(override.get("surface", "")) != surface:
        failures.append("override_surface_mismatch")
    assumption_change_id = override.get("assumption_change_id")
    if not isinstance(assumption_change_id, str) or not assumption_change_id.startswith("assumption-change/"):
        failures.append("missing_assumption_change_id")
    reason = override.get("reason")
    if not isinstance(reason, str) or len(reason.strip()) < 12:
        failures.append("missing_assumption_reason")
    if override.get("approved_by_governance") is not True:
        failures.append("missing_governance_approval")
    if override.get("acknowledged_no_user_net_claim") is not True:
        failures.append("missing_no_user_net_ack")
    recorded_cap = override.get("recorded_meet_cap_bps")
    if meet_cap_bps is None:
        if recorded_cap is not None:
            failures.append("recorded_cap_for_uncapped_surface")
    else:
        try:
            if int(recorded_cap) != int(meet_cap_bps):
                failures.append("recorded_cap_mismatch")
        except Exception:
            failures.append("recorded_cap_mismatch")
    return failures


def classify_fee_line(
    fee: FeeLine,
    *,
    meet_caps: dict[str, int],
    override: object | None,
) -> dict[str, object]:
    cap = meet_caps.get(fee.surface)
    override_failures = validate_override(override, surface=fee.surface, meet_cap_bps=cap) if override is not None else []
    override_valid = override is not None and not override_failures

    if cap is None:
        if override_valid:
            status = "ok_assumption_change_override"
            failures: list[str] = []
        else:
            status = "unknown_surface_without_valid_override"
            failures = override_failures or ["missing_override"]
    elif int(fee.fee_bps) <= int(cap):
        if override is None:
            status = "ok_under_meet_cap"
            failures = []
        else:
            status = "redundant_override"
            failures = ["redundant_override"]
    elif override_valid:
        status = "ok_assumption_change_override"
        failures = []
    else:
        status = "over_cap_without_valid_override"
        failures = override_failures or ["missing_override"]

    return {
        "surface": fee.surface,
        "fee_bps": int(fee.fee_bps),
        "meet_cap_bps": cap,
        "override_present": override is not None,
        "override_valid": override_valid,
        "status": status,
        "failures": failures,
    }


def evaluate_config(config: CandidateConfig, meet_caps: dict[str, int]) -> dict[str, object]:
    overrides_by_surface: dict[str, object] = {}
    duplicate_overrides: list[str] = []
    for override in config.overrides:
        surface = str(override.get("surface", "")) if isinstance(override, dict) else ""
        if surface in overrides_by_surface:
            duplicate_overrides.append(surface)
        overrides_by_surface[surface] = override

    checks = [
        classify_fee_line(fee, meet_caps=meet_caps, override=overrides_by_surface.get(fee.surface))
        for fee in config.fees
    ]
    used_surfaces = {fee.surface for fee in config.fees}
    stray_overrides = sorted(set(overrides_by_surface) - used_surfaces)

    config_failures: list[str] = []
    for check in checks:
        config_failures.extend(str(failure) for failure in check["failures"])
    if duplicate_overrides:
        config_failures.append("duplicate_override")
    if stray_overrides:
        config_failures.append("stray_override")

    has_assumption_override = any(check["status"] == "ok_assumption_change_override" for check in checks)
    evidence_compliant = bool(checks) and all(check["status"] == "ok_under_meet_cap" for check in checks)
    if config.claimed_evidence_compliant and not evidence_compliant:
        config_failures.append("unsafe_evidence_compliance_claim")

    accepted = not config_failures
    if accepted and evidence_compliant:
        acceptance_class = "accepted_without_override"
    elif accepted and has_assumption_override:
        acceptance_class = "accepted_with_override"
    else:
        acceptance_class = "rejected"

    return {
        "config_id": config.config_id,
        "claimed_evidence_compliant": config.claimed_evidence_compliant,
        "accepted": accepted,
        "acceptance_class": acceptance_class,
        "evidence_compliant": evidence_compliant,
        "has_assumption_override": has_assumption_override,
        "checks": checks,
        "stray_overrides": stray_overrides,
        "duplicate_overrides": duplicate_overrides,
        "config_failures": sorted(set(config_failures)),
    }


def audit_rows(rows: list[dict[str, object]]) -> dict[str, int]:
    accepted = [row for row in rows if row["accepted"]]
    accepted_without_override = [row for row in accepted if row["acceptance_class"] == "accepted_without_override"]
    accepted_with_override = [row for row in accepted if row["acceptance_class"] == "accepted_with_override"]
    rejected = [row for row in rows if not row["accepted"]]
    return {
        "accepted_without_override_fee_bound_failures": sum(
            1
            for row in accepted_without_override
            for check in row["checks"]
            if check["status"] != "ok_under_meet_cap"
        ),
        "accepted_with_override_missing_assumption_failures": sum(
            1
            for row in accepted_with_override
            for check in row["checks"]
            if check["status"] == "ok_assumption_change_override" and not check["override_valid"]
        ),
        "accepted_unsafe_evidence_claim_failures": sum(
            1 for row in accepted if row["claimed_evidence_compliant"] and not row["evidence_compliant"]
        ),
        "rejected_without_reason_failures": sum(1 for row in rejected if not row["config_failures"]),
    }


def run_cycle() -> dict[str, object]:
    GENERATED.mkdir(parents=True, exist_ok=True)
    meet_caps = load_meet_caps()
    rows = [evaluate_config(config, meet_caps) for config in CONFIGS]
    audit = audit_rows(rows)
    total_invariant_failures = sum(audit.values())

    acceptance_counts: dict[str, int] = {}
    failure_counts: dict[str, int] = {}
    for row in rows:
        acceptance_class = str(row["acceptance_class"])
        acceptance_counts[acceptance_class] = acceptance_counts.get(acceptance_class, 0) + 1
        for failure in row["config_failures"]:
            failure_key = str(failure)
            failure_counts[failure_key] = failure_counts.get(failure_key, 0) + 1

    report = {
        "schema": "zenodex/math-object-innovation-v194-report/v1",
        "object": "evidence_meet_launch_config_guard_v1",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": True,
        "discovery_domain": {
            "candidate_config_count": len(CONFIGS),
            "meet_cap_surface_count": len(meet_caps),
            "source": "v193 evidence-meet fee-cap lattice",
        },
        "holdout_domain": "none; bounded launch/config lint corpus over v193 meet caps",
        "config_count": len(rows),
        "surface_check_count": sum(len(row["checks"]) for row in rows),
        "accepted_without_override_count": acceptance_counts.get("accepted_without_override", 0),
        "accepted_with_override_count": acceptance_counts.get("accepted_with_override", 0),
        "rejected_count": acceptance_counts.get("rejected", 0),
        "evidence_compliant_config_count": sum(1 for row in rows if row["evidence_compliant"]),
        "governance_assumption_change_count": sum(
            1
            for row in rows
            if row["accepted"]
            for check in row["checks"]
            if check["status"] == "ok_assumption_change_override"
        ),
        "failure_counts": failure_counts,
        "config_rows": rows,
        "model_audit": {
            **audit,
            "total_config_invariant_failures": total_invariant_failures,
        },
        "strongest_claim": (
            "The v193 evidence-meet caps can be compiled into a fail-closed launch/config guard: "
            "a candidate fee surface is accepted only when the fee is at or below the meet cap, "
            "or a governance-approved assumption-change override explicitly records that the "
            "configuration is outside the evidence-compliant user-net claim."
        ),
        "non_claims": [
            "This is not a production launch fee schedule.",
            "Accepted-with-override configurations are not proved user-net safe by v193 evidence.",
            "The guard depends on truthful upstream meet-cap receipts and governance override records.",
        ],
    }
    (GENERATED / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (GENERATED / "config_rows.json").write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    report = run_cycle()
    print(
        json.dumps(
            {
                "config_count": report["config_count"],
                "accepted_without_override_count": report["accepted_without_override_count"],
                "accepted_with_override_count": report["accepted_with_override_count"],
                "rejected_count": report["rejected_count"],
                "invariant_failures": report["model_audit"]["total_config_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["model_audit"]["total_config_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
