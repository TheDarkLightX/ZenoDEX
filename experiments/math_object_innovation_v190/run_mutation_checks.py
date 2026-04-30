#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import run_cycle


def _named_policy(name: str) -> run_cycle.RevenuePolicy:
    for policy in run_cycle.NAMED_POLICIES:
        if policy.name == name:
            return policy
    raise KeyError(name)


def _mutate_surface(
    score: run_cycle.PolicyScore,
    surface_name: str,
    **changes: int,
) -> run_cycle.PolicyScore:
    surfaces = list(score.surfaces)
    for idx, surface in enumerate(surfaces):
        if surface.surface == surface_name:
            surfaces[idx] = replace(surface, **changes)
            return replace(score, surfaces=tuple(surfaces))
    raise KeyError(surface_name)


def mutation_receipt() -> dict[str, object]:
    zero = run_cycle.evaluate_policy(_named_policy("zero_fee"))
    launch = run_cycle.evaluate_policy(_named_policy("fee_surface_launch"))
    extractive = run_cycle.evaluate_policy(_named_policy("extractive_notional"))

    mutants = {
        "negative_gross_revenue": _mutate_surface(
            zero,
            "lp_loss_cover_premium",
            protocol_revenue_gross=-250,
        ),
        "wrong_user_net_identity": _mutate_surface(
            launch,
            "route_surplus_capture",
            user_net_value=999_999,
        ),
        "wrong_net_revenue_identity": _mutate_surface(
            launch,
            "lp_loss_cover_premium",
            protocol_revenue_net=999_999,
        ),
        "sink_budget_overallocation": replace(
            launch,
            burn_budget=launch.net_protocol_revenue + 1,
            treasury_budget=launch.net_protocol_revenue + 1,
        ),
        "false_survivor_flag": replace(extractive, survivor=True),
    }

    checks: dict[str, dict[str, object]] = {}
    for name, mutant in mutants.items():
        audit = run_cycle.audit_scores([mutant])
        checks[name] = {
            "detected": audit["total_model_invariant_failures"] > 0,
            "audit": audit,
        }

    receipt = {
        "cycle": "v190",
        "object": "revenue_surface_atlas_model_mutation_checks_v1",
        "mutant_count": len(mutants),
        "detected_count": sum(1 for item in checks.values() if item["detected"]),
        "all_detected": all(bool(item["detected"]) for item in checks.values()),
        "checks": checks,
        "non_claims": [
            "Mutation checks do not prove the economics are complete.",
            "Mutation checks prove only that the current audit layer is sensitive to these known bug classes.",
        ],
    }
    return receipt


def main() -> None:
    receipt = mutation_receipt()
    out = Path(__file__).resolve().parent / "generated" / "model_mutation_receipt.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: receipt[k] for k in ("mutant_count", "detected_count", "all_detected")}, indent=2))


if __name__ == "__main__":
    main()
