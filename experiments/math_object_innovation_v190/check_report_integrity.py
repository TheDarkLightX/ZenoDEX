#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

import run_cycle


def _project_score(score: run_cycle.PolicyScore) -> dict[str, object]:
    return {
        "policy": score.policy,
        "survivor": score.survivor,
        "gross_protocol_revenue": score.gross_protocol_revenue,
        "net_protocol_revenue": score.net_protocol_revenue,
        "total_user_net_value": score.total_user_net_value,
        "burn_budget": score.burn_budget,
        "deflation_margin": score.deflation_margin,
        "penalty_dependency_bps": score.penalty_dependency_bps,
        "wash_profit_max": score.wash_profit_max,
        "rail_violation_count": score.rail_violation_count,
        "negative_user_surface_count": score.negative_user_surface_count,
        "score": score.score,
    }


def integrity_receipt() -> dict[str, object]:
    report_path = Path(__file__).resolve().parent / "generated" / "report.json"
    report = json.loads(report_path.read_text(encoding="utf-8"))

    policies = run_cycle.iter_grid_policies()
    scores = [run_cycle.evaluate_policy(policy) for policy in policies]
    survivors = [score for score in scores if score.survivor]
    best = max(survivors or scores, key=lambda item: item.score)
    named_scores = {score.policy: score for score in scores if score.policy in {p.name for p in run_cycle.NAMED_POLICIES}}

    checks: dict[str, bool] = {
        "candidate_policy_count": report["candidate_policy_count"] == len(scores),
        "survivor_count": report["survivor_count"] == len(survivors),
        "best_survivor": _project_score(best) == _project_score(run_cycle.PolicyScore(**{
            **{k: report["best_survivor"][k] for k in run_cycle.PolicyScore.__dataclass_fields__.keys() if k != "surfaces"},
            "surfaces": tuple(run_cycle.SurfaceResult(**surface) for surface in report["best_survivor"]["surfaces"]),
        })),
        "model_audit": report["model_audit"] == run_cycle.audit_scores(scores),
    }

    for name in ("zero_fee", "fee_surface_launch", "surplus_bot_heavy", "extractive_notional", "wash_rebate_farm", "penalty_dependency", "subsidized_passive_yield"):
        checks[f"named_policy_{name}"] = (
            _project_score(named_scores[name])
            == _project_score(run_cycle.PolicyScore(**{
                **{k: report["named_policies"][name][k] for k in run_cycle.PolicyScore.__dataclass_fields__.keys() if k != "surfaces"},
                "surfaces": tuple(run_cycle.SurfaceResult(**surface) for surface in report["named_policies"][name]["surfaces"]),
            }))
        )

    return {
        "cycle": "v190",
        "object": "revenue_surface_atlas_report_integrity_v1",
        "check_count": len(checks),
        "passed_count": sum(1 for ok in checks.values() if ok),
        "all_passed": all(checks.values()),
        "checks": checks,
        "non_claims": [
            "Report integrity replay catches stale or hand-edited report fields.",
            "It does not independently validate the economic assumptions.",
        ],
    }


def main() -> None:
    receipt = integrity_receipt()
    out = Path(__file__).resolve().parent / "generated" / "report_integrity_receipt.json"
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({k: receipt[k] for k in ("check_count", "passed_count", "all_passed")}, indent=2))
    if not receipt["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
