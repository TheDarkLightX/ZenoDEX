#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"


@dataclass(frozen=True)
class Quest:
    quest_id: str
    reward_tokens: int
    verified_value: int
    budget_cap: int
    sybil_adjusted_cap: int
    treasury_cap: int
    proof_ok: bool
    anti_sybil_ok: bool
    receipt_scope_ok: bool
    xp_only: bool = False


QUESTS: tuple[Quest, ...] = (
    Quest("proof_mining_small", 80, 160, 120, 100, 100, True, True, True),
    Quest("disaster_witness_triage", 140, 260, 180, 160, 150, True, True, True),
    Quest("chaos_seed_reproducer", 90, 200, 130, 120, 110, True, True, True),
    Quest("liquidity_support_receipt", 220, 500, 300, 260, 240, True, True, True),
    Quest("market_maker_receipt", 180, 360, 260, 210, 190, True, True, True),
    Quest("social_hype_no_value_bad", 50, 0, 200, 200, 100, True, True, True),
    Quest("wash_loop_engagement_bad", 40, 100, 100, 0, 100, True, False, True),
    Quest("missing_proof_bad", 60, 180, 100, 90, 80, False, True, True),
    Quest("over_budget_bad", 160, 300, 150, 200, 180, True, True, True),
    Quest("over_sybil_adjusted_bad", 120, 400, 200, 90, 150, True, True, True),
    Quest("stale_receipt_scope_bad", 70, 180, 100, 90, 80, True, True, False),
    Quest("xp_only_learning_path", 0, 0, 0, 0, 0, False, False, False, True),
)


def meet_cap(quest: Quest) -> int:
    return min(
        int(quest.verified_value),
        int(quest.budget_cap),
        int(quest.sybil_adjusted_cap),
        int(quest.treasury_cap),
    )


def evaluate_quest(quest: Quest) -> dict[str, object]:
    cap = meet_cap(quest)
    proof_gates_ok = bool(quest.proof_ok and quest.anti_sybil_ok and quest.receipt_scope_ok)
    if quest.xp_only:
        status = "accepted_xp_only"
        accepted = int(quest.reward_tokens) == 0
        failures = [] if accepted else ["xp_only_token_reward"]
    elif not proof_gates_ok:
        status = "rejected_missing_proof_gate"
        accepted = False
        failures = []
        if not quest.proof_ok:
            failures.append("proof_missing")
        if not quest.anti_sybil_ok:
            failures.append("anti_sybil_missing")
        if not quest.receipt_scope_ok:
            failures.append("receipt_scope_missing")
    elif int(quest.reward_tokens) <= cap:
        status = "accepted_token_reward"
        accepted = True
        failures = []
    else:
        status = "rejected_over_meet_cap"
        accepted = False
        failures = ["reward_exceeds_meet_cap"]

    return {
        "quest_id": quest.quest_id,
        "reward_tokens": int(quest.reward_tokens),
        "verified_value": int(quest.verified_value),
        "budget_cap": int(quest.budget_cap),
        "sybil_adjusted_cap": int(quest.sybil_adjusted_cap),
        "treasury_cap": int(quest.treasury_cap),
        "meet_cap": cap,
        "proof_ok": quest.proof_ok,
        "anti_sybil_ok": quest.anti_sybil_ok,
        "receipt_scope_ok": quest.receipt_scope_ok,
        "proof_gates_ok": proof_gates_ok,
        "xp_only": quest.xp_only,
        "accepted": accepted,
        "status": status,
        "failures": failures,
        "net_verified_surplus": int(quest.verified_value) - int(quest.reward_tokens),
    }


def run_cycle() -> dict[str, object]:
    GENERATED.mkdir(parents=True, exist_ok=True)
    rows = [evaluate_quest(quest) for quest in QUESTS]
    accepted = [row for row in rows if row["accepted"]]
    token_rewards = [row for row in accepted if row["status"] == "accepted_token_reward"]
    xp_only = [row for row in accepted if row["status"] == "accepted_xp_only"]
    rejected = [row for row in rows if not row["accepted"]]
    failure_counts: dict[str, int] = {}
    for row in rows:
        for failure in row["failures"]:
            failure_counts[str(failure)] = failure_counts.get(str(failure), 0) + 1
    audit = {
        "accepted_token_reward_over_meet_cap": sum(
            1 for row in token_rewards if int(row["reward_tokens"]) > int(row["meet_cap"])
        ),
        "accepted_token_reward_missing_gate": sum(1 for row in token_rewards if not row["proof_gates_ok"]),
        "accepted_token_reward_negative_user_value": sum(
            1 for row in token_rewards if int(row["net_verified_surplus"]) < 0
        ),
        "xp_only_token_reward_failures": sum(
            1 for row in xp_only if int(row["reward_tokens"]) != 0
        ),
        "rejected_without_reason": sum(1 for row in rejected if not row["failures"]),
    }
    total_failures = sum(audit.values())
    report = {
        "schema": "zenodex/math-object-innovation-v197-report/v1",
        "object": "proof_gated_gamification_budget_v1",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": True,
        "discovery_domain": {
            "quest_count": len(QUESTS),
            "cap_components": [
                "verified_value",
                "budget_cap",
                "sybil_adjusted_cap",
                "treasury_cap",
            ],
            "proof_gates": ["proof_ok", "anti_sybil_ok", "receipt_scope_ok"],
        },
        "holdout_domain": "none; bounded gamification quest corpus",
        "quest_count": len(rows),
        "accepted_count": len(accepted),
        "accepted_token_reward_count": len(token_rewards),
        "accepted_xp_only_count": len(xp_only),
        "rejected_count": len(rejected),
        "failure_counts": failure_counts,
        "quest_rows": rows,
        "model_audit": {
            **audit,
            "total_gamification_budget_invariant_failures": total_failures,
        },
        "strongest_claim": (
            "Gamification token rewards can be bounded by the meet of verified value, budget, "
            "sybil-adjusted capacity, and treasury cap; non-token XP can remain available even when "
            "proof gates are absent."
        ),
        "non_claims": [
            "This is not a production reward schedule.",
            "The model does not prove proof receipts are truthful.",
            "The model does not prove token price appreciation or user retention.",
        ],
    }
    (GENERATED / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (GENERATED / "quest_rows.json").write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    report = run_cycle()
    print(
        json.dumps(
            {
                "quest_count": report["quest_count"],
                "accepted_token_reward_count": report["accepted_token_reward_count"],
                "accepted_xp_only_count": report["accepted_xp_only_count"],
                "rejected_count": report["rejected_count"],
                "invariant_failures": report["model_audit"]["total_gamification_budget_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["model_audit"]["total_gamification_budget_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
