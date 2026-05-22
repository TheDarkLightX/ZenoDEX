#!/usr/bin/env python3
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated"

COMPONENTS = (
    "value_loss",
    "replay_exposure",
    "stale_data",
    "authority_drift",
    "liquidity_shock",
    "resource_load",
    "semantic_ambiguity",
)
WEIGHTS = {
    "value_loss": 7,
    "replay_exposure": 6,
    "stale_data": 5,
    "authority_drift": 6,
    "liquidity_shock": 4,
    "resource_load": 3,
    "semantic_ambiguity": 5,
}
RECOVERY_CAP = 48


@dataclass(frozen=True)
class Morphism:
    morphism_id: str
    delta: dict[str, int]
    guards: tuple[str, ...]


STATES = {
    "clean": {component: 0 for component in COMPONENTS},
    "edge_stale": {
        "value_loss": 0,
        "replay_exposure": 0,
        "stale_data": 2,
        "authority_drift": 0,
        "liquidity_shock": 0,
        "resource_load": 0,
        "semantic_ambiguity": 1,
    },
    "edge_resource": {
        "value_loss": 0,
        "replay_exposure": 1,
        "stale_data": 0,
        "authority_drift": 0,
        "liquidity_shock": 0,
        "resource_load": 2,
        "semantic_ambiguity": 0,
    },
}

MORPHISMS = (
    Morphism("stale_oracle_spike", {"stale_data": 3, "semantic_ambiguity": 1}, ("oracle_freshness_proof", "settlement_freeze")),
    Morphism("receipt_replay_attempt", {"replay_exposure": 3, "semantic_ambiguity": 1}, ("nonce_binding", "receipt_epoch_binding")),
    Morphism("authority_override_drift", {"authority_drift": 3, "semantic_ambiguity": 1}, ("override_packet_v195", "registry_quorum")),
    Morphism("liquidity_withdrawal_shock", {"liquidity_shock": 4, "value_loss": 1}, ("drawdown_receipt", "liquidity_circuit")),
    Morphism("resource_spike", {"resource_load": 5}, ("resource_budget", "rate_limit")),
    Morphism("route_ambiguity_drift", {"semantic_ambiguity": 4}, ("canonical_witness", "bruteforce_receipt")),
    Morphism("budget_leak", {"value_loss": 3}, ("budget_guard", "sink_cap")),
    Morphism(
        "catastrophic_compound",
        {
            "value_loss": 2,
            "replay_exposure": 2,
            "stale_data": 2,
            "authority_drift": 2,
            "liquidity_shock": 2,
            "resource_load": 2,
            "semantic_ambiguity": 2,
        },
        (
            "budget_guard",
            "canonical_witness",
            "drawdown_receipt",
            "liquidity_circuit",
            "nonce_binding",
            "oracle_freshness_proof",
            "override_packet_v195",
            "rate_limit",
            "receipt_epoch_binding",
            "registry_quorum",
            "resource_budget",
            "settlement_freeze",
            "sink_cap",
        ),
    ),
    Morphism("settlement_repair", {"replay_exposure": -1, "stale_data": -2, "semantic_ambiguity": -1}, ()),
)


def risk_score(vector: dict[str, int]) -> int:
    return sum(int(vector[component]) * WEIGHTS[component] for component in COMPONENTS)


def apply_delta(vector: dict[str, int], delta: dict[str, int]) -> dict[str, int]:
    return {component: max(0, int(vector[component]) + int(delta.get(component, 0))) for component in COMPONENTS}


def guards_for(morphism: Morphism, mode: str) -> tuple[str, ...]:
    if mode == "none":
        return ()
    if mode == "exact":
        return morphism.guards
    if mode == "missing_first":
        return morphism.guards[1:] if morphism.guards else ()
    if mode == "all_known":
        return tuple(sorted({guard for item in MORPHISMS for guard in item.guards}))
    raise ValueError(mode)


def evaluate(state_id: str, morphism: Morphism, mode: str) -> dict[str, object]:
    pre_vector = STATES[state_id]
    post_vector = apply_delta(pre_vector, morphism.delta)
    pre_score = risk_score(pre_vector)
    post_score = risk_score(post_vector)
    provided = guards_for(morphism, mode)
    certificate = set(morphism.guards).issubset(set(provided)) and post_score <= RECOVERY_CAP
    risk_nonincrease = post_score <= pre_score
    accepted = risk_nonincrease or certificate
    return {
        "case_id": f"{state_id}::{morphism.morphism_id}::{mode}",
        "state_id": state_id,
        "morphism_id": morphism.morphism_id,
        "guard_mode": mode,
        "pre_risk_score": pre_score,
        "post_risk_score": post_score,
        "risk_delta": post_score - pre_score,
        "post_vector": post_vector,
        "required_guards": list(morphism.guards),
        "provided_guards": list(provided),
        "risk_nonincrease": risk_nonincrease,
        "recovery_certificate": certificate,
        "accepted": accepted,
    }


def run_cycle() -> dict[str, object]:
    GENERATED.mkdir(parents=True, exist_ok=True)
    modes = ("none", "exact", "missing_first", "all_known")
    cases = [evaluate(state_id, morphism, mode) for state_id in STATES for morphism in MORPHISMS for mode in modes]
    accepted = [case for case in cases if case["accepted"]]
    rejected = [case for case in cases if not case["accepted"]]
    direct_repairs = [case for case in cases if case["risk_nonincrease"]]
    certified = [case for case in cases if case["recovery_certificate"] and case["risk_delta"] > 0]
    catastrophic = [case for case in cases if case["morphism_id"] == "catastrophic_compound" and not case["accepted"]]
    audit = {
        "accepted_increasing_without_certificate": sum(
            1 for case in accepted if case["risk_delta"] > 0 and not case["recovery_certificate"]
        ),
        "rejected_nonincreasing_transition": sum(1 for case in rejected if case["risk_nonincrease"]),
        "certified_recovery_over_cap": sum(
            1 for case in cases if case["recovery_certificate"] and case["post_risk_score"] > RECOVERY_CAP
        ),
    }
    total_failures = sum(audit.values())
    report = {
        "schema": "zenodex/math-object-innovation-v198-report/v1",
        "object": "disaster_potential_chaos_morphism_v1",
        "tier": "symbolic_state_compiler",
        "oracle_dependent": True,
        "discovery_domain": {
            "state_count": len(STATES),
            "morphism_count": len(MORPHISMS),
            "guard_mode_count": len(modes),
            "risk_components": list(COMPONENTS),
            "recovery_cap": RECOVERY_CAP,
        },
        "holdout_domain": "none; bounded chaos-morphism corpus",
        "case_count": len(cases),
        "accepted_count": len(accepted),
        "rejected_count": len(rejected),
        "direct_repair_count": len(direct_repairs),
        "certified_recovery_count": len(certified),
        "catastrophic_rejection_count": len(catastrophic),
        "risk_weights": WEIGHTS,
        "cases": cases,
        "model_audit": {**audit, "total_disaster_potential_invariant_failures": total_failures},
        "strongest_claim": (
            "A bounded chaos-morphism harness can classify transitions by a weighted disaster potential: "
            "accepted risk-increasing transitions require the morphism's recovery certificate and must remain "
            "below the recovery cap; direct repairs are accepted by potential nonincrease."
        ),
        "non_claims": [
            "The weighted potential is a research model, not a complete production risk metric.",
            "The bounded chaos corpus does not prove every disaster state unreachable.",
            "Recovery certificates still depend on truthful guard receipts.",
        ],
    }
    (GENERATED / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (GENERATED / "cases.json").write_text(json.dumps(cases, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> int:
    report = run_cycle()
    print(
        json.dumps(
            {
                "case_count": report["case_count"],
                "accepted_count": report["accepted_count"],
                "rejected_count": report["rejected_count"],
                "certified_recovery_count": report["certified_recovery_count"],
                "direct_repair_count": report["direct_repair_count"],
                "invariant_failures": report["model_audit"]["total_disaster_potential_invariant_failures"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["model_audit"]["total_disaster_potential_invariant_failures"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
