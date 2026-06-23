#!/usr/bin/env python3
"""Run a deterministic 1000-node ZenoDEX imagination campaign.

The campaign is a hypothesis generator. It does not close any disaster state by
itself. It produces a stable, replayable frontier of Tau Net / Tau Lang aligned
candidate failures, each with a bounded game surface, attack query, mitigation
sketch, evidence lane, and explicit non-claim.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SCHEMA = "zenodex.aot_imagination_campaign.v1"
CAMPAIGN_ID = "zenodex-aot-1000-tau-net-v1"
REPLAY_COMMAND = "python3 tools/zenodex_aot_imagination_campaign.py --format text"


@dataclass(frozen=True)
class Surface:
    surface_id: str
    title: str
    base_impact: int
    runtime_adapter: str
    state_variables: tuple[str, ...]


@dataclass(frozen=True)
class Axis:
    axis_id: str
    title: str
    impact_delta: int
    evidence_lane: str
    manifest_axis: str
    proof_shape: str


@dataclass(frozen=True)
class Adversary:
    adversary_id: str
    title: str
    capability: str
    capability_score: int
    bonded: bool


@dataclass(frozen=True)
class Timing:
    timing_id: str
    title: str
    timing_score: int
    chronology: str


SURFACES = (
    Surface(
        "tau_lang_policy_admission",
        "Tau Lang policy admission",
        88,
        "Tau policy parser plus host-side bounded-fragment admission gate",
        ("policy_hash", "input_flags", "resource_bound", "parser_version"),
    ),
    Surface(
        "oracle_critical_action",
        "O3 oracle critical action",
        95,
        "critical-action map plus accepted aggregate receipt gate",
        ("query_id", "value_hash", "freshness_epoch", "consumer_profile"),
    ),
    Surface(
        "reporter_economics",
        "Reporter economics and slashing",
        90,
        "reporter economics replay plus unbonding cooldown/tombstone gate",
        ("reporter_id", "bond_e8", "dispute_id", "slashable_balance_e8"),
    ),
    Surface(
        "governance_amendment",
        "Governance amendment activation",
        92,
        "governance receipt checker plus rule-precedence registry",
        ("proposal_id", "policy_root", "activation_epoch", "precedence_edge"),
    ),
    Surface(
        "zenoproof_registry",
        "ZenoProof verifier registry",
        89,
        "ZenoProof registry root plus verifier policy binding",
        ("proof_id", "verifier_id", "policy_root", "toolchain_id"),
    ),
    Surface(
        "upba_batch_clearing",
        "UPBA batch clearing",
        87,
        "uniform clearing certificate verifier",
        ("batch_id", "order_multiset_hash", "price_vector", "fill_vector"),
    ),
    Surface(
        "quote_receipt_settlement",
        "Quote receipt settlement",
        86,
        "quote receipt freshness and pool snapshot binding gate",
        ("quote_id", "pool_snapshot_hash", "expiry_epoch", "settlement_id"),
    ),
    Surface(
        "perps_funding_liquidation",
        "Perps funding and liquidation",
        91,
        "perps snapshot usability gate plus liquidation policy receipt",
        ("account_id", "funding_index", "margin_health", "oracle_snapshot_id"),
    ),
    Surface(
        "collateral_admission",
        "Collateral admission",
        88,
        "collateral dependency graph admission checker",
        ("asset_id", "dependency_root", "oracle_source", "risk_tier"),
    ),
    Surface(
        "replay_receipt_dag",
        "Replay receipt DAG",
        94,
        "terminal receipt DAG checker plus artifact store replay",
        ("receipt_id", "parent_ids", "artifact_hash", "state_root"),
    ),
)

AXES = (
    Axis(
        "schema_bounds",
        "schema bounds",
        8,
        "boundary concolic replay",
        "proof_timeout_treated_as_success",
        "total parser theorem or finite malformed-input corpus",
    ),
    Axis(
        "time_freshness",
        "time freshness",
        9,
        "stateful sequence replay",
        "stale_read_used_for_critical_action",
        "monotone epoch/freshness preservation lemma",
    ),
    Axis(
        "value_binding",
        "value binding",
        10,
        "receipt mismatch replay",
        "wrong_value_hash_consumed_by_action",
        "content-hash equality implies consumed value equality",
    ),
    Axis(
        "precedence",
        "rule precedence",
        8,
        "Tau policy pair replay",
        "governance_policy_downgrade",
        "precedence resolution totality for registered rule pairs",
    ),
    Axis(
        "resource_budget",
        "resource budget",
        9,
        "bounded verifier replay",
        "proof_timeout_treated_as_success",
        "accepted artifact implies resource envelope membership",
    ),
    Axis(
        "economic_margin",
        "economic margin",
        7,
        "integer/rational mechanism replay",
        "reward_budget_overdraft",
        "budget conservation plus loss cap theorem",
    ),
    Axis(
        "independence",
        "source/proof independence",
        8,
        "quorum diversity replay",
        "source_cartel_collapses_quorum",
        "distinct operator/source lower-bound theorem",
    ),
    Axis(
        "canonicalization",
        "canonicalization",
        7,
        "hash-stability replay",
        "terminal_graph_authorization_mismatch",
        "canonical bytes injectivity over validated domain",
    ),
    Axis(
        "liveness",
        "liveness under guarded progress",
        6,
        "bounded temporal model",
        "open_dispute_feeds_critical_read",
        "eventually-resolved under bounded fair scheduler",
    ),
    Axis(
        "cross_module_sync",
        "cross-module sync",
        9,
        "split-brain replay",
        "cross_module_split_brain_divergence",
        "shared-world binding lemma",
    ),
)

ADVERSARIES = (
    Adversary("unbonded_spammer", "unbonded spammer", "submits malformed or high-cardinality inputs", 6, False),
    Adversary("bonded_reporter", "bonded reporter", "submits reports and times disputes/unbonding", 8, True),
    Adversary("source_cartel", "source cartel", "coordinates sources/operators under one economic actor", 9, True),
    Adversary("governance_operator", "governance operator", "proposes and sequences policy changes", 8, True),
    Adversary("strategic_trader", "strategic trader", "selects orders, quotes, timing, and collateral wrappers", 7, False),
)

TIMINGS = (
    Timing("single_epoch", "single epoch", 4, "all evidence and action attempts occur in one epoch"),
    Timing("cross_epoch", "cross epoch", 8, "setup, evidence drift, and action consumption cross epoch boundaries"),
)

TAU_NON_CLAIMS = (
    "does_not_claim_exhaustive_production_disaster_search",
    "does_not_claim_full_tau_net_consensus_safety",
    "does_not_claim_global_tau_lang_solver_complexity_bound",
    "does_not_claim_live_oracle_network_safety",
)


def _stable_int(*parts: str, modulus: int) -> int:
    joined = "\x1f".join(parts).encode("utf-8")
    digest = hashlib.sha256(joined).digest()
    return int.from_bytes(digest[:8], "big") % modulus


def _classify_candidate(surface: Surface, axis: Axis, adversary: Adversary, timing: Timing) -> dict[str, Any]:
    novelty = 40 + _stable_int(surface.surface_id, axis.axis_id, adversary.adversary_id, timing.timing_id, modulus=35)
    impact = min(100, surface.base_impact + axis.impact_delta + timing.timing_score // 2)
    tau_fit = 100
    tractability = 78 - (axis.impact_delta // 2) - (timing.timing_score // 4)
    if axis.axis_id in {"schema_bounds", "canonicalization", "value_binding"}:
        tractability += 8
    if surface.surface_id in {"tau_lang_policy_admission", "governance_amendment"}:
        tractability -= 5
    evidence_potential = 70 + _stable_int(axis.axis_id, surface.surface_id, modulus=24)
    if axis.evidence_lane in {"receipt mismatch replay", "hash-stability replay", "bounded verifier replay"}:
        evidence_potential += 4
    overclaim_risk = 12 + _stable_int(adversary.adversary_id, axis.axis_id, modulus=30)
    if axis.axis_id in {"liveness", "resource_budget", "precedence"}:
        overclaim_risk += 18
    if surface.surface_id in {"upba_batch_clearing", "tau_lang_policy_admission"}:
        overclaim_risk += 8
    raw_score = (
        impact * 3
        + novelty
        + tau_fit
        + evidence_potential * 2
        + tractability
        + adversary.capability_score * 3
        + timing.timing_score
        - overclaim_risk * 2
    )
    return {
        "impact": impact,
        "novelty": novelty,
        "tau_fit": tau_fit,
        "tractability": max(0, min(100, tractability)),
        "evidence_potential": max(0, min(100, evidence_potential)),
        "overclaim_risk": max(0, min(100, overclaim_risk)),
        "score": raw_score,
    }


def _attack_query(surface: Surface, axis: Axis, adversary: Adversary, timing: Timing) -> str:
    return (
        f"exists trace where {adversary.adversary_id} perturbs {surface.surface_id}.{axis.axis_id} "
        f"under {timing.timing_id} timing and a critical consumer accepts a state that should be rejected"
    )


def _mitigation(surface: Surface, axis: Axis) -> str:
    return (
        f"bind {axis.title} at {surface.runtime_adapter}; reject missing, stale, non-canonical, "
        "or out-of-policy evidence before optimization or settlement"
    )


def _promotion_gate(axis: Axis) -> str:
    if axis.evidence_lane == "bounded temporal model":
        return "bounded TLA/Tau trace plus replay witness and explicit fairness assumptions"
    if axis.evidence_lane == "integer/rational mechanism replay":
        return "exact arithmetic replay with positive and mitigated negative cases"
    if axis.evidence_lane == "Tau policy pair replay":
        return "Tau policy replay for both conflict and precedence cases"
    if axis.evidence_lane == "bounded verifier replay":
        return "resource-budget replay that rejects timeout or over-budget verifier output"
    return f"{axis.evidence_lane} with a focused pytest regression"


def _first_falsifier(surface: Surface, axis: Axis, adversary: Adversary, timing: Timing) -> str:
    return (
        f"construct the smallest {timing.timing_id} trace where {surface.state_variables[0]} changes "
        f"but the {axis.axis_id} guard still accepts"
    )


def _candidate(index: int, surface: Surface, axis: Axis, adversary: Adversary, timing: Timing) -> dict[str, Any]:
    scores = _classify_candidate(surface, axis, adversary, timing)
    atom_id = f"AOT-{index:04d}"
    return {
        "atom_id": atom_id,
        "status": "hypothesis",
        "surface": surface.surface_id,
        "axis": axis.axis_id,
        "adversary": adversary.adversary_id,
        "timing": timing.timing_id,
        "title": f"{surface.title}: {axis.title} under {adversary.title} ({timing.title})",
        "game_surface": {
            "players": ["protocol", adversary.adversary_id, "honest_consumer"],
            "actions": ["submit", "admit", "verify", "consume", "reject"],
            "information": "bounded local receipts and declared Tau Net chronology",
            "state_variables": list(surface.state_variables),
            "payoff": "attacker gains value, liveness leverage, or authority if a bad state is accepted",
        },
        "attack_query": _attack_query(surface, axis, adversary, timing),
        "bounded_model": {
            "tau_native": True,
            "uses_evm_assumptions": False,
            "capability": adversary.capability,
            "chronology": timing.chronology,
            "excluded_assumptions": ["gas_war", "1_wei_evm_semantics", "flash_loan_atomicity"],
        },
        "mitigation": _mitigation(surface, axis),
        "runtime_adapter_path": surface.runtime_adapter,
        "evidence_lane": axis.evidence_lane,
        "manifest_axis": axis.manifest_axis,
        "proof_shape": axis.proof_shape,
        "first_falsifier_24h": _first_falsifier(surface, axis, adversary, timing),
        "promotion_gate": _promotion_gate(axis),
        "non_claims": list(TAU_NON_CLAIMS),
        "scores": scores,
    }


def generate_candidates() -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    index = 1
    for surface in SURFACES:
        for axis in AXES:
            for adversary in ADVERSARIES:
                for timing in TIMINGS:
                    candidates.append(_candidate(index, surface, axis, adversary, timing))
                    index += 1
    return candidates


def _rank_key(candidate: dict[str, Any]) -> tuple[int, str]:
    return (-int(candidate["scores"]["score"]), str(candidate["atom_id"]))


def _select_diverse_targets(ranked: list[dict[str, Any]], *, limit: int) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    used_surfaces: set[str] = set()
    used_axes: set[str] = set()
    for candidate in ranked:
        if len(selected) >= limit:
            break
        surface = str(candidate["surface"])
        axis = str(candidate["axis"])
        if surface in used_surfaces or axis in used_axes:
            continue
        selected.append(candidate)
        used_surfaces.add(surface)
        used_axes.add(axis)
    for candidate in ranked:
        if len(selected) >= limit:
            break
        if candidate not in selected:
            selected.append(candidate)
    return selected


def build_receipt(*, top_n: int = 20) -> dict[str, Any]:
    candidates = generate_candidates()
    ranked = sorted(candidates, key=_rank_key)
    top = ranked[:top_n]
    axis_counts: dict[str, int] = {}
    surface_counts: dict[str, int] = {}
    evidence_counts: dict[str, int] = {}
    for candidate in candidates:
        axis_counts[candidate["axis"]] = axis_counts.get(candidate["axis"], 0) + 1
        surface_counts[candidate["surface"]] = surface_counts.get(candidate["surface"], 0) + 1
        evidence_counts[candidate["evidence_lane"]] = evidence_counts.get(candidate["evidence_lane"], 0) + 1

    rejected_evmism_count = sum(
        1
        for candidate in candidates
        if candidate["bounded_model"]["uses_evm_assumptions"]
    )
    diverse_targets = _select_diverse_targets(ranked, limit=5)
    top_promotion_targets = [
        {
            "atom_id": candidate["atom_id"],
            "title": candidate["title"],
            "first_falsifier_24h": candidate["first_falsifier_24h"],
            "promotion_gate": candidate["promotion_gate"],
            "runtime_adapter_path": candidate["runtime_adapter_path"],
            "score": candidate["scores"]["score"],
        }
        for candidate in diverse_targets
    ]
    return {
        "schema": SCHEMA,
        "campaign_id": CAMPAIGN_ID,
        "status": "accepted",
        "candidate_count": len(candidates),
        "top_n": top_n,
        "dimension_counts": {
            "surfaces": len(SURFACES),
            "axes": len(AXES),
            "adversaries": len(ADVERSARIES),
            "timings": len(TIMINGS),
        },
        "axis_counts": dict(sorted(axis_counts.items())),
        "surface_counts": dict(sorted(surface_counts.items())),
        "evidence_lane_counts": dict(sorted(evidence_counts.items())),
        "rejected_evmism_count": rejected_evmism_count,
        "top_candidates": top,
        "top_promotion_targets": top_promotion_targets,
        "not_claimed": list(TAU_NON_CLAIMS),
        "replay_command": REPLAY_COMMAND,
    }


def _markdown(receipt: dict[str, Any]) -> str:
    lines = [
        "# ZenoDEX AoT 1000 Imagination Campaign",
        "",
        f"Campaign: `{receipt['campaign_id']}`",
        "",
        "## Receipt",
        "",
        f"- status: `{receipt['status']}`",
        f"- candidate_count: `{receipt['candidate_count']}`",
        f"- rejected_evmism_count: `{receipt['rejected_evmism_count']}`",
        f"- replay_command: `{receipt['replay_command']}`",
        "",
        "## Top Promotion Targets",
        "",
    ]
    for row in receipt["top_promotion_targets"]:
        lines.extend(
            [
                f"### {row['atom_id']}: {row['title']}",
                "",
                f"- score: `{row['score']}`",
                f"- first falsifier: {row['first_falsifier_24h']}",
                f"- promotion gate: {row['promotion_gate']}",
                f"- runtime adapter: {row['runtime_adapter_path']}",
                "",
            ]
        )
    lines.extend(["## Non-Claims", ""])
    lines.extend(f"- `{item}`" for item in receipt["not_claimed"])
    lines.append("")
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text", "markdown"), default="json")
    parser.add_argument("--top-n", type=int, default=20)
    parser.add_argument("--output", type=Path, default=None)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.top_n <= 0:
        raise SystemExit("--top-n must be positive")
    receipt = build_receipt(top_n=args.top_n)
    if args.format == "json":
        output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    elif args.format == "markdown":
        output = _markdown(receipt)
    else:
        lines = [
            f"status = {receipt['status']}",
            f"candidate_count = {receipt['candidate_count']}",
            f"top_n = {receipt['top_n']}",
            f"rejected_evmism_count = {receipt['rejected_evmism_count']}",
        ]
        for row in receipt["top_promotion_targets"]:
            lines.append(f"target = {row['atom_id']} | score={row['score']} | {row['title']}")
        output = "\n".join(lines) + "\n"
    if args.output is not None:
        args.output.write_text(output, encoding="utf-8")
    sys.stdout.write(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
