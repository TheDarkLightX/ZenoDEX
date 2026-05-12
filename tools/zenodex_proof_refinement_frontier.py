#!/usr/bin/env python3
"""Build a deterministic 1000-candidate ZenoDEX proof-refinement frontier.

This is a work-queue generator for proof engineering, runtime binding, and
algorithm optimization. It is intentionally ZenoDEX-wide: CPMM kernels, routing,
batch settlement, certificate verification, oracle consumers, perps, zUSD,
LP/vault accounting, ZenoProof mechanisms, and evidence plumbing.

The output is a hypothesis frontier. It does not claim that a theorem exists,
that a runtime path is safe, or that a production surface is closed. Each row is
a candidate with a falsifier, evidence command, and promotion gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SCHEMA = "zenodex.proof_refinement_frontier.v1"
CAMPAIGN_ID = "zenodex-proof-refinement-1000-v1"
REPLAY_COMMAND = "python3 tools/zenodex_proof_refinement_frontier.py --format text"


@dataclass(frozen=True)
class Lane:
    lane_id: str
    title: str
    base_impact: int
    artifacts: tuple[str, ...]
    known_gap: str
    theorem_family: str
    optimization_family: str
    runtime_boundary: str


@dataclass(frozen=True)
class GapClass:
    gap_id: str
    title: str
    priority: int
    obligation: str
    negative_knowledge: str
    falsifier_shape: str
    promotion_gate: str


@dataclass(frozen=True)
class Method:
    method_id: str
    title: str
    strength: int
    evidence_template: str
    proof_quality_risk: int


@dataclass(frozen=True)
class BindingMode:
    binding_id: str
    title: str
    value: int
    requirement: str


LANES = (
    Lane(
        "cpmm_kernel_integer_math",
        "CPMM kernel integer math",
        92,
        (
            "src/core/cpmm.py",
            "src/kernels/python/cpmm_swap_v8.py",
            "lean-mathlib/Proofs/CPMMInvariants.lean",
            "lean-mathlib/Proofs/CpmmSwapV8ExactOutMinimality.lean",
        ),
        "Lean covers important CPMM identities, while runtime kernels still need exact domain and rounding bridges for every public operation.",
        "kernel arithmetic theorem: every accepted swap preserves the declared K/fee/rounding contract over the runtime integer domain",
        "replace heuristic edge handling with exact bounded arithmetic contracts and reusable remainder ledgers",
        "kernel entrypoints plus pool admission checks",
    ),
    Lane(
        "routing_exact_out_completeness",
        "Exact-out routing and candidate completeness",
        94,
        (
            "src/core/routing.py",
            "src/core/split_routing.py",
            "lean-mathlib/Proofs/ZenoDEXExactOutManyPoolRepairedKeyCoverInterpretationSemanticBridge.lean",
            "lean-mathlib/Proofs/ZenoDEXExactOutManyPoolSelectedDomainCompleteness.lean",
        ),
        "Current exact-out proofs are strong on selected and bounded domains; the dangerous gap is omitted candidates under deployed generator rules.",
        "candidate-cover theorem: every runtime-emitted candidate set covers all routes admitted by the deployed domain contract",
        "turn expensive route search into certifiable pruning with explicit omission witnesses and regret bounds",
        "quote generator, route certificate builder, and settlement quote consumer",
    ),
    Lane(
        "batch_upba_settlement",
        "Batch clearing and UPBA settlement",
        93,
        (
            "src/core/batch_clearing.py",
            "src/kernels/dex/batch_auction_settler_v1.yaml",
            "lean-mathlib/Proofs/BatchAuctionCanonical.lean",
            "lean-mathlib/Proofs/BatchCPMMUnification.lean",
        ),
        "Sequential batch modes still carry order-dependence; UPBA is a target architecture that needs verifier-bound runtime semantics.",
        "uniform-clearing theorem: accepted batch settlement depends on the order multiset and canonical price rule, independent of list order",
        "collapse permutation search into aggregation plus bounded price-certificate verification",
        "batch settlement mode switch and accepted settlement verifier",
    ),
    Lane(
        "settlement_certificate_verifier",
        "Settlement certificate verifier",
        97,
        (
            "src/core/settlement_strong_validator.py",
            "src/core/settlement.py",
            "lean-mathlib/Proofs/ZenoDEXSettlementEndToEndCertificatePacket.lean",
            "lean-mathlib/Proofs/SettlementAlgebra.lean",
        ),
        "Strong validation replay is the right shape; the proof frontier is totality, reject-order, and exact accepted-delta binding.",
        "verifier totality theorem: every parsed certificate is accepted exactly when replayed deltas, events, and support roots match",
        "make solver output cheap to check and remove ambiguous settlement encodings before they reach application",
        "validate_operations, strong validator, support-root proof lane",
    ),
    Lane(
        "oracle_runtime_consumers",
        "Oracle consumer runtime binding",
        94,
        (
            "tools/check_zeno_oracle_critical_action_map.py",
            "tools/check_zeno_oracle_perps_snapshot_gate.py",
            "lean-mathlib/Proofs/ZenoOracleMathWitness.lean",
            "docs/ZENO_ORACLE_GOAL_COMPLETION_AUDIT.md",
        ),
        "Oracle arithmetic and disaster corpus are strong; every critical runtime consumer still needs a bound receipt showing fail-closed use.",
        "consumer-binding theorem: critical actions can consume only fresh, diverse, pessimistic oracle receipts committed to the action evidence",
        "reduce oracle risk to a small typed receipt check per consumer instead of duplicated freshness logic",
        "critical-action map, perps snapshot gate, and query-policy consumers",
    ),
    Lane(
        "perps_margin_funding_liquidation",
        "Perps margin, funding, and liquidation",
        95,
        (
            "src/core/perp_v2/engine.py",
            "src/core/perp_v2/invariants.py",
            "lean-mathlib/Proofs/PerpProtocolSafety.lean",
            "lean-mathlib/Proofs/PerpIntegerBridge.lean",
        ),
        "Perps proofs cover key safety slices; composition across funding, liquidation, margin updates, oracle snapshots, and ADL remains the main risk.",
        "perps transition theorem: every accepted account transition preserves global health, funding conservation, and liquidation authorization",
        "replace local checks with one post-transition account/global health certificate",
        "perp_v2 engine transition gate and oracle snapshot usability gate",
    ),
    Lane(
        "zusd_redemption_and_mcr",
        "zUSD redemption and MCR accounting",
        90,
        (
            "src/core/zusd.py",
            "src/core/zusd_multi_redeem_selector.py",
            "lean-mathlib/Proofs/ZUSDCollateralFlowAlgebra.lean",
            "lean-mathlib/Proofs/ZUSDMCRHeadroom.lean",
        ),
        "zUSD algebra is well represented; selector fairness, minimum debt, and integer redemption boundaries need runtime equivalence evidence.",
        "redemption theorem: selector order, partial redemption, and MCR headroom match the exact integer runtime for every admitted vault state",
        "make redemption ordering an exact cross-multiplied key and isolate all rounding into named remainder accounts",
        "vault admission, redemption selector, and multi-redeem settlement",
    ),
    Lane(
        "lp_vault_share_accounting",
        "LP and vault share accounting",
        88,
        (
            "src/state/lp.py",
            "src/kernels/dex/lp_mint_v8.yaml",
            "lean-mathlib/Proofs/LpMintOptimalBounds.lean",
            "lean-mathlib/Proofs/LPValueAlgebra.lean",
        ),
        "LP age and share math have local defenses; donation, migration, lot semantics, and root binding need one coherent position theorem.",
        "LP position theorem: accepted mints/burns preserve share fairness, age policy, committed metadata, and minimum-liquidity constraints",
        "replace ad hoc LP metadata checks with a single position-state transition object and optional lot-level refinement",
        "LPTable mutations, snapshot import, support root, and mint kernel",
    ),
    Lane(
        "zenoproof_mechanism_economics",
        "ZenoProof mechanism economics",
        87,
        (
            "tools/zenoproof_verify.py",
            "tools/zenoproof_registry_manifest.json",
            "lean-mathlib/Proofs/ProofMarketSafety.lean",
            "docs/ZENOPROOF_LIVE_PRODUCTION_GOVERNANCE_POLICY.md",
        ),
        "Proof-market safety proofs need runtime registry binding, reward caps, slashing evidence, and anti-Sybil mechanism checks.",
        "mechanism theorem: accepted proof rewards are budget-capped, registry-bound, non-pivotal under declared bonds, and slashable on falsification",
        "convert proof mining incentives into checked certificates with explicit reward and slash accounting",
        "ZenoProof verifier registry, reward payout, and governance policy gate",
    ),
    Lane(
        "evidence_registry_and_replay",
        "Evidence registry and replay discipline",
        84,
        (
            "docs/claims_registry.yaml",
            "tools/check_claims_registry.py",
            "tools/check_zeno_oracle_goal_completion_audit.py",
            "docs/PUBLIC_ASSURANCE_REPLAY.md",
        ),
        "The repository has good evidence hygiene; the remaining gap is making disputed, bounded, and runtime-active claim scopes mechanically hard to confuse.",
        "claim-scope theorem: promoted claims require live evidence, exact scope tags, replay commands, and explicit external assumptions",
        "reduce audit cost by turning claim promotion into a finite schema validation problem with proof receipts",
        "claims registry, public replay docs, and CI promotion gates",
    ),
)


GAP_CLASSES = (
    GapClass(
        "runtime_binding",
        "runtime theorem binding",
        20,
        "prove that the implementation path consumes exactly the model state the theorem mentions",
        "model-only proofs can overstate safety when adapters, parsers, or config flags drift",
        "construct a valid model witness whose runtime fields are stale, missing, or differently encoded",
        "theorem name, runtime adapter test, and receipt showing the adapter rejects model/runtime mismatch",
    ),
    GapClass(
        "integer_rounding_bridge",
        "integer rounding bridge",
        18,
        "account for every floor, ceiling, remainder, and strict inequality in the runtime domain",
        "real-valued or algebraic curves can hide jagged integer boundaries",
        "search the smallest admitted integer where the model inequality holds and runtime truncation flips it",
        "Lean or exact replay proves the integer statement, including named remainders",
    ),
    GapClass(
        "candidate_generator_completeness",
        "candidate generator completeness",
        19,
        "show that the generated candidate set covers the deployed domain or emits a bounded-regret certificate",
        "canonical-winner proofs over a candidate set do not prove the candidate generator saw the true winner",
        "build a state where the optimal candidate exists but the generator omits it without an omission receipt",
        "coverage theorem or bounded-regret certificate plus generator regression",
    ),
    GapClass(
        "compositional_trace_induction",
        "compositional trace induction",
        16,
        "lift local one-step invariants through multi-step traces and mixed action sequences",
        "each transition can be locally valid while the composition creates the exploit",
        "alternate two locally safe actions until shared metadata, timing, or capital accounting diverges",
        "induction theorem over the trace language plus stateful replay witness",
    ),
    GapClass(
        "certificate_totality",
        "certificate totality and reject order",
        17,
        "prove verifier behavior for malformed, partial, conflicting, and valid certificates",
        "a certificate checker can be sound on happy paths and ambiguous on malformed boundaries",
        "generate a minimal malformed certificate that reaches a later semantic check before a structural reject",
        "boundary corpus and total parser/checker theorem with stable reject reasons",
    ),
    GapClass(
        "generic_canonical_theorem_refactor",
        "generic canonical theorem refactor",
        13,
        "factor repeated unique-winner proofs through one finite total-order theorem",
        "bespoke canonicality proofs duplicate proof effort and create drift between optimizer surfaces",
        "mutate an optimizer key tie-break and show one proof updates while another silently diverges",
        "shared theorem plus at least two migrated optimizer instances",
    ),
    GapClass(
        "conservation_accounting_identity",
        "conservation and accounting identity",
        15,
        "strengthen nonnegative or monotone checks into exact delta and remainder identities",
        "weak invariant checks can miss value moved into untracked dust, carry, or support metadata",
        "find a trace where the final inequality holds but an unaccounted remainder changes ownership",
        "exact accounting identity with a runtime ledger regression",
    ),
    GapClass(
        "resource_bound_complexity",
        "resource-bound complexity",
        14,
        "bound candidate counts, proof checking cost, recursion depth, and witness sizes",
        "proof-carrying systems can still fail open if checking becomes too expensive or times out",
        "submit the smallest valid-looking input that crosses the declared resource envelope",
        "resource envelope test plus static size/count bound on the accepted witness language",
    ),
    GapClass(
        "snapshot_migration_replay",
        "snapshot and migration replay",
        12,
        "prove new metadata is committed, migrated, and rejected when absent under enabled policy",
        "state-root changes can be locally correct and still ambiguous across old snapshots or support proofs",
        "load a legacy snapshot with value-moving state and missing safety metadata under the new gate",
        "migration policy, snapshot roundtrip test, and state/support-root compatibility receipt",
    ),
    GapClass(
        "negative_knowledge_claim_scope",
        "negative knowledge and claim scope",
        11,
        "record the counterexamples, non-claims, and exact domain boundaries next to every promoted theorem",
        "teams repeat refuted assumptions when negative knowledge stays in chat or ignored files",
        "reintroduce a previously falsified assumption and verify the claim registry catches the scope drift",
        "claim registry entry with falsifier link, domain tag, and replay command",
    ),
)


METHODS = (
    Method(
        "lean_theorem",
        "Lean theorem",
        18,
        "lake env lean {lean_hint}",
        14,
    ),
    Method(
        "esso_smt_invariant",
        "ESSO/SMT invariant",
        16,
        "python3 -m ESSO verify-multi --profile audit {esso_hint}",
        12,
    ),
    Method(
        "python_exact_replay",
        "Python exact replay",
        14,
        "pytest -q {test_hint}",
        6,
    ),
    Method(
        "julia_rational_search",
        "Julia rational search",
        10,
        "julia {julia_hint}",
        8,
    ),
    Method(
        "stateful_property_fuzzer",
        "stateful property fuzzer",
        13,
        "python3 {fuzz_hint}",
        10,
    ),
)


BINDING_MODES = (
    BindingMode(
        "model_anchor",
        "model-level anchor",
        4,
        "state a restricted theorem or refuter target before changing runtime behavior",
    ),
    BindingMode(
        "runtime_bound",
        "runtime-bound closure",
        20,
        "connect the theorem or refuter to the exact production code path and configuration gate",
    ),
)


NON_CLAIMS = (
    "does_not_claim_1000_items_are_1000_verified_theorems",
    "does_not_claim_exhaustive_zenodex_safety",
    "does_not_claim_global_routing_optimality",
    "does_not_claim_upba_is_deployed",
    "does_not_claim_internal_ignored_proofs_are_public_assurance",
)


def _stable_int(*parts: str, modulus: int) -> int:
    joined = "\x1f".join(parts).encode("utf-8")
    digest = hashlib.sha256(joined).digest()
    return int.from_bytes(digest[:8], "big") % modulus


def _path_hint(lane: Lane, suffix: str) -> str:
    stem = lane.lane_id.replace("_", "-")
    return f"tests/{suffix}/test_{stem}.py"


def _lean_hint(lane: Lane) -> str:
    for path in lane.artifacts:
        if path.startswith("lean-mathlib/Proofs/"):
            return path
    return "lean-mathlib/Proofs"


def _evidence_command(method: Method, lane: Lane, gap: GapClass) -> str:
    return method.evidence_template.format(
        lean_hint=_lean_hint(lane),
        esso_hint=f"internal/esso/{lane.lane_id}_{gap.gap_id}.yaml",
        test_hint=_path_hint(lane, "proof_frontier"),
        julia_hint=f"experimental/math_discovery_pipeline/src/{lane.lane_id}_{gap.gap_id}.jl",
        fuzz_hint=f"tools/run_{lane.lane_id}_{gap.gap_id}_fuzzer.py",
    )


def _proposed_statement(lane: Lane, gap: GapClass, binding: BindingMode) -> str:
    return (
        f"{lane.theorem_family}. Gap obligation: {gap.obligation}. "
        f"Binding mode: {binding.requirement}."
    )


def _optimization_angle(lane: Lane, gap: GapClass) -> str:
    if gap.gap_id == "generic_canonical_theorem_refactor":
        return "compress repeated proof work into one reusable order/canonicalizer theorem."
    if gap.gap_id == "candidate_generator_completeness":
        return "replace unbounded search with coverage certificates, omission receipts, or bounded regret."
    if gap.gap_id == "resource_bound_complexity":
        return "turn worst-case runtime cost into a finite witness-size contract checked before execution."
    if gap.gap_id == "conservation_accounting_identity":
        return "upgrade monotone checks into exact ledgers, which improves debugging and audit locality."
    return lane.optimization_family


def _first_falsifier(lane: Lane, gap: GapClass, method: Method, binding: BindingMode) -> str:
    return (
        f"{gap.falsifier_shape}; run it against {lane.runtime_boundary} using {method.title} "
        f"under {binding.title}."
    )


def _scores(lane: Lane, gap: GapClass, method: Method, binding: BindingMode) -> dict[str, int]:
    novelty = 35 + _stable_int(lane.lane_id, gap.gap_id, method.method_id, binding.binding_id, modulus=35)
    proof_feasibility = 74 + method.strength - gap.priority // 2
    if gap.gap_id in {"runtime_binding", "candidate_generator_completeness", "compositional_trace_induction"}:
        proof_feasibility -= 8
    if method.method_id in {"lean_theorem", "esso_smt_invariant"} and gap.gap_id == "snapshot_migration_replay":
        proof_feasibility -= 4
    optimization_potential = 55 + _stable_int(gap.gap_id, lane.lane_id, modulus=35)
    if gap.gap_id in {
        "candidate_generator_completeness",
        "resource_bound_complexity",
        "generic_canonical_theorem_refactor",
    }:
        optimization_potential += 10
    runtime_binding_value = binding.value
    proof_quality_risk = method.proof_quality_risk + max(0, gap.priority - 14)
    if binding.binding_id == "runtime_bound":
        proof_quality_risk += 5
    if gap.gap_id in {"negative_knowledge_claim_scope", "snapshot_migration_replay"}:
        proof_quality_risk -= 4
    raw_priority = (
        lane.base_impact * 4
        + gap.priority * 11
        + method.strength * 4
        + runtime_binding_value * 7
        + novelty
        + optimization_potential
        + proof_feasibility
        - proof_quality_risk * 3
    )
    return {
        "impact": min(100, lane.base_impact + gap.priority // 3),
        "gap_closure": gap.priority,
        "proof_feasibility": max(0, min(100, proof_feasibility)),
        "optimization_potential": max(0, min(100, optimization_potential)),
        "runtime_binding_value": runtime_binding_value,
        "novelty": novelty,
        "proof_quality_risk": max(0, min(100, proof_quality_risk)),
        "priority": raw_priority,
    }


def _confidence(scores: dict[str, int], binding: BindingMode) -> float:
    base = 0.36
    base += scores["proof_feasibility"] / 500
    base += scores["runtime_binding_value"] / 400
    base -= scores["proof_quality_risk"] / 600
    if binding.binding_id == "runtime_bound":
        base -= 0.03
    return round(max(0.25, min(0.82, base)), 3)


def _atom_dependencies(lane: Lane, gap: GapClass, method: Method, binding: BindingMode) -> list[str]:
    return [
        "ZDX-PRF-P0",
        f"ZDX-PRF-LANE-{lane.lane_id}",
        f"ZDX-PRF-GAP-{gap.gap_id}",
        f"ZDX-PRF-METHOD-{method.method_id}",
        f"ZDX-PRF-BIND-{binding.binding_id}",
    ]


def _candidate(
    index: int,
    lane: Lane,
    gap: GapClass,
    method: Method,
    binding: BindingMode,
) -> dict[str, Any]:
    candidate_id = f"PRF-{index:04d}"
    atom_id = f"ZDX-{candidate_id}"
    scores = _scores(lane, gap, method, binding)
    return {
        "candidate_id": candidate_id,
        "atom_id": atom_id,
        "thought_iteration_index": index,
        "atom_type": "hypothesis",
        "dependencies": _atom_dependencies(lane, gap, method, binding),
        "depth": 2,
        "confidence": _confidence(scores, binding),
        "is_verified": False,
        "status": "hypothesis",
        "lane": lane.lane_id,
        "gap_class": gap.gap_id,
        "method": method.method_id,
        "binding_mode": binding.binding_id,
        "title": f"{lane.title}: {gap.title} via {method.title} ({binding.title})",
        "artifact_paths": list(lane.artifacts),
        "current_gap": f"{lane.known_gap} Negative knowledge: {gap.negative_knowledge}.",
        "proposed_theorem_or_refinement": _proposed_statement(lane, gap, binding),
        "optimization_angle": _optimization_angle(lane, gap),
        "assumptions": [
            "all arithmetic claims use exact integer or rational semantics",
            "the candidate remains a hypothesis until its evidence command passes",
            "runtime-bound claims require the deployed configuration to enable the checked gate",
        ],
        "first_falsifier": _first_falsifier(lane, gap, method, binding),
        "evidence_command": _evidence_command(method, lane, gap),
        "runtime_binding_needed": lane.runtime_boundary,
        "promotion_gate": gap.promotion_gate,
        "non_claims": list(NON_CLAIMS),
        "scores": scores,
    }


def generate_candidates() -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    index = 1
    for lane in LANES:
        for gap in GAP_CLASSES:
            for method in METHODS:
                for binding in BINDING_MODES:
                    candidates.append(_candidate(index, lane, gap, method, binding))
                    index += 1
    return candidates


def _rank_key(candidate: dict[str, Any]) -> tuple[int, str]:
    return (-int(candidate["scores"]["priority"]), str(candidate["candidate_id"]))


def _select_diverse(ranked: list[dict[str, Any]], *, limit: int) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    used_lanes: set[str] = set()
    used_gaps: set[str] = set()
    for candidate in ranked:
        if len(selected) >= limit:
            break
        lane = str(candidate["lane"])
        gap = str(candidate["gap_class"])
        if lane in used_lanes or gap in used_gaps:
            continue
        selected.append(candidate)
        used_lanes.add(lane)
        used_gaps.add(gap)
    for candidate in ranked:
        if len(selected) >= limit:
            break
        if candidate not in selected:
            selected.append(candidate)
    return selected


def _counts(candidates: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for candidate in candidates:
        value = str(candidate[field])
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def build_receipt(
    *,
    top_n: int = 25,
    promotion_n: int = 10,
    include_candidates: bool = False,
) -> dict[str, Any]:
    candidates = generate_candidates()
    ranked = sorted(candidates, key=_rank_key)
    top = ranked[:top_n]
    promotion = _select_diverse(ranked, limit=promotion_n)
    receipt: dict[str, Any] = {
        "schema": SCHEMA,
        "campaign_id": CAMPAIGN_ID,
        "status": "accepted",
        "aot_contract": {
            "root_atom": {
                "atom_id": "ZDX-PRF-P0",
                "atom_type": "premise",
                "content": "ZenoDEX proof-refinement search should enumerate bounded, replayable hypotheses across value-moving protocol surfaces.",
                "dependencies": [],
                "confidence": 0.99,
                "is_verified": True,
                "depth": 0,
            },
            "candidate_atom_type": "hypothesis",
            "verification_rule": "a candidate atom becomes verified only after its evidence command and promotion gate pass",
        },
        "atom_iteration_count": len(candidates),
        "candidate_count": len(candidates),
        "top_n": top_n,
        "promotion_n": promotion_n,
        "dimension_counts": {
            "lanes": len(LANES),
            "gap_classes": len(GAP_CLASSES),
            "methods": len(METHODS),
            "binding_modes": len(BINDING_MODES),
        },
        "lane_counts": _counts(candidates, "lane"),
        "gap_counts": _counts(candidates, "gap_class"),
        "method_counts": _counts(candidates, "method"),
        "binding_counts": _counts(candidates, "binding_mode"),
        "top_candidates": top,
        "top_promotion_targets": [
            {
                "candidate_id": candidate["candidate_id"],
                "title": candidate["title"],
                "lane": candidate["lane"],
                "gap_class": candidate["gap_class"],
                "method": candidate["method"],
                "binding_mode": candidate["binding_mode"],
                "priority": candidate["scores"]["priority"],
                "first_falsifier": candidate["first_falsifier"],
                "evidence_command": candidate["evidence_command"],
                "promotion_gate": candidate["promotion_gate"],
            }
            for candidate in promotion
        ],
        "not_claimed": list(NON_CLAIMS),
        "replay_command": REPLAY_COMMAND,
    }
    if include_candidates:
        receipt["all_candidates"] = ranked
    return receipt


def _markdown(receipt: dict[str, Any]) -> str:
    lines = [
        "# ZenoDEX Proof Refinement Frontier",
        "",
        f"Campaign: `{receipt['campaign_id']}`",
        "",
        "## Receipt",
        "",
        f"- status: `{receipt['status']}`",
        f"- atom_iteration_count: `{receipt['atom_iteration_count']}`",
        f"- candidate_count: `{receipt['candidate_count']}`",
        f"- replay_command: `{receipt['replay_command']}`",
        "",
        "## Top Promotion Targets",
        "",
    ]
    for row in receipt["top_promotion_targets"]:
        lines.extend(
            [
                f"### {row['candidate_id']}: {row['title']}",
                "",
                f"- priority: `{row['priority']}`",
                f"- lane: `{row['lane']}`",
                f"- gap: `{row['gap_class']}`",
                f"- method: `{row['method']}`",
                f"- binding: `{row['binding_mode']}`",
                f"- first falsifier: {row['first_falsifier']}",
                f"- evidence command: `{row['evidence_command']}`",
                f"- promotion gate: {row['promotion_gate']}",
                "",
            ]
        )
    lines.extend(["## Non-Claims", ""])
    lines.extend(f"- `{item}`" for item in receipt["not_claimed"])
    lines.append("")
    return "\n".join(lines)


def _text(receipt: dict[str, Any]) -> str:
    lines = [
        f"status = {receipt['status']}",
        f"atom_iteration_count = {receipt['atom_iteration_count']}",
        f"candidate_count = {receipt['candidate_count']}",
        f"top_n = {receipt['top_n']}",
        f"promotion_n = {receipt['promotion_n']}",
        f"dimensions = {receipt['dimension_counts']}",
    ]
    for row in receipt["top_promotion_targets"]:
        lines.append(
            f"target = {row['candidate_id']} | priority={row['priority']} | "
            f"{row['lane']} | {row['gap_class']} | {row['title']}"
        )
    return "\n".join(lines) + "\n"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text", "markdown"), default="json")
    parser.add_argument("--top-n", type=int, default=25)
    parser.add_argument("--promotion-n", type=int, default=10)
    parser.add_argument(
        "--include-candidates",
        action="store_true",
        help="include the full ranked 1000-candidate atom list in JSON output",
    )
    parser.add_argument("--output", type=Path, default=None)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.top_n <= 0:
        raise SystemExit("--top-n must be positive")
    if args.promotion_n <= 0:
        raise SystemExit("--promotion-n must be positive")
    receipt = build_receipt(
        top_n=args.top_n,
        promotion_n=args.promotion_n,
        include_candidates=args.include_candidates,
    )
    if args.format == "json":
        output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    elif args.format == "markdown":
        output = _markdown(receipt)
    else:
        output = _text(receipt)
    if args.output is not None:
        args.output.write_text(output, encoding="utf-8")
    sys.stdout.write(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
