#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_tau_breakthrough_specs_20260627"
REPORT_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_TAU_BREAKTHROUGH_SPECS_20260627.md"
SPEC_ROOT = REPO_ROOT / "src" / "tau_specs" / "recommended"


@dataclass(frozen=True)
class Case:
    case_id: str
    step: dict[str, int]
    expected: dict[str, int]
    rationale: str


@dataclass(frozen=True)
class CandidateSpec:
    spec_id: str
    title: str
    spec_path: Path
    kind: str
    breakthrough_track: str
    value_score: int
    novelty_score: int
    projected_facts: int
    direct_bv_ops: int
    profile_budget_s: float
    frontier_note: str
    formal_obligations: tuple[str, ...]
    non_claims: tuple[str, ...]
    source: str
    cases: tuple[Case, ...]


def _frontier_menu_source() -> str:
    return """# Frontier Certificate Menu v1 - Tau Host-Projected Optimizer Envelope
#
# MUTABILITY: IMMUTABLE
# UPDATABLE_PARAMS: none
# PURPOSE:
#   A compact menu for frontier optimizer certificates. The host proves or
#   computes data-heavy facts; Tau combines them into a fail-closed admission
#   envelope. This lets route, oracle, AB-ordering, and CoW tracks share the
#   same proof-surface shape.
#
# Stream mapping:
# i1  = active_request
# i2  = host_facts_bound
# i3  = canonical_winner_or_interval_ok
# i4  = coverage_ok
# i5  = resource_budget_ok
# i6  = replay_or_trace_ok
# i7  = fallback_deterministic_or_explicit_failure_ok
# i8  = no_authority_effect
# i9  = trace_nonvacuous
# i10 = mode_route
# i11 = mode_oracle
# i12 = mode_ab_or_cow
# o1  = one_hot_mode_ok
# o2  = core_certificate_ok
# o3  = authority_boundary_ok
# o4  = frontier_candidate_admit
# o5  = inactive_safe

set charvar off

is1(x : sbf) := (x = 1:sbf).
one_hot3(a : sbf, b : sbf, c : sbf) := (is1(a) && !is1(b) && !is1(c)) || (!is1(a) && is1(b) && !is1(c)) || (!is1(a) && !is1(b) && is1(c)).
core_ok(host : sbf, canon : sbf, cover : sbf, budget : sbf, replay : sbf, nonvacuous : sbf) := is1(host) && is1(canon) && is1(cover) && is1(budget) && is1(replay) && is1(nonvacuous).
boundary_ok(fallback_ok : sbf, no_authority : sbf) := is1(fallback_ok) && is1(no_authority).
frontier_ok(active : sbf, host : sbf, canon : sbf, cover : sbf, budget : sbf, replay : sbf, fallback_ok : sbf, no_authority : sbf, nonvacuous : sbf, mode_route : sbf, mode_oracle : sbf, mode_ab_or_cow : sbf) := is1(active) && one_hot3(mode_route, mode_oracle, mode_ab_or_cow) && core_ok(host, canon, cover, budget, replay, nonvacuous) && boundary_ok(fallback_ok, no_authority).

always
  (o1[t]:sbf = 1:sbf <-> one_hot3(i10[t]:sbf, i11[t]:sbf, i12[t]:sbf)) &&
  (o2[t]:sbf = 1:sbf <-> core_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i9[t]:sbf)) &&
  (o3[t]:sbf = 1:sbf <-> boundary_ok(i7[t]:sbf, i8[t]:sbf)) &&
  (o4[t]:sbf = 1:sbf <-> frontier_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf, i12[t]:sbf)) &&
  (o5[t]:sbf = 1:sbf <-> (!is1(i1[t]:sbf) && is1(i8[t]:sbf))).
"""


def _route_dominance_source() -> str:
    return """# Route Dominance Frontier Envelope v1
#
# PURPOSE:
#   Guard a dominance-pruned exact-out route search. The expensive route search,
#   integer fee rounding, and quote replay stay in host/kernel code. Tau checks
#   that every proof-surface fact required by the pruned certificate is present.
#
# Stream mapping:
# i1  = route_request_active
# i2  = selected_domain_nonempty
# i3  = dominance_relation_host_checked
# i4  = every_pruned_label_has_kept_dominator
# i5  = argmin_stream_certificate_ok
# i6  = projection_cover_full_domain_ok
# i7  = exact_quote_replay_ok
# i8  = rounding_model_bound_ok
# i9  = resource_budget_ok
# i10 = fallback_available_or_explicit_failure
# i11 = no_settlement_authority
# o1  = dominance_cover_ok
# o2  = certificate_path_ok
# o3  = fallback_boundary_ok
# o4  = route_frontier_ok
# o5  = inactive_safe

set charvar off

is1(x : sbf) := (x = 1:sbf).
dominance_cover_ok(checked : sbf, dominated : sbf) := is1(checked) && is1(dominated).
certificate_path_ok(domain_nonempty : sbf, argmin_ok : sbf, projection_cover_ok : sbf, quote_replay_ok : sbf, rounding_ok : sbf, budget_ok : sbf) := is1(domain_nonempty) && is1(argmin_ok) && is1(projection_cover_ok) && is1(quote_replay_ok) && is1(rounding_ok) && is1(budget_ok).
fallback_boundary_ok(fallback_ok : sbf, no_authority : sbf) := is1(fallback_ok) && is1(no_authority).
route_ok(active : sbf, domain_nonempty : sbf, checked : sbf, dominated : sbf, argmin_ok : sbf, projection_cover_ok : sbf, quote_replay_ok : sbf, rounding_ok : sbf, budget_ok : sbf, fallback_ok : sbf, no_authority : sbf) := is1(active) && dominance_cover_ok(checked, dominated) && certificate_path_ok(domain_nonempty, argmin_ok, projection_cover_ok, quote_replay_ok, rounding_ok, budget_ok) && fallback_boundary_ok(fallback_ok, no_authority).

always
  (o1[t]:sbf = 1:sbf <-> dominance_cover_ok(i3[t]:sbf, i4[t]:sbf)) &&
  (o2[t]:sbf = 1:sbf <-> certificate_path_ok(i2[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf)) &&
  (o3[t]:sbf = 1:sbf <-> fallback_boundary_ok(i10[t]:sbf, i11[t]:sbf)) &&
  (o4[t]:sbf = 1:sbf <-> route_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf)) &&
  (o5[t]:sbf = 1:sbf <-> (!is1(i1[t]:sbf) && is1(i11[t]:sbf))).
"""


def _oracle_polytope_source() -> str:
    return """# Oracle Polytope Frontier Envelope v1
#
# PURPOSE:
#   Guard an oracle dispute-game interval compiler. The host computes exact
#   integer feasibility intervals and point-verifier parity. Tau checks the
#   interval proof surface, external-assumption disclosure, and authority rail.
#
# Stream mapping:
# i1  = oracle_param_update_requested
# i2  = interval_nonempty
# i3  = honest_challenge_profitable_interval_ok
# i4  = frivolous_dispute_deterrence_interval_ok
# i5  = slash_covers_cheat_gain_interval_ok
# i6  = point_verifier_parity_ok
# i7  = all_boundary_walls_checked
# i8  = mev_assumption_declared
# i9  = probability_assumption_declared
# i10 = no_oracle_update_authority
# i11 = fail_closed_default_ok
# o1  = interval_feasible_ok
# o2  = parity_and_boundary_ok
# o3  = external_assumptions_ok
# o4  = authority_ok
# o5  = oracle_polytope_guard_ok

set charvar off

is1(x : sbf) := (x = 1:sbf).
interval_feasible_ok(nonempty : sbf, honest_ok : sbf, frivolous_ok : sbf, slash_ok : sbf) := is1(nonempty) && is1(honest_ok) && is1(frivolous_ok) && is1(slash_ok).
parity_boundary_ok(parity_ok : sbf, boundary_ok : sbf) := is1(parity_ok) && is1(boundary_ok).
external_assumptions_ok(mev_declared : sbf, prob_declared : sbf) := is1(mev_declared) && is1(prob_declared).
authority_ok(no_update_authority : sbf, fail_closed_default : sbf) := is1(no_update_authority) && is1(fail_closed_default).
oracle_ok(active : sbf, nonempty : sbf, honest_ok : sbf, frivolous_ok : sbf, slash_ok : sbf, parity_ok : sbf, boundary_checked : sbf, mev_declared : sbf, prob_declared : sbf, no_update_authority : sbf, fail_closed_default : sbf) := is1(active) && interval_feasible_ok(nonempty, honest_ok, frivolous_ok, slash_ok) && parity_boundary_ok(parity_ok, boundary_checked) && external_assumptions_ok(mev_declared, prob_declared) && authority_ok(no_update_authority, fail_closed_default).

always
  (o1[t]:sbf = 1:sbf <-> interval_feasible_ok(i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf)) &&
  (o2[t]:sbf = 1:sbf <-> parity_boundary_ok(i6[t]:sbf, i7[t]:sbf)) &&
  (o3[t]:sbf = 1:sbf <-> external_assumptions_ok(i8[t]:sbf, i9[t]:sbf)) &&
  (o4[t]:sbf = 1:sbf <-> authority_ok(i10[t]:sbf, i11[t]:sbf)) &&
  (o5[t]:sbf = 1:sbf <-> oracle_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf)).
"""


def _ab_cow_source() -> str:
    return """# AB/CoW Exact Solver Envelope v1
#
# PURPOSE:
#   Cover the two algorithm work items from the TauSpec frontier report:
#   1. AB ordering: exact brute force for small batches, full-state subset DP for
#      larger bounded batches, deterministic fallback on state-cap exhaustion.
#   2. CoW matching: exact assignment for uncoupled sender balances, fail-closed
#      fallback when grouped capacity constraints appear.
#
# Stream mapping:
# i1  = optimizer_active
# i2  = mode_ab_ordering
# i3  = mode_cow_matching
# i4  = objective_binding_ok
# i5  = full_state_or_uncoupled_capacity_ok
# i6  = brute_dp_assignment_parity_ok
# i7  = deterministic_tie_ok
# i8  = fallback_limit_respected
# i9  = no_settlement_authority
# i10 = balance_slippage_constraints_ok
# i11 = resource_budget_ok
# o1  = mode_ok
# o2  = proof_surface_ok
# o3  = fallback_boundary_ok
# o4  = algorithm_item_1_ab_ok
# o5  = algorithm_item_2_cow_ok
# o6  = optimizer_certificate_ok

set charvar off

is1(x : sbf) := (x = 1:sbf).
mode_ok(ab : sbf, cow : sbf) := (is1(ab) && !is1(cow)) || (!is1(ab) && is1(cow)).
proof_surface_ok(objective_ok : sbf, state_capacity_ok : sbf, parity_ok : sbf, tie_ok : sbf, balance_ok : sbf, budget_ok : sbf) := is1(objective_ok) && is1(state_capacity_ok) && is1(parity_ok) && is1(tie_ok) && is1(balance_ok) && is1(budget_ok).
fallback_boundary_ok(fallback_ok : sbf, no_authority : sbf) := is1(fallback_ok) && is1(no_authority).
ab_ok(active : sbf, ab : sbf, cow : sbf, objective_ok : sbf, state_capacity_ok : sbf, parity_ok : sbf, tie_ok : sbf, fallback_ok : sbf, no_authority : sbf, balance_ok : sbf, budget_ok : sbf) := is1(active) && is1(ab) && mode_ok(ab, cow) && proof_surface_ok(objective_ok, state_capacity_ok, parity_ok, tie_ok, balance_ok, budget_ok) && fallback_boundary_ok(fallback_ok, no_authority).
cow_ok(active : sbf, ab : sbf, cow : sbf, objective_ok : sbf, state_capacity_ok : sbf, parity_ok : sbf, tie_ok : sbf, fallback_ok : sbf, no_authority : sbf, balance_ok : sbf, budget_ok : sbf) := is1(active) && is1(cow) && mode_ok(ab, cow) && proof_surface_ok(objective_ok, state_capacity_ok, parity_ok, tie_ok, balance_ok, budget_ok) && fallback_boundary_ok(fallback_ok, no_authority).

always
  (o1[t]:sbf = 1:sbf <-> mode_ok(i2[t]:sbf, i3[t]:sbf)) &&
  (o2[t]:sbf = 1:sbf <-> proof_surface_ok(i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i10[t]:sbf, i11[t]:sbf)) &&
  (o3[t]:sbf = 1:sbf <-> fallback_boundary_ok(i8[t]:sbf, i9[t]:sbf)) &&
  (o4[t]:sbf = 1:sbf <-> ab_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf)) &&
  (o5[t]:sbf = 1:sbf <-> cow_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf)) &&
  (o6[t]:sbf = 1:sbf <-> (ab_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf) || cow_ok(i1[t]:sbf, i2[t]:sbf, i3[t]:sbf, i4[t]:sbf, i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf, i9[t]:sbf, i10[t]:sbf, i11[t]:sbf))).
"""


def _cases() -> dict[str, tuple[Case, ...]]:
    return {
        "frontier_certificate_menu_v1": (
            Case(
                "route_mode_pass",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 0, "i12": 0},
                {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
                "A fully bound route-mode frontier certificate is admitted.",
            ),
            Case(
                "two_modes_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1, "i12": 0},
                {"o1": 0, "o2": 1, "o3": 1, "o4": 0},
                "Two simultaneous modes fail one-hot decoding.",
            ),
            Case(
                "authority_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 1, "i10": 0, "i11": 1, "i12": 0},
                {"o1": 1, "o2": 1, "o3": 0, "o4": 0},
                "A certificate that can directly authorize state effects is rejected.",
            ),
            Case(
                "inactive_safe",
                {"i1": 0, "i2": 0, "i3": 0, "i4": 0, "i5": 0, "i6": 0, "i7": 1, "i8": 1, "i9": 0, "i10": 0, "i11": 0, "i12": 0},
                {"o4": 0, "o5": 1},
                "No active request cannot admit, but the inactive authority rail is safe.",
            ),
        ),
        "route_dominance_frontier_envelope_v1": (
            Case(
                "dominance_route_pass",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0},
                "All dominance, projection-cover, rounding, replay, and boundary facts hold.",
            ),
            Case(
                "missing_dominator_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 0, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 0, "o2": 1, "o4": 0},
                "Every pruned label must have a kept dominating witness.",
            ),
            Case(
                "rounding_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 0, "o4": 0},
                "Continuous or approximate dominance is insufficient without integer rounding binding.",
            ),
            Case(
                "inactive_safe",
                {"i1": 0, "i2": 0, "i3": 0, "i4": 0, "i5": 0, "i6": 0, "i7": 0, "i8": 0, "i9": 0, "i10": 1, "i11": 1},
                {"o4": 0, "o5": 1},
                "No route request admits no route, while the authority rail remains closed.",
            ),
        ),
        "oracle_polytope_frontier_envelope_v1": (
            Case(
                "oracle_polytope_pass",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 1},
                "The interval is feasible, parity checked, assumptions declared, and authority-closed.",
            ),
            Case(
                "missing_mev_assumption_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 0, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 1, "o3": 0, "o5": 0},
                "External MEV assumptions must be explicit before an interval envelope is usable.",
            ),
            Case(
                "point_parity_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 0, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 0, "o5": 0},
                "The interval compiler cannot widen beyond the pointwise verifier.",
            ),
            Case(
                "authority_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 0, "i11": 1},
                {"o4": 0, "o5": 0},
                "The oracle envelope cannot itself authorize oracle updates.",
            ),
        ),
        "ab_cow_exact_solver_envelope_v1": (
            Case(
                "ab_item_1_pass",
                {"i1": 1, "i2": 1, "i3": 0, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 1, "o3": 1, "o4": 1, "o5": 0, "o6": 1},
                "AB ordering certificate accepts when objective, full-state DP/brute parity, ties, balances, and budget are bound.",
            ),
            Case(
                "cow_item_2_pass",
                {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 1, "o3": 1, "o4": 0, "o5": 1, "o6": 1},
                "CoW matching certificate accepts for the uncoupled exact-assignment surface.",
            ),
            Case(
                "coupled_capacity_reject",
                {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 0, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 1, "o2": 0, "o5": 0, "o6": 0},
                "Grouped sender capacity cannot be treated as pure bipartite matching.",
            ),
            Case(
                "two_modes_reject",
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1, "i11": 1},
                {"o1": 0, "o4": 0, "o5": 0, "o6": 0},
                "The AB and CoW certificate modes are disjoint.",
            ),
        ),
    }


def _candidate_specs() -> list[CandidateSpec]:
    cases = _cases()
    return [
        CandidateSpec(
            spec_id="frontier_certificate_menu_v1",
            title="Frontier Certificate Menu",
            spec_path=SPEC_ROOT / "frontier_certificate_menu_v1.tau",
            kind="host_projected_optimizer_menu",
            breakthrough_track="shared_tau_frontier",
            value_score=10,
            novelty_score=9,
            projected_facts=9,
            direct_bv_ops=0,
            profile_budget_s=5.0,
            frontier_note="Shared one-hot certificate menu for route, oracle, and AB/CoW optimizer envelopes.",
            formal_obligations=(
                "Each mode flag maps to exactly one host verifier surface.",
                "Coverage and replay facts are produced by deterministic host/kernel checks.",
                "No accepted menu output has authority to mutate settlement state by itself.",
            ),
            non_claims=(
                "Does not prove the underlying optimizer is globally correct.",
                "Does not replace route, oracle, AB, or CoW host verifiers.",
            ),
            source=_frontier_menu_source(),
            cases=cases["frontier_certificate_menu_v1"],
        ),
        CandidateSpec(
            spec_id="route_dominance_frontier_envelope_v1",
            title="Dominance-Pruned Exact-Out Route Envelope",
            spec_path=SPEC_ROOT / "route_dominance_frontier_envelope_v1.tau",
            kind="route_certificate_envelope",
            breakthrough_track="ZB-20260627-02",
            value_score=10,
            novelty_score=8,
            projected_facts=10,
            direct_bv_ops=0,
            profile_budget_s=5.0,
            frontier_note="Tau envelope for the #1 route-dominance track: pruned-label cover plus full-domain projection-cover binding.",
            formal_obligations=(
                "Dominance relation is sound under integer CPMM fee and rounding semantics.",
                "Every pruned label has a kept dominating witness.",
                "Projection cover links the selected domain back to the full bounded route domain.",
                "Argmin stream certificate selects the canonical winner among kept labels.",
            ),
            non_claims=(
                "Does not compute route dominance in Tau.",
                "Does not certify unbounded route domains.",
            ),
            source=_route_dominance_source(),
            cases=cases["route_dominance_frontier_envelope_v1"],
        ),
        CandidateSpec(
            spec_id="oracle_polytope_frontier_envelope_v1",
            title="Oracle Dispute-Game Polytope Envelope",
            spec_path=SPEC_ROOT / "oracle_polytope_frontier_envelope_v1.tau",
            kind="oracle_interval_envelope",
            breakthrough_track="ZB-20260627-03",
            value_score=9,
            novelty_score=8,
            projected_facts=10,
            direct_bv_ops=0,
            profile_budget_s=5.0,
            frontier_note="Tau envelope for the #2 oracle-polytope track: interval feasibility, point-verifier parity, boundary walls, and disclosed assumptions.",
            formal_obligations=(
                "Honest challenge profitability holds over the declared interval.",
                "Frivolous dispute deterrence holds over the declared interval.",
                "Slash coverage exceeds cheat gain plus declared margin over the interval.",
                "Every accepted interval is pointwise-parity checked against the existing verifier.",
            ),
            non_claims=(
                "Does not estimate MEV or challenge probability inside Tau.",
                "Does not authorize oracle updates.",
            ),
            source=_oracle_polytope_source(),
            cases=cases["oracle_polytope_frontier_envelope_v1"],
        ),
        CandidateSpec(
            spec_id="ab_cow_exact_solver_envelope_v1",
            title="AB/CoW Exact Solver Envelope",
            spec_path=SPEC_ROOT / "ab_cow_exact_solver_envelope_v1.tau",
            kind="algorithm_work_item_envelope",
            breakthrough_track="algorithm_items_1_and_2",
            value_score=8,
            novelty_score=7,
            projected_facts=9,
            direct_bv_ops=0,
            profile_budget_s=5.0,
            frontier_note="Tau envelope for work items 1 and 2: AB full-state subset DP and CoW uncoupled exact assignment.",
            formal_obligations=(
                "AB full-state DP state includes processed set, reserves, and sender balances.",
                "CoW assignment is only claimed for uncoupled sender capacities.",
                "Capacity-coupled CoW batches remain on bounded exact search or fail-closed fallback.",
                "Objective and deterministic tie key are host-bound.",
            ),
            non_claims=(
                "Does not make grouped-capacity CoW polynomial.",
                "Does not remove the fallback path when state caps are exceeded.",
            ),
            source=_ab_cow_source(),
            cases=cases["ab_cow_exact_solver_envelope_v1"],
        ),
    ]


def _write_specs(candidates: list[CandidateSpec]) -> None:
    SPEC_ROOT.mkdir(parents=True, exist_ok=True)
    for candidate in candidates:
        candidate.spec_path.write_text(candidate.source, encoding="utf-8")


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tau_version(tau_bin: str | None) -> str | None:
    if not tau_bin:
        return None
    try:
        proc = subprocess.run([tau_bin, "--version"], check=False, capture_output=True, text=True, timeout=10)
        return (proc.stdout + proc.stderr).strip()
    except Exception as exc:
        return f"version unavailable: {type(exc).__name__}: {exc}"


def _run_cases(candidate: CandidateSpec, tau_bin: str | None) -> dict[str, Any]:
    if not tau_bin:
        return {"ok": False, "skipped": True, "error": "tau binary not found", "elapsed_s": 0.0, "case_results": []}
    started = time.monotonic()
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=candidate.spec_path,
            steps=[case.step for case in candidate.cases],
            timeout_s=candidate.profile_budget_s,
        )
    except Exception as exc:
        return {
            "ok": False,
            "skipped": False,
            "error_type": type(exc).__name__,
            "error": str(exc),
            "elapsed_s": round(time.monotonic() - started, 6),
            "case_results": [],
        }

    ok = True
    case_results: list[dict[str, Any]] = []
    for idx, case in enumerate(candidate.cases):
        got = outputs.get(idx, {})
        mismatches = {
            key: {"expected": value, "got": got.get(key)}
            for key, value in case.expected.items()
            if got.get(key) != value
        }
        if mismatches:
            ok = False
        case_results.append(
            {
                "case_id": case.case_id,
                "ok": not mismatches,
                "expected": case.expected,
                "got": got,
                "mismatches": mismatches,
                "rationale": case.rationale,
            }
        )
    return {
        "ok": ok,
        "skipped": False,
        "elapsed_s": round(time.monotonic() - started, 6),
        "case_results": case_results,
    }


def _features(candidate: CandidateSpec) -> dict[str, int]:
    text = candidate.spec_path.read_text(encoding="utf-8")
    return {
        "bytes": len(text.encode("utf-8")),
        "non_comment_lines": len([line for line in text.splitlines() if line.strip() and not line.strip().startswith("#")]),
        "definitions": text.count(" := "),
        "sbf_count": text.count("sbf"),
        "bv_count": text.count("bv["),
        "and_count": text.count("&&"),
        "or_count": text.count("||"),
        "projected_facts": int(candidate.projected_facts),
        "direct_bv_ops": int(candidate.direct_bv_ops),
    }


def _energy(candidate: CandidateSpec, latest: dict[str, Any], feature_row: dict[str, int]) -> float:
    hard_penalty = 0.0 if latest.get("ok") else 1000.0
    elapsed = float(latest.get("elapsed_s") or candidate.profile_budget_s)
    budget_penalty = max(0.0, elapsed - candidate.profile_budget_s) * 20.0
    complexity_penalty = 0.002 * feature_row["bytes"] + 0.15 * feature_row["definitions"]
    frontier_reward = 8.0 * candidate.value_score + 3.0 * candidate.novelty_score
    projection_reward = 0.5 * candidate.projected_facts
    return round(hard_penalty + budget_penalty + complexity_penalty - frontier_reward - projection_reward, 4)


def _build_report(candidates: list[CandidateSpec]) -> dict[str, Any]:
    latest_bin = find_tau_bin(REPO_ROOT, profile="latest")
    runtime_bin = find_tau_bin(REPO_ROOT, profile="runtime")
    rows: list[dict[str, Any]] = []
    for candidate in candidates:
        latest = _run_cases(candidate, latest_bin)
        runtime = _run_cases(candidate, runtime_bin)
        feature_row = _features(candidate)
        rows.append(
            {
                "spec_id": candidate.spec_id,
                "title": candidate.title,
                "spec_path": str(candidate.spec_path.relative_to(REPO_ROOT)),
                "kind": candidate.kind,
                "breakthrough_track": candidate.breakthrough_track,
                "value_score": candidate.value_score,
                "novelty_score": candidate.novelty_score,
                "profile_budget_s": candidate.profile_budget_s,
                "frontier_note": candidate.frontier_note,
                "formal_obligations": list(candidate.formal_obligations),
                "non_claims": list(candidate.non_claims),
                "sha256": _sha256(candidate.spec_path),
                "features": feature_row,
                "latest": latest,
                "runtime": runtime,
                "tau_spec_ebrm_v1_energy": _energy(candidate, latest, feature_row),
            }
        )
    rankings = {
        "tau_spec_ebrm_v1": [row["spec_id"] for row in sorted(rows, key=lambda row: (row["tau_spec_ebrm_v1_energy"], row["spec_id"]))],
        "highest_value": [row["spec_id"] for row in sorted(rows, key=lambda row: (-row["value_score"], row["spec_id"]))],
        "most_projected_facts": [row["spec_id"] for row in sorted(rows, key=lambda row: (-row["features"]["projected_facts"], row["spec_id"]))],
        "grammar_minimal": [row["spec_id"] for row in sorted(rows, key=lambda row: (row["features"]["bytes"], row["spec_id"]))],
    }
    return {
        "schema": "zenodex.tau_breakthrough_specs_report.v1",
        "date": "2026-06-27",
        "authority_boundary": "specs guard host-projected proof surfaces; deterministic host/kernel verifiers remain authoritative",
        "tau_bins": {
            "latest": {"path": latest_bin, "version": _tau_version(latest_bin)},
            "runtime": {"path": runtime_bin, "version": _tau_version(runtime_bin)},
        },
        "candidates": rows,
        "rankings": rankings,
        "breakthrough": {
            "spec_id": rankings["tau_spec_ebrm_v1"][0] if rankings["tau_spec_ebrm_v1"] else None,
            "reason": "Lowest deterministic energy among specs that ran through the latest Tau profile, balancing pass/fail, compactness, frontier value, and projected-fact coverage.",
        },
        "algorithm_work_items": {
            "1": {
                "name": "AB ordering",
                "artifact": "ab_cow_exact_solver_envelope_v1",
                "status": "Tau envelope added for host-bound full-state subset DP/brute-force certificate facts.",
            },
            "2": {
                "name": "CoW matching",
                "artifact": "ab_cow_exact_solver_envelope_v1",
                "status": "Tau envelope added for uncoupled exact-assignment certificate facts and grouped-capacity rejection.",
            },
        },
        "replay_command": "python3 tools/zenodex_tau_breakthrough_specs_20260627.py",
    }


def _write_markdown(report: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Tau Breakthrough Specifications - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    breakthrough_id = report["breakthrough"]["spec_id"]
    breakthrough = next(row for row in report["candidates"] if row["spec_id"] == breakthrough_id)
    lines.append(
        f"The breakthrough is `{breakthrough_id}`: {breakthrough['frontier_note']}"
    )
    lines.append(
        "It turns frontier optimizers into a shared Tau-facing certificate menu: the host proves search, interval, rounding, replay, and capacity facts; Tau checks one-hot mode selection, non-vacuity, coverage, budget, fallback, and no-authority rails."
    )
    lines.append("")
    lines.append("Authority boundary: these specs guard proof surfaces and research candidates. They do not authorize settlement, oracle updates, or governance by themselves.")
    lines.append("")
    lines.append("## Tau Builds")
    lines.append("")
    for profile, meta in report["tau_bins"].items():
        lines.append(f"- `{profile}`: `{meta['path']}`")
        lines.append(f"  - `{meta['version']}`")
    lines.append("")
    lines.append("## New Specifications")
    lines.append("")
    lines.append("| spec | track | latest | runtime | elapsed latest | energy | bytes |")
    lines.append("| --- | --- | --- | --- | ---: | ---: | ---: |")
    for row in report["candidates"]:
        latest = row["latest"]
        runtime = row["runtime"]
        lines.append(
            f"| `{row['spec_id']}` | `{row['breakthrough_track']}` | `{latest.get('ok')}` | `{runtime.get('ok')}` | `{float(latest.get('elapsed_s', 0.0)):.6f}s` | `{row['tau_spec_ebrm_v1_energy']:.4f}` | `{row['features']['bytes']}` |"
        )
    lines.append("")
    lines.append("## What Tau Language Can Do Here")
    lines.append("")
    lines.append("1. Encode compact optimizer certificate menus with one-hot mode selection and fail-closed admission.")
    lines.append("2. Combine 9 to 10 host-projected proof facts per step without embedding route search, interval arithmetic, hashes, or matching inside Tau.")
    lines.append("3. Expose mode-specific diagnostic outputs, so a failed candidate tells reviewers whether the gap is coverage, replay, authority, capacity, or external assumptions.")
    lines.append("4. Keep high-complexity algorithms out of Tau while still requiring every accepted optimizer to carry a small, replayable proof-surface packet.")
    lines.append("")
    lines.append("## Breakthrough Specification")
    lines.append("")
    lines.append(f"`{breakthrough_id}` ranked first under `tau_spec_ebrm_v1`.")
    lines.append("")
    lines.append("```text")
    lines.append("host verifier facts + one-hot optimizer mode + no-authority rail -> Tau certificate admit")
    lines.append("```")
    lines.append("")
    lines.append("The practical consequence is a reusable certificate layer: route dominance, oracle parameter intervals, AB ordering, and CoW matching can share the same Tau admission shape while preserving their own host/kernel verifiers.")
    lines.append("")
    lines.append("## Work Items 1 And 2")
    lines.append("")
    lines.append("### 1. AB Ordering")
    lines.append("")
    lines.append("`ab_cow_exact_solver_envelope_v1` adds a Tau rail for the existing AB full-state subset DP/brute-force path. It requires objective binding, full-state or bounded-search facts, parity, deterministic tie handling, balance/slippage checks, budget checks, fallback bounds, and no settlement authority.")
    lines.append("")
    lines.append("### 2. CoW Matching")
    lines.append("")
    lines.append("The same spec covers the exact CoW assignment subcase. It admits only the uncoupled-capacity surface and rejects grouped sender-capacity cases unless the host treats them as a separate bounded search or fail-closed fallback.")
    lines.append("")
    lines.append("## Track-Specific Notes")
    lines.append("")
    for row in report["candidates"]:
        lines.append(f"### `{row['spec_id']}`")
        lines.append("")
        lines.append(row["frontier_note"])
        lines.append("")
        lines.append("Formal obligations:")
        for item in row["formal_obligations"]:
            lines.append(f"- {item}")
        lines.append("")
        lines.append("Non-claims:")
        for item in row["non_claims"]:
            lines.append(f"- {item}")
        lines.append("")
    lines.append("## EBRM Ranking")
    lines.append("")
    lines.append("| method | order |")
    lines.append("| --- | --- |")
    for method, order in report["rankings"].items():
        lines.append(f"| `{method}` | `{', '.join(order)}` |")
    lines.append("")
    lines.append("`tau_spec_ebrm_v1` is deterministic and advisory. It uses hard Tau trace results, profile budget, source size, definition count, value score, novelty score, and projected-fact coverage.")
    lines.append("")
    lines.append("## Refutation Plan")
    lines.append("")
    lines.append("- Route dominance: compare dominance-pruned exact-out winners against the full bounded oracle on <=5 pools, then require every pruned label to have a kept dominating witness under integer rounding.")
    lines.append("- Oracle polytope: sample every accepted interval wall and reject if any point passes the interval compiler but fails the existing point verifier.")
    lines.append("- AB/CoW: keep brute-force parity for small AB batches and reject pure matching claims whenever grouped sender capacities are present.")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(report["replay_command"])
    lines.append("```")
    lines.append("")
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    candidates = _candidate_specs()
    _write_specs(candidates)
    report = _build_report(candidates)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    json_path = OUT_DIR / "report.json"
    json_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    print(
        json.dumps(
            {
                "ok": all(row["latest"].get("ok") for row in report["candidates"]),
                "report": str(REPORT_PATH),
                "json": str(json_path),
                "breakthrough": report["breakthrough"]["spec_id"],
            },
            indent=2,
        )
    )
    return 0 if all(row["latest"].get("ok") for row in report["candidates"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
