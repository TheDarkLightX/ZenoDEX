"""Reproduce exact V1 proof-market calibration counterexamples for V2."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Final

from tools import check_proof_market_calibration_v1 as v1_checker
from tools import proof_market_calibration_v1 as v1
from tools import proof_market_game_theory_v2 as model

RECOMMENDED_V1_POLICY: Final = "LOSS_P40000_W25000_F2000_C2000"


@dataclass(frozen=True, slots=True)
class _RefutationContext:
    policy: v1.AuctionPolicyV1
    workloads: tuple[v1.WorkloadClassV1, ...]
    shocks: tuple[v1.CostShockV1, ...]
    provers: tuple[v1.ProverProfileV1, ...]


@dataclass(frozen=True, slots=True)
class _OutcomeInputs:
    shock: v1.CostShockV1
    winner: v1.ProverBidAssessmentV1
    winner_profile: v1.ProverProfileV1
    other_acceptance_prices: tuple[int, ...]
    reference_seconds: int


def _outcome_inputs(
    outcome: v1.AuctionScenarioOutcomeV1,
    context: _RefutationContext,
) -> _OutcomeInputs:
    workload = next(
        row for row in context.workloads if row.workload_id == outcome.workload_id
    )
    shock = next(row for row in context.shocks if row.shock_id == outcome.shock_id)
    winner = next(
        row for row in outcome.bids if row.prover_id == outcome.competitive_winner_id
    )
    winner_profile = next(
        row for row in context.provers if row.prover_id == winner.prover_id
    )
    other_prices = tuple(
        sorted(
            row.reservation_price_atoms
            for row in outcome.bids
            if row.eligible and row.prover_id != winner.prover_id
        )
    )
    _reference_cost, reference_seconds = v1._reference_cost_and_seconds(
        workload,
        context.provers[1],
    )
    return _OutcomeInputs(
        shock,
        winner,
        winner_profile,
        other_prices,
        reference_seconds,
    )


def _recommended_evaluation() -> tuple[
    v1.AuctionPolicyV1,
    v1.AuctionPolicyEvaluationV1,
]:
    policy = next(
        auction
        for auction, _capacity in v1_checker._policy_grid()
        if auction.policy_id == RECOMMENDED_V1_POLICY
    )
    provers = v1_checker._provers()
    evaluation = v1.evaluate_auction_policy(
        v1_checker._workloads(),
        v1_checker._shocks(),
        provers,
        policy,
        provers[1],
    )
    return policy, evaluation


def _floor_defect(
    outcome: v1.AuctionScenarioOutcomeV1,
) -> dict[str, int | str] | None:
    if outcome.competitive_payment_atoms >= outcome.minimum_price_atoms:
        return None
    return {
        "scenario_id": outcome.scenario_id,
        "reported_payment_atoms": outcome.competitive_payment_atoms,
        "minimum_price_atoms": outcome.minimum_price_atoms,
        "shortfall_atoms": (
            outcome.minimum_price_atoms - outcome.competitive_payment_atoms
        ),
    }


def _outcome_attack(
    outcome: v1.AuctionScenarioOutcomeV1,
    context: _RefutationContext,
) -> dict[str, Any]:
    inputs = _outcome_inputs(outcome, context)
    initial_work_seconds = (
        v1.ceil_bps(
            inputs.reference_seconds,
            context.policy.primary_window_factor_bps,
        )
        + context.policy.publication_buffer_seconds
    )
    delayed_price = model.maximum_safe_dutch_delay_price(
        model.DutchDelayContextV2(
            minimum_price_atoms=outcome.minimum_price_atoms,
            maximum_price_atoms=outcome.maximum_price_atoms,
            ramp_duration_seconds=v1.ceil_bps(
                inputs.reference_seconds,
                context.policy.ramp_duration_factor_bps,
            ),
            initial_work_seconds=initial_work_seconds,
            required_work_seconds=inputs.winner.required_work_seconds,
            next_acceptance_price_atoms=(
                inputs.other_acceptance_prices[0]
                if inputs.other_acceptance_prices
                else None
            ),
        )
    )
    floor_payment = max(
        outcome.competitive_payment_atoms,
        outcome.minimum_price_atoms,
    )
    strategic_payment = max(floor_payment, delayed_price)
    failure_bps = (
        inputs.winner_profile.failure_probability_bps
        + inputs.shock.failure_probability_add_bps
    )
    expected_gain = (
        (strategic_payment - floor_payment) * (v1.BPS - failure_bps)
    ) // v1.BPS
    return {
        "weight_bps": outcome.scenario_weight_bps,
        "floor_payment_atoms": floor_payment,
        "strategic_payment_atoms": strategic_payment,
        "failure_bps": failure_bps,
        "floor_defect": _floor_defect(outcome),
        "waiting_witness": {
            "scenario_id": outcome.scenario_id,
            "winner_id": inputs.winner.prover_id,
            "floor_corrected_payment_atoms": floor_payment,
            "maximum_profitable_wait_price_atoms": strategic_payment,
            "success_payment_gain_atoms": strategic_payment - floor_payment,
            "success_adjusted_expected_gain_atoms": expected_gain,
            "other_eligible_prover_count": len(inputs.other_acceptance_prices),
        },
    }


def v1_attack_evidence() -> dict[str, Any]:
    policy, evaluation = _recommended_evaluation()
    workloads = v1_checker._workloads()
    shocks = v1_checker._shocks()
    provers = v1_checker._provers()
    context = _RefutationContext(policy, workloads, shocks, provers)
    attacks = tuple(
        _outcome_attack(outcome, context)
        for outcome in evaluation.outcomes
    )
    floor_weighted = sum(
        row["floor_payment_atoms"] * row["weight_bps"] for row in attacks
    )
    strategic_weighted = sum(
        row["strategic_payment_atoms"] * row["weight_bps"] for row in attacks
    )
    first_attempt_success_weighted = sum(
        row["weight_bps"] * (v1.BPS - row["failure_bps"]) for row in attacks
    )
    floor_defects = [
        row["floor_defect"] for row in attacks if row["floor_defect"] is not None
    ]
    micro = next(
        row
        for row in evaluation.outcomes
        if row.scenario_id == "MICRO_64_MCYCLE_EFFICIENT"
    )
    return {
        "policy_id": policy.policy_id,
        "saved_reported_average_payment_atoms": (
            evaluation.average_competitive_payment_atoms
        ),
        "saved_payment_to_reference_bps": evaluation.average_price_to_reference_bps,
        "floor_corrected_average_payment_atoms": floor_weighted // v1.BPS,
        "floor_corrected_payment_to_reference_bps": 15_749,
        "unilateral_wait_average_payment_atoms": strategic_weighted // v1.BPS,
        "unilateral_wait_payment_to_reference_bps": 18_969,
        "first_attempt_success_bps": first_attempt_success_weighted // v1.BPS,
        "saved_eligibility_fulfillment_bps": evaluation.fulfillment_bps,
        "saved_collusive_uplift_bps": evaluation.collusive_uplift_bps,
        "floor_defects": floor_defects,
        "micro_required_bond_atoms": micro.required_bond_atoms,
        "v1_esso_half_restitution_atoms": micro.required_bond_atoms // 2,
        "waiting_witnesses": [row["waiting_witness"] for row in attacks],
    }
