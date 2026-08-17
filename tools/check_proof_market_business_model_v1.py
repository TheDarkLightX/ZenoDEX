#!/usr/bin/env python3
"""Generate or verify the research-only general proof-market packet."""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT: Final = REPO_ROOT / "docs/research/PROOF_MARKET_BUSINESS_MODEL_V1.json"
SERVICE_FUNDING_PATH: Final = (
    REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json"
)
SCHEMA: Final = "zenodex/proof-market-business-model/v1"
REVIEWED_SOURCE_COMMIT: Final = "6ea6b6d6d0f32cd569529ee620b0a8685cb1f582"
SOURCE_PATHS: Final = (
    "tools/check_proof_market_business_model_v1.py",
    "tools/proof_market_business_model_v1.py",
    "tools/proof_market_boundless_primary_sources_v1.py",
    "tools/proof_market_bmse_adapter_v1.py",
    "docs/research/PROOF_MARKET_BUSINESS_MODEL_V1.md",
    "src/kernels/dex/proof_market_lifecycle_v1.yaml",
    "docs/research/PROOF_MARKET_LIFECYCLE_ESSO_V1.json",
    "docs/research/PROOF_MARKET_LEAN_EVIDENCE_V1.json",
    "tools/zrpf_business_model_v1.py",
    "docs/research/ZRPF_BUSINESS_MODEL_V1.json",
    "src/kernels/dex/zrpf_fee_waterfall_v1.yaml",
    "docs/research/ZRPF_FEE_WATERFALL_ESSO_V1.json",
    "docs/ZENOPROOF_V0_DESIGN.md",
    "docs/PROOF_MINING.md",
    "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json",
    "internal/proofs/ZenoProofBountyMechanism.lean",
    "internal/proofs/ZenoProofMechanismComposition.lean",
    "internal/proofs/ZenoProofLinkedAssurance_v2.lean",
    "internal/proofs/ZenoProofMaintenanceFolk.lean",
    "internal/proofs/ZenoProofSybilBondBound.lean",
    "internal/proofs/ZenoProofDisputeGameBound.lean",
)

sys.path.insert(0, str(REPO_ROOT))

from tools import proof_market_boundless_primary_sources_v1 as boundless_sources  # noqa: E402
from tools import proof_market_business_model_v1 as model  # noqa: E402


def _canonical_bytes(document: dict[str, Any]) -> bytes:
    return json.dumps(document, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _source_pins() -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    for relative_path in SOURCE_PATHS:
        path = REPO_ROOT / relative_path
        if not path.is_file():
            raise ValueError(f"missing proof-market source: {relative_path}")
        result.append({"path": relative_path, "sha256": _sha256(path.read_bytes())})
    return result


def _asdict(value: object) -> dict[str, Any]:
    return dataclasses.asdict(value)


def _accepted_checks(**overrides: bool) -> model.ProofAdmissionChecksV1:
    values = {
        field.name: True
        for field in dataclasses.fields(model.ProofAdmissionChecksV1)
    }
    values.update(overrides)
    return model.ProofAdmissionChecksV1(**values)


def _settlement_contract() -> dict[str, Any]:
    terms = model.ProofJobTermsV1(
        product_kind=model.ProofProductKindV1.ASSIGNED_VALIDITY_PROOF,
        funding_scope=model.FundingScopeV1.EXTERNAL_BUYER,
        access_policy=model.AccessPolicyV1.PUBLIC_CONTENT_ADDRESSED,
        maximum_seller_payment_atoms=100_000,
        protocol_success_fee_bps=300,
        listing_fee_atoms=1_000,
        verifier_budget_atoms=10_000,
        publication_budget_atoms=2_000,
        seller_bond_atoms=50_000,
    )
    accepted = model.settle_proof_job(
        terms,
        _accepted_checks(),
        requested_seller_payment_atoms=80_000,
        verifier_cost_atoms=7_000,
        publication_cost_atoms=1_500,
    )
    duplicate = model.settle_proof_job(
        terms,
        _accepted_checks(canonical_work_key_unclaimed=False),
        requested_seller_payment_atoms=80_000,
        verifier_cost_atoms=7_000,
        publication_cost_atoms=1_500,
        seller_default_damage_atoms=20_000,
        seller_reprocurement_claim_atoms=10_000,
    )
    cases = 0
    fields = tuple(field.name for field in dataclasses.fields(model.ProofAdmissionChecksV1))
    for mask in range(1 << len(fields)):
        checks = model.ProofAdmissionChecksV1(
            **{
                field_name: bool(mask & (1 << index))
                for index, field_name in enumerate(fields)
            }
        )
        outcome = model.settle_proof_job(
            terms,
            checks,
            requested_seller_payment_atoms=80_000,
            verifier_cost_atoms=7_000,
            publication_cost_atoms=1_500,
            seller_default_damage_atoms=20_000,
            seller_reprocurement_claim_atoms=10_000,
        )
        accounted_prefund = (
            outcome.seller_payment_atoms
            + outcome.verifier_payment_atoms
            + outcome.publication_payment_atoms
            + outcome.protocol_revenue_atoms
            + outcome.buyer_refund_atoms
        )
        if accounted_prefund != outcome.required_buyer_prefund_atoms:
            raise AssertionError("buyer prefund does not conserve")
        if outcome.accepted != checks.accepted:
            raise AssertionError("settlement admission differs from closed checks")
        if not outcome.accepted and outcome.seller_payment_atoms:
            raise AssertionError("rejected proof paid a seller")
        if (
            outcome.seller_bond_return_atoms
            + outcome.seller_bond_restitution_atoms
            + outcome.seller_bond_reprocurement_atoms
            != terms.seller_bond_atoms
        ):
            raise AssertionError("seller bond does not conserve")
        cases += 1
    return {
        "terms": _asdict(terms),
        "accepted_example": _asdict(accepted),
        "duplicate_work_example": _asdict(duplicate),
        "exhaustive_boolean_cases": cases,
        "invariants": [
            "buyer escrow equals seller payment plus verifier and publication costs plus protocol fee plus refund",
            "seller bond equals returned bond plus restitution and reprocurement",
            "seller payment requires every closed admission check",
            "a duplicate canonical work key receives no seller payment",
            "post-completion buyer discretion cannot override the precommitted objective verifier",
            "a rejected job funds restitution and reprocurement before any residual burn",
        ],
    }


def _boundless_guard_model() -> dict[str, Any]:
    safe_lock = model.assess_auction_lock(
        model.AuctionLockScheduleV1(
            auction_start_height=100,
            lock_height=120,
            primary_deadline_height=240,
            final_deadline_height=400,
            estimated_proving_blocks=80,
            safety_margin_blocks=20,
        )
    )
    late_lock = model.assess_auction_lock(
        model.AuctionLockScheduleV1(
            auction_start_height=100,
            lock_height=210,
            primary_deadline_height=240,
            final_deadline_height=400,
            estimated_proving_blocks=80,
            safety_margin_blocks=20,
        )
    )
    underfunded_claims = model.allocate_default_bond(
        1_000,
        model.DefaultBondClaimsV1(
            buyer_restitution_claim_atoms=800,
            reprocurement_claim_atoms=600,
            insurance_recovery_claim_atoms=100,
            residual_burn_cap_atoms=500,
        ),
    )
    fully_funded_claims = model.allocate_default_bond(
        1_000,
        model.DefaultBondClaimsV1(
            buyer_restitution_claim_atoms=300,
            reprocurement_claim_atoms=200,
            insurance_recovery_claim_atoms=100,
            residual_burn_cap_atoms=500,
        ),
    )
    protected_capacity = model.assess_capacity_partition(
        model.CapacityPartitionPolicyV1(
            total_slots=16,
            priority_reserved_slots=6,
            permissionless_floor_slots=8,
            max_priority_slots_per_requestor=2,
        )
    )
    starvation_capacity = model.assess_capacity_partition(
        model.CapacityPartitionPolicyV1(
            total_slots=16,
            priority_reserved_slots=16,
            permissionless_floor_slots=0,
            max_priority_slots_per_requestor=16,
        )
    )
    if not safe_lock.admissible or late_lock.admissible:
        raise AssertionError("effective lock-window guard is not fail closed")
    if underfunded_claims.residual_burn_atoms != 0:
        raise AssertionError("default bond burned while loss claims remained unfunded")
    if not protected_capacity.admissible or starvation_capacity.admissible:
        raise AssertionError("permissionless capacity floor is not fail closed")
    return {
        "safe_lock_example": _asdict(safe_lock),
        "late_lock_counterexample": _asdict(late_lock),
        "underfunded_claims_example": _asdict(underfunded_claims),
        "fully_funded_claims_example": _asdict(fully_funded_claims),
        "protected_capacity_example": _asdict(protected_capacity),
        "starvation_capacity_counterexample": _asdict(starvation_capacity),
        "rules": [
            "lock admission uses effective remaining ledger-height window rather than the headline timeout",
            "buyer restitution, replacement procurement, and insurance recovery precede any predeclared residual penalty burn",
            "paid priority can reserve only an explicit partition and cannot consume the nonzero permissionless floor",
            "request, proof, ordered batch, signature role, escrow, durable receipt, and external-effect uniqueness all gate payment",
        ],
    }


def _scenario_matrix() -> tuple[model.MarketMonthScenarioV1, ...]:
    demand_rows = (
        {
            "id": "LOW",
            "weight": 2_500,
            "gmv": 20_000_000,
            "jobs": 80,
            "listings": 120,
            "enterprise": 2,
            "catalog": 100,
            "public_good": 2_000_000,
            "anchor_fee": 4_000_000,
            "anchor_cost": 4_500_000,
            "fixed": 5_000_000,
        },
        {
            "id": "BASE",
            "weight": 5_000,
            "gmv": 100_000_000,
            "jobs": 400,
            "listings": 520,
            "enterprise": 10,
            "catalog": 2_000,
            "public_good": 10_000_000,
            "anchor_fee": 12_000_000,
            "anchor_cost": 10_000_000,
            "fixed": 8_000_000,
        },
        {
            "id": "HIGH",
            "weight": 2_500,
            "gmv": 500_000_000,
            "jobs": 1_800,
            "listings": 2_200,
            "enterprise": 40,
            "catalog": 20_000,
            "public_good": 50_000_000,
            "anchor_fee": 50_000_000,
            "anchor_cost": 35_000_000,
            "fixed": 15_000_000,
        },
    )
    cost_rows = (
        {"id": "EFFICIENT", "weight": 2_500, "multiplier_bps": 8_000},
        {"id": "BASE_COST", "weight": 5_000, "multiplier_bps": 10_000},
        {"id": "STRESSED", "weight": 2_500, "multiplier_bps": 15_000},
    )
    scenarios: list[model.MarketMonthScenarioV1] = []
    for demand in demand_rows:
        for cost in cost_rows:
            multiplier_bps = int(cost["multiplier_bps"])
            scenarios.append(
                model.MarketMonthScenarioV1(
                    scenario_id=f"{demand['id']}_{cost['id']}",
                    weight_bps=int(demand["weight"]) * int(cost["weight"]) // model.BPS,
                    external_success_gmv_atoms=int(demand["gmv"]),
                    successful_external_jobs=int(demand["jobs"]),
                    external_listings=int(demand["listings"]),
                    enterprise_accounts=int(demand["enterprise"]),
                    catalog_service_events=int(demand["catalog"]),
                    public_good_gmv_atoms=int(demand["public_good"]),
                    anchor_user_fee_atoms=int(demand["anchor_fee"]),
                    anchor_proof_cost_atoms=model.ceil_bps(
                        int(demand["anchor_cost"]), multiplier_bps
                    ),
                    fixed_operations_cost_atoms=model.ceil_bps(
                        int(demand["fixed"]), multiplier_bps
                    ),
                    variable_cost_per_listing_atoms=model.ceil_bps(500, multiplier_bps),
                    variable_cost_per_success_atoms=model.ceil_bps(1_000, multiplier_bps),
                    variable_cost_per_catalog_event_atoms=model.ceil_bps(100, multiplier_bps),
                    enterprise_service_cost_per_account_atoms=model.ceil_bps(
                        50_000, multiplier_bps
                    ),
                )
            )
    if sum(scenario.weight_bps for scenario in scenarios) != model.BPS:
        raise AssertionError("scenario matrix weights do not close")
    return tuple(scenarios)


def _candidates() -> tuple[model.MarketCandidateV1, ...]:
    return (
        model.MarketCandidateV1(
            "SUCCESS_FEE_ONLY",
            500,
            0,
            0,
            0,
            False,
            False,
            False,
            0,
            0,
            2,
        ),
        model.MarketCandidateV1(
            "LISTING_PLUS_SUCCESS",
            350,
            1_000,
            0,
            0,
            False,
            False,
            False,
            0,
            0,
            3,
        ),
        model.MarketCandidateV1(
            "HYBRID_SLA",
            300,
            1_000,
            500_000,
            0,
            True,
            False,
            False,
            0,
            50,
            5,
        ),
        model.MarketCandidateV1(
            "HYBRID_SLA_CATALOG",
            300,
            1_000,
            500_000,
            1_000,
            True,
            True,
            False,
            0,
            50,
            6,
        ),
        model.MarketCandidateV1(
            "FULL_HYBRID_ASSURANCE",
            300,
            1_000,
            500_000,
            1_000,
            True,
            True,
            True,
            0,
            50,
            7,
        ),
        model.MarketCandidateV1(
            "SUBSCRIPTION_ONLY",
            0,
            0,
            1_000_000,
            0,
            True,
            False,
            False,
            0,
            0,
            3,
        ),
        model.MarketCandidateV1(
            "RAW_VOLUME_EMISSION",
            300,
            1_000,
            500_000,
            1_000,
            True,
            True,
            True,
            500,
            0,
            7,
        ),
    )


def _business_model_evaluation() -> dict[str, Any]:
    scenarios = _scenario_matrix()
    candidates = _candidates()
    evaluations = tuple(
        model.evaluate_market_candidate(candidate, scenarios)
        for candidate in candidates
    )
    frontier = model.pareto_frontier(evaluations)
    ranked = sorted(
        evaluations,
        key=lambda row: (
            not row.manipulation_safe,
            -row.expected_monthly_surplus_after_bonus_atoms,
            -row.probability_positive_bps,
            row.worst_monthly_loss_atoms,
            -row.negative_complexity_units,
            row.candidate_id,
        ),
    )
    break_even_rows: list[dict[str, int]] = []
    for monthly_gap_atoms in (5_000_000, 10_000_000, 25_000_000):
        for success_fee_bps in (200, 300, 500):
            break_even_rows.append(
                {
                    "monthly_gap_atoms": monthly_gap_atoms,
                    "success_fee_bps": success_fee_bps,
                    "required_external_gmv_atoms": model.minimum_external_gmv_for_break_even(
                        monthly_fixed_gap_atoms=monthly_gap_atoms,
                        success_fee_bps=success_fee_bps,
                    ),
                    "equivalent_5000_usd_subscription_accounts": model.ceil_div(
                        monthly_gap_atoms, 500_000
                    ),
                }
            )
    return {
        "units": {
            "cash": "QUOTE_ATOMS; illustrative fixture uses 100 atoms per USD",
            "probability": "BASIS_POINTS",
            "complexity": "ORDINAL_RESEARCH_UNITS",
        },
        "scenario_contract": {
            "count": len(scenarios),
            "weights_sum_bps": sum(row.weight_bps for row in scenarios),
            "source": "illustrative demand-by-cost stress matrix; not calibrated forecast",
            "scenarios": [_asdict(row) for row in scenarios],
        },
        "candidates": [_asdict(row) for row in candidates],
        "evaluations": [_asdict(row) for row in evaluations],
        "pareto_frontier": [row.candidate_id for row in frontier],
        "deterministic_ranking": [row.candidate_id for row in ranked],
        "break_even_surface": break_even_rows,
        "interpretation": [
            "buyer-funded seller payments are GMV and never counted as protocol revenue",
            "ZRPF user-fee inflow and proof cost are reported as a separate anchor contribution",
            "subscription and catalog lanes contribute only when the candidate implements them",
            "raw-volume candidates that let a buyer-seller coalition earn more bonus than fee are ineligible",
            "the scenario matrix ranks structures under stated assumptions and does not forecast demand",
        ],
    }


def _counterexample_market() -> dict[str, Any]:
    contributions = (
        model.SearchContributionV1("coverage-a", "partition-a", 1, 30, True, False),
        model.SearchContributionV1("coverage-b", "partition-b", 1, 70, True, False),
        model.SearchContributionV1("refutation", "partition-c", 2, 0, True, True),
    )
    outcome = model.allocate_counterexample_pool(
        total_budget_atoms=1_000,
        milestone_budget_bps=2_000,
        contributions=contributions,
    )
    return {
        "fixture": [_asdict(row) for row in contributions],
        "outcome": _asdict(outcome),
        "recommended_mechanism": "PARTITIONED_NOVELTY_POOL_PLUS_TERMINAL_REFUTATION_BOUNTY",
        "reason": [
            "a first-valid-only bounty pays one result while every searcher duplicates private compute",
            "registry-issued disjoint partitions make contribution identity independent of wallet count",
            "a small milestone pool pays accepted novel search coverage",
            "the decisive valid counterexample receives the terminal pool",
            "coverage units remain unsafe unless a release-selected verifier proves novelty and non-overlap",
        ],
    }


def _game_theory() -> dict[str, Any]:
    safe_bonus = model.contribution_locked_bonus(
        model.ContributionBonusRequestV1(
            verified_useful_value_atoms=100_000,
            irreversible_external_fee_atoms=3_000,
            verified_protocol_savings_atoms=2_000,
            scheduled_reserve_cap_atoms=5_000,
            useful_value_bonus_bps=100,
            external_fee_capture_cap_bps=5_000,
            savings_capture_cap_bps=2_500,
        )
    )
    safe_self_dealing_profit = model.self_dealing_profit_atoms(
        bonus_atoms=safe_bonus.bonus_atoms,
        fee_credit_atoms=0,
        irreversible_fee_atoms=3_000,
        verification_cost_atoms=500,
        computation_cost_atoms=1_000,
        expected_penalty_atoms=0,
    )
    raw_volume_attack_profit = model.self_dealing_profit_atoms(
        bonus_atoms=5_000,
        fee_credit_atoms=0,
        irreversible_fee_atoms=3_000,
        verification_cost_atoms=0,
        computation_cost_atoms=0,
        expected_penalty_atoms=0,
    )
    external_only_cases = 0
    for fee_atoms in range(101):
        for bonus_atoms in range(fee_atoms // 2 + 1):
            profit_atoms = model.self_dealing_profit_atoms(
                bonus_atoms=bonus_atoms,
                fee_credit_atoms=0,
                irreversible_fee_atoms=fee_atoms,
                verification_cost_atoms=0,
                computation_cost_atoms=0,
                expected_penalty_atoms=0,
            )
            if profit_atoms > 0:
                raise AssertionError("half-fee contribution cap admits self-dealing profit")
            external_only_cases += 1
    return {
        "contribution_locked_bonus": _asdict(safe_bonus),
        "contribution_locked_self_dealing_profit_atoms": safe_self_dealing_profit,
        "raw_volume_counterexample_profit_atoms": raw_volume_attack_profit,
        "external_only_half_fee_cases": external_only_cases,
        "sybil_bond_witness": {
            "total_reward_atoms": 100,
            "cohort_size": 4,
            "minimum_bond_atoms": model.minimum_sybil_bond_atoms(100, 4),
        },
        "dispute_bond_witness": _asdict(
            model.dispute_bond_interval(
                honest_reward_atoms=15,
                honest_external_gain_atoms=0,
                frivolous_external_gain_atoms=0,
            )
        ),
        "linked_assurance_witnesses": {
            "pledge_30_for_value_100_at_half_delay": model.linked_assurance_pledge_dominates(
                buyer_value_atoms=100,
                pledge_atoms=30,
                delay_numerator=1,
                delay_denominator=2,
            ),
            "pledge_60_for_value_100_at_half_delay": model.linked_assurance_pledge_dominates(
                buyer_value_atoms=100,
                pledge_atoms=60,
                delay_numerator=1,
                delay_denominator=2,
            ),
        },
        "maintenance_witnesses": {
            "sustainable": model.maintenance_subscription_sustainable(
                maintenance_cost_atoms=1,
                period_payment_atoms=5,
                slash_atoms=3,
                discount_numerator=1,
                discount_denominator=2,
                continuation_surplus_numerator=1,
                continuation_surplus_denominator=1,
            ),
            "unsustainable": model.maintenance_subscription_sustainable(
                maintenance_cost_atoms=10,
                period_payment_atoms=1,
                slash_atoms=1,
                discount_numerator=1,
                discount_denominator=2,
                continuation_surplus_numerator=1,
                continuation_surplus_denominator=1,
            ),
        },
    }


def _reserve_envelope() -> dict[str, Any]:
    whole_zdex = 30_000_000
    lanes = (
        ("ZRPF_AND_PROTOCOL_CRITICAL_PROOFS", 5_000),
        ("EXTERNAL_VERIFIED_WORK_MATCH", 2_000),
        ("COUNTEREXAMPLE_AND_IMPROVEMENT", 1_500),
        ("VERIFIER_AND_MAINTENANCE", 1_000),
        ("UNALLOCATED_SAFETY", 500),
    )
    allocations = [
        {
            "lane": lane,
            "cap_bps": cap_bps,
            "cap_whole_zdex": model.floor_bps(whole_zdex, cap_bps),
        }
        for lane, cap_bps in lanes
    ]
    if sum(row[1] for row in lanes) != model.BPS:
        raise AssertionError("reserve envelope does not sum to 10000 bps")
    if sum(int(row["cap_whole_zdex"]) for row in allocations) != whole_zdex:
        raise AssertionError("reserve allocation does not conserve")
    return {
        "total_whole_zdex": whole_zdex,
        "total_atoms": model.PROOF_RESERVE_ATOMS,
        "status": "RECOMMENDED_UNSELECTED_ENVELOPE",
        "allocations": allocations,
        "global_release_rule": {
            "candidate_daily_release_bps_of_remaining_reserve": 5,
            "payment_source": "fixed genesis proof reserve only",
            "no_mint": True,
            "exhaustion": "bonus stops; buyer-funded proof procurement continues",
        },
        "per_job_rule": (
            "bonus <= scheduled lane cap; bonus <= verified contribution rate; "
            "external bonus <= 50% of irreversible external fee; protocol-job "
            "bonus may additionally use an independently verified savings cap"
        ),
        "nonclaim": "The lane percentages are a launch research envelope, not an activated distribution.",
    }


def _service_funding_boundary() -> dict[str, Any]:
    payload = json.loads(SERVICE_FUNDING_PATH.read_text(encoding="utf-8"))
    expected_schema = "zenodex/production-readiness-g1-service-funding/v1"
    if payload.get("schema") != expected_schema:
        raise ValueError("unexpected service-funding artifact schema")
    bounded_model = payload.get("bounded_model")
    activation_gate = payload.get("activation_gate")
    if not isinstance(bounded_model, dict) or not isinstance(activation_gate, dict):
        raise ValueError("service-funding artifact lacks its bounded model or gate")
    registry = bounded_model.get("participant_funding_registry")
    role_budgets = bounded_model.get("selected_role_budgets")
    funding_sources = bounded_model.get("allowed_funding_sources")
    exhaustion = bounded_model.get("role_specific_exhaustion")
    if not all(
        isinstance(value, dict)
        for value in (registry, role_budgets, funding_sources, exhaustion)
    ):
        raise ValueError("service-funding artifact has malformed role registries")
    if len(registry) != activation_gate.get("participant_count"):
        raise ValueError("service-funding participant count does not close")
    if len(role_budgets) != activation_gate.get("budget_eligible_role_count"):
        raise ValueError("service-funding budget-eligible count does not close")
    if set(role_budgets) != set(funding_sources) or set(role_budgets) != set(exhaustion):
        raise ValueError("service-funding role registries disagree")
    selected_count = sum(value is not None for value in role_budgets.values())
    if selected_count != activation_gate.get("selected_budget_count"):
        raise ValueError("service-funding selected-budget count does not close")
    return {
        "source": {
            "path": str(SERVICE_FUNDING_PATH.relative_to(REPO_ROOT)),
            "sha256": _sha256(SERVICE_FUNDING_PATH.read_bytes()),
            "schema": expected_schema,
            "status": payload.get("status"),
        },
        "participant_count": len(registry),
        "budget_eligible_role_count": len(role_budgets),
        "selected_budget_count": selected_count,
        "participant_funding_registry": registry,
        "allowed_funding_sources": funding_sources,
        "role_specific_exhaustion": exhaustion,
        "selected_role_budgets": role_budgets,
        "integration_rules": [
            "buyer proof-job escrow funds only that job's declared seller, verifier, publication, fee, and refund legs",
            "finalized proof-market fee revenue may enter the protocol service waterfall only after job liabilities close",
            "property claims and prefunded critical services precede buy-and-burn surplus",
            "an unfunded critical role disables its dependent feature or prevents activation",
            "genesis ZDEX inventory cannot satisfy a stable-asset liability without an admitted conversion",
        ],
    }


def _document() -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_UNMOUNTED_UNSELECTED",
        "source_subject": {
            "reviewed_source_commit": REVIEWED_SOURCE_COMMIT,
            "source_pins": _source_pins(),
            "checker_bootstrap_verified": False,
        },
        "architecture": {
            "market_boundary": (
                "ZenoProof is a general market for claim-bound proofs, counterexamples, "
                "improvement certificates, maintenance, and verified reuse services."
            ),
            "zrpf_role": (
                "ZRPF is recurring anchor demand and pays from DEX resource fees; it is "
                "one buyer lane rather than the market definition."
            ),
            "asset_semantics": (
                "A public proof is non-rival. The scarce economic object is a funded work "
                "order, private-access right, maintenance obligation, or claim-bound "
                "settlement right; no opaque proof token carries truth or finality."
            ),
            "authority": (
                "Proof-market verification may admit evidence and payment requests. "
                "ZenoLedger alone commits payments and economic state; proof artifacts "
                "never select the ledger head."
            ),
            "secondary_market": {
                "launch_status": "DISABLED_UNSELECTED",
                "eligible_right_shapes": [
                    "funded work-order assignment before prover lock",
                    "private-access or embargo right with an exact disclosure deadline",
                    "reserved-capacity right with a named service period",
                    "maintenance obligation with a named verifier and freshness window",
                    "claim-bound settlement right after exact legal and custody review",
                ],
                "forbidden_semantics": [
                    "ownership of a public mathematical fact",
                    "transfer of verifier truth, ZenoLedger finality, or settlement authority",
                    "an unbound proof token whose holder can change the claim or assumptions",
                ],
            },
        },
        "external_primary_source_review": boundless_sources.primary_source_review(),
        "game_surface": {
            "players": [
                "external proof buyer or bounty sponsor",
                "ZRPF anchor buyer",
                "proof miner or assigned prover",
                "counterexample and improvement searcher",
                "verifier and aggregation operator",
                "artifact maintainer",
                "enterprise reserved-capacity customer",
                "protocol treasury and proof-reserve controller",
                "ZenoLedger validators",
            ],
            "products": [kind.value for kind in model.ProofProductKindV1],
            "actions": [
                "list and prefund a canonical claim-bound job",
                "lock an assigned proof job or search an admitted counterexample partition",
                "submit, verify, reject, pay, refund, slash for restitution, or expire",
                "fund a public proof through linked assurance",
                "buy private delivery or request public artifact verification and adaptation",
                "subscribe for reserved capacity and maintenance without changing verifier outcomes",
            ],
            "information": [
                "claim, assumptions, inputs, verifier profile, deadline, and maximum liability are public before lock",
                "private witnesses may remain committed until payment is finalized or escrow-locked",
                "beneficial ownership, off-ledger compute cost, and undisclosed collusion remain external premises",
            ],
        },
        "attack_query": [
            "seller paid without verifier acceptance or exact claim binding",
            "same work paid twice through artifact-byte or wallet changes",
            "buyer and seller coalition earns more bootstrap reward than irreversible cost",
            "counterexample hunters split identities or overlapping search space to multiply rewards",
            "frivolous dispute expected gain exceeds its bond while honest challenge is unprofitable",
            "ZRPF internal transfers are misreported as external proof-market revenue",
            "buyer escrow or seller GMV is misreported as protocol revenue",
            "subscription, reputation, or proof token substitutes for verifier admission or ledger finality",
            "maintenance provider profits by withholding freshness or manufacturing expiry",
            "request identifier or ordered proof leaf is substituted while a batch root still verifies",
            "a client or prover signature is replayed across authority roles",
            "a valid proof finalizes without reserved buyer payment",
            "a callback or other external effect executes twice for one request occurrence",
            "a reward receipt disappears across restart, container recreation, or upgrade",
            "paid-priority capacity starves the permissionless market",
        ],
        "bounded_model": {
            "settlement": _settlement_contract(),
            "boundless_derived_guards": _boundless_guard_model(),
            "business_model": _business_model_evaluation(),
            "counterexample_market": _counterexample_market(),
            "game_theory": _game_theory(),
            "proof_reserve": _reserve_envelope(),
            "protocol_service_funding": _service_funding_boundary(),
        },
        "recommendation": {
            "name": "HYBRID_PROOF_SERVICE_MARKET_V1",
            "launch_order": [
                "assigned proof and ZRPF jobs with prefunded reverse-Dutch lock procurement",
                "objective counterexample and improvement bounties with canonical work keys",
                "external listing-cost recovery plus 2%-5% success-fee experiment",
                "enterprise reserved-capacity subscription whose SLA cannot affect verification",
                "public catalog verification/adaptation after canonical reuse semantics are stable",
                "linked-assurance public-good funding after the pledge/refund lifecycle is mounted",
            ],
            "payment_sources": {
                "external_jobs": "buyer escrow",
                "zrpf_jobs": "DEX per-resource fees with direct-execution fallback",
                "protocol_public_goods": "purpose-bound treasury or pooled sponsor escrow",
                "bootstrap_bonus": "30M fixed ZDEX proof reserve",
                "validators": "separate finality service budget; never paid from seller escrow by implication",
            },
            "revenue": (
                "Protocol revenue is listing-cost recovery, external success fees, "
                "catalog verification/adaptation fees, and enterprise subscriptions. "
                "Buyer principal, seller payment, verifier pass-through, refundable "
                "escrow, restitution, and internal ZRPF transfers are excluded."
            ),
            "surplus": (
                "Finalized unrestricted revenue remaining after refunds, property claims, "
                "proof sellers, verifiers, validators, oracles, safety reserves, hosting, "
                "operations, maintenance, and admitted growth liabilities."
            ),
            "burn": (
                "Only true protocol-wide surplus enters buy-and-burn. A proof-market "
                "business model cannot pre-commit revenue needed by other participants."
            ),
        },
        "evidence_lane": {
            "current": [
                "exact integer escrow, fee, refund, bond, bonus, dispute, assurance, maintenance, and cash-flow model",
                "closed fourteen-check settlement sweep over 16,384 admission vectors",
                "Boundless-derived effective-window, liability-first slash, and permissionless-capacity guard examples",
                "source-status-preserving review of official Boundless docs, releases, and four published audit PDFs",
                "bounded half-fee self-dealing search",
                "nine-scenario demand-by-cost business-model sweep",
                "dual-solver ESSO lifecycle proof covering durable receipt-before-payment, atomic callback-outbox ancestry, and one-shot delivery",
                "BMSE stock marketplace baseline plus certified Pareto replay over proof-specific candidate evaluations",
                "six direct-compiled Lean theorem files for bounty caps, composition, Sybil bonds, linked assurance, maintenance, and disputes",
                "ZRPF dual-solver fee-waterfall ESSO receipt retained as the anchor-buyer submodel",
            ],
            "required": [
                "repository-wide Lean-root integration and runtime projection for the direct-compiled theorem files",
                "calibrated job demand, compute cost, verifier cost, and customer acquisition distributions",
                "beneficial-owner and related-party policy with false-positive and evasion analysis",
                "production Rust transition, canonical codec, mounted ZenoLedger payment port, and no-bypass inventory",
                "independent-process crash, restart, migration, and redelivery evidence for durable receipts and committed-outbox effect idempotency",
            ],
        },
        "promotion_boundary": {
            "claim": (
                "The research model closes exact bounded accounting and identifies a "
                "hybrid two-sided service market as the strongest structure to test."
            ),
            "nonclaims": [
                "No fee, subscription price, reserve lane, bounty amount, or product is activated.",
                "Illustrative scenario outputs are sensitivity results rather than demand, price, profit, or token-value forecasts.",
                "The model does not prove beneficial ownership, novelty, proof correctness, market adoption, or legal classification.",
                "The BMSE generic marketplace baseline does not express proof-specific verification, reuse, counterexample, or token-reserve semantics.",
                "No proof artifact, market receipt, subscription, or token carries finality or settlement authority.",
            ],
            "production_ready": False,
            "selected": False,
            "mounted": False,
        },
    }


def _write_or_check(output_path: Path, write: bool) -> tuple[bool, dict[str, Any]]:
    document = _document()
    expected = _canonical_bytes(document)
    if write:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_bytes(expected)
    actual = output_path.read_bytes() if output_path.is_file() else b""
    ok = actual == expected
    return ok, {
        "schema": SCHEMA,
        "ok": ok,
        "output": str(output_path),
        "sha256": _sha256(expected),
        "bytes": len(expected),
        "status": document["status"],
        "selected": False,
        "mounted": False,
        "production_ready": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        ok, report = _write_or_check(Path(args.output).resolve(), args.write)
    except Exception as exc:
        report = {"schema": SCHEMA, "ok": False, "error": str(exc)}
        ok = False
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("PASS" if ok else "FAIL")
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
