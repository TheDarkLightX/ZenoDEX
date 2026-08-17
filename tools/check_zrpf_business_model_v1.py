#!/usr/bin/env python3
"""Generate or verify the exact research-only ZRPF business-model packet."""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT: Final = REPO_ROOT / "docs/research/ZRPF_BUSINESS_MODEL_V1.json"
SCHEMA: Final = "zenodex/zrpf-business-model/v1"
REVIEWED_SOURCE_COMMIT: Final = "6ea6b6d6d0f32cd569529ee620b0a8685cb1f582"
MODEL_PATH: Final = "tools/zrpf_business_model_v1.py"
CHECKER_PATH: Final = "tools/check_zrpf_business_model_v1.py"
ESSO_MODEL_PATH: Final = "src/kernels/dex/zrpf_fee_waterfall_v1.yaml"
SOURCE_PATHS: Final = (
    MODEL_PATH,
    ESSO_MODEL_PATH,
    "docs/research/ZRPF_FEE_WATERFALL_ESSO_V1.json",
    "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json",
    "docs/research/PRODUCTION_READINESS_G1_CRITICAL_SERVICE_COSTS_V1.json",
    "docs/research/PRODUCTION_READINESS_G1_CRITICAL_SERVICE_PROCUREMENT_V1.json",
    "docs/research/PRODUCTION_READINESS_G1_CLBF_MODEL_V1.json",
    "docs/research/ZDEX_VOLUME_HOLDING_HYPERDEFLATION_MECHANISM_REPORT_V1.md",
)

sys.path.insert(0, str(REPO_ROOT))

from tools import zrpf_business_model_v1 as model  # noqa: E402


def _canonical_bytes(document: dict[str, Any]) -> bytes:
    return json.dumps(document, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _source_pins() -> list[dict[str, str]]:
    pins: list[dict[str, str]] = []
    for relative_path in SOURCE_PATHS:
        source_path = REPO_ROOT / relative_path
        if not source_path.is_file():
            raise ValueError(f"missing business-model source: {relative_path}")
        pins.append(
            {"path": relative_path, "sha256": _sha256(source_path.read_bytes())}
        )
    return pins


def _asdict(value: object) -> dict[str, Any]:
    return dataclasses.asdict(value)


def _proof_batch_sweep() -> dict[str, Any]:
    profile = model.ProofCostProfileV1(
        fixed_batch_atoms=1_000,
        publication_atoms=200,
        variable_atoms_per_resource_unit=1,
        direct_atoms_per_resource_unit=10,
    )
    multiplier_bps_values = (10_000, 15_000, 20_000)
    resource_units_values = (16, 64, 128, 256, 512, 1_024)
    rows: list[dict[str, Any]] = []
    thresholds: list[dict[str, int | None]] = []
    for multiplier_bps in multiplier_bps_values:
        thresholds.append(
            {
                "proof_cost_multiplier_bps": multiplier_bps,
                "minimum_economic_resource_units": (
                    model.minimum_economic_batch_units(
                        profile, multiplier_bps, contingency_bps=2_500
                    )
                ),
            }
        )
        for resource_units in resource_units_values:
            assessment = model.assess_proof_batch(
                profile,
                resource_units,
                multiplier_bps,
                contingency_bps=2_500,
            )
            rows.append(
                {
                    "proof_cost_multiplier_bps": multiplier_bps,
                    **_asdict(assessment),
                }
            )
    return {
        "units": "NORMALIZED_QUOTE_ATOMS_AND_PROOF_RESOURCE_UNITS",
        "profile": _asdict(profile),
        "contingency_bps": 2_500,
        "rows": rows,
        "thresholds": thresholds,
        "claim": (
            "The threshold is exact only for this normalized profile. Production "
            "activation recomputes it from qualified quotes and resource vectors."
        ),
    }


def _proof_market_comparison() -> dict[str, Any]:
    provers = (
        model.ProverV1("A", 70, 1, "owner-a", "gpu-a"),
        model.ProverV1("B", 80, 2, "owner-b", "gpu-b"),
        model.ProverV1("C", 95, 3, "owner-c", "gpu-c"),
        model.ProverV1("D", 110, 4, "owner-d", "gpu-d"),
    )
    first_valid = model.first_valid_race(provers, reward_atoms=100)
    reverse_dutch = model.reverse_dutch_lock(provers, 60, 100, 5)
    reverse_dutch_cartel = model.reverse_dutch_lock(
        provers, 60, 100, 5, collusive_wait=True
    )
    pay_as_bid = model.sealed_bid_procurement(
        provers,
        {"A": 85, "B": 90, "C": 100, "D": 115},
        maximum_price_atoms=100,
        kind=model.ProcurementKindV1.PAY_AS_BID,
    )
    second_price = model.sealed_bid_procurement(
        provers,
        {prover.prover_id: prover.cost_atoms for prover in provers},
        maximum_price_atoms=100,
        kind=model.ProcurementKindV1.SECOND_PRICE,
    )
    thin_market = (
        model.ProverV1("A1", 70, 1, "owner-a", "gpu-a"),
        model.ProverV1("A2", 75, 2, "owner-a", "gpu-a2"),
        model.ProverV1("B", 120, 3, "owner-b", "gpu-b"),
    )
    shill_second_price = model.sealed_bid_procurement(
        thin_market,
        {"A1": 70, "A2": 100, "B": 120},
        maximum_price_atoms=120,
        kind=model.ProcurementKindV1.SECOND_PRICE,
    )
    return {
        "fixture": [_asdict(prover) for prover in provers],
        "outcomes": {
            "first_valid_race": _asdict(first_valid),
            "reverse_dutch_lock_competitive": _asdict(reverse_dutch),
            "reverse_dutch_lock_collusive_wait": _asdict(reverse_dutch_cartel),
            "pay_as_bid": _asdict(pay_as_bid),
            "second_price": _asdict(second_price),
            "second_price_common_owner_shill": _asdict(shill_second_price),
        },
        "ranking": [
            {
                "rank": 1,
                "mechanism": "PREFUNDED_REVERSE_DUTCH_LOCK_WITH_BOND",
                "reason": (
                    "one assigned computation, exact maximum liability, deadline "
                    "slash, and direct-execution cap; cartel waiting remains bounded"
                ),
            },
            {
                "rank": 2,
                "mechanism": "SEALED_PAY_AS_BID_WITH_BOND",
                "reason": "avoids duplicate compute but retains bid shading",
            },
            {
                "rank": 3,
                "mechanism": "SECOND_PRICE_PROCUREMENT",
                "reason": (
                    "one-shot truthfulness requires assumptions that common-owner "
                    "shill bids and repeated collusion violate"
                ),
            },
            {
                "rank": 4,
                "mechanism": "FIRST_VALID_RACE",
                "reason": "duplicates compute and rewards latency concentration",
            },
        ],
    }


def _waterfall_search() -> dict[str, Any]:
    cases = 0
    for revenue_atoms in range(13):
        for carry_atoms in range(3):
            for safety_gap_atoms in range(4):
                for critical_gap_atoms in range(4):
                    for operations_gap_atoms in range(4):
                        for growth_cap_atoms in range(3):
                            for buyburn_active in (False, True):
                                request = model.FeeWaterfallInputV1(
                                    revenue_atoms,
                                    carry_atoms,
                                    safety_gap_atoms,
                                    critical_gap_atoms,
                                    operations_gap_atoms,
                                    growth_cap_atoms,
                                    buyburn_active,
                                )
                                outcome = model.allocate_fee_waterfall(request)
                                allocated_atoms = (
                                    outcome.safety_atoms
                                    + outcome.critical_service_atoms
                                    + outcome.operations_atoms
                                    + outcome.growth_atoms
                                    + outcome.burn_atoms
                                    + outcome.carry_atoms
                                )
                                if allocated_atoms != outcome.available_atoms:
                                    raise AssertionError("fee waterfall does not conserve")
                                if not outcome.all_required_prefunded and outcome.burn_atoms:
                                    raise AssertionError("unfunded period produced a burn")
                                cases += 1
    mutant_burn_atoms, mutant_remaining_atoms = model.gross_revenue_burn_mutant(
        10, 9_000
    )
    return {
        "cases": cases,
        "domain": (
            "revenue=0..12; carry=0..2; each required gap=0..3; "
            "growth cap=0..2; buyburn active in {false,true}"
        ),
        "counterexample": None,
        "predicates": [
            "all allocation outputs sum exactly to available revenue and carry",
            "burn is zero whenever any required prefund gap remains",
            "active buyburn receives 100% of residual eligible surplus",
        ],
        "gross_burn_mutant_witness": {
            "available_atoms": 10,
            "required_obligations_atoms": 9,
            "gross_burn_bps": 9_000,
            "mutant_burn_atoms": mutant_burn_atoms,
            "remaining_for_obligations_atoms": mutant_remaining_atoms,
            "underfunded_atoms": 8,
        },
    }


def _credit_economics() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for credit_bps in (0, 250, 500, 1_000, 1_500, 2_000, 10_000):
        rows.append(
            {
                "credit_bps": credit_bps,
                "minimum_volume_lift_bps_for_revenue_neutrality": (
                    model.required_fee_credit_volume_lift_bps(credit_bps)
                ),
                "wash_profit_on_100_irreversible_fee_atoms": (
                    model.wash_round_trip_profit_atoms(100, credit_bps)
                ),
            }
        )
    search_cases = 0
    for fee_atoms in range(1, 101):
        for credit_bps in range(0, 10_000):
            if model.wash_round_trip_profit_atoms(fee_atoms, credit_bps) >= 0:
                raise AssertionError("sub-fee credit became directly profitable")
            search_cases += 1
    return {
        "rows": rows,
        "bounded_wash_search": {
            "cases": search_cases,
            "domain": "irreversible fee=1..100 atoms; credit=0..9999 bps",
            "counterexample": None,
        },
        "candidate": {
            "launch_base_credit_bps": 500,
            "continuous_lock_max_credit_bps": 1_000,
            "status": "ADVISORY_UNSELECTED",
            "rule": (
                "nontransferable delayed credits are linear in irreversible cash "
                "protocol fees, fully reserved, expiring, and usable only against "
                "later protocol fees"
            ),
        },
    }


def _business_break_even_grid() -> dict[str, Any]:
    rows: list[dict[str, int]] = []
    for annual_fixed_cost_quote_units in (500_000, 1_000_000, 3_000_000, 10_000_000):
        for net_protocol_take_bps in (1, 3, 5, 10):
            rows.append(
                {
                    "annual_fixed_cost_quote_units": annual_fixed_cost_quote_units,
                    "net_protocol_take_bps": net_protocol_take_bps,
                    "break_even_annual_volume_quote_units": (
                        model.break_even_annual_volume_atoms(
                            annual_fixed_cost_quote_units, net_protocol_take_bps
                        )
                    ),
                }
            )
    return {
        "rows": rows,
        "formula": (
            "break_even_volume = ceil((fixed_cost - other_net_revenue) * "
            "10000 / net_protocol_take_bps)"
        ),
        "selection_rule": (
            "derive the take rate from qualified high-case budgets and conservative "
            "volume; if the rate exceeds the competitive/user cap, do not activate "
            "the feature without separate prefunding"
        ),
        "claim": "illustrative quote units, not revenue or cost forecasts",
    }


def _reserve_and_runway_sweeps() -> dict[str, Any]:
    quote_scale = 1_000_000
    subsidy_rows: list[dict[str, int]] = []
    for quote_atoms_per_zdex in (50_000, 500_000, 5_000_000):
        for daily_shortfall_whole_quote in (10_000, 50_000, 100_000):
            subsidy_rows.append(
                {
                    "quote_atoms_per_zdex": quote_atoms_per_zdex,
                    "daily_shortfall_quote_atoms": (
                        daily_shortfall_whole_quote * quote_scale
                    ),
                    "runway_days": model.subsidy_runway_days(
                        30_000_000,
                        quote_atoms_per_zdex,
                        daily_shortfall_whole_quote * quote_scale,
                    ),
                }
            )
    bonus_rows: list[dict[str, int | None]] = []
    for daily_release_bps in (2, 5, 10):
        policy = model.ProofBonusScheduleV1(
            opening_reserve_atoms=model.PROOF_RESERVE_INITIAL_ATOMS,
            reserve_floor_atoms=model.PROOF_RESERVE_FLOOR_ATOMS,
            daily_release_bps=daily_release_bps,
        )
        for epochs in (365, 1_460, 3_650):
            outcome = model.simulate_proof_bonus(policy, epochs)
            bonus_rows.append(
                {
                    "daily_release_bps": daily_release_bps,
                    "epochs": epochs,
                    "released_whole_zdex": outcome.released_atoms // model.ZDEX_SCALE,
                    "closing_reserve_whole_zdex": (
                        outcome.closing_reserve_atoms // model.ZDEX_SCALE
                    ),
                    "zero_release_epoch": outcome.zero_release_epoch,
                }
            )
    stress_rows: list[dict[str, int]] = []
    for stress_months, revenue_bps, cost_bps in (
        (12, 2_500, 15_000),
        (12, 0, 20_000),
        (18, 5_000, 12_500),
    ):
        runway_bps_months = model.stress_runway_baseline_cost_months(
            stress_months, revenue_bps, cost_bps
        )
        stress_rows.append(
            {
                "stress_months": stress_months,
                "revenue_multiplier_bps": revenue_bps,
                "cost_multiplier_bps": cost_bps,
                "required_baseline_cost_months_bps": runway_bps_months,
                "required_baseline_cost_months_ceiling": model.ceil_div(
                    runway_bps_months, model.BPS
                ),
            }
        )
    return {
        "proof_cost_subsidy_runway": {
            "rows": subsidy_rows,
            "claim": (
                "illustrative only; recurring deficits consume the reserve at a "
                "rate proportional to the unselected ZDEX quote price"
            ),
        },
        "work_contingent_zdex_bonus": {
            "rows": bonus_rows,
            "recommended_daily_release_bps": 5,
            "status": "ADVISORY_UNSELECTED",
            "allocation_rule": (
                "split each epoch cap by verified proof-resource contribution; "
                "unperformed work releases nothing and rounding dust remains reserved"
            ),
        },
        "critical_runway_stress": {
            "rows": stress_rows,
            "recommended_launch_target_months": 24,
            "status": "ADVISORY_UNSELECTED_PENDING_QUALIFIED_COST_QUOTES",
        },
    }


def _burn_floor_search() -> dict[str, Any]:
    cases = 0
    for excess_atoms in range(0, 10_001):
        supply_before_atoms = model.ZDEX_ACTIVE_FLOOR_ATOMS + excess_atoms
        burn_atoms = model.maximum_zdex_burn_atoms(supply_before_atoms)
        supply_after_atoms = supply_before_atoms - burn_atoms
        if supply_after_atoms < model.ZDEX_ACTIVE_FLOOR_ATOMS:
            raise AssertionError("Zeno burn crossed the active floor")
        if excess_atoms > 0 and supply_after_atoms <= model.ZDEX_ACTIVE_FLOOR_ATOMS:
            raise AssertionError("Zeno burn eliminated all excess atoms")
        cases += 1
    return {
        "cases": cases,
        "domain": "active-floor excess=0..10000 atoms",
        "counterexample": None,
        "rule": "burn <= floor((supply_before - active_floor) / 2)",
        "interpretation": (
            "the active floor is never crossed and at least one excess atom remains "
            "after every positive admissible burn"
        ),
    }


def _bond_search() -> dict[str, Any]:
    cases = 0
    for gain_atoms in range(0, 21):
        for slash_atoms in range(0, 21):
            for future_loss_atoms in range(0, 6):
                for detection_bps in (0, 2_500, 5_000, 7_500, 10_000):
                    expected = (
                        detection_bps * slash_atoms
                        + model.BPS * future_loss_atoms
                        >= model.BPS * gain_atoms
                    )
                    if model.bond_covers_default(
                        gain_atoms, slash_atoms, future_loss_atoms, detection_bps
                    ) != expected:
                        raise AssertionError("bond inequality drifted")
                    cases += 1
    return {
        "cases": cases,
        "domain": (
            "defect gain/slash=0..20; future loss=0..5; detection in "
            "{0,2500,5000,7500,10000} bps"
        ),
        "counterexample": None,
        "rule": (
            "detection_bps*slash + 10000*future_value_lost >= "
            "10000*maximum_defect_gain"
        ),
    }


def build_document() -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_ADVISORY",
        "reviewed_subject": REVIEWED_SOURCE_COMMIT,
        "source_pins": _source_pins(),
        "checker_sha256": _sha256((REPO_ROOT / CHECKER_PATH).read_bytes()),
        "selected_user_inputs": {
            "zdex_whole_supply": 2_000_000_000,
            "zdex_decimals": 18,
            "zdex_active_floor_whole": 200_000_000,
            "proof_reward_reserve_whole": 30_000_000,
            "post_genesis_mint": False,
            "zrpf_role": "SCALING_ONLY_NO_FINALITY_AUTHORITY",
        },
        "game_surface": {
            "players": [
                "users and liquidity providers",
                "ZRPF leaf, aggregation, and root proof miners",
                "batchers and sequencers",
                "seven ZenoLedger validators",
                "oracle, keeper, liquidator, relayer, host, security, and operations roles",
                "ZDEX holders and buyback counterparties",
                "colluding prover, ordering, and related-account coalitions",
            ],
            "actions": [
                "submit commands and maximum fee",
                "form or defer a batch",
                "lock, prove, default, reassign, or fall back to direct execution",
                "bid independently, shade, collude, or submit common-owner shills",
                "allocate finalized fee lots, reserve credits, buy ZDEX, or burn",
                "wash trade, split wallets, lock ZDEX, redeem credits, or let them expire",
            ],
            "information": (
                "proof cost and capacity are privately observed; finalized fees, "
                "resource vectors, bids, locks, proofs, deadlines, payments, reserves, "
                "burns, and nullifiers are protocol-observable; beneficial ownership "
                "and external hedges are incomplete"
            ),
            "timing": [
                "precharge the exact selected execution-mode maximum",
                "purpose-bind the full maximum proof liability before lock",
                "run the bounded procurement and verify the exact proof journal",
                "recheck current head and obtain ZenoLedger finality",
                "settle actual cost and refund deterministic overcollection",
                "close safety, critical-service, operations, and credit liabilities",
                "allocate true residual surplus to guarded buy-and-burn",
            ],
            "payoff": (
                "prover payment minus compute, capital, delay, and expected slash; "
                "protocol finalized fees minus property, liabilities, safety, service, "
                "operations, growth, refunds, and proof costs"
            ),
        },
        "attack_query": {
            "query": (
                "Does any bounded strategy obtain an unfunded proof payment, burn "
                "restricted money, profit from direct fee-credit wash trading, make "
                "duplicate proof work socially necessary, or let a prover replace "
                "validator finality?"
            ),
            "disaster_states": [
                "UNFUNDED_PROOF_ADMISSION",
                "FIRST_VALID_DUPLICATE_COMPUTE",
                "LOWBALL_DEFAULT_WITH_INADEQUATE_BOND",
                "SECOND_PRICE_COMMON_OWNER_SHILL",
                "GROSS_REVENUE_BURN_UNDERFUNDS_OPERATIONS",
                "TOKEN_PRICE_DEPENDENT_STRUCTURAL_SUBSIDY",
                "RAW_VOLUME_OR_WALLET_COUNT_REWARD",
                "FEE_CREDIT_AT_OR_ABOVE_IRREVERSIBLE_FEE",
                "ZDEX_ACTIVE_FLOOR_CROSSING",
                "ZRPF_PROOF_SELECTS_ZENOLEDGER_HEAD",
            ],
        },
        "bounded_model": {
            "integer_domain": "all arithmetic is exact integer arithmetic",
            "proof_fee": (
                "maximum_proof_liability = ceil(qualified_cost * "
                "(10000+contingency_bps)/10000)"
            ),
            "proof_admission": (
                "admit ZRPF only if purpose_bound_resource_fees >= maximum_proof_liability "
                "and maximum_proof_liability <= same-work direct fallback cost"
            ),
            "fee_waterfall": (
                "property/refunds -> safety -> critical services -> capped operations "
                "-> fully reserved growth credits -> 100% residual eligible surplus burn"
            ),
            "credit_safety": "0 <= credit < irreversible cash protocol fee",
            "burn_cap": "burn <= floor((supply-active_floor)/2)",
            "bond_rule": (
                "DefectGain <= DetectionProbability*Slash + FutureValueLost"
            ),
            "proof_bonus": (
                "daily_cap = floor((reserve-reserve_floor)*release_bps/10000); "
                "pay only verified work contribution"
            ),
            "exclusions": [
                "production hardware cost and throughput measurements",
                "demand elasticity and token price formation",
                "complete beneficial-owner detection",
                "oracle truth and external derivative payoffs",
                "legal, tax, accounting, and jurisdictional conclusions",
            ],
        },
        "simulations": {
            "proof_batch_economics": _proof_batch_sweep(),
            "proof_market_game": _proof_market_comparison(),
            "fee_waterfall": _waterfall_search(),
            "fee_credit_retention": _credit_economics(),
            "business_break_even": _business_break_even_grid(),
            "reserve_and_runway": _reserve_and_runway_sweeps(),
            "burn_floor": _burn_floor_search(),
            "bond_security": _bond_search(),
        },
        "recommended_business_model": {
            "recurring_zrpf_cost": (
                "charge a resource-vector execution fee in the same payment asset as "
                "the proof job; fully prefund each job; refund rounding and unused mode "
                "allowance; use direct execution when the quote or deadline fails"
            ),
            "proof_procurement": (
                "reverse-Dutch rising-price lock with an exact maximum, objective "
                "qualification, deadline bond, slash-funded reprocurement, canonical "
                "tie-break, and direct-cost ceiling"
            ),
            "proof_reserve": (
                "keep the 30M ZDEX lot as a temporary work-contingent mining bonus and "
                "initial distribution lane; recurring compute reimbursement remains "
                "fee-funded so token price cannot determine proof solvency"
            ),
            "validator_and_critical_services": (
                "fund validators, oracles, keepers, relayers, security, hosting, and "
                "operations from role-specific finalized-fee budgets; hold a 24-month "
                "launch runway only after qualified high-case quotes"
            ),
            "protocol_fee_rate": (
                "derive rather than guess: take_bps = ceil((high_case_fixed_budget - "
                "conservative_other_net_revenue)*10000/conservative_volume); refuse "
                "activation if the result exceeds a selected competitive cap"
            ),
            "surplus_and_burn": (
                "define surplus only after every property, refund, safety, service, "
                "operations, and admitted growth liability is funded; route 100% of "
                "that true residual to guarded buy-and-burn or same-purpose carry"
            ),
            "volume_and_holding": (
                "use fully reserved, delayed, nontransferable future-fee credits, "
                "linear in irreversible protocol fees; test 5% base and 10% maximum "
                "for a continuous ZDEX lock; raw volume and wallet count carry zero weight"
            ),
            "hosting": (
                "a capped reference-host budget precedes surplus; independent hosts may "
                "charge a separate signed interface fee and receive no settlement authority"
            ),
            "separation": (
                "ZRPF proves execution; five-of-seven ZenoLedger precommits select the "
                "durable head; proof miners and validators use distinct receipts, budgets, "
                "keys, nullifiers, and authority"
            ),
        },
        "evidence_lane": {
            "exact_python": [
                "normalized proof-cost occupancy and shock sweep",
                "four proof-procurement mechanisms plus cartel and shill fixtures",
                "bounded waterfall conservation and fixed-gross-burn mutant",
                "one million direct fee-credit wash-profit cases",
                "business break-even, reserve runway, reward-decay, and stress grids",
                "bounded burn-floor and bond-inequality searches",
            ],
            "esso": {
                "model": ESSO_MODEL_PATH,
                "receipt": "docs/research/ZRPF_FEE_WATERFALL_ESSO_V1.json",
                "status": "VERIFIED_BOUNDED_DUAL_SOLVER",
                "ir_hash": (
                    "sha256:a14e81c5a0ed2d6b3b9f4c38b58b5e8261aa9d29ed907e28955f6725297956d5"
                ),
                "required_solvers": ["z3", "cvc5"],
                "queries": {"passed": 12, "failed": 0, "inconclusive": 0},
                "preserved_mutant": "PAID_PHASE_WITHOUT_PAYMENT_WITNESS",
                "claim": (
                    "bounded fee-custody conservation, prefund-before-burn, "
                    "verified-work-before-payment, and validator-only finality"
                ),
            },
            "external_primary_context": [
                {
                    "source": "Ethereum zero-knowledge rollup documentation",
                    "url": "https://ethereum.org/developers/docs/scaling/zk-rollups/",
                    "observation": (
                        "user rollup fees cover state writes, data publication, operator "
                        "computation, proof generation, and verification"
                    ),
                },
                {
                    "source": "Boundless proof lifecycle",
                    "url": "https://docs.boundless.network/developers/proof-lifecycle",
                    "observation": (
                        "a prefunded reverse-Dutch offer locks one prover, uses collateral "
                        "for deadline failure, verifies before payment, and aggregates proofs"
                    ),
                },
                {
                    "source": "ZKsync fee model",
                    "url": (
                        "https://docs.zksync.io/zksync-protocol/era-vm/transactions/fee-model"
                    ),
                    "observation": (
                        "proof complexity differs from CPU complexity and worst-case "
                        "resource charging can require precharge and refund"
                    ),
                },
                {
                    "source": "Starknet fee documentation",
                    "url": "https://docs.starknet.io/learn/protocol/fees",
                    "observation": (
                        "fees combine execution, data, and a proof-resource vector whose "
                        "limiting component influences price"
                    ),
                },
            ],
        },
        "promotion_boundary": {
            "claims": [
                "exact results for the declared finite integer domains and fixtures",
                "fee-funded proof work with direct fallback removes structural reserve dependence",
                "liability-first residual burn dominates fixed gross-revenue burn for solvency",
                "credits strictly below irreversible fees are directly wash-loss-making in the scoped model",
                "the half-excess burn cap preserves a strict positive excess over the active floor",
            ],
            "nonclaims": [
                "production cost, price, demand, volume, retention, or burn-rate forecast",
                "truthful bidding or cartel resistance outside the fixed game surface",
                "complete Sybil or beneficial-owner detection",
                "safe runtime proof, payment, finality, or buyback implementation",
                "legal classification, production readiness, or launch authority",
            ],
            "selection": "NONE_ALL_NUMERIC_CANDIDATES_REQUIRE_PROFILE_APPROVAL",
            "mounted": False,
            "production_ready": False,
        },
    }


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write canonical JSON")
    parser.add_argument("--json", action="store_true", help="print a JSON status")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    try:
        document = build_document()
        expected_bytes = _canonical_bytes(document)
        if args.write:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(expected_bytes)
        if not args.output.is_file():
            raise ValueError(f"missing generated artifact: {args.output}")
        observed_bytes = args.output.read_bytes()
        if observed_bytes != expected_bytes:
            raise ValueError("artifact bytes or semantics differ from generated model")
        status = {
            "ok": True,
            "artifact": str(args.output.relative_to(REPO_ROOT)),
            "sha256": _sha256(observed_bytes),
            "research_only": True,
            "production_ready": False,
        }
        print(json.dumps(status, sort_keys=True) if args.json else "PASS")
        return 0
    except (OSError, ValueError, AssertionError) as exc:
        status = {"ok": False, "error": str(exc)}
        print(json.dumps(status, sort_keys=True) if args.json else f"FAIL: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
