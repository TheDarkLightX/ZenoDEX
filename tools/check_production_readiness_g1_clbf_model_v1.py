#!/usr/bin/env python3
"""Generate and check the exact research-only CLBF accounting model."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping
from functools import lru_cache
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_CLBF_MODEL_V1.json"
SCHEMA = "zenodex/production-readiness-g1-clbf-model/v1"
RESEARCH_SOURCE_SUBJECT = "ab1476dedee730b3a2c922a9cd19e2d3a02c7e27"
CONTRACT_PATH = "tools/production_readiness_g1_clbf_contract_v1.py"
CHECKER_PATH = "tools/check_production_readiness_g1_clbf_model_v1.py"

sys.path.insert(0, str(REPO_ROOT))

from tools import production_readiness_g1_clbf_contract_v1 as contract  # noqa: E402

EXPECTED_PARAMETER_KEYS = frozenset(
    {
        "growth_reserve_bps",
        "earn_bps",
        "redemption_bps",
        "event_benefit_bps",
        "maturity_epochs",
        "expiry_epochs",
        "lock_epochs",
        "lock_value_multiple_bps",
        "aggregate_liability_bps",
    }
)

EXPECTED_ALLOWED_DESTINATIONS = {
    "THIRD_PARTY_PROPERTY": frozenset(
        {"P0_AUTHORIZED_SETTLEMENT", "P0_REFUND_OR_WITHDRAWAL", "P0_CARRY"}
    ),
    "REFUNDABLE_SERVICE_BOND": frozenset(
        {"P0_REFUND_OR_WITHDRAWAL", "P0_ADMITTED_SLASH_TRANSFORM", "P0_CARRY"}
    ),
    "BACKSTOP_RISK_PRINCIPAL": frozenset(
        {
            "P0_REFUND_OR_WITHDRAWAL",
            "P0_CONTRACTUAL_LOSS",
            "P0_ADMITTED_SLASH_TRANSFORM",
            "P0_CARRY",
        }
    ),
    "MARKET_MAKER_LIQUIDITY": frozenset(
        {
            "P0_AUTHORIZED_SETTLEMENT",
            "P0_REFUND_OR_WITHDRAWAL",
            "P0_CONTRACTUAL_LOSS",
            "P0_CARRY",
        }
    ),
    "UNRESTRICTED_PROTOCOL_REVENUE": frozenset(
        {
            "P1_SAFETY_RESERVE",
            "P2_SERVICE_PAYMENT",
            "P3_OPERATIONS_PAYMENT",
            "G_CREDIT_RESERVE_CREATE",
            "X_BUYBACK_EXECUTION",
            "C_REVENUE_CARRY",
            "C_BUYBACK_CARRY",
        }
    ),
    "REVENUE_CARRY": frozenset(
        {
            "P1_SAFETY_RESERVE",
            "P2_SERVICE_PAYMENT",
            "P3_OPERATIONS_PAYMENT",
            "G_CREDIT_RESERVE_CREATE",
            "X_BUYBACK_EXECUTION",
            "C_REVENUE_CARRY",
            "C_BUYBACK_CARRY",
        }
    ),
    "SERVICE_PREFUND": frozenset(
        {"P0_REFUND_OR_WITHDRAWAL", "P2_SERVICE_PAYMENT", "C_SERVICE_CARRY"}
    ),
    "OPERATIONS_PREFUND": frozenset(
        {
            "P0_REFUND_OR_WITHDRAWAL",
            "P3_OPERATIONS_PAYMENT",
            "C_OPERATIONS_CARRY",
        }
    ),
    "ADMITTED_SLASH_PROCEEDS": frozenset(
        {"P0_RESTITUTION", "P1_SAFETY_RESERVE", "C_SLASH_CARRY"}
    ),
    "CREDIT_RESERVE": frozenset(
        {"CREDIT_REDEMPTION", "CREDIT_EXPIRY_TO_BUYBACK", "C_CREDIT_RESERVE"}
    ),
    "BUYBACK_CARRY": frozenset(
        {"X_BUYBACK_EXECUTION", "C_BUYBACK_CARRY"}
    ),
    "GENESIS_LOT": frozenset({"GENESIS_DISTRIBUTION", "C_GENESIS_CARRY"}),
}


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _git_bytes(repo_root: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout


def _source_pins(repo_root: Path) -> list[dict[str, str]]:
    pins: list[dict[str, str]] = []
    for path in contract.RESEARCH_SOURCE_PATHS:
        frozen = _git_bytes(
            repo_root,
            "show",
            f"{RESEARCH_SOURCE_SUBJECT}:{path}",
        )
        observed = (repo_root / path).read_bytes()
        if observed != frozen:
            raise ValueError(f"CLBF research source drift: {path}")
        pins.append(
            {
                "path": path,
                "sha256": _sha256(frozen),
                "subject": RESEARCH_SOURCE_SUBJECT,
            }
        )
    return pins


def _validate_contract() -> dict[str, list[str]]:
    selected = contract.SELECTED_CLBF_PARAMETERS
    if set(selected) != EXPECTED_PARAMETER_KEYS:
        raise ValueError("CLBF selected-parameter registry differs from the checker")
    if any(value is not None for value in selected.values()):
        raise ValueError("CLBF parameters must remain unselected in this artifact")

    observed = {
        lot_type.value: frozenset(destination.value for destination in destinations)
        for lot_type, destinations in contract.allowed_destinations_v1().items()
    }
    if observed != EXPECTED_ALLOWED_DESTINATIONS:
        raise ValueError("source-lot routing registry differs from the independent checker")
    if set(observed) != {lot_type.value for lot_type in contract.LotTypeV1}:
        raise ValueError("source-lot registry does not cover every lot type")
    return {key: sorted(value) for key, value in sorted(observed.items())}


@lru_cache(maxsize=1)
def bounded_attack_evidence() -> dict[str, Any]:
    """Run terminating exact integer searches over the declared small domain."""

    credit_counterexample: dict[str, int] | None = None
    event_counterexample: dict[str, int] | None = None
    credit_cases = 0
    event_cases = 0
    for fee_atoms in range(33):
        for basis_points in range(contract.BPS_DENOMINATOR):
            benefit_atoms = (
                fee_atoms * basis_points // contract.BPS_DENOMINATOR
            )
            credit_cases += 1
            if benefit_atoms - fee_atoms > 0 and credit_counterexample is None:
                credit_counterexample = {
                    "fee_atoms": fee_atoms,
                    "basis_points": basis_points,
                    "benefit_atoms": benefit_atoms,
                }
            event_cases += 1
            if benefit_atoms - fee_atoms > 0 and event_counterexample is None:
                event_counterexample = {
                    "fee_atoms": fee_atoms,
                    "basis_points": basis_points,
                    "benefit_atoms": benefit_atoms,
                }

    sybil_counterexample: dict[str, int] | None = None
    sybil_cases = 0
    for first_fee_atoms in range(17):
        for second_fee_atoms in range(17):
            for basis_points in range(contract.BPS_DENOMINATOR):
                split_atoms = (
                    first_fee_atoms * basis_points // contract.BPS_DENOMINATOR
                    + second_fee_atoms * basis_points // contract.BPS_DENOMINATOR
                )
                combined_atoms = (
                    (first_fee_atoms + second_fee_atoms)
                    * basis_points
                    // contract.BPS_DENOMINATOR
                )
                sybil_cases += 1
                if split_atoms > combined_atoms and sybil_counterexample is None:
                    sybil_counterexample = {
                        "first_fee_atoms": first_fee_atoms,
                        "second_fee_atoms": second_fee_atoms,
                        "basis_points": basis_points,
                        "split_atoms": split_atoms,
                        "combined_atoms": combined_atoms,
                    }

    return {
        "credit_direct_profit_search": {
            "domain": "fee_atoms=0..32; earn_bps=0..9999",
            "cases": credit_cases,
            "counterexample": credit_counterexample,
            "predicate": "floor(fee_atoms * earn_bps / 10000) - fee_atoms > 0",
        },
        "event_cap_profit_search": {
            "domain": "fee_atoms=0..32; total_event_benefit_bps=0..9999",
            "cases": event_cases,
            "counterexample": event_counterexample,
            "predicate": (
                "floor(fee_atoms * total_event_benefit_bps / 10000) "
                "- fee_atoms > 0"
            ),
        },
        "sybil_split_search": {
            "domain": "two fee lots each 0..16 atoms; earn_bps=0..9999",
            "cases": sybil_cases,
            "counterexample": sybil_counterexample,
            "predicate": "sum(floor(split_fee * bps / 10000)) > floor(sum(fee) * bps / 10000)",
        },
        "named_mutant_witnesses": [
            {
                "id": "CREDIT_RATE_AT_OR_ABOVE_FULL_FEE",
                "fee_atoms": 4,
                "mutant_bps": 12_500,
                "benefit_atoms": 5,
                "profit_atoms": 1,
            },
            {
                "id": "STACKED_EVENT_BENEFIT_ABOVE_FULL_FEE",
                "fee_atoms": 4,
                "mutant_bps": 12_500,
                "benefit_atoms": 5,
                "profit_atoms": 1,
            },
            {
                "id": "RAW_VOLUME_SUBSIDY_ABOVE_IRREVERSIBLE_FEE",
                "fee_atoms": 1,
                "benefit_atoms": 2,
                "profit_atoms": 1,
            },
            {
                "id": "PER_WALLET_BASE_AWARD",
                "fee_atoms": 1,
                "wallet_count": 2,
                "benefit_atoms": 2,
                "profit_atoms": 1,
            },
        ],
        "claim_ceiling": (
            "Exact for the finite declared domains and direct protocol-funded "
            "benefit terms only; it is not an unbounded theorem or a model of "
            "external positions, recaptured fees, legal status, or behavior."
        ),
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    lot_registry = _validate_contract()
    source_pins = _source_pins(repo_root)
    contract_bytes = (repo_root / CONTRACT_PATH).read_bytes()
    checker_bytes = (repo_root / CHECKER_PATH).read_bytes()

    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_UNSELECTED",
        "production_promotion": False,
        "reviewed_subject": RESEARCH_SOURCE_SUBJECT,
        "research_source_pins": source_pins,
        "implementation_source_pins": [
            {"path": CONTRACT_PATH, "sha256": _sha256(contract_bytes)},
            {"path": CHECKER_PATH, "sha256": _sha256(checker_bytes)},
        ],
        "game_surface": {
            "actors": [
                "traders and related-account coalitions",
                "LPs and Stability Pool depositors",
                "proof provers and proof-market suppliers",
                "validators and finality operators",
                "oracle reporters, aggregators, disputers, and watchers",
                "keepers, liquidators, solvers, sequencers, and relayers",
                "interface, API, static-mirror, and infrastructure hosts",
                "security, legal, operations, and core contributors",
                "treasury, reserve, and buyback executors",
            ],
            "observable_inputs": [
                "finalized externally paid protocol-fee atoms",
                "canonical source-lot lineage and single-use nullifier",
                "release-selected service, lock, proof, and finality receipts",
                "named prefunded role budgets and exact remaining capacity",
            ],
            "unobservable_or_incomplete_inputs": [
                "real-world beneficial-owner uniqueness",
                "off-ledger side payments and fee recapture",
                "external spot, option, lending, or perpetual positions",
                "whether nominally distinct wallets form one coalition",
            ],
        },
        "attack_query": {
            "query": "exists admitted coalition action with total economic profit_atoms > 0",
            "direct_program_profit": (
                "protocol_funded_benefit - irreversible_external_protocol_fee "
                "- nonrecaptured_costs - forfeiture - expected_slash"
            ),
            "excluded_from_bounded_result": [
                "external market positions",
                "unobserved related-party fee recapture",
                "oracle and derivative manipulation gains",
                "behavioral adoption or retention claims",
            ],
        },
        "bounded_model": {
            "integer_domain": "all accounting quantities are integer atoms in [0, 2^256 - 1]",
            "source_lot_registry": lot_registry,
            "flywheel_sequence": [
                "genuine finalized use pays an external protocol fee",
                "the per-asset waterfall closes safety, service, and operations shortfalls",
                "a selected small share of the remainder reserves delayed future-fee credits",
                "the eligible remainder buys ZDEX and atomically burns the acquired amount",
                "credit redemption requires a later fee-paying use and continued ZDEX lock",
                "early unlock cancels credit and expired reserves return to buyback carry",
            ],
            "priority_waterfall": [
                {
                    "priority": 0,
                    "id": "P0_PROPERTY_AND_ACCRUED_ENTITLEMENTS",
                    "rule": (
                        "Reconcile user balances, LP principal and LP-owned fees, "
                        "Stability Pool principal, bonds, backstop principal, and "
                        "already accrued claims in separate custody."
                    ),
                },
                {
                    "priority": 1,
                    "id": "P1_SAFETY_AND_SOLVENCY",
                    "rule": "Fund release-selected insurance, solvency, and safety minima.",
                },
                {
                    "priority": 2,
                    "id": "P2_PARTICIPANT_AND_SERVICE_COMPENSATION",
                    "rule": (
                        "Prefund and pay proof, validator, oracle, keeper, "
                        "liquidator, solver, relayer, Stability Pool reward, and "
                        "other selected service contracts."
                    ),
                },
                {
                    "priority": 3,
                    "id": "P3_OPERATIONS",
                    "rule": (
                        "Fund capped hosting, infrastructure, security, legal, "
                        "audit, maintenance, and contributor obligations."
                    ),
                },
                {
                    "priority": 4,
                    "id": "G_GROWTH_RESERVE",
                    "rule": (
                        "Optionally reserve a selected capped share for delayed "
                        "future-fee credits; zero while unselected."
                    ),
                },
                {
                    "priority": 5,
                    "id": "X_BUYBACK_OR_TYPED_CARRY",
                    "rule": (
                        "Route the remaining eligible surplus to guarded buyback "
                        "or preserve it as same-purpose carry."
                    ),
                },
            ],
            "surplus_definition": {
                "revenue_set": (
                    "R[a,e] contains only finalized, unrestricted, externally "
                    "funded protocol-revenue lots in asset a and epoch e"
                ),
                "excluded": [
                    "all P0 property and liabilities",
                    "genesis and treasury principal",
                    "purpose-bound service and operations prefunds",
                    "refundable bonds and unadmitted slash value",
                    "credit reserves and buyback carry",
                    "internal reserve releases and circular fee-credit value",
                ],
                "formula": [
                    "shortfall_Pn = max(0, release_selected_required_Pn - existing_same_purpose_prefund_Pn)",
                    "required_funding = shortfall_P1 + shortfall_P2 + shortfall_P3",
                    "require required_funding <= R; otherwise no surplus allocation exists",
                    "pre_growth_surplus = R - required_funding",
                    "0 <= growth_reserve <= floor(growth_reserve_bps * pre_growth_surplus / 10000)",
                    "eligible_surplus = pre_growth_surplus - growth_reserve",
                    "buyback_execution + buyback_carry = eligible_surplus",
                ],
                "interpretation": (
                    "Surplus is the unrestricted remainder after all due and "
                    "selected reserve, service, and operating allocations. An "
                    "unfunded promised cost makes surplus zero and blocks the "
                    "affected feature; it cannot be relabeled as burn money."
                ),
                "cross_asset_rule": (
                    "Every equation is per asset. Cross-asset funding requires an "
                    "exact release-selected conversion receipt before allocation."
                ),
            },
            "funding_sources": {
                "bootstrap": {
                    "candidate": (
                        "Separately selected genesis or treasury lots may prefund "
                        "qualified launch service budgets."
                    ),
                    "current_authority": "NONE_DISTRIBUTION_AND_ROLE_AMOUNTS_UNSELECTED",
                },
                "recurring": [
                    "selected protocol share of finalized swap or auction fees",
                    "selected protocol-owned perps, borrowing, redemption, or liquidation fees",
                    "explicit opt-in interface or API fees kept distinct from LP and protocol fees",
                    "verified user-granted execution improvement for the solver that produced it",
                ],
                "restricted_nonrevenue": [
                    "LP and user property pays only its owner or authenticated settlement",
                    "Stability Pool and backstop principal absorbs only selected contractual risk",
                    "bonds return to owners or become admitted slash proceeds with restricted destinations",
                ],
                "role_routes": {
                    "proof_market": "P2 role-specific proof-reward prefund; direct execution survives exhaustion",
                    "validators": "P2 or P3 validator-operations prefund required before validator profile activation",
                    "oracles": "P2 role-specific reporter, aggregator, disputer, and watcher budgets plus separate bonds",
                    "stability_pool": "P0 principal and liquidation entitlement; optional separately prefunded P2 reward",
                    "keepers_liquidators_solvers_relayers": "P2 service budgets or exact user-granted improvement where applicable",
                    "hosting_security_legal_operations": "P3 capped budgets or separately quoted opt-in interface fee",
                },
                "insufficiency_rule": (
                    "No service may earn an uncapped unfunded claim. The affected "
                    "optional lane disables or carries pending work; release-critical "
                    "services require bootstrap runway before activation."
                ),
                "compensation_asset_rule": (
                    "A later profile must choose each role's payment asset. A "
                    "genesis ZDEX service reserve releases existing supply; fee-"
                    "asset payment consumes protocol revenue. Neither is implied here."
                ),
            },
            "volume_and_retention_policy": {
                "wallet_count_reward_weight": 0,
                "transaction_count_reward_weight": 0,
                "passive_wallet_balance_reward_weight": 0,
                "permanent_raw_nominal_volume_emission_weight": 0,
                "recommended_self_executing_basis": (
                    "finalized irreversible external protocol-fee atoms, with "
                    "continuous ZDEX lock and a global benefit cap below those fees"
                ),
                "why_fee_linked": (
                    "At a fixed fee rate, paid fees track volume while measuring "
                    "the attacker's nonrefundable economic input directly. Zero-fee "
                    "or rebated turnover contributes zero qualifying fee."
                ),
                "deterministic_campaign_formula": [
                    "qualifying_fee_i = sum(finalized external protocol-fee atoms not funded by credits or rebates)",
                    "ranking_score_i = qualifying_fee_i * selected_lock_weight_i",
                    "award_i <= floor(event_benefit_bps * qualifying_fee_i / 10000)",
                    "sum(awards) <= named_prefunded_campaign_budget",
                    "0 <= event_benefit_bps < 10000",
                ],
                "raw_volume_campaign_option": {
                    "status": "RESEARCH_ONLY_NONPROMOTABLE_WITHOUT_SEPARATE_MODEL",
                    "allowed_role": (
                        "A bounded time-limited marketing campaign may use nominal "
                        "volume as a threshold or leaderboard signal."
                    ),
                    "required_nonclaim": (
                        "Fixed prize pools, identity screens, and wash-trade "
                        "disqualification bound treasury loss; they do not prove "
                        "permissionless manipulation resistance."
                    ),
                },
            },
            "credit_lifecycle": {
                "earn": "credit <= floor(earn_bps * irreversible cash fee / 10000) and named reserve",
                "mature": "requires a later epoch and continuous-lock witness",
                "redeem": "credit <= floor(redemption_bps * later gross fee / 10000)",
                "settlement_identity": "external cash fee + reserve release = gross fee",
                "early_unlock": "cancel all pending credit into buyback carry",
                "expiry": "close remaining liability into buyback carry",
                "prohibitions": [
                    "no transfer, cash redemption, ZDEX redemption, or same-event earn-and-redeem",
                    "reserve release cannot generate another credit or count as external revenue",
                ],
            },
            "candidate_parameter_ranges": {
                "growth_reserve_bps": {"minimum": 500, "maximum": 2_000, "hard_maximum": 2_500},
                "earn_bps": {"minimum": 500, "maximum": 1_500, "hard_maximum_exclusive": 10_000},
                "redemption_bps": {"minimum": 1_000, "maximum": 2_500, "hard_maximum_exclusive": 10_000},
                "event_benefit_bps": {"minimum": 500, "maximum": 2_500, "hard_maximum_exclusive": 10_000},
                "maturity_epochs": {"minimum": 30, "maximum": 90},
                "expiry_epochs": {"minimum": 180, "maximum": 365},
                "lock_epochs": {"candidates": [90, 180, 365]},
                "lock_value_multiple_bps": {"minimum": 20_000, "maximum": 100_000},
                "aggregate_liability_bps": {"minimum": 100, "maximum": 500},
            },
            "selected_parameters": contract.SELECTED_CLBF_PARAMETERS,
        },
        "bounded_attack_evidence": bounded_attack_evidence(),
        "comparative_context": {
            "status": "NON_NORMATIVE_LINKS_RECHECK_BEFORE_SELECTION",
            "observed_on": "2026-08-16",
            "items": [
                {
                    "protocol": "PulseX",
                    "observation": (
                        "Its official page describes swap fees, an LP share, a "
                        "possible buy-and-burn share, and a separate LP incentive "
                        "token; this is not evidence of a permanent trader raw-volume payout."
                    ),
                    "url": "https://pulsex.com/",
                },
                {
                    "protocol": "PancakeSwap campaigns",
                    "observation": (
                        "Official limited campaigns have used volume thresholds, "
                        "leaderboards, fixed prize pools, and discretionary "
                        "wash/self-dealing disqualification."
                    ),
                    "url": (
                        "https://blog.pancakeswap.finance/articles/"
                        "trade-tst-trump-pepe-and-more-tokens-on-pancake-swap-"
                        "perpetual-v2-on-chain-and-share-a-10-000-prize-pool"
                    ),
                },
                {
                    "protocol": "PancakeSwap perpetual trading rewards",
                    "observation": (
                        "The published rewards model weights effective trading "
                        "fees and staking and uses a daily reward cap."
                    ),
                    "url": (
                        "https://docs.pancakeswap.finance/trade/perpetual-trading/"
                        "perpetual-trading-v2/trading-rewards-program"
                    ),
                },
            ],
        },
        "evidence_lane": {
            "deterministic_checks": [
                "closed source-lot routing registry",
                "exact input-allocation and successor conservation",
                "single-use source-lot replay rejection",
                "credit reserve equals pending plus matured liability",
                "reject-is-no-op for lot and credit transitions",
                "finite exact direct-profit, event-cap, and Sybil-split searches",
                "named profitable semantic mutants",
            ],
            "required_before_selection": [
                "complete participant amounts, assets, caps, claimant witnesses, and terminal paths",
                "stateful coalition simulation including related LP, host, solver, and external positions",
                "formal per-asset conservation and global benefit-composition proofs",
                "legal and tax classification for genesis, rewards, credits, and service payments",
                "runtime, migration, mounting, and exact release evidence",
            ],
        },
        "promotion_boundary": {
            "claim": (
                "The research model makes restricted-fund routes explicit and "
                "establishes finite direct bounds for fee-linked benefits below 100%."
            ),
            "nonclaims": [
                "No CLBF parameter, payment, genesis transfer, or raw-volume campaign is selected.",
                "The model does not establish adoption, retention, token price, or legal treatment.",
                "Finite searches do not prove unbounded arithmetic or coalition safety with external positions.",
                "The Python model is unmounted and is not a ZenoLedger settlement implementation.",
                "Source-lot validation does not authorize a source lot or authenticate a service receipt.",
            ],
        },
        "activation_gate": {
            "selected_parameter_count": 0,
            "participant_compensation_complete": False,
            "genesis_distribution_complete": False,
            "formal_composition_complete": False,
            "runtime_implemented": False,
            "mounted": False,
            "tested_exact_release": False,
            "activation_allowed": False,
            "production_ready": False,
        },
    }


def _load_json_no_duplicates(path: Path) -> object:
    def pairs_hook(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        duplicates: list[str] = []
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        if duplicates:
            raise ValueError(
                "duplicate JSON keys: " + ", ".join(sorted(set(duplicates)))
            )
        return result

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs_hook)


def check_artifact(
    path: Path = DEFAULT_OUTPUT,
    repo_root: Path = REPO_ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        expected = build_document(repo_root)
        observed = _load_json_no_duplicates(path)
        if not isinstance(observed, dict):
            errors.append("artifact root must be an object")
        elif path.read_bytes() != _encoded(expected):
            errors.append("artifact bytes or semantics differ from generated CLBF model")
    except (OSError, ValueError, json.JSONDecodeError, subprocess.SubprocessError) as exc:
        errors.append(str(exc))

    return {
        "ok": not errors,
        "artifact": str(path),
        "errors": errors,
        "selected_parameter_count": 0,
        "activation_allowed": False,
        "production_ready": False,
    }


def _write_atomic(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
    )
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_path, path)
        directory_descriptor = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_descriptor)
        finally:
            os.close(directory_descriptor)
    finally:
        if temporary_path.exists():
            temporary_path.unlink()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, _encoded(build_document()))
    report: dict[str, Any] = check_artifact(args.output) if args.check else {
        "ok": True,
        "activation_allowed": False,
        "production_ready": False,
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif args.check:
        print("PASS" if report["ok"] else "FAIL")
        for error in report.get("errors", []):
            print(f"- {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
