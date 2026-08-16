#!/usr/bin/env python3
"""Generate and check the research-only G1 participant-service funding model."""

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
DEFAULT_OUTPUT = (
    REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_SERVICE_FUNDING_V1.json"
)
SCHEMA = "zenodex/production-readiness-g1-service-funding/v1"
RESEARCH_SOURCE_SUBJECT = "5398d2faa32216be513b61c6cd2f0125564a01e9"
CONTRACT_PATH = "tools/production_readiness_g1_service_funding_contract_v1.py"
CHECKER_PATH = "tools/check_production_readiness_g1_service_funding_v1.py"

sys.path.insert(0, str(REPO_ROOT))

from tools import production_readiness_g1_service_funding_contract_v1 as contract  # noqa: E402

EXPECTED_BOUNDARIES = {
    "spot_trader_and_order_user": "PROPERTY_OR_LIABILITY",
    "liquidity_provider": "PROPERTY_OR_LIABILITY",
    "zusd_borrower_and_redeemer": "PROPERTY_OR_LIABILITY",
    "stability_pool_depositor": "PROPERTY_WITH_OPTIONAL_REWARD",
    "liquidator_and_keeper": "SERVICE_BUDGET",
    "oracle_reporter_aggregator_disputer_and_watcher": "SERVICE_BUDGET",
    "perps_trader_and_funding_counterparty": "PROPERTY_OR_LIABILITY",
    "insurance_and_bad_debt_backstop": "SERVICE_BUDGET",
    "sealed_bid_seller": "PROPERTY_OR_LIABILITY",
    "sealed_bid_bidder_and_private_swap_party": "PROPERTY_OR_LIABILITY",
    "tau_depositor_and_withdrawer": "PROPERTY_OR_LIABILITY",
    "tau_relayer_and_destination_operator": "SERVICE_BUDGET",
    "proof_prover_and_proof_miner": "SERVICE_BUDGET",
    "validator_finality_operator": "SERVICE_BUDGET",
    "solver_batcher_and_sequencer": "SERVICE_BUDGET",
    "interface_api_and_static_host": "OPERATIONS_OR_SERVICE_BUDGET",
    "security_auditor_and_bounty_researcher": "OPERATIONS_OR_SERVICE_BUDGET",
    "core_contributor_contractor_and_operations_provider": (
        "OPERATIONS_OR_SERVICE_BUDGET"
    ),
    "liquidity_bootstrapper_and_market_maker": (
        "SERVICE_OR_DISTRIBUTION_PROGRAM"
    ),
    "community_testnet_and_usage_award_recipient": "DISTRIBUTION_PROGRAM",
    "founder_team_partner_and_capital_recipient": "GENESIS_DISTRIBUTION_PROGRAM",
    "protocol_treasury_reserve_and_buyburn_executor": "RESERVE_AND_EXECUTION",
}

EXPECTED_BUDGET_ROLE_IDS = frozenset(
    role_id
    for role_id, boundary in EXPECTED_BOUNDARIES.items()
    if boundary
    in {
        "PROPERTY_WITH_OPTIONAL_REWARD",
        "SERVICE_BUDGET",
        "OPERATIONS_OR_SERVICE_BUDGET",
        "SERVICE_OR_DISTRIBUTION_PROGRAM",
    }
)

COMMON_FUNDING_SOURCE_VALUES = frozenset(
    {
        "DEPLOYMENT_CAPITAL_PREFUND",
        "SELECTED_GENESIS_SERVICE_LOT",
        "FINALIZED_PROTOCOL_REVENUE_PREFUND",
    }
)

EXPECTED_FUNDING_SOURCES = {
    role_id: COMMON_FUNDING_SOURCE_VALUES for role_id in EXPECTED_BUDGET_ROLE_IDS
}
EXPECTED_FUNDING_SOURCES["liquidator_and_keeper"] |= {"SELECTED_ACTION_FEE"}
EXPECTED_FUNDING_SOURCES["tau_relayer_and_destination_operator"] |= {
    "EXPLICIT_EXTERNAL_IO_FEE"
}
EXPECTED_FUNDING_SOURCES["solver_batcher_and_sequencer"] |= {
    "USER_GRANTED_EXECUTION_IMPROVEMENT"
}
EXPECTED_FUNDING_SOURCES["interface_api_and_static_host"] |= {
    "SIGNED_USER_INTERFACE_FEE"
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
        if (repo_root / path).read_bytes() != frozen:
            raise ValueError(f"service-funding research source drift: {path}")
        pins.append(
            {
                "path": path,
                "sha256": _sha256(frozen),
                "subject": RESEARCH_SOURCE_SUBJECT,
            }
        )
    return pins


def _validate_contract() -> tuple[
    dict[str, dict[str, str | None]],
    dict[str, list[str]],
]:
    routes = contract.participant_funding_registry_v1()
    observed_boundaries = {
        role_id: route.boundary.value for role_id, route in routes.items()
    }
    if observed_boundaries != EXPECTED_BOUNDARIES:
        raise ValueError("participant funding boundaries differ from the checker")
    if contract.ALL_PARTICIPANT_IDS != frozenset(EXPECTED_BOUNDARIES):
        raise ValueError("participant funding registry does not cover exact 22 roles")
    if contract.BUDGET_ELIGIBLE_ROLE_IDS != EXPECTED_BUDGET_ROLE_IDS:
        raise ValueError("budget-eligible role set differs from the checker")
    if set(contract.SELECTED_ROLE_BUDGETS) != EXPECTED_BUDGET_ROLE_IDS:
        raise ValueError("selected role-budget registry has wrong role set")
    if any(value is not None for value in contract.SELECTED_ROLE_BUDGETS.values()):
        raise ValueError("role budgets must remain unselected in this artifact")

    observed_sources = {
        role_id: frozenset(source.value for source in sources)
        for role_id, sources in contract.allowed_funding_sources_v1().items()
    }
    if observed_sources != EXPECTED_FUNDING_SOURCES:
        raise ValueError("role funding-source registry differs from the checker")

    route_rows = {
        role_id: {
            "boundary": route.boundary.value,
            "service_criticality": (
                route.service_criticality.value
                if route.service_criticality is not None
                else None
            ),
            "unfunded_behavior": route.unfunded_behavior,
        }
        for role_id, route in sorted(routes.items())
    }
    source_rows = {
        role_id: sorted(sources)
        for role_id, sources in sorted(observed_sources.items())
    }
    return route_rows, source_rows


@lru_cache(maxsize=1)
def bounded_funding_evidence() -> dict[str, Any]:
    payment_counterexample: dict[str, int] | None = None
    payment_cases = 0
    for reserve_atoms in range(17):
        for period_cap_atoms in range(1, 9):
            for period_spent_atoms in range(period_cap_atoms + 1):
                for job_cap_atoms in range(1, 9):
                    for request_atoms in range(1, 11):
                        accepted = (
                            request_atoms <= job_cap_atoms
                            and period_spent_atoms + request_atoms
                            <= period_cap_atoms
                            and request_atoms <= reserve_atoms
                        )
                        payment_cases += 1
                        if not accepted:
                            continue
                        remaining = reserve_atoms - request_atoms
                        updated_spent = period_spent_atoms + request_atoms
                        if (
                            remaining < 0
                            or updated_spent > period_cap_atoms
                            or request_atoms > job_cap_atoms
                        ):
                            payment_counterexample = {
                                "reserve_atoms": reserve_atoms,
                                "period_cap_atoms": period_cap_atoms,
                                "period_spent_atoms": period_spent_atoms,
                                "job_cap_atoms": job_cap_atoms,
                                "request_atoms": request_atoms,
                            }
                            break

    runway_counterexample: dict[str, int] | None = None
    runway_cases = 0
    for reserve_atoms in range(33):
        for period_cap_atoms in range(1, 9):
            for target_periods in range(1, 9):
                required = period_cap_atoms * target_periods
                shortfall = max(0, required - reserve_atoms)
                funded = reserve_atoms // period_cap_atoms
                target_met = shortfall == 0
                runway_cases += 1
                if target_met != (funded >= target_periods):
                    runway_counterexample = {
                        "reserve_atoms": reserve_atoms,
                        "period_cap_atoms": period_cap_atoms,
                        "target_periods": target_periods,
                    }
                    break

    return {
        "accepted_payment_bound_search": {
            "domain": (
                "reserve=0..16; period_cap=1..8; spent=0..cap; "
                "job_cap=1..8; request=1..10"
            ),
            "cases": payment_cases,
            "counterexample": payment_counterexample,
            "predicate": (
                "accepted and (remaining<0 or updated_spent>period_cap "
                "or request>job_cap)"
            ),
        },
        "runway_shortfall_search": {
            "domain": "reserve=0..32; period_cap=1..8; target_periods=1..8",
            "cases": runway_cases,
            "counterexample": runway_counterexample,
            "predicate": "target_met differs from funded_full_periods >= target_periods",
        },
        "named_mutant_witnesses": [
            {
                "id": "MISSING_RESERVE_CHECK",
                "reserve_atoms": 0,
                "payment_atoms": 1,
                "loss_atoms": 1,
            },
            {
                "id": "MISSING_PERIOD_CAP",
                "period_cap_atoms": 4,
                "already_spent_atoms": 4,
                "payment_atoms": 1,
                "loss_atoms": 1,
            },
            {
                "id": "MISSING_JOB_NULLIFIER",
                "first_payment_atoms": 5,
                "duplicate_payment_atoms": 5,
                "loss_atoms": 5,
            },
            {
                "id": "SILENT_FIXED_OBLIGATION_EXPIRY",
                "unpaid_fixed_atoms": 10,
                "loss_atoms": 10,
            },
            {
                "id": "MISSING_TOPUP_NULLIFIER",
                "first_topup_atoms": 5,
                "duplicate_topup_atoms": 5,
                "loss_atoms": 5,
            },
        ],
        "claim_ceiling": (
            "Exact only for the finite declared integer domains and direct "
            "budget arithmetic. Work correctness, market selection, claimant "
            "identity, legal status, and future revenue remain external premises."
        ),
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    route_rows, source_rows = _validate_contract()
    source_pins = _source_pins(repo_root)

    return {
        "schema": SCHEMA,
        "status": "RESEARCH_ONLY_UNSELECTED",
        "production_promotion": False,
        "reviewed_subject": RESEARCH_SOURCE_SUBJECT,
        "research_source_pins": source_pins,
        "implementation_source_pins": [
            {
                "path": CONTRACT_PATH,
                "sha256": _sha256((repo_root / CONTRACT_PATH).read_bytes()),
            },
            {
                "path": CHECKER_PATH,
                "sha256": _sha256((repo_root / CHECKER_PATH).read_bytes()),
            },
        ],
        "game_surface": {
            "players": sorted(EXPECTED_BOUNDARIES),
            "actions": [
                "prefund one role-specific budget in one payment asset",
                "admit fixed or variable service work",
                "pay, replay, exhaust, top up, advance, disable, or replace a role",
                "select a recipient by proof market, auction, mining, governance, or procurement",
            ],
            "authoritative_state": [
                "purpose-bound reserve atoms",
                "period cap and spent atoms",
                "fixed obligation status and variable job count",
                "paid job nullifiers",
                "policy, work-witness, claimant, period, and asset bindings",
            ],
            "unobservable_or_external": [
                "real-world beneficial ownership and related parties",
                "legal classification and tax treatment",
                "whether submitted work is correct before a production verifier admits it",
                "future fee volume, asset prices, and off-ledger service costs",
            ],
        },
        "attack_query": {
            "query": (
                "Can a role receive duplicate, cross-role, cross-asset, "
                "over-cap, unfunded, or unverifiable payment, or can a fixed "
                "obligation disappear during period advance?"
            ),
            "disaster_states": [
                "USER_OR_LP_PROPERTY_FUNDS_A_SERVICE",
                "PROOF_MARKET_CREATES_AN_UNFUNDED_REWARD",
                "DUPLICATE_JOB_PAYMENT",
                "PERIOD_OR_JOB_CAP_BYPASS",
                "UNPAID_FIXED_SERVICE_SILENTLY_EXPIRES",
                "UNFUNDED_CRITICAL_PERIOD_ACTIVATES",
                "GENESIS_INVENTORY_IS_RELABELED_AS_CASH_REVENUE",
            ],
        },
        "bounded_model": {
            "integer_domain": "all accounting quantities are integer atoms in [0, 2^256 - 1]",
            "participant_funding_registry": route_rows,
            "allowed_funding_sources": source_rows,
            "selected_role_budgets": contract.SELECTED_ROLE_BUDGETS,
            "runway_contract": {
                "maximum_period_liability": (
                    "fixed_atoms_per_period + maximum_jobs_per_period "
                    "* maximum_atoms_per_job"
                ),
                "admission_rule": "maximum_period_liability <= period_cap_atoms",
                "required_prefund": (
                    "period_cap_atoms * target_prefund_periods"
                ),
                "funded_full_periods": (
                    "opening_reserve_atoms // period_cap_atoms"
                ),
                "prefund_shortfall": (
                    "max(0, required_prefund - opening_reserve_atoms)"
                ),
                "period_activation": (
                    "remaining_reserve_atoms >= period_cap_atoms"
                ),
                "candidate_critical_runway_months": {
                    "minimum": 18,
                    "maximum": 36,
                    "status": "PROPOSED_UNSELECTED",
                    "conversion_requirement": (
                        "A selected block schedule must convert calendar months "
                        "to exact budget periods before activation."
                    ),
                },
            },
            "payment_contract": [
                "payment role, asset, policy, period, claimant, job, and admitted-work root must bind",
                "fixed payment equals the declared fixed liability exactly and occurs once",
                "variable payment <= per-job cap and job count <= period maximum",
                "period_spent + payment <= period cap",
                "payment <= remaining purpose-bound reserve",
                "each job id is consumed once across all later periods",
                "each admitted top-up source id is consumed once and preserves the payment asset",
                "period advance cannot erase an unpaid fixed obligation",
                "the next period activates only with its complete cap prefunded",
                "reject leaves reserve, counters, obligations, and nullifiers unchanged",
            ],
            "source_and_selector_separation": {
                "rule": (
                    "A proof market, auction, mining rule, usage rule, or "
                    "governance process may select a claimant and requested "
                    "amount. It cannot create the payment source."
                ),
                "payment_formula": [
                    "require admitted_requested_atoms <= per_job_cap",
                    "require admitted_requested_atoms <= remaining_period_cap",
                    "require admitted_requested_atoms <= remaining_reserve",
                    "paid_atoms = admitted_requested_atoms",
                ],
                "production_requirement": (
                    "Selection output becomes an opaque admitted-work witness "
                    "only after the release-selected verifier accepts it."
                ),
            },
            "bootstrap_and_recurring_sources": {
                "bootstrap": [
                    "purpose-bound deployment capital in the promised payment asset",
                    "a separately selected and counsel-activated genesis service lot",
                ],
                "recurring": [
                    "finalized protocol revenue routed through its selected P2 or "
                    "P3 target after P0 and P1 reconciliation and before growth "
                    "or buyback surplus",
                    "selected action or external-I/O fee for the corresponding role",
                    "signed opt-in interface fee for an independent host",
                    "verified user-granted execution improvement for a solver",
                ],
                "genesis_rule": (
                    "Genesis ZDEX is distribution inventory. It cannot satisfy "
                    "a stable-asset liability without an admitted conversion, "
                    "and its release increases observable liquid supply."
                ),
                "future_revenue_rule": (
                    "Forecast revenue may support sensitivity analysis. Only "
                    "already purpose-bound reserve counts as prefunded runway."
                ),
            },
            "role_specific_exhaustion": {
                role_id: row["unfunded_behavior"]
                for role_id, row in route_rows.items()
                if row["service_criticality"] is not None
            },
            "distribution_boundary": {
                "service_compensation": (
                    "May activate only after asset, source, amount, cap, witness, "
                    "claimant, custody, replay, exhaustion, terminal, legal, and "
                    "release fields are selected."
                ),
                "genesis_and_community_distribution": (
                    "Remain separately disabled pending beneficial-owner, "
                    "vesting, custody, anti-sybil, tax, counsel, and release roots."
                ),
            },
        },
        "bounded_funding_evidence": bounded_funding_evidence(),
        "evidence_lane": {
            "current": [
                "closed 22-participant classification",
                "closed role-specific funding-source registry",
                "checked integer runway evaluator",
                "typed fixed, variable, replay, exhaustion, and period transitions",
                "typed replay-protected recurring-revenue top-up transition",
                "finite independent overspend and runway searches",
                "named overspend, replay, and unpaid-obligation mutants",
            ],
            "required_before_selection": [
                "payment asset and amount for every enabled role",
                "independent operating-cost and fee-revenue evidence",
                "worst-case job arrival and replacement assumptions",
                "release-selected work verifiers and opaque witnesses",
                "cross-role stacking and related-party coalition model",
                "legal, tax, employment, securities, and distribution review",
            ],
            "required_before_production": [
                "Rust production transition and canonical codec",
                "formal per-asset conservation, replay, and exhaustion proofs",
                "mounted ZenoLedger payment capability and no-bypass inventory",
                "migration, restart, authority-epoch, and exact-release tests",
            ],
        },
        "approval_packet": {
            "status": "NOT_READY_FOR_BLANKET_APPROVAL",
            "next_decisions": [
                "choose payment asset and target runway unit for each critical role",
                "choose fixed versus per-job compensation and exact caps",
                "choose bootstrap source without treating genesis ZDEX as revenue",
                "choose recurring protocol fee lanes and exhaustion behavior",
                "choose work verifier, claimant credential, bond, slash, and terminal rule",
                "obtain counsel activation independently from genesis distribution",
            ],
            "recommended_staging": [
                "fund consensus and risk-critical roles before launch",
                "launch optional proof scaling only with direct-execution fallback",
                "keep optional growth and distribution programs disabled initially",
                "top up role reserves before computing eligible burn surplus",
            ],
        },
        "promotion_boundary": {
            "claim": (
                "The research model prevents direct arithmetic overspend and "
                "silent fixed-obligation expiry inside its typed finite model."
            ),
            "nonclaims": [
                "No role budget, payment asset, amount, runway, fee lane, or recipient is selected.",
                "Caller-constructible Python work witnesses provide no production authority.",
                "The model does not prove service quality, future revenue, claimant identity, or legal status.",
                "The model is unmounted and cannot pay a participant or move genesis inventory.",
                "Finite enumeration is not an unbounded proof or a production readiness receipt.",
            ],
        },
        "activation_gate": {
            "participant_count": 22,
            "budget_eligible_role_count": len(EXPECTED_BUDGET_ROLE_IDS),
            "selected_budget_count": 0,
            "critical_role_assets_selected": False,
            "critical_role_runway_selected": False,
            "work_verifiers_selected": False,
            "legal_activation_complete": False,
            "runtime_implemented": False,
            "mounted": False,
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
            errors.append(
                "artifact bytes or semantics differ from generated service-funding model"
            )
    except (OSError, ValueError, json.JSONDecodeError, subprocess.SubprocessError) as exc:
        errors.append(str(exc))
    return {
        "ok": not errors,
        "artifact": str(path),
        "errors": errors,
        "selected_budget_count": 0,
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
