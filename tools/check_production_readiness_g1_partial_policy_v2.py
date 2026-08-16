#!/usr/bin/env python3
"""Check the exact G1 partial policy and participant-compensation hold."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_PARTIAL_POLICY_V2.json"
SCHEMA = "zenodex/production-readiness-g1-partial-policy/v2"
RESEARCH_SOURCE_SUBJECT = "5361df3ad977a53a7a773cc53730fc57405e25fc"

EXPECTED_SUPPLY_DECISION = (
    "ZDEX",
    2_000_000_000,
    18,
    1,
    200_000_000,
)
EXPECTED_SCALED_MODELING_ALLOCATIONS = (
    ("founder_original_rd", 1_500, 300_000_000),
    ("core_team_future_contributors", 1_000, 200_000_000),
    ("dao_protocol_treasury", 2_500, 500_000_000),
    ("ecosystem_lp_solver_operator_proof_incentives", 2_500, 500_000_000),
    ("community_retroactive_airdrop_testnet_users", 1_000, 200_000_000),
    ("security_audits_bounties_insurance_reserve", 500, 100_000_000),
    ("liquidity_bootstrap_market_making", 500, 100_000_000),
    ("strategic_partners_investors_chain_partners", 500, 100_000_000),
)
EXPECTED_COMPENSATION_SELECTION_FIELDS = (
    "compensation_asset",
    "funding_source",
    "amount_and_rounding_rule",
    "budget_and_epoch_cap",
    "eligibility_witness",
    "claimant_identity",
    "custody_account",
    "claim_and_nullifier_scope",
    "bond_and_slashing_rule",
    "failure_retry_and_exhaustion_rule",
    "conflict_sybil_and_self_dealing_controls",
    "terminal_disposition",
    "tax_counsel_and_legal_activation",
    "release_root",
)
EXPECTED_GENESIS_DISTRIBUTION_SELECTION_FIELDS = (
    "recipient_and_beneficial_owner_set",
    "allocation_atoms_per_recipient",
    "allocation_purpose",
    "eligibility_and_snapshot_rule",
    "claim_or_direct_delivery_mechanism",
    "vesting_cliff_unlock_and_remainder_rule",
    "transfer_and_resale_restrictions",
    "custody_and_key_recovery",
    "anti_sybil_wash_and_related_party_controls",
    "tax_accounting_compensation_and_counsel_review",
    "unclaimed_expired_and_terminal_disposition",
    "genesis_distribution_root",
)
EXPECTED_PARTICIPANT_IDS = frozenset(
    {
        "spot_trader_and_order_user",
        "liquidity_provider",
        "zusd_borrower_and_redeemer",
        "stability_pool_depositor",
        "liquidator_and_keeper",
        "oracle_reporter_aggregator_disputer_and_watcher",
        "perps_trader_and_funding_counterparty",
        "insurance_and_bad_debt_backstop",
        "sealed_bid_seller",
        "sealed_bid_bidder_and_private_swap_party",
        "tau_depositor_and_withdrawer",
        "tau_relayer_and_destination_operator",
        "proof_prover_and_proof_miner",
        "validator_finality_operator",
        "solver_batcher_and_sequencer",
        "interface_api_and_static_host",
        "security_auditor_and_bounty_researcher",
        "core_contributor_contractor_and_operations_provider",
        "liquidity_bootstrapper_and_market_maker",
        "community_testnet_and_usage_award_recipient",
        "founder_team_partner_and_capital_recipient",
        "protocol_treasury_reserve_and_buyburn_executor",
    }
)
EXPECTED_PAYMENT_PRIORITY_IDS = (
    "exact_user_property_and_accrued_liabilities",
    "selected_solvency_and_safety_minimums",
    "prefunded_contracted_service_compensation",
    "capped_operations_security_and_hosting",
    "eligible_surplus_buy_and_burn",
    "pending_policy_or_guarded_execution_carry",
)
EXPECTED_MECHANISM_IMPROVEMENT_IDS = frozenset(
    {
        "close_unnamed_fee_remainder",
        "disable_burn_indexed_insider_acceleration",
        "isolate_work_reward_budgets",
        "separate_host_payment_from_authority",
        "hold_activity_rewards_against_wash_and_legal_risk",
    }
)
EXPECTED_VOLUME_INCENTIVE_IDS = (
    "loss_bounded_future_fee_credit",
    "executable_depth_reverse_auction",
    "net_surplus_performance_milestone",
)

sys.path.insert(0, str(REPO_ROOT))

from tools import check_production_readiness_g1_profile_inputs as profile_inputs  # noqa: E402
from tools import check_production_readiness_g1_semantics as semantics  # noqa: E402
from tools import production_readiness_g1_partial_policy_contract_v2 as contract  # noqa: E402


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _plain(value: object) -> Any:
    return json.loads(json.dumps(value, sort_keys=True))


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
        frozen = _git_bytes(repo_root, "show", f"{RESEARCH_SOURCE_SUBJECT}:{path}")
        if (repo_root / path).read_bytes() != frozen:
            raise ValueError(f"partial-policy research source drift: {path}")
        pins.append(
            {
                "path": path,
                "sha256": _sha256(frozen),
                "subject": RESEARCH_SOURCE_SUBJECT,
            }
        )
    return pins


def _profile_input_binding(repo_root: Path) -> dict[str, object]:
    document = profile_inputs.build_document(repo_root)
    path = repo_root / profile_inputs.DEFAULT_OUTPUT.relative_to(profile_inputs.REPO_ROOT)
    report = profile_inputs.check_artifact(path, repo_root)
    if report["ok"] is not True:
        raise ValueError("source-pinned G1 profile inputs do not pass")
    observed = path.read_bytes()
    if observed != _encoded(document):
        raise ValueError("G1 profile-input bytes differ from generated document")
    return {
        "artifact": str(path.relative_to(repo_root)),
        "decision_count": len(document["decision_inputs"]),
        "open_decision_count": sum(
            entry["decision_status"] == "OPEN_UNSELECTED"
            for entry in document["decision_inputs"]
        ),
        "sha256": _sha256(observed),
        "status": "EXACT_RESEARCH_INPUT_PASS",
    }


def _validate_contract() -> tuple[set[str], set[str]]:
    supply_decision = (
        contract.ZDEX_SYMBOL,
        contract.ZDEX_WHOLE_SUPPLY,
        contract.ZDEX_DECIMALS,
        contract.ZDEX_ABSOLUTE_FLOOR_ATOMS,
        contract.ZDEX_LAUNCH_ACTIVE_FLOOR_WHOLE,
    )
    if supply_decision != EXPECTED_SUPPLY_DECISION:
        raise ValueError("ZDEX partial supply decision differs from exact approval")
    if contract.ZDEX_UNIT_SCALE != 10**contract.ZDEX_DECIMALS:
        raise ValueError("ZDEX unit scale does not match the selected decimals")
    if contract.ZDEX_GENESIS_SUPPLY_ATOMS != (
        contract.ZDEX_WHOLE_SUPPLY * contract.ZDEX_UNIT_SCALE
    ):
        raise ValueError("ZDEX genesis atoms do not match whole supply and scale")
    if contract.ZDEX_SUPPLY_CEILING_ATOMS != contract.ZDEX_GENESIS_SUPPLY_ATOMS:
        raise ValueError("ZDEX ceiling differs from the genesis supply")
    if contract.ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS != (
        contract.ZDEX_LAUNCH_ACTIVE_FLOOR_WHOLE * contract.ZDEX_UNIT_SCALE
    ):
        raise ValueError("ZDEX launch floor atoms do not match its whole-token value")
    if not (
        0
        < contract.ZDEX_ABSOLUTE_FLOOR_ATOMS
        <= contract.ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS
        < contract.ZDEX_GENESIS_SUPPLY_ATOMS
    ):
        raise ValueError("ZDEX floor ordering is invalid")
    allocation_rows = tuple(
        (
            allocation["id"],
            allocation["allocation_bps"],
            allocation["whole_tokens"],
        )
        for allocation in contract.SCALED_MODELING_ALLOCATIONS
    )
    if allocation_rows != EXPECTED_SCALED_MODELING_ALLOCATIONS:
        raise ValueError("scaled modeling allocations differ from exact approval")
    allocation_ids = [allocation[0] for allocation in allocation_rows]
    if len(allocation_ids) != len(set(allocation_ids)):
        raise ValueError("scaled modeling allocation ids are not unique")
    if sum(
        allocation["allocation_bps"]
        for allocation in contract.SCALED_MODELING_ALLOCATIONS
    ) != 10_000:
        raise ValueError("scaled modeling allocation basis points do not close")
    if sum(
        allocation["whole_tokens"]
        for allocation in contract.SCALED_MODELING_ALLOCATIONS
    ) != contract.ZDEX_WHOLE_SUPPLY:
        raise ValueError("scaled modeling allocations do not equal ZDEX supply")
    for allocation in contract.SCALED_MODELING_ALLOCATIONS:
        expected = (
            contract.ZDEX_WHOLE_SUPPLY * allocation["allocation_bps"] // 10_000
        )
        if allocation["whole_tokens"] != expected:
            raise ValueError(
                f"scaled modeling allocation is inconsistent: {allocation['id']}"
            )

    if (
        contract.COMPENSATION_SELECTION_FIELDS
        != EXPECTED_COMPENSATION_SELECTION_FIELDS
    ):
        raise ValueError("participant compensation selection fields differ")
    if (
        contract.GENESIS_DISTRIBUTION_SELECTION_FIELDS
        != EXPECTED_GENESIS_DISTRIBUTION_SELECTION_FIELDS
    ):
        raise ValueError("genesis distribution selection fields differ")
    expected_profile_decisions = set(profile_inputs.DECISION_INPUTS)
    if contract.PROFILE_DECISION_IDS != expected_profile_decisions:
        raise ValueError("partial policy does not bind the exact nine profile decisions")

    required_keys = {
        "id",
        "participant_class",
        "value_class",
        "payment_description",
        "affected_profile_decisions",
        "affected_commands",
        "must_have_explicit_economic_owner",
        "default_if_unselected",
    }
    participant_ids: set[str] = set()
    covered_decisions: set[str] = set()
    covered_commands: set[str] = set()
    expected_commands = {command.value for command in semantics.EXPECTED_COMMANDS}
    for participant in contract.PARTICIPANT_OBLIGATIONS:
        if set(participant) != required_keys:
            raise ValueError(
                f"participant obligation has wrong fields: {participant.get('id')}"
            )
        participant_id = participant["id"]
        if not isinstance(participant_id, str) or participant_id in participant_ids:
            raise ValueError("participant obligation ids must be unique strings")
        participant_ids.add(participant_id)
        decisions = set(participant["affected_profile_decisions"])
        commands = set(participant["affected_commands"])
        if not decisions or not decisions <= contract.PROFILE_DECISION_IDS:
            raise ValueError(f"participant has invalid decision coverage: {participant_id}")
        if not commands <= expected_commands:
            raise ValueError(f"participant has invalid command coverage: {participant_id}")
        if participant["must_have_explicit_economic_owner"] is not True:
            raise ValueError(f"participant can lose explicit ownership: {participant_id}")
        if participant["default_if_unselected"] != "AFFECTED_FEATURE_DISABLED":
            raise ValueError(f"participant obligation does not fail closed: {participant_id}")
        covered_decisions.update(decisions)
        covered_commands.update(commands)
    if participant_ids != EXPECTED_PARTICIPANT_IDS:
        raise ValueError("participant obligation set differs from exact inventory")
    if covered_decisions != contract.PROFILE_DECISION_IDS:
        raise ValueError("participant obligations do not cover all nine profile decisions")
    if covered_commands != expected_commands:
        raise ValueError("participant obligations do not cover all 33 commands")

    priorities = contract.MECHANISM_REVIEW.get("payment_priority_tiers")
    if not isinstance(priorities, tuple):
        raise ValueError("payment priority tiers must be an exact tuple")
    priority_ids = tuple(
        entry.get("id") for entry in priorities if isinstance(entry, Mapping)
    )
    priority_numbers = tuple(
        entry.get("priority") for entry in priorities if isinstance(entry, Mapping)
    )
    if priority_ids != EXPECTED_PAYMENT_PRIORITY_IDS or priority_numbers != tuple(
        range(len(EXPECTED_PAYMENT_PRIORITY_IDS))
    ):
        raise ValueError("payment priority tiers differ from exact waterfall")

    improvements = contract.MECHANISM_REVIEW.get("mechanism_improvements")
    if not isinstance(improvements, tuple):
        raise ValueError("mechanism improvements must be an exact tuple")
    improvement_by_id = {
        entry.get("id"): entry for entry in improvements if isinstance(entry, Mapping)
    }
    if set(improvement_by_id) != EXPECTED_MECHANISM_IMPROVEMENT_IDS:
        raise ValueError("mechanism improvement set differs")
    burn_hold = improvement_by_id["disable_burn_indexed_insider_acceleration"]
    if not str(burn_hold.get("closure", "")).startswith("HELD_FOR_LAUNCH"):
        raise ValueError("burn-indexed unlock no longer fails closed for launch")

    volume_stack = contract.MECHANISM_REVIEW.get(
        "recommended_volume_incentive_stack"
    )
    if not isinstance(volume_stack, tuple):
        raise ValueError("volume incentive stack must be an exact tuple")
    volume_ids = tuple(
        entry.get("id") for entry in volume_stack if isinstance(entry, Mapping)
    )
    ranks = tuple(
        entry.get("rank") for entry in volume_stack if isinstance(entry, Mapping)
    )
    if volume_ids != EXPECTED_VOLUME_INCENTIVE_IDS or ranks != (1, 2, 3):
        raise ValueError("volume incentive stack differs from exact candidate order")
    if any(
        not isinstance(entry, Mapping)
        or entry.get("status") != "PROPOSED_UNSELECTED"
        for entry in volume_stack
    ):
        raise ValueError("volume incentive candidate gained activation status")
    fee_credit_bounds = volume_stack[0].get("parameter_bounds")
    expected_fee_credit_bounds = {
        "earn_bps_minimum": 0,
        "earn_bps_maximum_exclusive": 10_000,
        "redemption_bps_minimum": 0,
        "redemption_bps_maximum_exclusive": 10_000,
        "total_incentive_bps_maximum_exclusive": 10_000,
    }
    if fee_credit_bounds != expected_fee_credit_bounds:
        raise ValueError("future fee-credit manipulation bounds differ")

    burn_candidate = contract.MECHANISM_REVIEW.get("burn_indexed_unlock_candidate")
    if not isinstance(burn_candidate, Mapping):
        raise ValueError("burn-indexed unlock candidate is missing")
    if burn_candidate.get("status") != "HELD_UNSELECTED" or burn_candidate.get(
        "historical_candidate_unlock_bps_of_eligible_burn"
    ) != 2_500:
        raise ValueError("burn-indexed unlock candidate gained authority or drifted")
    return covered_decisions, covered_commands


def _participant_entries() -> list[dict[str, object]]:
    selected_fields = {
        field: None for field in contract.COMPENSATION_SELECTION_FIELDS
    }
    return [
        {
            **entry,
            "status": "OPEN_UNSELECTED_COMPENSATION_POLICY",
            "production_authority": "NONE",
            "selected_policy": dict(selected_fields),
        }
        for entry in contract.PARTICIPANT_OBLIGATIONS
    ]


def _historical_candidate(repo_root: Path) -> dict[str, object]:
    path = repo_root / "internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json"
    value = json.loads(path.read_text(encoding="utf-8"))
    fee_split = value["value_capture"]["fee_split_bps"]
    allocation_total = sum(entry["amount"] for entry in value["allocations"])
    return {
        "status": "HISTORICAL_UNSELECTED_CONFLICT_INPUT",
        "path": str(path.relative_to(repo_root)),
        "historical_whole_supply": value["total_supply"],
        "historical_allocation_total": allocation_total,
        "historical_fee_split_declared_bps": sum(fee_split.values()),
        "historical_fee_split_status": "INCOMPLETE_2500_BPS_UNNAMED",
        "public_launch_allowed": value["launch"]["public_launch_allowed"],
        "current_selection_effect": "NONE",
        "scaling_rule": "SCALED_2X_AS_APPROVED_MODELING_BASELINE_ONLY",
    }


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    covered_decisions, covered_commands = _validate_contract()
    source_pins = _source_pins(repo_root)
    profile_binding = _profile_input_binding(repo_root)
    participants = _participant_entries()
    document = {
        "schema": SCHEMA,
        "version": "v2",
        "status": "PARTIAL_POLICY_SELECTED_COMPENSATION_AND_DISTRIBUTION_OPEN",
        "production_promotion": False,
        "policy_authority": "RESEARCH_RECORD_ONLY",
        "source_subject": {
            "research_commit": RESEARCH_SOURCE_SUBJECT,
            "current_head_must_descend_from_research_commit": True,
        },
        "source_pins": source_pins,
        "profile_input_binding": profile_binding,
        "decision_provenance": {
            "channel": "INTERACTIVE_USER_INSTRUCTION",
            "recorded_date": "2026-08-16",
            "cryptographic_user_signature": None,
            "exact_artifact_root_reapproval_required": True,
            "scaled_historical_allocation_modeling_approval": True,
            "scaled_allocation_activation_authority": "NONE_PENDING_LEGAL_AND_RELEASE_SELECTION",
        },
        "selected_parameters": {
            "selection_status": "SELECTED_FOR_G1_SPECIFICATION_ONLY",
            "zdex_symbol": contract.ZDEX_SYMBOL,
            "whole_token_supply": contract.ZDEX_WHOLE_SUPPLY,
            "decimals": contract.ZDEX_DECIMALS,
            "unit_scale": contract.ZDEX_UNIT_SCALE,
            "genesis_supply_atoms": contract.ZDEX_GENESIS_SUPPLY_ATOMS,
            "supply_ceiling_atoms": contract.ZDEX_SUPPLY_CEILING_ATOMS,
            "issue_authority": "GENESIS_ONLY",
            "post_genesis_mint": "FORBIDDEN",
            "absolute_floor_atoms": contract.ZDEX_ABSOLUTE_FLOOR_ATOMS,
            "launch_active_floor_whole_tokens": contract.ZDEX_LAUNCH_ACTIVE_FLOOR_WHOLE,
            "launch_active_floor_atoms": contract.ZDEX_LAUNCH_ACTIVE_FLOOR_ATOMS,
            "burn_rule": {
                "precondition": "supply_before_atoms >= active_floor_atoms",
                "excess_atoms": "supply_before_atoms - active_floor_atoms",
                "zeno_cap_atoms": "floor(excess_atoms / 2)",
                "admitted_burn_atoms": (
                    "min(acquired_atoms, zeno_cap_atoms, selected_epoch_cap_atoms, "
                    "selected_price_impact_cap_atoms)"
                ),
                "successor_supply": "supply_before_atoms - admitted_burn_atoms",
                "atomicity": "ACQUIRED_ZDEX_AND_SUPPLY_REDUCTION_COMMIT_TOGETHER",
                "zero_or_invalid_route": "REJECT_NO_COMMIT",
                "active_floor_change": "NEW_PROFILE_ROOT_AND_RELEASE_ONLY",
                "minimum_permitted_active_floor_atoms": 1,
            },
            "waterfall_order": (
                "PAY_EXACT_PROPERTY_AND_LIABILITY_ENTITLEMENTS_THEN_FUND_SELECTED_"
                "SAFETY_AND_OPERATIONS_OBLIGATIONS_THEN_ASSIGN_EXPLICIT_BUYBURN_BUDGET"
            ),
            "unallocated_or_unselected_revenue": "NAMED_PENDING_POLICY_CARRY_ONLY",
            "implicit_buyburn_or_treasury_sweep": "FORBIDDEN",
        },
        "participant_compensation_gate": {
            "status": "OPEN_UNSELECTED",
            "participant_count": len(participants),
            "open_participant_count": len(participants),
            "covered_profile_decisions": sorted(covered_decisions),
            "covered_command_count": len(covered_commands),
            "required_selection_fields": list(contract.COMPENSATION_SELECTION_FIELDS),
            "participants": participants,
            "activation_rule": (
                "Each affected feature remains disabled until every applicable "
                "participant row has an exact release-bound compensation and terminal policy."
            ),
            "mint_fallback": "FORBIDDEN",
        },
        "genesis_distribution_gate": {
            "status": "OPEN_UNSELECTED_COUNSEL_REQUIRED",
            "modeling_baseline_status": "APPROVED_SCALED_2X_FOR_ECONOMIC_MODELING",
            "scaled_modeling_allocations": contract.SCALED_MODELING_ALLOCATIONS,
            "scaled_modeling_allocation_total_whole_tokens": sum(
                entry["whole_tokens"]
                for entry in contract.SCALED_MODELING_ALLOCATIONS
            ),
            "selected_distribution_release": None,
            "required_selection_fields": list(
                contract.GENESIS_DISTRIBUTION_SELECTION_FIELDS
            ),
            "reconciliation": (
                f"sum(allocation_atoms) = {contract.ZDEX_GENESIS_SUPPLY_ATOMS}"
            ),
            "genesis_mint_allowed": False,
            "transfer_activation_allowed": False,
            "counsel_review_required": True,
            "counsel_review_complete": False,
            "legal_clearance_claim": False,
            "burn_indexed_insider_unlock_accelerator": (
                "HELD_UNSELECTED_PENDING_MANIPULATION_AND_COUNSEL_GATES"
            ),
            "distribution_mechanism_examples_are_unselected": (
                "proof_market",
                "proof_mining",
                "usage_based_award",
                "retroactive_or_testnet_distribution",
                "liquidity_program",
                "direct_or_vested_allocation",
            ),
        },
        "historical_candidate_conflict": _historical_candidate(repo_root),
        "mechanism_review": contract.MECHANISM_REVIEW,
        "g1_exit_gate": {
            "complete": False,
            "profile_complete": False,
            "launch_allowed": False,
            "production_ready": False,
            "blocking_reasons": (
                "participant compensation policies are unselected",
                "genesis recipients, allocations, vesting, custody, and legal activation are unselected",
                "fee splits, reward budgets, host funding, and buyback route parameters are unselected",
                "exact artifact root has no cryptographic user signature or release authority",
            ),
        },
        "nonclaims": (
            "No participant amount, asset, fee share, reward, budget, vesting term, or funding source is selected.",
            "The historical one-billion-token candidate and its allocation percentages have no current selection effect.",
            "Two billion tokens and E18 denomination do not predict price, market capitalization, adoption, or liquidity.",
            "A mathematical total-supply floor does not guarantee live float or market depth.",
            "Total supply can decline while vesting or reward releases increase protocol-observable liquid supply.",
            "This artifact provides no legal, tax, securities, compensation, custody, launch, or distribution clearance.",
            "A passing checker grants no settlement, writer, mint, burn, release, mount, or production authority.",
        ),
    }
    return _plain(document)


def _load(path: Path) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                duplicates.append(key)
            value[key] = item
        return value

    with path.open(encoding="utf-8") as stream:
        result = json.load(stream, object_pairs_hook=hook)
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(result, dict):
        raise ValueError("partial-policy artifact root must be an object")
    return result


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(_encoded(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def check_artifact(path: Path, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    errors: list[str] = []
    observed: dict[str, Any] = {}
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", RESEARCH_SOURCE_SUBJECT, "HEAD"],
        cwd=repo_root,
        check=False,
    )
    if ancestry.returncode != 0:
        errors.append("current HEAD does not descend from the research source subject")
    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if path.read_bytes() != _encoded(observed):
            errors.append("partial-policy artifact is not canonically encoded JSON")
        if observed != expected:
            errors.append("artifact differs from the exact partial-policy record")
    except (OSError, TypeError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))

    participant_gate = observed.get("participant_compensation_gate")
    participants = (
        participant_gate.get("participants", [])
        if isinstance(participant_gate, Mapping)
        else []
    )
    genesis_gate = observed.get("genesis_distribution_gate")
    genesis_selected = (
        genesis_gate.get("selected_distribution_release") is not None
        if isinstance(genesis_gate, Mapping)
        else False
    )
    return {
        "schema": "zenodex/production-readiness-g1-partial-policy-check/v2",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "launch_allowed": False,
        "whole_token_supply": observed.get("selected_parameters", {}).get(
            "whole_token_supply"
        )
        if isinstance(observed.get("selected_parameters"), Mapping)
        else None,
        "participant_count": len(participants) if isinstance(participants, list) else 0,
        "open_participant_count": sum(
            isinstance(entry, Mapping)
            and entry.get("status") == "OPEN_UNSELECTED_COMPENSATION_POLICY"
            for entry in participants
        )
        if isinstance(participants, list)
        else 0,
        "genesis_distribution_selected": genesis_selected,
        "errors": errors,
        "nonclaim": (
            "PASS confirms an exact partial decision record and fail-closed open "
            "obligations; it grants no economic or production authority."
        ),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    if args.write:
        _write_atomic(args.output, build_document(args.repo_root))
    report = check_artifact(args.output, args.repo_root)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif report["ok"]:
        print("production readiness G1 partial policy: PASS (launch blocked)")
    else:
        for error in report["errors"]:
            print(f"production readiness G1 partial policy: {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
