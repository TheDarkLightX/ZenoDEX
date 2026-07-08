"""Local-testnet protocol token distribution helpers.

The public token docs currently name ZDEX as the protocol token. Older local
testnet lanes used tZENO as a placeholder symbol, so these helpers accept the
symbol selected by the bundle builder while enforcing the same deterministic
local distribution shape.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping, cast

from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

PROTOCOL_TOKEN_DISTRIBUTION_SCHEMA_V0 = "zenodex.zeno_ledger.protocol_token_distribution.v0"
PROTOCOL_TOKEN_DISTRIBUTION_IMMUTABILITY_SCHEMA_V0 = "zenodex.zeno_ledger.protocol_token_distribution_immutability.v0"
PROTOCOL_TOKEN_DISTRIBUTION_TAU_POLICY_ID = "protocol_token_distribution_guard_v1"
PROTOCOL_TOKEN_DISTRIBUTION_TAU_POLICY_PATH = "src/tau_specs/recommended/protocol_token_distribution_guard_v1.tau"
ACTIVE_PARTICIPANT_REWARD_CLAIM_SCHEMA_V0 = "zenodex.zeno_ledger.active_participant_reward_claim.v0"
ACTIVE_PARTICIPANT_REWARD_CLAIM_TAU_POLICY_ID = "active_participant_reward_claim_guard_v1"
ACTIVE_PARTICIPANT_REWARD_CLAIM_TAU_POLICY_PATH = "src/tau_specs/recommended/active_participant_reward_claim_guard_v1.tau"
ACTIVE_PARTICIPANT_EMISSION_EPOCH_SCHEMA_V0 = "zenodex.zeno_ledger.active_participant_emission_epoch.v0"
ACTIVE_PARTICIPANT_EMISSION_TAU_POLICY_ID = "active_participant_emission_guard_v1"
ACTIVE_PARTICIPANT_EMISSION_TAU_POLICY_PATH = "src/tau_specs/recommended/active_participant_emission_guard_v1.tau"
TOKENOMICS_BUYBACK_BURN_EVENT_SCHEMA_V0 = "zenodex.zeno_ledger.tokenomics_buyback_burn_event.v0"
TOKENOMICS_BUYBACK_BURN_TAU_POLICY_ID = "tokenomics_buyback_burn_v2"
TOKENOMICS_BUYBACK_BURN_TAU_POLICY_PATH = "src/tau_specs/recommended/tokenomics_buyback_burn_v2.tau"
DEFAULT_PROTOCOL_TOKEN_SYMBOL = "ZDEX"
DEFAULT_PROTOCOL_TOKEN_INITIAL_SUPPLY = 1_000_000
DEFAULT_PROTOCOL_TOKEN_SUPPLY_FLOOR = 100_000
DEFAULT_ACTIVE_PARTICIPANT_REWARD_RESERVE_FLOOR = 10_000
DEFAULT_ACTIVE_PARTICIPANT_REWARD_REFILL_TARGET = 25_000
DEFAULT_ACTIVE_PARTICIPANT_EMISSION_BPS = 100
DEFAULT_ACTIVE_PARTICIPANT_EMISSION_MIN_REMAINING_EPOCHS = 365
DEFAULT_ACTIVE_PARTICIPANT_EMISSION_MAX_EPOCH_BUDGET = 250
DEFAULT_ACTIVE_PARTICIPANT_REWARD_TO_BURN_BPS = 2_500
ACTIVE_PARTICIPANT_REWARD_POOL_ID = "active_participant_rewards_pool"
MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT = 1_000
LOCAL_TESTNET_BUYBACK_SOURCE_ALLOCATION_ID = "dao_protocol_treasury"
LOCAL_TESTNET_BUYBACK_SHARE_BPS = 2_000

_BPS_SCALE = 10_000

LOCAL_TESTNET_ALLOCATION_SPECS_V0: tuple[dict[str, Any], ...] = (
    {
        "id": "founder_original_rd",
        "category": "founder",
        "bps": 1500,
        "fixture_role": "operator",
    },
    {
        "id": "core_team_future_contributors",
        "category": "team",
        "bps": 1000,
        "fixture_role": "perps_wallet_authority",
    },
    {
        "id": "dao_protocol_treasury",
        "category": "treasury",
        "bps": 2500,
        "fixture_role": "guardian_1",
    },
    {
        "id": "ecosystem_lp_solver_operator_proof_incentives",
        "category": "ecosystem",
        "bps": 2500,
        "fixture_role": "autotrader_supervisor",
    },
    {
        "id": ACTIVE_PARTICIPANT_REWARD_POOL_ID,
        "category": "active_participant_rewards",
        "bps": 1000,
        "fixture_role": "guardian_2",
    },
    {
        "id": "security_audits_bounties_insurance_reserve",
        "category": "security",
        "bps": 500,
        "fixture_role": "oracle_authority",
    },
    {
        "id": "liquidity_bootstrap_market_making",
        "category": "liquidity",
        "bps": 500,
        "fixture_role": "bootstrap_sender",
    },
    {
        "id": "strategic_partners_investors_chain_partners",
        "category": "strategic",
        "bps": 500,
        "fixture_role": "bob",
    },
)

LOCAL_TESTNET_ACTIVE_PARTICIPANT_PROGRAM_SPECS_V0: tuple[dict[str, Any], ...] = (
    {
        "id": "lp_liquidity_provider_rewards",
        "category": "liquidity_providers",
        "share_bps_of_reward_pool": 3000,
        "claim_amount": 25,
        "eligibility_receipts": ["add_liquidity", "remove_liquidity", "lp_position_snapshot"],
    },
    {
        "id": "stability_pool_depositor_rewards",
        "category": "stability_pool_depositors",
        "share_bps_of_reward_pool": 2500,
        "claim_amount": 40,
        "eligibility_receipts": ["stability_pool_deposit", "stability_pool_epoch_snapshot"],
    },
    {
        "id": "oracle_reporter_and_user_rewards",
        "category": "oracle_reporters_and_users",
        "share_bps_of_reward_pool": 1500,
        "claim_amount": 15,
        "eligibility_receipts": ["oracle_report", "oracle_query_usage"],
    },
    {
        "id": "proof_mining_rewards",
        "category": "proof_miners",
        "share_bps_of_reward_pool": 1500,
        "claim_amount": 15,
        "eligibility_receipts": ["proof_mining_claim", "verified_proof_work"],
    },
    {
        "id": "perps_zusd_active_user_rewards",
        "category": "perps_and_zusd_active_users",
        "share_bps_of_reward_pool": 1500,
        "claim_amount": 15,
        "eligibility_receipts": ["perps_position_activity", "zusd_vault_activity"],
    },
)


def load_role_pubkeys_from_key_bundle_v0(path: Path | str | None) -> dict[str, str]:
    """Load local-testnet fixture role pubkeys from `keys.json`.

    Missing paths return an empty map so non-local bundle builders keep using
    the deterministic bootstrap fallback.
    """

    if path is None:
        return {}
    bundle_path = Path(path)
    if not bundle_path.is_file():
        return {}
    obj = json.loads(bundle_path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("fixture key bundle must decode to an object")
    roles = obj.get("roles")
    if not isinstance(roles, Mapping):
        raise ValueError("fixture key bundle roles must be an object")
    out: dict[str, str] = {}
    for role, material in roles.items():
        if not isinstance(role, str) or not isinstance(material, Mapping):
            continue
        pubkey = material.get("public_key")
        if not isinstance(pubkey, str) or not pubkey.strip():
            continue
        out[role] = canonical_hex_fixed_allow_0x(pubkey, nbytes=48, name=f"roles.{role}.public_key")
    return out


def build_protocol_token_distribution_v0(
    *,
    chain_id: str,
    token_symbol: str,
    token_asset_id: str,
    role_pubkeys: Mapping[str, str] | None,
    fallback_pubkey: str,
    initial_supply: int = DEFAULT_PROTOCOL_TOKEN_INITIAL_SUPPLY,
    supply_floor: int = DEFAULT_PROTOCOL_TOKEN_SUPPLY_FLOOR,
) -> dict[str, Any]:
    """Build the deterministic local-testnet protocol token distribution."""

    if not isinstance(chain_id, str) or not chain_id:
        raise ValueError("chain_id must be non-empty")
    if not isinstance(token_symbol, str) or not token_symbol:
        raise ValueError("token_symbol must be non-empty")
    token_asset = canonical_hex_fixed_allow_0x(token_asset_id, nbytes=32, name="token_asset_id")
    fallback = canonical_hex_fixed_allow_0x(fallback_pubkey, nbytes=48, name="fallback_pubkey")
    if not isinstance(initial_supply, int) or isinstance(initial_supply, bool) or initial_supply <= 0:
        raise ValueError("initial_supply must be a positive int")
    if not isinstance(supply_floor, int) or isinstance(supply_floor, bool) or supply_floor <= 0:
        raise ValueError("supply_floor must be a positive int")
    if supply_floor > initial_supply:
        raise ValueError("supply_floor must be <= initial_supply")

    role_map = dict(role_pubkeys or {})
    allocations: list[dict[str, Any]] = []
    active_rewards_allocation: dict[str, Any] | None = None
    total = 0
    bps_total = 0
    for spec in LOCAL_TESTNET_ALLOCATION_SPECS_V0:
        bps = int(spec["bps"])
        amount_num = initial_supply * bps
        if amount_num % _BPS_SCALE != 0:
            raise ValueError(f"allocation {spec['id']} does not divide initial_supply exactly")
        amount = amount_num // _BPS_SCALE
        fixture_role = str(spec["fixture_role"])
        if fixture_role == "bootstrap_sender":
            recipient = fallback
        else:
            recipient = role_map.get(fixture_role, fallback)
        recipient = canonical_hex_fixed_allow_0x(recipient, nbytes=48, name=f"allocation.{spec['id']}.recipient_pubkey")
        allocation = {
            "id": str(spec["id"]),
            "category": str(spec["category"]),
            "amount": amount,
            "share_bps": bps,
            "recipient_role": fixture_role if fixture_role in role_map or fixture_role == "bootstrap_sender" else "bootstrap_sender",
            "recipient_pubkey": recipient,
        }
        allocations.append(allocation)
        if allocation["id"] == ACTIVE_PARTICIPANT_REWARD_POOL_ID:
            active_rewards_allocation = allocation
        total += amount
        bps_total += bps

    if active_rewards_allocation is None:
        raise ValueError("active participant reward pool allocation missing")
    active_participant_programs = _build_active_participant_programs_v0(active_rewards_allocation)
    body = {
        "schema": PROTOCOL_TOKEN_DISTRIBUTION_SCHEMA_V0,
        "chain_id": chain_id,
        "token_symbol": token_symbol,
        "token_asset_id": token_asset,
        "initial_supply": int(initial_supply),
        "supply_floor": int(supply_floor),
        "allocation_basis": {
            "share_source": "internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json percentage buckets, with the community bucket wired as active-participant rewards",
            "supply_source": "docs/ZDEX_TOKEN.md local-testnet unit supply",
            "scaled_for_local_testnet": True,
        },
        "allocations": allocations,
        "allocation_total": total,
        "allocation_share_bps_total": bps_total,
        "active_participant_reward_pool_id": ACTIVE_PARTICIPANT_REWARD_POOL_ID,
        "active_participant_programs": active_participant_programs,
        "active_participant_emission_policy": _build_active_participant_emission_policy_v0(
            active_rewards_allocation,
            active_participant_programs,
        ),
        "immutability": {
            "schema": PROTOCOL_TOKEN_DISTRIBUTION_IMMUTABILITY_SCHEMA_V0,
            "tokenomics_version": "local_testnet_candidate_v0",
            "mutable_before_genesis": True,
            "post_genesis_mutation_allowed": False,
            "runtime_mutation_allowed": False,
            "python_override_allowed_after_genesis": False,
            "requires_new_distribution_hash_for_any_change": True,
            "requires_new_chain_or_explicit_governance_migration_for_post_genesis_change": True,
            "operator_note": (
                "Allocation constants may be edited before a launch bundle is built; "
                "after genesis the distribution hash is the authority anchor."
            ),
        },
        "protocol_token_faucet_mint_allowed": False,
        "external_minting_allowed": False,
        "tau_policy": {
            "policy_id": PROTOCOL_TOKEN_DISTRIBUTION_TAU_POLICY_ID,
            "path": PROTOCOL_TOKEN_DISTRIBUTION_TAU_POLICY_PATH,
            "mode": "host_computed_flags",
            "host_computed_flags": {},
        },
        "production_security_claim": False,
        "non_claims": [
            "local-testnet fixture distribution only",
            "active participant rewards use local-testnet receipt gates; production claim authority still requires deployed Tau kernel admission",
            "not public launch readiness",
            "not legal or securities clearance",
            "not secondary-market value evidence",
        ],
    }
    body["tau_policy"]["host_computed_flags"] = _distribution_policy_flags_v0(body)
    validate_protocol_token_distribution_v0(body)
    return {**body, "distribution_hash": protocol_token_distribution_hash_v0(body)}


def protocol_token_distribution_hash_v0(distribution: Mapping[str, Any]) -> str:
    """Hash a distribution, excluding its self-hash field when present."""

    return hash_v0("protocol_token_distribution_v0", {k: v for k, v in dict(distribution).items() if k != "distribution_hash"})


def _build_active_participant_programs_v0(active_rewards_allocation: Mapping[str, Any]) -> list[dict[str, Any]]:
    pool_amount = int(active_rewards_allocation["amount"])
    controller_role = str(active_rewards_allocation["recipient_role"])
    controller_pubkey = str(active_rewards_allocation["recipient_pubkey"])
    programs: list[dict[str, Any]] = []
    for spec in LOCAL_TESTNET_ACTIVE_PARTICIPANT_PROGRAM_SPECS_V0:
        share_bps = int(spec["share_bps_of_reward_pool"])
        budget_num = pool_amount * share_bps
        if budget_num % _BPS_SCALE != 0:
            raise ValueError(f"active participant program {spec['id']} does not divide reward pool exactly")
        programs.append(
            {
                "id": str(spec["id"]),
                "category": str(spec["category"]),
                "budget_amount": budget_num // _BPS_SCALE,
                "share_bps_of_reward_pool": share_bps,
                "claim_amount": int(spec["claim_amount"]),
                "reward_source_allocation_id": str(active_rewards_allocation["id"]),
                "controller_role": controller_role,
                "controller_pubkey": controller_pubkey,
                "eligibility_receipts": list(spec["eligibility_receipts"]),
            }
        )
    return programs


def _build_active_participant_emission_policy_v0(
    active_rewards_allocation: Mapping[str, Any],
    active_participant_programs: list[dict[str, Any]],
) -> dict[str, Any]:
    pool_amount = int(active_rewards_allocation["amount"])
    refill_trigger = min(DEFAULT_ACTIVE_PARTICIPANT_REWARD_RESERVE_FLOOR, pool_amount)
    refill_target = min(max(refill_trigger, DEFAULT_ACTIVE_PARTICIPANT_REWARD_REFILL_TARGET), pool_amount)
    program_weights = {
        str(program["id"]): int(program["share_bps_of_reward_pool"])
        for program in active_participant_programs
    }
    return {
        "schema": "zenodex.zeno_ledger.active_participant_emission_policy.v0",
        "reward_source_allocation_id": ACTIVE_PARTICIPANT_REWARD_POOL_ID,
        "reward_reserve_floor": refill_trigger,
        "refill_trigger_balance": refill_trigger,
        "refill_target_balance": refill_target,
        "initial_emission_bps": DEFAULT_ACTIVE_PARTICIPANT_EMISSION_BPS,
        "min_remaining_epochs": DEFAULT_ACTIVE_PARTICIPANT_EMISSION_MIN_REMAINING_EPOCHS,
        "max_epoch_budget": DEFAULT_ACTIVE_PARTICIPANT_EMISSION_MAX_EPOCH_BUDGET,
        "reward_to_burn_bps": DEFAULT_ACTIVE_PARTICIPANT_REWARD_TO_BURN_BPS,
        "program_weight_bps": program_weights,
        "refill_sources": [
            "protocol_fee_reward_refill_when_reserve_at_or_below_trigger",
            "governance_migration_explicit_refill",
        ],
        "rate_update_rule": "monotone_nonincreasing",
        "refill_rule": "refill_amount = 0 when reserve_before > refill_trigger_balance; otherwise refill_amount <= min(refill_available, refill_target_balance - reserve_before)",
        "budget_formula": "min(floor(max(0,reserve_before+refill-reserve_floor)*emission_bps/10000), floor(max(0,reserve_before+refill-reserve_floor)/min_remaining_epochs), max_epoch_budget, floor(epoch_burn_amount*reward_to_burn_bps/10000))",
        "non_claims": [
            "does_not_mint_protocol_tokens",
            "does_not_refill while reward reserve is above trigger",
            "does_not_guarantee positive emissions when reserve remains at or below floor",
            "does_not_claim demand support from rewards unless separate staking or utility sinks are live",
        ],
    }


def active_participant_program_by_id_v0(distribution: Mapping[str, Any], program_id: str) -> dict[str, Any]:
    validate_protocol_token_distribution_v0(distribution)
    if not isinstance(program_id, str) or not program_id:
        raise ValueError("program_id must be non-empty")
    for program in distribution.get("active_participant_programs", []):
        if isinstance(program, Mapping) and program.get("id") == program_id:
            return dict(program)
    raise ValueError("active participant program not found")


def active_participant_reward_claim_key_v0(
    *,
    program_id: str,
    recipient_pubkey: str,
    receipt_hash: str,
) -> str:
    return hash_v0(
        "active_participant_reward_claim_key_v0",
        {
            "program_id": _require_nonempty_str(program_id, name="program_id"),
            "recipient_pubkey": canonical_hex_fixed_allow_0x(recipient_pubkey, nbytes=48, name="recipient_pubkey"),
            "receipt_hash": canonical_hex_fixed_allow_0x(receipt_hash, nbytes=32, name="receipt_hash"),
        },
    )


def build_active_participant_emission_epoch_v0(
    *,
    distribution: Mapping[str, Any],
    epoch: int,
    reserve_before: int,
    protocol_fee_refill_available: int,
    epoch_burn_amount: int,
    previous_emission_bps: int,
    emission_bps: int,
    production_security_claim: bool = False,
) -> dict[str, Any]:
    """Build a conditional active-reward emission epoch.

    Normal epochs spend only from the existing reward reserve. The refill leg is
    admitted only when the reserve is at or below the configured trigger, and
    it may refill only up to the configured target. Any unused fee amount
    remains available to the buyback/burn path.
    """

    validate_protocol_token_distribution_v0(distribution)
    policy = _active_participant_emission_policy_v0(distribution)
    normalized_epoch = _require_positive_int(epoch, name="emission.epoch", maximum=9_223_372_036_854_775_807)
    reserve_in = _require_nonnegative_int(reserve_before, name="emission.reserve_before")
    refill_available = _require_nonnegative_int(
        protocol_fee_refill_available,
        name="emission.protocol_fee_refill_available",
    )
    burn_amount = _require_nonnegative_int(epoch_burn_amount, name="emission.epoch_burn_amount")
    previous_rate = _require_nonnegative_int(previous_emission_bps, name="emission.previous_emission_bps")
    rate = _require_nonnegative_int(emission_bps, name="emission.emission_bps")
    if previous_rate > _BPS_SCALE or rate > _BPS_SCALE:
        raise ValueError("emission bps must be <= 10000")
    if rate > previous_rate:
        raise ValueError("emission rate must be monotone non-increasing")

    reserve_floor = int(policy["reward_reserve_floor"])
    refill_trigger = int(policy["refill_trigger_balance"])
    refill_target = int(policy["refill_target_balance"])
    min_remaining_epochs = int(policy["min_remaining_epochs"])
    max_epoch_budget = int(policy["max_epoch_budget"])
    reward_to_burn_bps = int(policy["reward_to_burn_bps"])
    refill_triggered = reserve_in <= refill_trigger
    refill_capacity = max(0, refill_target - reserve_in) if refill_triggered else 0
    refill_amount = min(refill_available, refill_capacity)
    reserve_after_refill = reserve_in + refill_amount
    spendable_above_floor = max(0, reserve_after_refill - reserve_floor)
    base_drip_budget = spendable_above_floor * rate // _BPS_SCALE
    horizon_budget = spendable_above_floor // min_remaining_epochs
    burn_cap_budget = burn_amount * reward_to_burn_bps // _BPS_SCALE
    epoch_budget = min(base_drip_budget, horizon_budget, max_epoch_budget, burn_cap_budget)
    program_epoch_budgets = _active_participant_program_epoch_budgets_v0(
        distribution=distribution,
        epoch_budget=epoch_budget,
    )
    program_budget_total = sum(int(row["epoch_budget"]) for row in program_epoch_budgets)
    event_base: dict[str, Any] = {
        "schema": ACTIVE_PARTICIPANT_EMISSION_EPOCH_SCHEMA_V0,
        "version": "local_testnet_v0",
        "chain_id": str(distribution["chain_id"]),
        "epoch": normalized_epoch,
        "distribution_hash": protocol_token_distribution_hash_v0(distribution),
        "reward_source_allocation_id": ACTIVE_PARTICIPANT_REWARD_POOL_ID,
        "reserve_before": reserve_in,
        "reward_reserve_floor": reserve_floor,
        "refill_trigger_balance": refill_trigger,
        "refill_target_balance": refill_target,
        "protocol_fee_refill_available": refill_available,
        "refill_triggered": refill_triggered,
        "refill_amount": refill_amount,
        "refill_remainder_for_buyback": refill_available - refill_amount,
        "reserve_after_refill": reserve_after_refill,
        "spendable_above_floor": spendable_above_floor,
        "epoch_burn_amount": burn_amount,
        "reward_to_burn_bps": reward_to_burn_bps,
        "burn_cap_budget": burn_cap_budget,
        "previous_emission_bps": previous_rate,
        "emission_bps": rate,
        "min_remaining_epochs": min_remaining_epochs,
        "max_epoch_budget": max_epoch_budget,
        "base_drip_budget": base_drip_budget,
        "horizon_budget": horizon_budget,
        "epoch_budget": epoch_budget,
        "program_epoch_budgets": program_epoch_budgets,
        "program_epoch_budget_total": program_budget_total,
        "unallocated_epoch_budget": epoch_budget - program_budget_total,
        "reserve_after_epoch_if_fully_spent": reserve_after_refill - epoch_budget,
        "tau_policy": {
            "policy_id": ACTIVE_PARTICIPANT_EMISSION_TAU_POLICY_ID,
            "path": ACTIVE_PARTICIPANT_EMISSION_TAU_POLICY_PATH,
            "mode": "host_computed_flags",
            "host_computed_flags": {},
        },
        "production_security_claim": bool(production_security_claim),
    }
    event_base["tau_policy"]["host_computed_flags"] = _active_participant_emission_policy_flags_v0(
        event_base,
        distribution=distribution,
    )
    event_base["event_hash"] = hash_v0("active_participant_emission_epoch_v0", event_base)
    return validate_active_participant_emission_epoch_v0(event_base, distribution=distribution)


def validate_active_participant_emission_epoch_v0(
    event: Mapping[str, Any],
    *,
    distribution: Mapping[str, Any],
) -> dict[str, Any]:
    validate_protocol_token_distribution_v0(distribution)
    obj = dict(event)
    if obj.get("schema") != ACTIVE_PARTICIPANT_EMISSION_EPOCH_SCHEMA_V0:
        raise ValueError("active participant emission epoch schema mismatch")
    if obj.get("version") != "local_testnet_v0":
        raise ValueError("active participant emission epoch version mismatch")
    if obj.get("chain_id") != distribution.get("chain_id"):
        raise ValueError("active participant emission epoch chain_id mismatch")
    _require_positive_int(obj.get("epoch"), name="emission.epoch", maximum=9_223_372_036_854_775_807)
    if obj.get("distribution_hash") != protocol_token_distribution_hash_v0(distribution):
        raise ValueError("active participant emission epoch distribution_hash mismatch")
    if obj.get("reward_source_allocation_id") != ACTIVE_PARTICIPANT_REWARD_POOL_ID:
        raise ValueError("active participant emission epoch reward source mismatch")
    policy = _active_participant_emission_policy_v0(distribution)
    reserve_before = _require_nonnegative_int(obj.get("reserve_before"), name="emission.reserve_before")
    reserve_floor = _require_nonnegative_int(obj.get("reward_reserve_floor"), name="emission.reward_reserve_floor")
    refill_trigger = _require_nonnegative_int(obj.get("refill_trigger_balance"), name="emission.refill_trigger_balance")
    refill_target = _require_nonnegative_int(obj.get("refill_target_balance"), name="emission.refill_target_balance")
    refill_available = _require_nonnegative_int(
        obj.get("protocol_fee_refill_available"),
        name="emission.protocol_fee_refill_available",
    )
    burn_amount = _require_nonnegative_int(obj.get("epoch_burn_amount"), name="emission.epoch_burn_amount")
    refill_amount = _require_nonnegative_int(obj.get("refill_amount"), name="emission.refill_amount")
    if reserve_floor != int(policy["reward_reserve_floor"]):
        raise ValueError("active participant emission reward_reserve_floor mismatch")
    if refill_trigger != int(policy["refill_trigger_balance"]):
        raise ValueError("active participant emission refill_trigger_balance mismatch")
    if refill_target != int(policy["refill_target_balance"]):
        raise ValueError("active participant emission refill_target_balance mismatch")
    refill_triggered = reserve_before <= refill_trigger
    if obj.get("refill_triggered") is not refill_triggered:
        raise ValueError("active participant emission refill_triggered mismatch")
    expected_refill_capacity = max(0, refill_target - reserve_before) if refill_triggered else 0
    expected_refill = min(refill_available, expected_refill_capacity)
    if refill_amount != expected_refill:
        raise ValueError("active participant emission refill amount mismatch")
    if _require_nonnegative_int(obj.get("refill_remainder_for_buyback"), name="emission.refill_remainder_for_buyback") != refill_available - refill_amount:
        raise ValueError("active participant emission refill remainder mismatch")
    reserve_after_refill = reserve_before + refill_amount
    if _require_nonnegative_int(obj.get("reserve_after_refill"), name="emission.reserve_after_refill") != reserve_after_refill:
        raise ValueError("active participant emission reserve_after_refill mismatch")
    spendable = max(0, reserve_after_refill - reserve_floor)
    if _require_nonnegative_int(obj.get("spendable_above_floor"), name="emission.spendable_above_floor") != spendable:
        raise ValueError("active participant emission spendable_above_floor mismatch")
    previous_rate = _require_nonnegative_int(obj.get("previous_emission_bps"), name="emission.previous_emission_bps")
    rate = _require_nonnegative_int(obj.get("emission_bps"), name="emission.emission_bps")
    if previous_rate > _BPS_SCALE or rate > _BPS_SCALE:
        raise ValueError("active participant emission bps must be <= 10000")
    if rate > previous_rate:
        raise ValueError("active participant emission rate must be monotone non-increasing")
    min_remaining_epochs = _require_positive_int(
        obj.get("min_remaining_epochs"),
        name="emission.min_remaining_epochs",
        maximum=9_223_372_036_854_775_807,
    )
    max_epoch_budget = _require_positive_int(
        obj.get("max_epoch_budget"),
        name="emission.max_epoch_budget",
        maximum=9_223_372_036_854_775_807,
    )
    reward_to_burn_bps = _require_nonnegative_int(obj.get("reward_to_burn_bps"), name="emission.reward_to_burn_bps")
    if reward_to_burn_bps > _BPS_SCALE:
        raise ValueError("active participant emission reward_to_burn_bps must be <= 10000")
    if min_remaining_epochs != int(policy["min_remaining_epochs"]):
        raise ValueError("active participant emission min_remaining_epochs mismatch")
    if max_epoch_budget != int(policy["max_epoch_budget"]):
        raise ValueError("active participant emission max_epoch_budget mismatch")
    if reward_to_burn_bps != int(policy["reward_to_burn_bps"]):
        raise ValueError("active participant emission reward_to_burn_bps mismatch")
    base_drip = spendable * rate // _BPS_SCALE
    horizon_budget = spendable // min_remaining_epochs
    burn_cap_budget = burn_amount * reward_to_burn_bps // _BPS_SCALE
    epoch_budget = min(base_drip, horizon_budget, max_epoch_budget, burn_cap_budget)
    if _require_nonnegative_int(obj.get("burn_cap_budget"), name="emission.burn_cap_budget") != burn_cap_budget:
        raise ValueError("active participant emission burn_cap_budget mismatch")
    if _require_nonnegative_int(obj.get("base_drip_budget"), name="emission.base_drip_budget") != base_drip:
        raise ValueError("active participant emission base_drip_budget mismatch")
    if _require_nonnegative_int(obj.get("horizon_budget"), name="emission.horizon_budget") != horizon_budget:
        raise ValueError("active participant emission horizon_budget mismatch")
    if _require_nonnegative_int(obj.get("epoch_budget"), name="emission.epoch_budget") != epoch_budget:
        raise ValueError("active participant emission epoch_budget mismatch")
    expected_program_budgets = _active_participant_program_epoch_budgets_v0(
        distribution=distribution,
        epoch_budget=epoch_budget,
    )
    if obj.get("program_epoch_budgets") != expected_program_budgets:
        raise ValueError("active participant emission program_epoch_budgets mismatch")
    program_total = sum(int(row["epoch_budget"]) for row in expected_program_budgets)
    if _require_nonnegative_int(obj.get("program_epoch_budget_total"), name="emission.program_epoch_budget_total") != program_total:
        raise ValueError("active participant emission program_epoch_budget_total mismatch")
    if _require_nonnegative_int(obj.get("unallocated_epoch_budget"), name="emission.unallocated_epoch_budget") != epoch_budget - program_total:
        raise ValueError("active participant emission unallocated_epoch_budget mismatch")
    if _require_nonnegative_int(
        obj.get("reserve_after_epoch_if_fully_spent"),
        name="emission.reserve_after_epoch_if_fully_spent",
    ) != reserve_after_refill - epoch_budget:
        raise ValueError("active participant emission reserve_after_epoch_if_fully_spent mismatch")
    flags = _active_participant_emission_policy_flags_v0(obj, distribution=distribution)
    if not all(flags.values()):
        failed = sorted(key for key, value in flags.items() if value is not True)
        raise ValueError(f"active participant emission policy flags failed: {','.join(failed)}")
    tau_policy = obj.get("tau_policy")
    if not isinstance(tau_policy, Mapping):
        raise ValueError("active participant emission tau_policy must be an object")
    if tau_policy.get("policy_id") != ACTIVE_PARTICIPANT_EMISSION_TAU_POLICY_ID:
        raise ValueError("active participant emission tau_policy policy_id mismatch")
    if tau_policy.get("path") != ACTIVE_PARTICIPANT_EMISSION_TAU_POLICY_PATH:
        raise ValueError("active participant emission tau_policy path mismatch")
    if tau_policy.get("mode") != "host_computed_flags":
        raise ValueError("active participant emission tau_policy mode mismatch")
    if dict(tau_policy.get("host_computed_flags", {})) != flags:
        raise ValueError("active participant emission tau_policy host_computed_flags mismatch")
    if obj.get("production_security_claim") is not False:
        raise ValueError("active participant emission production_security_claim must be false")
    expected_hash = hash_v0("active_participant_emission_epoch_v0", {k: v for k, v in obj.items() if k != "event_hash"})
    if obj.get("event_hash") != expected_hash:
        raise ValueError("active participant emission event_hash mismatch")
    return obj


def build_tokenomics_buyback_burn_event_v0(
    *,
    distribution: Mapping[str, Any],
    chain_id: str,
    height: int,
    tx_index: int,
    tx_hash: str,
    total_swap_fee: int,
    carry_before: int,
    source_balance_before: int,
    current_supply_before: int,
    buyback_share_bps: int = LOCAL_TESTNET_BUYBACK_SHARE_BPS,
    source_allocation_id: str = LOCAL_TESTNET_BUYBACK_SOURCE_ALLOCATION_ID,
    execution_mode: str = "treasury_allocation_burn_only",
    market_purchase: Mapping[str, Any] | None = None,
    production_security_claim: bool = False,
) -> dict[str, Any]:
    """Build the local-testnet protocol-fee buyback/burn event.

    The event records deterministic dust carry:
        scaled = carry_before + total_swap_fee * buyback_share_bps
        burn_amount = scaled // 10000
        carry_after = scaled % 10000
    """

    validate_protocol_token_distribution_v0(distribution)
    if not isinstance(chain_id, str) or not chain_id:
        raise ValueError("chain_id must be non-empty")
    normalized_height = _require_positive_int(height, name="buyback.height", maximum=9_223_372_036_854_775_807)
    normalized_tx_index = _require_nonnegative_int(tx_index, name="buyback.tx_index")
    tx_root = canonical_hex_fixed_allow_0x(tx_hash, nbytes=32, name="buyback.tx_hash")
    fee = _require_nonnegative_int(total_swap_fee, name="buyback.total_swap_fee")
    carry_in = _require_nonnegative_int(carry_before, name="buyback.carry_before")
    if carry_in >= _BPS_SCALE:
        raise ValueError("buyback.carry_before must be < 10000")
    share = _require_nonnegative_int(buyback_share_bps, name="buyback.buyback_share_bps")
    if share > _BPS_SCALE:
        raise ValueError("buyback.buyback_share_bps must be <= 10000")
    source_balance = _require_nonnegative_int(source_balance_before, name="buyback.source_balance_before")
    supply_before = _require_nonnegative_int(current_supply_before, name="buyback.current_supply_before")
    if supply_before <= 0:
        raise ValueError("buyback.current_supply_before must be positive")
    supply_floor = int(distribution["supply_floor"])
    if supply_before < supply_floor:
        raise ValueError("buyback.current_supply_before below supply floor")
    allocation = _allocation_by_id_v0(distribution, source_allocation_id)
    source_pubkey = canonical_hex_fixed_allow_0x(
        allocation.get("recipient_pubkey"),
        nbytes=48,
        name="buyback.source_pubkey",
    )
    scaled = carry_in + fee * share
    treasury_burn_amount = scaled // _BPS_SCALE
    carry_after = scaled % _BPS_SCALE
    mode = str(execution_mode or "treasury_allocation_burn_only")
    if mode not in {"treasury_allocation_burn_only", "market_purchase_then_burn"}:
        raise ValueError("buyback execution_mode invalid")
    market_obj = dict(market_purchase) if isinstance(market_purchase, Mapping) else None
    if mode == "market_purchase_then_burn":
        if not isinstance(market_obj, Mapping):
            raise ValueError("buyback market_purchase required")
        burn_amount = _require_nonnegative_int(market_obj.get("token_amount_out"), name="buyback.market_purchase.token_amount_out")
        source_after = source_balance
    else:
        burn_amount = treasury_burn_amount
        source_after = source_balance - burn_amount
        market_obj = None
    if source_after < 0:
        raise ValueError("buyback source balance insufficient")
    if supply_before - burn_amount < supply_floor:
        raise ValueError("buyback supply floor violation")
    event_base: dict[str, Any] = {
        "schema": TOKENOMICS_BUYBACK_BURN_EVENT_SCHEMA_V0,
        "version": "local_testnet_v0",
        "chain_id": chain_id,
        "height": normalized_height,
        "tx_index": normalized_tx_index,
        "tx_hash": tx_root,
        "distribution_hash": protocol_token_distribution_hash_v0(distribution),
        "token_asset_id": canonical_hex_fixed_allow_0x(distribution.get("token_asset_id"), nbytes=32, name="distribution.token_asset_id"),
        "source_allocation_id": str(source_allocation_id),
        "source_pubkey": source_pubkey,
        "source_balance_before": source_balance,
        "source_balance_after": source_after,
        "current_supply_before": supply_before,
        "current_supply_after": supply_before - burn_amount,
        "supply_floor": supply_floor,
        "total_swap_fee": fee,
        "buyback_share_bps": share,
        "execution_mode": mode,
        "treasury_burn_amount": treasury_burn_amount,
        "market_purchase": market_obj,
        "carry_before": carry_in,
        "burn_amount": burn_amount,
        "carry_after": carry_after,
        "tau_policy": {
            "policy_id": TOKENOMICS_BUYBACK_BURN_TAU_POLICY_ID,
            "path": TOKENOMICS_BUYBACK_BURN_TAU_POLICY_PATH,
            "mode": "host_computed_flags",
            "host_computed_flags": {},
        },
        "production_security_claim": bool(production_security_claim),
    }
    event_base["tau_policy"]["host_computed_flags"] = _tokenomics_buyback_burn_policy_flags_v0(
        event_base,
        distribution=distribution,
    )
    event_base["event_hash"] = hash_v0("tokenomics_buyback_burn_event_v0", event_base)
    return validate_tokenomics_buyback_burn_event_v0(event_base, distribution=distribution)


def validate_tokenomics_buyback_burn_event_v0(
    event: Mapping[str, Any],
    *,
    distribution: Mapping[str, Any],
) -> dict[str, Any]:
    validate_protocol_token_distribution_v0(distribution)
    obj = dict(event)
    if obj.get("schema") != TOKENOMICS_BUYBACK_BURN_EVENT_SCHEMA_V0:
        raise ValueError("tokenomics buyback burn event schema mismatch")
    if obj.get("version") != "local_testnet_v0":
        raise ValueError("tokenomics buyback burn event version mismatch")
    if obj.get("chain_id") != distribution.get("chain_id"):
        raise ValueError("tokenomics buyback burn event chain_id mismatch")
    _require_positive_int(obj.get("height"), name="buyback.height", maximum=9_223_372_036_854_775_807)
    _require_nonnegative_int(obj.get("tx_index"), name="buyback.tx_index")
    canonical_hex_fixed_allow_0x(obj.get("tx_hash"), nbytes=32, name="buyback.tx_hash")
    if obj.get("distribution_hash") != protocol_token_distribution_hash_v0(distribution):
        raise ValueError("tokenomics buyback burn event distribution_hash mismatch")
    if canonical_hex_fixed_allow_0x(obj.get("token_asset_id"), nbytes=32, name="buyback.token_asset_id") != canonical_hex_fixed_allow_0x(
        distribution.get("token_asset_id"),
        nbytes=32,
        name="distribution.token_asset_id",
    ):
        raise ValueError("tokenomics buyback burn event token_asset_id mismatch")
    allocation = _allocation_by_id_v0(distribution, str(obj.get("source_allocation_id", "")))
    source_pubkey = canonical_hex_fixed_allow_0x(obj.get("source_pubkey"), nbytes=48, name="buyback.source_pubkey")
    if source_pubkey != canonical_hex_fixed_allow_0x(allocation.get("recipient_pubkey"), nbytes=48, name="allocation.recipient_pubkey"):
        raise ValueError("tokenomics buyback burn event source_pubkey mismatch")
    source_before = _require_nonnegative_int(obj.get("source_balance_before"), name="buyback.source_balance_before")
    source_after = _require_nonnegative_int(obj.get("source_balance_after"), name="buyback.source_balance_after")
    supply_before = _require_nonnegative_int(obj.get("current_supply_before"), name="buyback.current_supply_before")
    supply_after = _require_nonnegative_int(obj.get("current_supply_after"), name="buyback.current_supply_after")
    supply_floor = _require_nonnegative_int(obj.get("supply_floor"), name="buyback.supply_floor")
    if supply_floor != int(distribution["supply_floor"]):
        raise ValueError("tokenomics buyback burn event supply_floor mismatch")
    fee = _require_nonnegative_int(obj.get("total_swap_fee"), name="buyback.total_swap_fee")
    share = _require_nonnegative_int(obj.get("buyback_share_bps"), name="buyback.buyback_share_bps")
    if share > _BPS_SCALE:
        raise ValueError("tokenomics buyback burn event buyback_share_bps invalid")
    carry_before = _require_nonnegative_int(obj.get("carry_before"), name="buyback.carry_before")
    carry_after = _require_nonnegative_int(obj.get("carry_after"), name="buyback.carry_after")
    burn_amount = _require_nonnegative_int(obj.get("burn_amount"), name="buyback.burn_amount")
    mode = str(obj.get("execution_mode", "treasury_allocation_burn_only"))
    if mode not in {"treasury_allocation_burn_only", "market_purchase_then_burn"}:
        raise ValueError("tokenomics buyback burn event execution_mode invalid")
    treasury_burn_amount = _require_nonnegative_int(
        obj.get("treasury_burn_amount", burn_amount),
        name="buyback.treasury_burn_amount",
    )
    if carry_before >= _BPS_SCALE or carry_after >= _BPS_SCALE:
        raise ValueError("tokenomics buyback burn event carry must be < 10000")
    scaled = carry_before + fee * share
    if treasury_burn_amount != scaled // _BPS_SCALE:
        raise ValueError("tokenomics buyback treasury burn amount mismatch")
    if carry_after != scaled % _BPS_SCALE:
        raise ValueError("tokenomics buyback burn carry_after mismatch")
    market_purchase = obj.get("market_purchase")
    if mode == "market_purchase_then_burn":
        if not isinstance(market_purchase, Mapping):
            raise ValueError("tokenomics buyback market_purchase missing")
        if burn_amount != _require_nonnegative_int(
            market_purchase.get("token_amount_out"),
            name="buyback.market_purchase.token_amount_out",
        ):
            raise ValueError("tokenomics buyback market burn amount mismatch")
        if source_after != source_before:
            raise ValueError("tokenomics buyback market source token balance mismatch")
        canonical_hex_fixed_allow_0x(market_purchase.get("quote_asset_id"), nbytes=32, name="buyback.market_purchase.quote_asset_id")
        canonical_hex_fixed_allow_0x(market_purchase.get("token_asset_id"), nbytes=32, name="buyback.market_purchase.token_asset_id")
        if canonical_hex_fixed_allow_0x(
            market_purchase.get("token_asset_id"),
            nbytes=32,
            name="buyback.market_purchase.token_asset_id",
        ) != canonical_hex_fixed_allow_0x(obj.get("token_asset_id"), nbytes=32, name="buyback.token_asset_id"):
            raise ValueError("tokenomics buyback market token_asset_id mismatch")
        _require_nonnegative_int(market_purchase.get("quote_amount_in"), name="buyback.market_purchase.quote_amount_in")
        for key in ("reserve0_before", "reserve1_before", "reserve0_after", "reserve1_after"):
            _require_nonnegative_int(market_purchase.get(key), name=f"buyback.market_purchase.{key}")
    else:
        if burn_amount != treasury_burn_amount:
            raise ValueError("tokenomics buyback burn amount mismatch")
        if market_purchase is not None:
            raise ValueError("tokenomics buyback market_purchase unexpected")
        if source_after != source_before - burn_amount:
            raise ValueError("tokenomics buyback burn source balance mismatch")
    if supply_after != supply_before - burn_amount:
        raise ValueError("tokenomics buyback burn supply mismatch")
    if supply_after < supply_floor:
        raise ValueError("tokenomics buyback burn supply floor violation")
    flags = _tokenomics_buyback_burn_policy_flags_v0(obj, distribution=distribution)
    if not all(flags.values()):
        failed = sorted(key for key, value in flags.items() if value is not True)
        raise ValueError(f"tokenomics buyback burn policy flags failed: {','.join(failed)}")
    tau_policy = obj.get("tau_policy")
    if not isinstance(tau_policy, Mapping):
        raise ValueError("tokenomics buyback burn tau_policy must be an object")
    if tau_policy.get("policy_id") != TOKENOMICS_BUYBACK_BURN_TAU_POLICY_ID:
        raise ValueError("tokenomics buyback burn tau_policy policy_id mismatch")
    if tau_policy.get("path") != TOKENOMICS_BUYBACK_BURN_TAU_POLICY_PATH:
        raise ValueError("tokenomics buyback burn tau_policy path mismatch")
    if tau_policy.get("mode") != "host_computed_flags":
        raise ValueError("tokenomics buyback burn tau_policy mode mismatch")
    if dict(tau_policy.get("host_computed_flags", {})) != flags:
        raise ValueError("tokenomics buyback burn tau_policy host_computed_flags mismatch")
    if obj.get("production_security_claim") is not False:
        raise ValueError("tokenomics buyback burn production_security_claim must be false")
    expected_hash = hash_v0("tokenomics_buyback_burn_event_v0", {k: v for k, v in obj.items() if k != "event_hash"})
    if obj.get("event_hash") != expected_hash:
        raise ValueError("tokenomics buyback burn event_hash mismatch")
    return obj


def build_active_participant_reward_claim_v0(
    *,
    distribution: Mapping[str, Any],
    program_id: str,
    recipient_pubkey: str,
    receipt_kind: str,
    receipt_hash: str,
    amount: int,
    source_height: int,
    source_tx_index: int,
    source_tx_hash: str,
    spent_by_program: Mapping[str, int] | None = None,
    claimed_keys: set[str] | frozenset[str] | None = None,
    reward_source_balance: int,
    production_security_claim: bool = False,
) -> dict[str, Any]:
    """Build a local-testnet active participant reward claim.

    This is a deterministic host-computed gate that prepares the claim object.
    The node still validates the referenced receipt against the local ledger
    before it transfers any protocol tokens.
    """

    validate_protocol_token_distribution_v0(distribution)
    program = active_participant_program_by_id_v0(distribution, program_id)
    recipient = canonical_hex_fixed_allow_0x(recipient_pubkey, nbytes=48, name="recipient_pubkey")
    receipt_root = canonical_hex_fixed_allow_0x(receipt_hash, nbytes=32, name="receipt_hash")
    tx_root = canonical_hex_fixed_allow_0x(source_tx_hash, nbytes=32, name="source_tx_hash")
    normalized_amount = _require_positive_int(
        amount,
        name="claim.amount",
        maximum=MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT,
    )
    height = _require_positive_int(source_height, name="claim.source_height", maximum=9_223_372_036_854_775_807)
    tx_index = _require_nonnegative_int(source_tx_index, name="claim.source_tx_index")
    claim_key = active_participant_reward_claim_key_v0(
        program_id=program_id,
        recipient_pubkey=recipient,
        receipt_hash=receipt_root,
    )
    spent_before = int((spent_by_program or {}).get(program_id, 0))
    source_balance_before = _require_nonnegative_int(reward_source_balance, name="reward_source_balance")
    budget_amount = int(program["budget_amount"])
    claim_base: dict[str, Any] = {
        "schema": ACTIVE_PARTICIPANT_REWARD_CLAIM_SCHEMA_V0,
        "program_id": str(program_id),
        "program_category": str(program["category"]),
        "recipient_pubkey": recipient,
        "receipt_kind": _require_nonempty_str(receipt_kind, name="receipt_kind"),
        "receipt_hash": receipt_root,
        "amount": normalized_amount,
        "token_asset_id": canonical_hex_fixed_allow_0x(
            distribution.get("token_asset_id"),
            nbytes=32,
            name="distribution.token_asset_id",
        ),
        "reward_source_allocation_id": ACTIVE_PARTICIPANT_REWARD_POOL_ID,
        "controller_role": str(program["controller_role"]),
        "controller_pubkey": canonical_hex_fixed_allow_0x(
            program.get("controller_pubkey"),
            nbytes=48,
            name="program.controller_pubkey",
        ),
        "program_budget_amount": budget_amount,
        "program_spent_before": spent_before,
        "program_remaining_before": budget_amount - spent_before,
        "program_spent_after": spent_before + normalized_amount,
        "reward_source_balance_before": source_balance_before,
        "reward_source_balance_after": source_balance_before - normalized_amount,
        "claim_key": claim_key,
        "source_height": height,
        "source_tx_index": tx_index,
        "source_tx_hash": tx_root,
        "tau_policy": {
            "policy_id": ACTIVE_PARTICIPANT_REWARD_CLAIM_TAU_POLICY_ID,
            "path": ACTIVE_PARTICIPANT_REWARD_CLAIM_TAU_POLICY_PATH,
            "mode": "host_computed_flags",
            "host_computed_flags": {},
        },
        "production_security_claim": bool(production_security_claim),
    }
    claim_base["tau_policy"]["host_computed_flags"] = _active_participant_reward_claim_policy_flags_v0(
        distribution=distribution,
        claim=claim_base,
        spent_by_program=spent_by_program or {},
        claimed_keys=claimed_keys or set(),
        reward_source_balance=source_balance_before,
    )
    claim_base["claim_hash"] = hash_v0("active_participant_reward_claim_v0", claim_base)
    validate_active_participant_reward_claim_v0(
        claim_base,
        distribution=distribution,
        spent_by_program=spent_by_program or {},
        claimed_keys=claimed_keys or set(),
        reward_source_balance=source_balance_before,
    )
    return claim_base


def validate_active_participant_reward_claim_v0(
    claim: Mapping[str, Any],
    *,
    distribution: Mapping[str, Any],
    spent_by_program: Mapping[str, int] | None = None,
    claimed_keys: set[str] | frozenset[str] | None = None,
    reward_source_balance: int,
) -> dict[str, Any]:
    validate_protocol_token_distribution_v0(distribution)
    obj = dict(claim)
    if obj.get("schema") != ACTIVE_PARTICIPANT_REWARD_CLAIM_SCHEMA_V0:
        raise ValueError("active participant reward claim schema mismatch")
    program_id = _require_nonempty_str(obj.get("program_id"), name="claim.program_id")
    program = active_participant_program_by_id_v0(distribution, program_id)
    if obj.get("program_category") != program["category"]:
        raise ValueError("active participant reward claim program_category mismatch")
    recipient = canonical_hex_fixed_allow_0x(obj.get("recipient_pubkey"), nbytes=48, name="claim.recipient_pubkey")
    _require_nonempty_str(obj.get("receipt_kind"), name="claim.receipt_kind")
    receipt_hash = canonical_hex_fixed_allow_0x(obj.get("receipt_hash"), nbytes=32, name="claim.receipt_hash")
    amount = _require_positive_int(
        obj.get("amount"),
        name="claim.amount",
        maximum=MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT,
    )
    program_claim_amount = _require_positive_int(
        program.get("claim_amount"),
        name="program.claim_amount",
        maximum=MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT,
    )
    if amount != program_claim_amount:
        raise ValueError("active participant reward claim amount must match program claim_amount")
    token_asset_id = canonical_hex_fixed_allow_0x(obj.get("token_asset_id"), nbytes=32, name="claim.token_asset_id")
    if token_asset_id != canonical_hex_fixed_allow_0x(distribution.get("token_asset_id"), nbytes=32, name="distribution.token_asset_id"):
        raise ValueError("active participant reward claim token_asset_id mismatch")
    if obj.get("reward_source_allocation_id") != ACTIVE_PARTICIPANT_REWARD_POOL_ID:
        raise ValueError("active participant reward claim reward source mismatch")
    if obj.get("controller_role") != program["controller_role"]:
        raise ValueError("active participant reward claim controller_role mismatch")
    controller = canonical_hex_fixed_allow_0x(obj.get("controller_pubkey"), nbytes=48, name="claim.controller_pubkey")
    if controller != canonical_hex_fixed_allow_0x(program.get("controller_pubkey"), nbytes=48, name="program.controller_pubkey"):
        raise ValueError("active participant reward claim controller_pubkey mismatch")
    budget_amount = _require_positive_int(obj.get("program_budget_amount"), name="claim.program_budget_amount", maximum=10**30)
    if budget_amount != int(program["budget_amount"]):
        raise ValueError("active participant reward claim program_budget_amount mismatch")
    spent_before = _require_nonnegative_int(obj.get("program_spent_before"), name="claim.program_spent_before")
    expected_spent_before = int((spent_by_program or {}).get(program_id, 0))
    if spent_before != expected_spent_before:
        raise ValueError("active participant reward claim program_spent_before mismatch")
    if _require_nonnegative_int(obj.get("program_remaining_before"), name="claim.program_remaining_before") != budget_amount - spent_before:
        raise ValueError("active participant reward claim program_remaining_before mismatch")
    if _require_nonnegative_int(obj.get("program_spent_after"), name="claim.program_spent_after") != spent_before + amount:
        raise ValueError("active participant reward claim program_spent_after mismatch")
    source_balance_before = _require_nonnegative_int(
        obj.get("reward_source_balance_before"),
        name="claim.reward_source_balance_before",
    )
    if source_balance_before != _require_nonnegative_int(reward_source_balance, name="reward_source_balance"):
        raise ValueError("active participant reward claim reward_source_balance_before mismatch")
    if _require_nonnegative_int(obj.get("reward_source_balance_after"), name="claim.reward_source_balance_after") != source_balance_before - amount:
        raise ValueError("active participant reward claim reward_source_balance_after mismatch")
    claim_key = active_participant_reward_claim_key_v0(
        program_id=program_id,
        recipient_pubkey=recipient,
        receipt_hash=receipt_hash,
    )
    if obj.get("claim_key") != claim_key:
        raise ValueError("active participant reward claim claim_key mismatch")
    _require_positive_int(obj.get("source_height"), name="claim.source_height", maximum=9_223_372_036_854_775_807)
    _require_nonnegative_int(obj.get("source_tx_index"), name="claim.source_tx_index")
    canonical_hex_fixed_allow_0x(obj.get("source_tx_hash"), nbytes=32, name="claim.source_tx_hash")
    flags = _active_participant_reward_claim_policy_flags_v0(
        distribution=distribution,
        claim=obj,
        spent_by_program=spent_by_program or {},
        claimed_keys=claimed_keys or set(),
        reward_source_balance=source_balance_before,
    )
    if not all(flags.values()):
        failed = sorted(key for key, value in flags.items() if value is not True)
        raise ValueError(f"active participant reward claim policy flags failed: {','.join(failed)}")
    tau_policy = obj.get("tau_policy")
    if not isinstance(tau_policy, Mapping):
        raise ValueError("active participant reward claim tau_policy must be an object")
    if tau_policy.get("policy_id") != ACTIVE_PARTICIPANT_REWARD_CLAIM_TAU_POLICY_ID:
        raise ValueError("active participant reward claim tau_policy policy_id mismatch")
    if tau_policy.get("path") != ACTIVE_PARTICIPANT_REWARD_CLAIM_TAU_POLICY_PATH:
        raise ValueError("active participant reward claim tau_policy path mismatch")
    if tau_policy.get("mode") != "host_computed_flags":
        raise ValueError("active participant reward claim tau_policy mode mismatch")
    if dict(tau_policy.get("host_computed_flags", {})) != flags:
        raise ValueError("active participant reward claim tau_policy host_computed_flags mismatch")
    if obj.get("production_security_claim") is not False:
        raise ValueError("active participant reward claim production_security_claim must be false")
    expected_hash = hash_v0("active_participant_reward_claim_v0", {k: v for k, v in obj.items() if k != "claim_hash"})
    if obj.get("claim_hash") != expected_hash:
        raise ValueError("active participant reward claim claim_hash mismatch")
    return obj


def _active_participant_reward_claim_policy_flags_v0(
    *,
    distribution: Mapping[str, Any],
    claim: Mapping[str, Any],
    spent_by_program: Mapping[str, int],
    claimed_keys: set[str] | frozenset[str],
    reward_source_balance: int,
) -> dict[str, bool]:
    try:
        program = active_participant_program_by_id_v0(distribution, str(claim.get("program_id", "")))
        program_exists = True
    except Exception:
        program = {}
        program_exists = False
    receipt_kind = claim.get("receipt_kind")
    amount = claim.get("amount")
    program_id = str(claim.get("program_id", ""))
    spent_before = int(spent_by_program.get(program_id, 0))
    budget = int(program.get("budget_amount", 0)) if program_exists else 0
    program_claim_amount = int(program.get("claim_amount", 0)) if program_exists else 0
    claim_key = claim.get("claim_key")
    source_balance = reward_source_balance if isinstance(reward_source_balance, int) and not isinstance(reward_source_balance, bool) else -1
    return {
        "program_exists": program_exists,
        "receipt_kind_eligible": isinstance(receipt_kind, str) and receipt_kind in set(program.get("eligibility_receipts", [])),
        "recipient_pubkey_canonical": _is_canonical_hex_v0(claim.get("recipient_pubkey"), nbytes=48),
        "receipt_hash_canonical": _is_canonical_hex_v0(claim.get("receipt_hash"), nbytes=32),
        "source_tx_hash_canonical": _is_canonical_hex_v0(claim.get("source_tx_hash"), nbytes=32),
        "amount_positive": isinstance(amount, int)
        and not isinstance(amount, bool)
        and 0 < amount <= MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT,
        "amount_matches_program_claim_amount": isinstance(amount, int)
        and not isinstance(amount, bool)
        and program_claim_amount > 0
        and amount == program_claim_amount,
        "amount_within_program_remaining": isinstance(amount, int)
        and not isinstance(amount, bool)
        and spent_before >= 0
        and 0 < amount
        and spent_before + amount <= budget,
        "amount_within_reward_source_balance": isinstance(amount, int)
        and not isinstance(amount, bool)
        and source_balance >= 0
        and 0 < amount <= source_balance,
        "receipt_not_previously_claimed": isinstance(claim_key, str) and claim_key not in claimed_keys,
        "production_security_claim_false": claim.get("production_security_claim") is False,
    }


def _active_participant_emission_policy_v0(distribution: Mapping[str, Any]) -> dict[str, Any]:
    policy = distribution.get("active_participant_emission_policy")
    if not isinstance(policy, Mapping):
        raise ValueError("token distribution active_participant_emission_policy must be an object")
    if policy.get("schema") != "zenodex.zeno_ledger.active_participant_emission_policy.v0":
        raise ValueError("token distribution active_participant_emission_policy schema mismatch")
    if policy.get("reward_source_allocation_id") != ACTIVE_PARTICIPANT_REWARD_POOL_ID:
        raise ValueError("token distribution active participant emission reward source mismatch")
    active_pool = _allocation_by_id_v0(distribution, ACTIVE_PARTICIPANT_REWARD_POOL_ID)
    active_pool_amount = _require_nonnegative_int(active_pool.get("amount"), name="active_reward_pool.amount")
    reserve_floor = _require_nonnegative_int(policy.get("reward_reserve_floor"), name="emission_policy.reward_reserve_floor")
    refill_trigger = _require_nonnegative_int(policy.get("refill_trigger_balance"), name="emission_policy.refill_trigger_balance")
    refill_target = _require_nonnegative_int(policy.get("refill_target_balance"), name="emission_policy.refill_target_balance")
    if reserve_floor != refill_trigger:
        raise ValueError("emission policy reserve floor must equal refill trigger")
    if refill_target < refill_trigger:
        raise ValueError("emission policy refill target must be >= refill trigger")
    if refill_target > active_pool_amount:
        raise ValueError("emission policy refill target exceeds reward pool")
    initial_rate = _require_nonnegative_int(policy.get("initial_emission_bps"), name="emission_policy.initial_emission_bps")
    if initial_rate > _BPS_SCALE:
        raise ValueError("emission policy initial_emission_bps must be <= 10000")
    min_remaining_epochs = _require_positive_int(
        policy.get("min_remaining_epochs"),
        name="emission_policy.min_remaining_epochs",
        maximum=9_223_372_036_854_775_807,
    )
    max_epoch_budget = _require_positive_int(
        policy.get("max_epoch_budget"),
        name="emission_policy.max_epoch_budget",
        maximum=9_223_372_036_854_775_807,
    )
    reward_to_burn_bps = _require_nonnegative_int(policy.get("reward_to_burn_bps"), name="emission_policy.reward_to_burn_bps")
    if reward_to_burn_bps > _BPS_SCALE:
        raise ValueError("emission policy reward_to_burn_bps must be <= 10000")
    raw_weights = policy.get("program_weight_bps")
    if not isinstance(raw_weights, Mapping) or not raw_weights:
        raise ValueError("emission policy program_weight_bps must be a non-empty object")
    programs = distribution.get("active_participant_programs")
    if not isinstance(programs, list):
        raise ValueError("token distribution active_participant_programs must be a list")
    expected_weights = {
        str(program["id"]): int(program["share_bps_of_reward_pool"])
        for program in programs
        if isinstance(program, Mapping)
    }
    weights = {
        str(program_id): _require_nonnegative_int(weight, name=f"emission_policy.program_weight_bps.{program_id}")
        for program_id, weight in raw_weights.items()
    }
    if weights != expected_weights:
        raise ValueError("emission policy program weights must match active participant programs")
    if sum(weights.values()) != _BPS_SCALE:
        raise ValueError("emission policy program weights must sum to 10000 bps")
    if policy.get("rate_update_rule") != "monotone_nonincreasing":
        raise ValueError("emission policy rate_update_rule mismatch")
    refill_sources = policy.get("refill_sources")
    if not isinstance(refill_sources, list) or "protocol_fee_reward_refill_when_reserve_at_or_below_trigger" not in refill_sources:
        raise ValueError("emission policy conditional protocol-fee refill source missing")
    return {
        **dict(policy),
        "reward_reserve_floor": reserve_floor,
        "refill_trigger_balance": refill_trigger,
        "refill_target_balance": refill_target,
        "initial_emission_bps": initial_rate,
        "min_remaining_epochs": min_remaining_epochs,
        "max_epoch_budget": max_epoch_budget,
        "reward_to_burn_bps": reward_to_burn_bps,
        "program_weight_bps": weights,
    }


def _active_participant_program_epoch_budgets_v0(
    *,
    distribution: Mapping[str, Any],
    epoch_budget: int,
) -> list[dict[str, Any]]:
    policy = _active_participant_emission_policy_v0(distribution)
    budget = _require_nonnegative_int(epoch_budget, name="emission.epoch_budget")
    weights = dict(policy["program_weight_bps"])
    return [
        {
            "program_id": program_id,
            "weight_bps": weight,
            "epoch_budget": budget * int(weight) // _BPS_SCALE,
        }
        for program_id, weight in sorted(weights.items())
    ]


def _active_participant_emission_policy_flags_v0(
    event: Mapping[str, Any],
    *,
    distribution: Mapping[str, Any],
) -> dict[str, bool]:
    try:
        _active_participant_emission_policy_v0(distribution)
        policy_exists = True
    except Exception:
        policy_exists = False
    reserve_before = event.get("reserve_before")
    reserve_after_refill = event.get("reserve_after_refill")
    reserve_floor = event.get("reward_reserve_floor")
    refill_trigger = event.get("refill_trigger_balance")
    refill_target = event.get("refill_target_balance")
    refill_available = event.get("protocol_fee_refill_available")
    refill_amount = event.get("refill_amount")
    refill_remainder = event.get("refill_remainder_for_buyback")
    previous_rate = event.get("previous_emission_bps")
    rate = event.get("emission_bps")
    spendable = event.get("spendable_above_floor")
    burn_amount = event.get("epoch_burn_amount")
    reward_to_burn_bps = event.get("reward_to_burn_bps")
    burn_cap_budget = event.get("burn_cap_budget")
    base_drip = event.get("base_drip_budget")
    horizon_budget = event.get("horizon_budget")
    epoch_budget = event.get("epoch_budget")
    min_remaining_epochs = event.get("min_remaining_epochs")
    max_epoch_budget = event.get("max_epoch_budget")
    program_budget_total = event.get("program_epoch_budget_total")
    unallocated = event.get("unallocated_epoch_budget")
    reserve_after_epoch = event.get("reserve_after_epoch_if_fully_spent")
    ints_ok = all(
        isinstance(value, int) and not isinstance(value, bool) and value >= 0
        for value in (
            reserve_before,
            reserve_after_refill,
            reserve_floor,
            refill_trigger,
            refill_target,
            refill_available,
            refill_amount,
            refill_remainder,
            previous_rate,
            rate,
            spendable,
            burn_amount,
            reward_to_burn_bps,
            burn_cap_budget,
            base_drip,
            horizon_budget,
            epoch_budget,
            min_remaining_epochs,
            max_epoch_budget,
            program_budget_total,
            unallocated,
            reserve_after_epoch,
        )
    )
    if not ints_ok:
        return {
            "policy_exists": policy_exists,
            "distribution_hash_matches": False,
            "refill_only_when_triggered": False,
            "refill_math_matches": False,
            "rate_monotone_nonincreasing": False,
            "reward_budget_below_burn_budget": False,
            "epoch_budget_matches_decay_formula": False,
            "program_budgets_within_epoch_budget": False,
            "reserve_floor_preserved_if_epoch_fully_spent": False,
            "production_security_claim_false": event.get("production_security_claim") is False,
        }
    rb = cast(int, reserve_before)
    rar = cast(int, reserve_after_refill)
    floor = cast(int, reserve_floor)
    trigger = cast(int, refill_trigger)
    target = cast(int, refill_target)
    refill_in = cast(int, refill_available)
    refill = cast(int, refill_amount)
    remainder = cast(int, refill_remainder)
    prev_bps = cast(int, previous_rate)
    bps = cast(int, rate)
    spendable_value = cast(int, spendable)
    burn_value = cast(int, burn_amount)
    reward_to_burn = cast(int, reward_to_burn_bps)
    burn_cap_value = cast(int, burn_cap_budget)
    base_drip_value = cast(int, base_drip)
    horizon_value = cast(int, horizon_budget)
    epoch_budget_value = cast(int, epoch_budget)
    min_epochs = cast(int, min_remaining_epochs)
    max_budget = cast(int, max_epoch_budget)
    program_total = cast(int, program_budget_total)
    unallocated_budget = cast(int, unallocated)
    reserve_after_spend = cast(int, reserve_after_epoch)
    expected_triggered = rb <= trigger
    expected_capacity = max(0, target - rb) if expected_triggered else 0
    expected_refill = min(refill_in, expected_capacity)
    expected_spendable = max(0, rar - floor)
    expected_base_drip = expected_spendable * bps // _BPS_SCALE
    expected_horizon = expected_spendable // min_epochs if min_epochs > 0 else -1
    expected_burn_cap = burn_value * reward_to_burn // _BPS_SCALE
    expected_epoch_budget = min(expected_base_drip, expected_horizon, max_budget, expected_burn_cap)
    expected_program_budgets = _active_participant_program_epoch_budgets_v0(
        distribution=distribution,
        epoch_budget=expected_epoch_budget,
    ) if policy_exists else []
    expected_program_total = sum(int(row["epoch_budget"]) for row in expected_program_budgets)
    return {
        "policy_exists": policy_exists,
        "distribution_hash_matches": event.get("distribution_hash") == protocol_token_distribution_hash_v0(distribution),
        "refill_only_when_triggered": (expected_triggered or refill == 0)
        and event.get("refill_triggered") is expected_triggered,
        "refill_math_matches": refill == expected_refill
        and remainder == refill_in - expected_refill
        and rar == rb + expected_refill,
        "rate_monotone_nonincreasing": bps <= prev_bps <= _BPS_SCALE,
        "reward_budget_below_burn_budget": reward_to_burn <= _BPS_SCALE
        and burn_cap_value == expected_burn_cap
        and epoch_budget_value <= expected_burn_cap,
        "epoch_budget_matches_decay_formula": spendable_value == expected_spendable
        and base_drip_value == expected_base_drip
        and horizon_value == expected_horizon
        and epoch_budget_value == expected_epoch_budget,
        "program_budgets_within_epoch_budget": event.get("program_epoch_budgets") == expected_program_budgets
        and program_total == expected_program_total
        and unallocated_budget == expected_epoch_budget - expected_program_total
        and expected_program_total <= expected_epoch_budget,
        "reserve_floor_preserved_if_epoch_fully_spent": reserve_after_spend == rar - expected_epoch_budget
        and reserve_after_spend >= floor,
        "production_security_claim_false": event.get("production_security_claim") is False,
    }


def _distribution_policy_flags_v0(distribution: Mapping[str, Any]) -> dict[str, bool]:
    allocations = distribution.get("allocations")
    allocation_rows = allocations if isinstance(allocations, list) else []
    initial_supply = distribution.get("initial_supply")
    supply_floor = distribution.get("supply_floor")
    active_pool = next(
        (
            row
            for row in allocation_rows
            if isinstance(row, Mapping) and row.get("id") == ACTIVE_PARTICIPANT_REWARD_POOL_ID
        ),
        None,
    )
    active_programs = distribution.get("active_participant_programs")
    program_rows = active_programs if isinstance(active_programs, list) else []
    allocation_sum = sum(
        int(row.get("amount", -1))
        for row in allocation_rows
        if isinstance(row, Mapping) and isinstance(row.get("amount"), int) and not isinstance(row.get("amount"), bool)
    )
    allocation_bps = sum(
        int(row.get("share_bps", -1))
        for row in allocation_rows
        if isinstance(row, Mapping) and isinstance(row.get("share_bps"), int) and not isinstance(row.get("share_bps"), bool)
    )
    program_sum = sum(
        int(row.get("budget_amount", -1))
        for row in program_rows
        if isinstance(row, Mapping)
        and isinstance(row.get("budget_amount"), int)
        and not isinstance(row.get("budget_amount"), bool)
    )
    program_bps = sum(
        int(row.get("share_bps_of_reward_pool", -1))
        for row in program_rows
        if isinstance(row, Mapping)
        and isinstance(row.get("share_bps_of_reward_pool"), int)
        and not isinstance(row.get("share_bps_of_reward_pool"), bool)
    )
    program_claim_amounts_valid = all(
        isinstance(row, Mapping)
        and isinstance(row.get("claim_amount"), int)
        and not isinstance(row.get("claim_amount"), bool)
        and 0 < int(row.get("claim_amount", 0)) <= MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT
        for row in program_rows
    )
    active_amount = active_pool.get("amount") if isinstance(active_pool, Mapping) else None
    try:
        _active_participant_emission_policy_v0(distribution)
        active_emission_policy_valid = True
    except Exception:
        active_emission_policy_valid = False
    immutability = distribution.get("immutability")
    immutable = immutability if isinstance(immutability, Mapping) else {}
    ids = [
        str(row.get("id", "")).lower()
        for row in allocation_rows
        if isinstance(row, Mapping)
    ]
    user_fixture_roles = {"alice", "bob", "carol"}
    active_role = str(active_pool.get("recipient_role", "")) if isinstance(active_pool, Mapping) else ""
    return {
        "allocations_sum_to_initial_supply": isinstance(initial_supply, int) and allocation_sum == initial_supply,
        "allocation_bps_sum_to_10000": allocation_bps == _BPS_SCALE,
        "active_programs_sum_to_pool": isinstance(active_amount, int) and program_sum == active_amount and program_bps == _BPS_SCALE,
        "active_program_claim_amounts_valid": program_claim_amounts_valid,
        "active_emission_policy_valid": active_emission_policy_valid,
        "active_rewards_pool_present": isinstance(active_pool, Mapping),
        "protocol_faucet_disabled": distribution.get("protocol_token_faucet_mint_allowed") is False,
        "external_minting_disabled": distribution.get("external_minting_allowed") is False,
        "supply_floor_valid": isinstance(initial_supply, int)
        and isinstance(supply_floor, int)
        and 0 < supply_floor <= initial_supply,
        "no_retroactive_airdrop_bucket": all("retroactive" not in allocation_id and "airdrop" not in allocation_id for allocation_id in ids),
        "active_pool_not_direct_user_fixture": active_role not in user_fixture_roles,
        "post_genesis_mutation_disabled": immutable.get("post_genesis_mutation_allowed") is False,
        "runtime_mutation_disabled": immutable.get("runtime_mutation_allowed") is False,
        "python_override_disabled_after_genesis": immutable.get("python_override_allowed_after_genesis") is False,
        "distribution_changes_require_new_hash": immutable.get("requires_new_distribution_hash_for_any_change") is True,
        "post_genesis_changes_require_new_chain_or_governance_migration": (
            immutable.get("requires_new_chain_or_explicit_governance_migration_for_post_genesis_change") is True
        ),
        "production_security_claim_false": distribution.get("production_security_claim") is False,
    }


def _allocation_by_id_v0(distribution: Mapping[str, Any], allocation_id: str) -> Mapping[str, Any]:
    if not isinstance(allocation_id, str) or not allocation_id:
        raise ValueError("allocation_id must be non-empty")
    allocations = distribution.get("allocations")
    if not isinstance(allocations, list):
        raise ValueError("token distribution allocations must be a list")
    for row in allocations:
        if isinstance(row, Mapping) and row.get("id") == allocation_id:
            return row
    raise ValueError("token distribution allocation not found")


def _tokenomics_buyback_burn_policy_flags_v0(
    event: Mapping[str, Any],
    *,
    distribution: Mapping[str, Any],
) -> dict[str, bool]:
    try:
        allocation = _allocation_by_id_v0(distribution, str(event.get("source_allocation_id", "")))
        source_allocation_exists = True
    except Exception:
        allocation = {}
        source_allocation_exists = False
    fee = event.get("total_swap_fee")
    share = event.get("buyback_share_bps")
    carry_before = event.get("carry_before")
    carry_after = event.get("carry_after")
    burn = event.get("burn_amount")
    treasury_burn = event.get("treasury_burn_amount", burn)
    mode = str(event.get("execution_mode", "treasury_allocation_burn_only"))
    source_before = event.get("source_balance_before")
    source_after = event.get("source_balance_after")
    supply_before = event.get("current_supply_before")
    supply_after = event.get("current_supply_after")
    supply_floor = event.get("supply_floor")
    scaled_ok = (
        isinstance(fee, int)
        and not isinstance(fee, bool)
        and isinstance(share, int)
        and not isinstance(share, bool)
        and isinstance(carry_before, int)
        and not isinstance(carry_before, bool)
        and isinstance(carry_after, int)
        and not isinstance(carry_after, bool)
        and isinstance(burn, int)
        and not isinstance(burn, bool)
        and isinstance(treasury_burn, int)
        and not isinstance(treasury_burn, bool)
        and fee >= 0
        and 0 <= share <= _BPS_SCALE
        and 0 <= carry_before < _BPS_SCALE
        and 0 <= carry_after < _BPS_SCALE
        and burn >= 0
        and treasury_burn == (carry_before + fee * share) // _BPS_SCALE
        and carry_after == (carry_before + fee * share) % _BPS_SCALE
    )
    if mode == "treasury_allocation_burn_only":
        scaled_ok = scaled_ok and burn == treasury_burn
        expected_source_after = source_before - burn if isinstance(source_before, int) and isinstance(burn, int) else None
    elif mode == "market_purchase_then_burn":
        market_purchase = event.get("market_purchase")
        scaled_ok = (
            scaled_ok
            and isinstance(market_purchase, Mapping)
            and isinstance(market_purchase.get("token_amount_out"), int)
            and not isinstance(market_purchase.get("token_amount_out"), bool)
            and burn == market_purchase.get("token_amount_out")
        )
        expected_source_after = source_before
    else:
        scaled_ok = False
        expected_source_after = None
    source_ok = (
        isinstance(source_before, int)
        and not isinstance(source_before, bool)
        and isinstance(source_after, int)
        and not isinstance(source_after, bool)
        and isinstance(burn, int)
        and not isinstance(burn, bool)
        and source_before >= 0
        and source_after >= 0
        and source_after == expected_source_after
    )
    supply_ok = (
        isinstance(supply_before, int)
        and not isinstance(supply_before, bool)
        and isinstance(supply_after, int)
        and not isinstance(supply_after, bool)
        and isinstance(supply_floor, int)
        and not isinstance(supply_floor, bool)
        and supply_before >= 0
        and supply_after >= 0
        and supply_floor == distribution.get("supply_floor")
        and supply_after == supply_before - (burn if isinstance(burn, int) and not isinstance(burn, bool) else -1)
        and supply_after >= supply_floor
    )
    return {
        "source_allocation_exists": source_allocation_exists,
        "source_pubkey_matches_allocation": source_allocation_exists
        and _is_canonical_hex_v0(event.get("source_pubkey"), nbytes=48)
        and event.get("source_pubkey") == allocation.get("recipient_pubkey"),
        "tx_hash_canonical": _is_canonical_hex_v0(event.get("tx_hash"), nbytes=32),
        "distribution_hash_matches": event.get("distribution_hash") == protocol_token_distribution_hash_v0(distribution),
        "token_asset_matches": event.get("token_asset_id") == distribution.get("token_asset_id"),
        "buyback_math_matches": scaled_ok,
        "source_balance_matches": source_ok,
        "supply_floor_preserved": supply_ok,
        "production_security_claim_false": event.get("production_security_claim") is False,
    }


def validate_protocol_token_distribution_v0(distribution: Mapping[str, Any]) -> None:
    obj = dict(distribution)
    if obj.get("schema") != PROTOCOL_TOKEN_DISTRIBUTION_SCHEMA_V0:
        raise ValueError("token distribution schema mismatch")
    chain_id = obj.get("chain_id")
    if not isinstance(chain_id, str) or not chain_id:
        raise ValueError("token distribution chain_id must be non-empty")
    token_symbol = obj.get("token_symbol")
    if not isinstance(token_symbol, str) or not token_symbol:
        raise ValueError("token distribution token_symbol must be non-empty")
    canonical_hex_fixed_allow_0x(obj.get("token_asset_id"), nbytes=32, name="token_distribution.token_asset_id")
    initial_supply = _require_nonnegative_int(obj.get("initial_supply"), name="token_distribution.initial_supply")
    supply_floor = _require_nonnegative_int(obj.get("supply_floor"), name="token_distribution.supply_floor")
    if initial_supply <= 0:
        raise ValueError("token distribution initial_supply must be positive")
    if supply_floor <= 0:
        raise ValueError("token distribution supply_floor must be positive")
    if supply_floor > initial_supply:
        raise ValueError("token distribution supply_floor must be <= initial_supply")
    allocations = obj.get("allocations")
    if not isinstance(allocations, list) or not allocations:
        raise ValueError("token distribution allocations must be a non-empty list")
    seen: set[str] = set()
    amount_total = 0
    bps_total = 0
    for index, raw in enumerate(allocations):
        if not isinstance(raw, Mapping):
            raise ValueError(f"token distribution allocations[{index}] must be an object")
        allocation_id = raw.get("id")
        if not isinstance(allocation_id, str) or not allocation_id:
            raise ValueError(f"token distribution allocations[{index}].id must be non-empty")
        if allocation_id in seen:
            raise ValueError("token distribution allocation ids must be unique")
        seen.add(allocation_id)
        if not isinstance(raw.get("category"), str) or not raw.get("category"):
            raise ValueError(f"token distribution allocations[{index}].category must be non-empty")
        if not isinstance(raw.get("recipient_role"), str) or not raw.get("recipient_role"):
            raise ValueError(f"token distribution allocations[{index}].recipient_role must be non-empty")
        canonical_hex_fixed_allow_0x(
            raw.get("recipient_pubkey"),
            nbytes=48,
            name=f"token_distribution.allocations[{index}].recipient_pubkey",
        )
        amount = _require_nonnegative_int(raw.get("amount"), name=f"token_distribution.allocations[{index}].amount")
        share_bps = _require_nonnegative_int(raw.get("share_bps"), name=f"token_distribution.allocations[{index}].share_bps")
        if amount <= 0:
            raise ValueError(f"token distribution allocations[{index}].amount must be positive")
        if share_bps <= 0:
            raise ValueError(f"token distribution allocations[{index}].share_bps must be positive")
        amount_total += amount
        bps_total += share_bps
    if amount_total != initial_supply:
        raise ValueError("token distribution allocation_total must equal initial_supply")
    if bps_total != _BPS_SCALE:
        raise ValueError("token distribution allocation shares must sum to 10000 bps")
    if obj.get("allocation_total") != amount_total:
        raise ValueError("token distribution allocation_total mismatch")
    if obj.get("allocation_share_bps_total") != bps_total:
        raise ValueError("token distribution allocation_share_bps_total mismatch")
    active_pool = next((row for row in allocations if row.get("id") == ACTIVE_PARTICIPANT_REWARD_POOL_ID), None)
    if active_pool is None:
        raise ValueError("token distribution active participant reward pool missing")
    active_programs = obj.get("active_participant_programs")
    if not isinstance(active_programs, list) or not active_programs:
        raise ValueError("token distribution active participant programs must be a non-empty list")
    active_budget_total = 0
    active_bps_total = 0
    active_seen: set[str] = set()
    for index, raw in enumerate(active_programs):
        if not isinstance(raw, Mapping):
            raise ValueError(f"token distribution active_participant_programs[{index}] must be an object")
        program_id = raw.get("id")
        if not isinstance(program_id, str) or not program_id:
            raise ValueError(f"token distribution active_participant_programs[{index}].id must be non-empty")
        if program_id in active_seen:
            raise ValueError("token distribution active participant program ids must be unique")
        active_seen.add(program_id)
        if raw.get("reward_source_allocation_id") != ACTIVE_PARTICIPANT_REWARD_POOL_ID:
            raise ValueError(f"token distribution active_participant_programs[{index}] reward source mismatch")
        if not isinstance(raw.get("category"), str) or not raw.get("category"):
            raise ValueError(f"token distribution active_participant_programs[{index}].category must be non-empty")
        if not isinstance(raw.get("controller_role"), str) or not raw.get("controller_role"):
            raise ValueError(f"token distribution active_participant_programs[{index}].controller_role must be non-empty")
        canonical_hex_fixed_allow_0x(
            raw.get("controller_pubkey"),
            nbytes=48,
            name=f"token_distribution.active_participant_programs[{index}].controller_pubkey",
        )
        budget_amount = _require_nonnegative_int(
            raw.get("budget_amount"),
            name=f"token_distribution.active_participant_programs[{index}].budget_amount",
        )
        share_bps = _require_nonnegative_int(
            raw.get("share_bps_of_reward_pool"),
            name=f"token_distribution.active_participant_programs[{index}].share_bps_of_reward_pool",
        )
        if budget_amount <= 0:
            raise ValueError(f"token distribution active_participant_programs[{index}].budget_amount must be positive")
        if share_bps <= 0:
            raise ValueError(f"token distribution active_participant_programs[{index}].share_bps_of_reward_pool must be positive")
        claim_amount = _require_nonnegative_int(
            raw.get("claim_amount"),
            name=f"token distribution active_participant_programs[{index}].claim_amount",
        )
        if claim_amount <= 0 or claim_amount > MAX_LOCAL_TESTNET_ACTIVE_PARTICIPANT_CLAIM_AMOUNT:
            raise ValueError(f"token distribution active_participant_programs[{index}].claim_amount invalid")
        receipts = raw.get("eligibility_receipts")
        if not isinstance(receipts, list) or not receipts or not all(isinstance(item, str) and item for item in receipts):
            raise ValueError(f"token distribution active_participant_programs[{index}].eligibility_receipts invalid")
        active_budget_total += budget_amount
        active_bps_total += share_bps
    if active_budget_total != int(active_pool["amount"]):
        raise ValueError("token distribution active participant budgets must equal reward pool amount")
    if active_bps_total != _BPS_SCALE:
        raise ValueError("token distribution active participant program shares must sum to 10000 bps")
    _active_participant_emission_policy_v0(obj)
    immutability = obj.get("immutability")
    if not isinstance(immutability, Mapping):
        raise ValueError("token distribution immutability must be an object")
    if immutability.get("schema") != PROTOCOL_TOKEN_DISTRIBUTION_IMMUTABILITY_SCHEMA_V0:
        raise ValueError("token distribution immutability schema mismatch")
    if not isinstance(immutability.get("tokenomics_version"), str) or not immutability.get("tokenomics_version"):
        raise ValueError("token distribution immutability tokenomics_version must be non-empty")
    if immutability.get("mutable_before_genesis") is not True:
        raise ValueError("token distribution must remain editable before genesis")
    if immutability.get("post_genesis_mutation_allowed") is not False:
        raise ValueError("token distribution post-genesis mutation must be disabled")
    if immutability.get("runtime_mutation_allowed") is not False:
        raise ValueError("token distribution runtime mutation must be disabled")
    if immutability.get("python_override_allowed_after_genesis") is not False:
        raise ValueError("token distribution Python override after genesis must be disabled")
    if immutability.get("requires_new_distribution_hash_for_any_change") is not True:
        raise ValueError("token distribution changes must require a new distribution hash")
    if immutability.get("requires_new_chain_or_explicit_governance_migration_for_post_genesis_change") is not True:
        raise ValueError("token distribution post-genesis changes must require a new chain or explicit governance migration")
    flags = _distribution_policy_flags_v0(obj)
    if not all(flags.values()):
        failed = sorted(key for key, value in flags.items() if value is not True)
        raise ValueError(f"token distribution policy flags failed: {','.join(failed)}")
    tau_policy = obj.get("tau_policy")
    if not isinstance(tau_policy, Mapping):
        raise ValueError("token distribution tau_policy must be an object")
    if tau_policy.get("policy_id") != PROTOCOL_TOKEN_DISTRIBUTION_TAU_POLICY_ID:
        raise ValueError("token distribution tau_policy policy_id mismatch")
    if tau_policy.get("path") != PROTOCOL_TOKEN_DISTRIBUTION_TAU_POLICY_PATH:
        raise ValueError("token distribution tau_policy path mismatch")
    if tau_policy.get("mode") != "host_computed_flags":
        raise ValueError("token distribution tau_policy mode mismatch")
    if dict(tau_policy.get("host_computed_flags", {})) != flags:
        raise ValueError("token distribution tau_policy host_computed_flags mismatch")
    if obj.get("protocol_token_faucet_mint_allowed") is not False:
        raise ValueError("protocol token faucet minting must be disabled")
    if obj.get("external_minting_allowed") is not False:
        raise ValueError("protocol token external minting must be disabled")
    distribution_hash = obj.get("distribution_hash")
    if distribution_hash is not None and distribution_hash != protocol_token_distribution_hash_v0(obj):
        raise ValueError("token distribution hash mismatch")


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return int(value)


def _require_positive_int(value: object, *, name: str, maximum: int) -> int:
    amount = _require_nonnegative_int(value, name=name)
    if amount <= 0:
        raise ValueError(f"{name} must be positive")
    if amount > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return amount


def _require_nonempty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _is_canonical_hex_v0(value: object, *, nbytes: int) -> bool:
    if not isinstance(value, str):
        return False
    try:
        return canonical_hex_fixed_allow_0x(value, nbytes=nbytes, name="hex") == value
    except Exception:
        return False
