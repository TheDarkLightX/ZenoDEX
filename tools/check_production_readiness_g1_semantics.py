#!/usr/bin/env python3
"""Check the exact-subject, research-only G1 semantic mapping.

G1 establishes a closed mapping from the source command registry to the
semantic surfaces that still need decisions and evidence.  The artifact is
deliberately subordinate to the frozen source subject: it can describe source
semantics and open decisions, but it cannot enable a command, mount an
entrypoint, or promote a production claim.
"""

from __future__ import annotations

import argparse
import ast
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
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_G1_SEMANTICS_V1.json"
SOURCE_SUBJECT = "e8059cb5e27e80c2f8ba627501d6097f3c5e6b0c"
SOURCE_PATH = "src/core/m6_safe_mount_types_v1.py"
TRANSITION_PATH = "src/core/m6_safe_mount_transition_v1.py"
SCHEMA = "zenodex/production-readiness-g1-semantics/v1"

sys.path.insert(0, str(REPO_ROOT))

from src.core.m6_safe_mount_types_v1 import (  # noqa: E402
    M6_RESEARCH_DISABLED_COMMANDS_V1,
    GlobalCommandKindV1,
)

EXPECTED_COMMANDS = frozenset(GlobalCommandKindV1)
EXPECTED_DISABLED = frozenset(M6_RESEARCH_DISABLED_COMMANDS_V1)
EXPECTED_STATE_FIELDS = (
    "balances",
    "custody",
    "supply",
    "debt",
    "lp_state",
    "perps_liabilities",
    "escrows",
    "reserves",
    "auctions",
    "withdrawals",
    "outbox",
    "history",
    "nullifiers",
    "release_state",
)
EXPECTED_DELTA_CLASSES = (
    "internal_transfer",
    "mint",
    "burn",
    "liability",
    "reserve_transfer",
    "fee_allocation",
    "reward",
    "external_in",
    "external_out",
    "refund",
    "slash",
)
EXPECTED_EXCLUDED_COMMANDS = ("zusd_emergency_shutdown",)

_STATE_FIELD_CONTRACTS: dict[str, dict[str, Any]] = {
    "balances": {
        "owner": "asset_accounting_core",
        "meaning": "owned asset amounts indexed by owner and custody",
        "delta_classes": [
            "internal_transfer",
            "reserve_transfer",
            "fee_allocation",
            "reward",
            "external_in",
            "external_out",
            "refund",
            "slash",
        ],
        "terminal_obligation": "every claim is drained or assigned to an explicit reserve owner",
    },
    "custody": {
        "owner": "custody_reconciliation_core",
        "meaning": "external custody and claim buckets for managed assets",
        "delta_classes": ["internal_transfer", "external_in", "external_out", "refund"],
        "terminal_obligation": "no external effect exists without an ancestor custody claim",
    },
    "supply": {
        "owner": "asset_issue_burn_policy",
        "meaning": "per-asset supply and protected-floor quantities",
        "delta_classes": ["mint", "burn", "internal_transfer"],
        "terminal_obligation": "issue, burn, and terminal supply disposition are explicit",
    },
    "debt": {
        "owner": "zusd_monetary_core",
        "meaning": "owner- and asset-indexed liability amounts",
        "delta_classes": ["liability", "mint", "burn", "refund", "slash"],
        "terminal_obligation": "every liability has an exact close, redemption, or recovery owner",
    },
    "lp_state": {
        "owner": "spot_and_liquidity_core",
        "meaning": "pool reserves, LP shares, fees, and rounding residues",
        "delta_classes": [
            "internal_transfer",
            "mint",
            "burn",
            "reserve_transfer",
            "fee_allocation",
            "refund",
        ],
        "terminal_obligation": "final LP removal drains reserves, fees, and dust exactly",
    },
    "perps_liabilities": {
        "owner": "perps_risk_and_settlement_core",
        "meaning": "margin, PnL, funding, insurance, and bad-debt liabilities",
        "delta_classes": [
            "liability",
            "internal_transfer",
            "reserve_transfer",
            "fee_allocation",
            "reward",
            "external_out",
            "refund",
            "slash",
        ],
        "terminal_obligation": "closed positions leave no unowned margin or liability",
    },
    "escrows": {
        "owner": "escrow_and_auction_custody_core",
        "meaning": "phase-bound deposits, bonds, inventory, and claims",
        "delta_classes": [
            "internal_transfer",
            "reserve_transfer",
            "refund",
            "slash",
            "external_out",
        ],
        "terminal_obligation": "cancel, expire, settle, or recover every escrow exactly once",
    },
    "reserves": {
        "owner": "reserve_policy_core",
        "meaning": "fee, insurance, reward, and protected reserve buckets",
        "delta_classes": [
            "internal_transfer",
            "mint",
            "burn",
            "reserve_transfer",
            "fee_allocation",
            "reward",
            "refund",
            "slash",
        ],
        "terminal_obligation": "each reserve has a named beneficiary and terminal disposition",
    },
    "auctions": {
        "owner": "sealed_bid_commit_reveal_settlement_core",
        "meaning": "auction phase, commitment, winner, and settlement records",
        "delta_classes": [
            "internal_transfer",
            "reserve_transfer",
            "fee_allocation",
            "refund",
            "slash",
            "external_out",
        ],
        "terminal_obligation": "all bids and inventory reach a deterministic final phase",
    },
    "withdrawals": {
        "owner": "withdrawal_and_outbox_core",
        "meaning": "requested, acknowledged, retried, and completed withdrawals",
        "delta_classes": ["external_out", "refund", "slash"],
        "terminal_obligation": "each withdrawal has one idempotent completion or refund",
    },
    "outbox": {
        "owner": "committed_effect_outbox_core",
        "meaning": "committed external effect identities and delivery state",
        "delta_classes": ["external_out", "refund", "slash"],
        "terminal_obligation": "every effect descends from one committed outbox ancestor",
    },
    "history": {
        "owner": "durable_publication_core",
        "meaning": "canonical command decisions, receipts, and publication lineage",
        "delta_classes": ["internal_transfer"],
        "terminal_obligation": "replay and recovery classify one immutable publication identity",
    },
    "nullifiers": {
        "owner": "authenticated_replay_core",
        "meaning": "consumed sender nonces, proof identities, and replay keys",
        "delta_classes": ["internal_transfer"],
        "terminal_obligation": "one nonce or nullifier authorizes at most one transition",
    },
    "release_state": {
        "owner": "promotion_and_authority_core",
        "meaning": "deployment, authority epoch, profile, and release bindings",
        "delta_classes": ["internal_transfer"],
        "terminal_obligation": "authority changes require an exact governed migration",
    },
}

_DELTA_CLASS_CONTRACTS: dict[str, dict[str, Any]] = {
    "internal_transfer": {
        "required_fields": [
            "asset",
            "amount_atoms",
            "source_owner",
            "destination_owner",
            "source_custody",
            "destination_custody",
            "economic_event",
        ],
        "supply_effect": "zero",
        "law": "source debit equals destination credit in the same asset and event",
    },
    "mint": {
        "required_fields": ["asset", "amount_atoms", "issuer_authority", "recipient_owner", "economic_event"],
        "supply_effect": "positive_exact_amount",
        "law": "issue authority and supply increase are bound in one accepted transition",
    },
    "burn": {
        "required_fields": ["asset", "amount_atoms", "burn_authority", "source_owner", "economic_event"],
        "supply_effect": "negative_exact_amount",
        "law": "burn authority, source custody, and supply decrease are bound in one accepted transition",
    },
    "liability": {
        "required_fields": ["asset", "amount_atoms", "liability_owner", "liability_kind", "economic_event"],
        "supply_effect": "profile_defined_relation",
        "law": "the liability owner, asset, and before/after relation are explicit",
    },
    "reserve_transfer": {
        "required_fields": [
            "asset",
            "amount_atoms",
            "direction",
            "reserve_owner",
            "reserve_ledger_allocation",
            "counterparty_owner",
            "counterparty_ledger_allocation",
            "economic_event",
        ],
        "supply_effect": "zero",
        "law": "one event moves the exact amount between a named reserve and a distinct counterparty allocation",
    },
    "fee_allocation": {
        "required_fields": [
            "asset",
            "amount_atoms",
            "fee_source_owner",
            "fee_source_ledger_allocation",
            "beneficiary_owner",
            "beneficiary_ledger_allocation",
            "fee_policy_root",
            "economic_event",
        ],
        "supply_effect": "zero",
        "law": "fee source, beneficiary, amount, and policy root are bound in one event",
    },
    "reward": {
        "required_fields": [
            "asset",
            "amount_atoms",
            "reserve_owner",
            "reserve_ledger_allocation",
            "reward_owner",
            "reward_ledger_allocation",
            "reward_policy_root",
            "economic_event",
        ],
        "supply_effect": "zero",
        "law": "reward reserve, recipient, amount, and policy root are bound in one event",
    },
    "external_in": {
        "required_fields": ["asset", "amount_atoms", "source_effect", "destination_custody", "economic_event"],
        "supply_effect": "outside_core_or_profile_defined",
        "law": "ingress is authenticated and creates one custody claim before internal credit",
    },
    "external_out": {
        "required_fields": ["asset", "amount_atoms", "source_custody", "destination_effect", "economic_event"],
        "supply_effect": "outside_core_or_profile_defined",
        "law": "outflow requires an ancestor custody claim and one committed outbox identity",
    },
    "refund": {
        "required_fields": ["asset", "amount_atoms", "refund_owner", "source_event", "economic_event"],
        "supply_effect": "zero_or_profile_defined",
        "law": "refund target and source event are explicit and idempotent",
    },
    "slash": {
        "required_fields": ["asset", "amount_atoms", "slashed_owner", "beneficiary_owner", "economic_event"],
        "supply_effect": "zero_or_profile_defined",
        "law": "slashing authority, beneficiary, and residue disposition are explicit",
    },
}

_FAMILY_DEFINITIONS: dict[str, dict[str, Any]] = {
    "spot_and_liquidity": {
        "actor": "trader_or_liquidity_provider",
        "economic_owner": "spot_and_liquidity_core",
        "terminal_path": "spot_lp_reserve_and_custody_terminal",
        "formal_obligation_ids": ["M6-R01", "M6-R04", "M6-R09", "M6-R13"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "accounting",
            "terminal",
            "replay",
        ],
    },
    "zusd_monetary": {
        "actor": "borrower_or_stability_provider",
        "economic_owner": "zusd_monetary_core",
        "terminal_path": "zusd_debt_supply_redemption_terminal",
        "formal_obligation_ids": ["M6-R04", "M6-R08", "M6-R09", "M6-R13"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "accounting",
            "freshness",
            "terminal",
            "replay",
        ],
    },
    "perps_risk": {
        "actor": "perp_trader_or_liquidator",
        "economic_owner": "perps_risk_and_settlement_core",
        "terminal_path": "perps_margin_insurance_close_terminal",
        "formal_obligation_ids": ["M6-R04", "M6-R08", "M6-R09", "M6-R13"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "accounting",
            "freshness",
            "terminal",
            "replay",
        ],
    },
    "oracle": {
        "actor": "oracle_reporter_or_disputer",
        "economic_owner": "oracle_admission_and_commit_core",
        "terminal_path": "oracle_report_dispute_recovery_terminal",
        "formal_obligation_ids": ["M6-R05", "M6-R08", "M6-R09"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "freshness",
            "recovery",
            "replay",
        ],
    },
    "protocol_token": {
        "actor": "protocol_treasury_operator",
        "economic_owner": "protocol_token_buy_and_burn_core",
        "terminal_path": "protocol_token_treasury_and_burn_terminal",
        "formal_obligation_ids": ["M6-R01", "M6-R04", "M6-R09", "M6-R13"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "accounting",
            "terminal",
        ],
    },
    "proof_reward": {
        "actor": "proof_miner",
        "economic_owner": "proof_reward_claim_core",
        "terminal_path": "proof_reward_reserve_claim_terminal",
        "formal_obligation_ids": ["M6-R06", "M6-R07", "M6-R09", "M6-R13"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "accounting",
            "replay",
            "terminal",
        ],
    },
    "sealed_bid": {
        "actor": "sealed_bidder_or_auction_operator",
        "economic_owner": "sealed_bid_commit_reveal_settlement_core",
        "terminal_path": "auction_inventory_escrow_outbox_terminal",
        "formal_obligation_ids": ["M6-R04", "M6-R05", "M6-R09", "M6-R10", "M6-R13"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "commit",
            "reveal",
            "cancel",
            "recovery",
            "terminal",
            "replay",
        ],
    },
    "tau_escrow": {
        "actor": "tau_user_or_recovery_operator",
        "economic_owner": "tau_escrow_and_rejoin_core",
        "terminal_path": "tau_escrow_withdrawal_ack_rejoin_terminal",
        "formal_obligation_ids": ["M6-R03", "M6-R07", "M6-R09", "M6-R10", "M6-R11", "M6-R12"],
        "scenario_classes": [
            "happy",
            "authorization",
            "rejection",
            "recovery",
            "outage",
            "rejoin",
            "terminal",
            "replay",
        ],
    },
}

_COMMAND_FAMILY: dict[GlobalCommandKindV1, str] = {
    GlobalCommandKindV1.SPOT_SWAP: "spot_and_liquidity",
    GlobalCommandKindV1.LP_ADD: "spot_and_liquidity",
    GlobalCommandKindV1.LP_REMOVE: "spot_and_liquidity",
    GlobalCommandKindV1.ZUSD_BORROW: "zusd_monetary",
    GlobalCommandKindV1.ZUSD_REPAY: "zusd_monetary",
    GlobalCommandKindV1.ZUSD_REDEEM: "zusd_monetary",
    GlobalCommandKindV1.ZUSD_LIQUIDATE: "zusd_monetary",
    GlobalCommandKindV1.STABILITY_POOL_DEPOSIT: "zusd_monetary",
    GlobalCommandKindV1.STABILITY_POOL_WITHDRAW: "zusd_monetary",
    GlobalCommandKindV1.ZUSD_REDISTRIBUTE: "zusd_monetary",
    GlobalCommandKindV1.PERP_OPEN: "perps_risk",
    GlobalCommandKindV1.PERP_CLOSE: "perps_risk",
    GlobalCommandKindV1.PERP_FUNDING: "perps_risk",
    GlobalCommandKindV1.PERP_LIQUIDATE: "perps_risk",
    GlobalCommandKindV1.ORACLE_SUBMIT: "oracle",
    GlobalCommandKindV1.ORACLE_DISPUTE: "oracle",
    GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN: "protocol_token",
    GlobalCommandKindV1.ZRPF_PROVER_REWARD: "proof_reward",
    GlobalCommandKindV1.SELLER_AUCTION_COMMIT: "sealed_bid",
    GlobalCommandKindV1.SELLER_AUCTION_REVEAL: "sealed_bid",
    GlobalCommandKindV1.SELLER_AUCTION_SETTLE: "sealed_bid",
    GlobalCommandKindV1.SELLER_AUCTION_CANCEL: "sealed_bid",
    GlobalCommandKindV1.SELLER_AUCTION_EXPIRE: "sealed_bid",
    GlobalCommandKindV1.PRIVATE_SWAP_COMMIT: "sealed_bid",
    GlobalCommandKindV1.PRIVATE_SWAP_REVEAL: "sealed_bid",
    GlobalCommandKindV1.PRIVATE_SWAP_SETTLE: "sealed_bid",
    GlobalCommandKindV1.PRIVATE_SWAP_CANCEL: "sealed_bid",
    GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE: "sealed_bid",
    GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: "tau_escrow",
    GlobalCommandKindV1.TAU_WITHDRAWAL: "tau_escrow",
    GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: "tau_escrow",
    GlobalCommandKindV1.FALLBACK_ACTIVATE: "tau_escrow",
    GlobalCommandKindV1.TAU_REJOIN: "tau_escrow",
}

_HANDLER_BY_COMMAND: dict[GlobalCommandKindV1, str] = {
    GlobalCommandKindV1.SPOT_SWAP: "_apply_spot_swap",
    GlobalCommandKindV1.LP_ADD: "_apply_lp_add",
    GlobalCommandKindV1.LP_REMOVE: "_apply_lp_remove",
    GlobalCommandKindV1.ZUSD_BORROW: "_apply_zusd_borrow",
    GlobalCommandKindV1.ZUSD_REPAY: "_apply_zusd_repay",
    GlobalCommandKindV1.ZUSD_REDEEM: "_apply_zusd_redeem",
    GlobalCommandKindV1.ZUSD_LIQUIDATE: "_apply_zusd_liquidate",
    GlobalCommandKindV1.STABILITY_POOL_DEPOSIT: "_apply_stability_deposit",
    GlobalCommandKindV1.STABILITY_POOL_WITHDRAW: "_apply_stability_withdraw",
    GlobalCommandKindV1.ZUSD_REDISTRIBUTE: "_apply_zusd_redistribute",
    GlobalCommandKindV1.PERP_OPEN: "_apply_perp_open",
    GlobalCommandKindV1.PERP_CLOSE: "_apply_perp_close",
    GlobalCommandKindV1.PERP_FUNDING: "_apply_perp_funding",
    GlobalCommandKindV1.PERP_LIQUIDATE: "_apply_perp_liquidate",
    GlobalCommandKindV1.ORACLE_SUBMIT: "_apply_oracle_submit",
    GlobalCommandKindV1.ORACLE_DISPUTE: "_apply_oracle_dispute",
    GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN: "_apply_protocol_buy_and_burn",
    GlobalCommandKindV1.ZRPF_PROVER_REWARD: "_apply_prover_reward",
    GlobalCommandKindV1.SELLER_AUCTION_COMMIT: "_apply_seller_auction_commit",
    GlobalCommandKindV1.SELLER_AUCTION_REVEAL: "_apply_seller_auction_reveal",
    GlobalCommandKindV1.SELLER_AUCTION_SETTLE: "_apply_seller_auction_settle",
    GlobalCommandKindV1.SELLER_AUCTION_CANCEL: "_apply_seller_auction_cancel",
    GlobalCommandKindV1.SELLER_AUCTION_EXPIRE: "_apply_seller_auction_expire",
    GlobalCommandKindV1.PRIVATE_SWAP_COMMIT: "_apply_private_swap_commit",
    GlobalCommandKindV1.PRIVATE_SWAP_REVEAL: "_apply_private_swap_reveal",
    GlobalCommandKindV1.PRIVATE_SWAP_SETTLE: "_apply_private_swap_settle",
    GlobalCommandKindV1.PRIVATE_SWAP_CANCEL: "_apply_private_swap_cancel",
    GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE: "_apply_private_swap_expire",
    GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: "_apply_tau_escrow_deposit",
    GlobalCommandKindV1.TAU_WITHDRAWAL: "_apply_tau_withdrawal",
    GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: "_apply_tau_withdrawal_ack",
    GlobalCommandKindV1.FALLBACK_ACTIVATE: "_apply_fallback_activate",
    GlobalCommandKindV1.TAU_REJOIN: "_apply_tau_rejoin",
}

_PROFILE_DECISIONS = (
    "asset_issue_burn_policy",
    "spot_lp_fee_dust_withdrawal_policy",
    "zusd_monetary_lifecycle_policy",
    "oracle_lifecycle_policy",
    "perps_risk_and_terminal_policy",
    "protocol_buy_burn_policy",
    "proof_reward_reserve_policy",
    "sealed_bid_inventory_and_lifecycle_policy",
    "tau_escrow_outage_rejoin_policy",
)

_PROFILE_DECISION_REQUIREMENTS: dict[str, tuple[str, ...]] = {
    "asset_issue_burn_policy": (
        "managed asset classes and integer base-unit scales",
        "one issue authority and one burn authority per managed asset",
        "supply bounds, genesis bindings, and terminal supply disposition",
    ),
    "spot_lp_fee_dust_withdrawal_policy": (
        "spot and LP fee rates, rounding direction, and fee beneficiaries",
        "LP share mint and burn arithmetic with reserve reconciliation",
        "dust ownership, withdrawal rules, and final-pool terminal drain",
    ),
    "zusd_monetary_lifecycle_policy": (
        "borrowing and redemption fees with current liability owners",
        "collateral, redemption, liquidation, and redistribution parameters",
        "Stability Pool gain, loss, rounding, recovery, and terminal rules",
    ),
    "oracle_lifecycle_policy": (
        "reporter and dispute authority plus bond disposition",
        "aggregation, occurrence, freshness, and finality semantics",
        "stale, disputed, outage, and recovery behavior by command class",
    ),
    "perps_risk_and_terminal_policy": (
        "market, collateral, margin, fee, and funding definitions",
        "liquidation, insurance, and bad-debt allocation",
        "oracle gating, recovery subset, and terminal close semantics",
    ),
    "protocol_buy_burn_policy": (
        "buyback funding source, route, price guard, budget, and cadence",
        "acquired-token custody, protected supply floor, and burn authority",
        "rounding, failure, recovery, and terminal reserve disposition",
    ),
    "proof_reward_reserve_policy": (
        "reward reserve funding and beneficial owner",
        "eligibility, schedule, cap, claim identity, and nullifier scope",
        "rounding, exhaustion, recovery, and terminal reserve drain",
    ),
    "sealed_bid_inventory_and_lifecycle_policy": (
        "inventory, payment, bond assets, amounts, and custody owners",
        "phase deadlines, cancellation, expiry, and non-reveal disposition",
        "tie order, fees, dust, settlement port, and terminal refunds or slashes",
    ),
    "tau_escrow_outage_rejoin_policy": (
        "deposit evidence, finality, asset mapping, and replay scope",
        "withdrawal queue, acknowledgment, retry, and destination idempotency",
        "outage continuation, pending effects, rejoin proof, and profile rotation",
    ),
}

_PROFILE_DECISION_QUESTIONS: dict[str, str] = {
    "asset_issue_burn_policy": "Which managed assets, units, issue authorities, burn authorities, and supply floors are in scope?",
    "spot_lp_fee_dust_withdrawal_policy": "Which spot and LP fee, rounding, dust, withdrawal, and final-pool rules are selected?",
    "zusd_monetary_lifecycle_policy": "Which zUSD collateral, fee, redemption, liquidation, redistribution, and Stability Pool rules are selected?",
    "oracle_lifecycle_policy": "Which reporter, dispute, aggregation, freshness, outage, and recovery rules are selected?",
    "perps_risk_and_terminal_policy": "Which perps funding, liquidation, insurance, bad-debt, oracle, and terminal-close rules are selected?",
    "protocol_buy_burn_policy": "Which buyback funding, route, price guard, supply floor, burn, and reserve rules are selected?",
    "proof_reward_reserve_policy": "Which proof-reward reserve, eligibility, schedule, claim, nullifier, and exhaustion rules are selected?",
    "sealed_bid_inventory_and_lifecycle_policy": "Which seller-auction and private-swap inventory, phase, fee, cancellation, and terminal rules are selected?",
    "tau_escrow_outage_rejoin_policy": "Which Tau escrow deposit, withdrawal, outage, acknowledgment, retry, and rejoin rules are selected?",
}

_PROFILE_DECISION_FAMILIES: dict[str, tuple[str, ...]] = {
    "asset_issue_burn_policy": (
        "spot_and_liquidity",
        "zusd_monetary",
        "protocol_token",
        "proof_reward",
        "sealed_bid",
        "tau_escrow",
    ),
    "spot_lp_fee_dust_withdrawal_policy": ("spot_and_liquidity",),
    "zusd_monetary_lifecycle_policy": ("zusd_monetary",),
    "oracle_lifecycle_policy": ("oracle", "zusd_monetary", "perps_risk"),
    "perps_risk_and_terminal_policy": ("perps_risk",),
    "protocol_buy_burn_policy": ("protocol_token",),
    "proof_reward_reserve_policy": ("proof_reward",),
    "sealed_bid_inventory_and_lifecycle_policy": ("sealed_bid",),
    "tau_escrow_outage_rejoin_policy": ("tau_escrow",),
}

_PROFILE_OPTION_SHAPES = {
    "EXPLICIT_NAMED_PROFILE": {
        "status": "UNSELECTED_OPTION_SHAPE",
        "meaning": "Select one exact policy with integer units, authority, bounds, effects, and terminal disposition.",
    },
    "VERSIONED_PROFILE_ALTERNATIVE": {
        "status": "UNSELECTED_OPTION_SHAPE",
        "meaning": "Select a versioned alternative with explicit activation, migration, compatibility, and rollback rules.",
    },
    "EXCLUDE_UNTIL_CLOSED": {
        "status": "UNSELECTED_OPTION_SHAPE",
        "meaning": "Keep affected commands unreachable and without a production writer until the decision is closed.",
    },
}

_PROFILE_DECISION_REJECTION_CONDITIONS = (
    "missing integer units, rounding direction, or dust owner",
    "missing authority, claimant, custody, liability, or terminal owner",
    "missing stale, outage, replay, recovery, or migration behavior",
    "no deterministic value-delta equations and independent reconciliation evidence",
)

_DECISIONS_BY_FAMILY: dict[str, tuple[str, ...]] = {
    "spot_and_liquidity": (
        "asset_issue_burn_policy",
        "spot_lp_fee_dust_withdrawal_policy",
    ),
    "zusd_monetary": (
        "asset_issue_burn_policy",
        "zusd_monetary_lifecycle_policy",
        "oracle_lifecycle_policy",
    ),
    "perps_risk": (
        "perps_risk_and_terminal_policy",
        "oracle_lifecycle_policy",
    ),
    "oracle": ("oracle_lifecycle_policy",),
    "protocol_token": (
        "asset_issue_burn_policy",
        "protocol_buy_burn_policy",
    ),
    "proof_reward": (
        "asset_issue_burn_policy",
        "proof_reward_reserve_policy",
    ),
    "sealed_bid": (
        "asset_issue_burn_policy",
        "sealed_bid_inventory_and_lifecycle_policy",
    ),
    "tau_escrow": (
        "asset_issue_burn_policy",
        "tau_escrow_outage_rejoin_policy",
    ),
}

_REQUIRED_BDD_SCENARIO_CLASSES = (
    "happy",
    "rejection",
    "authorization",
    "recovery",
    "terminal",
)


def _run_git(repo_root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _frozen_transition_tree(repo_root: Path) -> ast.Module:
    source = _run_git(repo_root, "show", f"{SOURCE_SUBJECT}:{TRANSITION_PATH}")
    return ast.parse(source, filename=f"{SOURCE_SUBJECT}:{TRANSITION_PATH}")


def _frozen_handler_bindings(repo_root: Path) -> dict[GlobalCommandKindV1, str]:
    tree = _frozen_transition_tree(repo_root)
    for node in tree.body:
        if not isinstance(node, ast.AnnAssign):
            continue
        if not isinstance(node.target, ast.Name) or node.target.id != "_BUSINESS_HANDLERS":
            continue
        if not isinstance(node.value, ast.Call) or not node.value.args:
            break
        mapping = node.value.args[0]
        if not isinstance(mapping, ast.Dict):
            break
        bindings: dict[GlobalCommandKindV1, str] = {}
        for key, value in zip(mapping.keys, mapping.values, strict=True):
            if not isinstance(key, ast.Attribute) or not isinstance(value, ast.Name):
                raise ValueError("unsupported frozen business-handler binding shape")
            try:
                command = GlobalCommandKindV1[key.attr]
            except KeyError as exc:
                raise ValueError(f"unknown frozen handler command: {key.attr}") from exc
            if command in bindings:
                raise ValueError(f"duplicate frozen handler command: {command.value}")
            bindings[command] = value.id
        return bindings
    raise ValueError("frozen _BUSINESS_HANDLERS mapping was not found")


def _frozen_disabled_guard(repo_root: Path) -> frozenset[GlobalCommandKindV1]:
    tree = _frozen_transition_tree(repo_root)
    function = next(
        (
            node
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
            and node.name == "_is_research_disabled_command_v1"
        ),
        None,
    )
    if function is None:
        raise ValueError("frozen disabled-command guard was not found")
    return_node = next((node for node in ast.walk(function) if isinstance(node, ast.Return)), None)
    if return_node is None or not isinstance(return_node.value, ast.Compare):
        raise ValueError("unsupported frozen disabled-command guard shape")
    comparison = return_node.value
    if len(comparison.ops) != 1 or not isinstance(comparison.ops[0], ast.In):
        raise ValueError("frozen disabled-command guard is not a closed membership test")
    if len(comparison.comparators) != 1 or not isinstance(comparison.comparators[0], ast.Tuple):
        raise ValueError("frozen disabled-command guard is not a literal tuple")
    disabled: set[GlobalCommandKindV1] = set()
    for item in comparison.comparators[0].elts:
        if not isinstance(item, ast.Attribute):
            raise ValueError("unsupported frozen disabled-command member shape")
        try:
            disabled.add(GlobalCommandKindV1[item.attr])
        except KeyError as exc:
            raise ValueError(f"unknown frozen disabled command: {item.attr}") from exc
    return frozenset(disabled)


def _validate_frozen_runtime_bindings(repo_root: Path) -> dict[str, Any]:
    handlers = _frozen_handler_bindings(repo_root)
    disabled = _frozen_disabled_guard(repo_root)
    if handlers != _HANDLER_BY_COMMAND:
        raise ValueError("declared core-transition map differs from frozen runtime dispatch")
    if disabled != EXPECTED_DISABLED:
        raise ValueError("source disable registry differs from frozen runtime reject guard")
    return {
        "handler_binding_count": len(handlers),
        "handler_bindings_match_frozen_dispatch": True,
        "disabled_guard_count": len(disabled),
        "disabled_guard_matches_source_registry": True,
    }


def _source_pins(repo_root: Path) -> list[dict[str, str]]:
    pins: list[dict[str, str]] = []
    for path in (SOURCE_PATH, TRANSITION_PATH):
        frozen = _run_git(repo_root, "show", f"{SOURCE_SUBJECT}:{path}").encode()
        current = (repo_root / path).read_bytes()
        if current != frozen:
            raise ValueError(f"source drift from frozen subject: {path}")
        pins.append(
            {
                "path": path,
                "sha256": _sha256_bytes(frozen),
                "subject": SOURCE_SUBJECT,
            }
        )
    return pins


def _command_entries() -> list[dict[str, Any]]:
    if set(_COMMAND_FAMILY) != set(EXPECTED_COMMANDS):
        raise ValueError("command family map does not cover the closed source registry")
    if set(_HANDLER_BY_COMMAND) != set(EXPECTED_COMMANDS):
        raise ValueError("handler map does not cover the closed source registry")
    if set(_DECISIONS_BY_FAMILY) != set(_FAMILY_DEFINITIONS):
        raise ValueError("profile-decision map does not cover every workflow family")
    if set(_PROFILE_DECISIONS) != set(_PROFILE_DECISION_REQUIREMENTS):
        raise ValueError("profile-decision requirements do not cover the closed decision registry")
    if set(_PROFILE_DECISIONS) != set(_PROFILE_DECISION_QUESTIONS):
        raise ValueError("profile-decision questions do not cover the closed decision registry")
    if set(_PROFILE_DECISIONS) != set(_PROFILE_DECISION_FAMILIES):
        raise ValueError("profile-decision family map does not cover the closed decision registry")
    referenced_decisions = {
        decision
        for decisions in _DECISIONS_BY_FAMILY.values()
        for decision in decisions
    }
    if referenced_decisions != set(_PROFILE_DECISIONS):
        raise ValueError("workflow families do not reference the closed decision registry exactly")

    entries: list[dict[str, Any]] = []
    for command in sorted(EXPECTED_COMMANDS, key=lambda item: item.value):
        family_name = _COMMAND_FAMILY[command]
        family = _FAMILY_DEFINITIONS[family_name]
        disabled = command in EXPECTED_DISABLED
        required_scenarios = list(_REQUIRED_BDD_SCENARIO_CLASSES)
        if family_name == "sealed_bid":
            required_scenarios.append("cancellation")
        entries.append(
            {
                "id": command.value,
                "enum_member": command.name,
                "v1_profile": "M6_RESEARCH_DISABLED_COMMANDS_V1"
                if disabled
                else "M6_RESEARCH_ENABLED_COMMANDS_V1",
                "production_enablement": "RESEARCH_DISABLED_NO_PRODUCTION_WRITER"
                if disabled
                else "RESEARCH_ENABLED_PROFILE_REQUIRED",
                "semantic_status": "GAP_OPEN_PROFILE_DECISION",
                "actor": family["actor"],
                "economic_owner": family["economic_owner"],
                "economic_owner_status": "IMPLEMENTATION_MODULE_ONLY_BENEFICIAL_OWNER_UNSELECTED",
                "beneficial_owner": None,
                "user_story": None,
                "user_story_status": "GAP_PRODUCT_STORY_NOT_FROZEN",
                "source_registry": f"{SOURCE_PATH}:GlobalCommandKindV1.{command.name}",
                "normative_spec": None,
                "normative_spec_status": "GAP_PROFILE_NOT_SELECTED",
                "core_transition": f"{TRANSITION_PATH}:{_HANDLER_BY_COMMAND[command]}",
                "core_transition_status": "SOURCE_PRESENT_RUNTIME_REJECTED"
                if disabled
                else "RESEARCH_SOURCE_PRESENT_NOT_PRODUCTION_SPECIFIED",
                "terminal_path": family["terminal_path"],
                "terminal_path_status": "DECLARED_FAMILY_LABEL_NOT_CLOSED_SEMANTICS",
                "formal_obligation_ids": list(family["formal_obligation_ids"]),
                "formal_obligation_status": "DECLARED_NOT_PROVED_OR_COMPOSITION_CHECKED",
                "runtime_projection": "G1_GLOBAL_ECONOMIC_STATE_PROJECTION_ONLY",
                "runtime_projection_status": "DECLARED_NOT_IMPLEMENTED_OR_REFINED",
                "mounted_entrypoint": "UNMOUNTED_RESEARCH_ONLY",
                "mounted_entrypoint_status": "UNMOUNTED",
                "workflow_family": family_name,
                "blocking_profile_decision_ids": list(_DECISIONS_BY_FAMILY[family_name]),
                "bdd_required_scenario_classes": required_scenarios,
                "bdd_additional_scenario_classes": list(family["scenario_classes"]),
                "bdd_executable_scenarios": [],
                "bdd_status": "GAP_NO_EXACT_SUBJECT_EXECUTABLE_SCENARIOS",
            }
        )
    return entries


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    source_pins = _source_pins(repo_root)
    runtime_bindings = _validate_frozen_runtime_bindings(repo_root)
    commands = _command_entries()
    command_ids = {entry["id"] for entry in commands}
    if set(_STATE_FIELD_CONTRACTS) != set(EXPECTED_STATE_FIELDS):
        raise ValueError("state field contracts do not cover the declared projection")
    if set(_DELTA_CLASS_CONTRACTS) != set(EXPECTED_DELTA_CLASSES):
        raise ValueError("delta class contracts do not cover the declared algebra")
    if command_ids.intersection(EXPECTED_EXCLUDED_COMMANDS):
        raise ValueError("excluded launch command is present in the closed registry")
    blocking_decisions = list(_PROFILE_DECISIONS)
    return {
        "schema": SCHEMA,
        "version": "v1",
        "status": "G1_SEMANTIC_MAPPING_RESEARCH_ONLY",
        "production_promotion": False,
        "source_subject": {
            "base_commit": SOURCE_SUBJECT,
            "current_head_must_descend_from_base": True,
            "source_authority": "frozen source bytes at the exact base commit",
        },
        "source_pins": source_pins,
        "source_observations": {
            "command_count": len(EXPECTED_COMMANDS),
            "disabled_command_count": len(EXPECTED_DISABLED),
            "received_plan_disabled_command_count": 10,
            "excluded_command_ids": list(EXPECTED_EXCLUDED_COMMANDS),
            "reconciliation": "EXACT_SOURCE_PARTITION_RECORDED_RECEIVED_COUNT_RETAINED_AS_NONAUTHORITATIVE",
            "source_authority": "GlobalCommandKindV1 and M6_RESEARCH_DISABLED_COMMANDS_V1 at the frozen subject",
            **runtime_bindings,
        },
        "launch_profile_exclusions": {
            "status": "EXPLICITLY_UNSELECTED_RESEARCH_EXCLUSION",
            "command_ids": list(EXPECTED_EXCLUDED_COMMANDS),
            "registry_absent": True,
            "production_authority": "NONE",
            "reentry_requires_new_profile_decision": True,
        },
        "command_registry": commands,
        "global_state_projection": {
            "schema": "M6GlobalEconomicStateProjectionV1",
            "status": "DECLARED_RESEARCH_PROJECTION",
            "closure_status": "GAP_FIELD_TYPES_ROOT_CODEC_AND_RECONCILIATION_UNSPECIFIED",
            "authority": "ZenoLedger_candidate_state_before_publication",
            "canonical_order": list(EXPECTED_STATE_FIELDS),
            "field_contracts": [
                {
                    "name": field,
                    **_STATE_FIELD_CONTRACTS[field],
                }
                for field in EXPECTED_STATE_FIELDS
            ],
            "fields": [
                {
                    "name": field,
                    "type": "canonical_integer_or_owned_record",
                    "value_moving": True,
                    "terminal_path_required": True,
                }
                for field in EXPECTED_STATE_FIELDS
            ],
            "no_production_authority": True,
        },
        "value_delta_algebra": {
            "status": "DECLARED_RESEARCH_ALGEBRA",
            "closure_status": "GAP_EVENT_EQUATIONS_OWNERS_AND_RECONCILIATION_UNSPECIFIED",
            "entry_key": ["asset", "owner", "custody", "economic_event"],
            "amount_representation": "nonnegative_integer_base_units",
            "delta_classes": list(EXPECTED_DELTA_CLASSES),
            "class_contracts": [
                {
                    "class": delta_class,
                    **_DELTA_CLASS_CONTRACTS[delta_class],
                }
                for delta_class in EXPECTED_DELTA_CLASSES
            ],
            "laws": [
                "internal_transfer_preserves_asset_supply",
                "issue_and_burn_require_explicit_authority_and_supply_delta",
                "liability_delta_names_both_owner_and_asset",
                "reserve_transfer_preserves_supply_and_names_both_allocations",
                "fee_allocation_binds_source_beneficiary_and_policy",
                "reward_binds_reserve_recipient_and_policy",
                "external_outflow_requires_ancestor_custody_or_claim",
                "rounding_and_dust_are_assigned_to_an_owner_or_rejected",
            ],
            "no_production_authority": True,
        },
        "profile_decisions": [
            {
                "id": decision,
                "status": "OPEN",
                "owner": "G1_product_semantics_decision",
                "question": _PROFILE_DECISION_QUESTIONS[decision],
                "affected_workflow_families": list(_PROFILE_DECISION_FAMILIES[decision]),
                "allowed_option_shapes": list(_PROFILE_OPTION_SHAPES),
                "rejection_conditions": list(_PROFILE_DECISION_REJECTION_CONDITIONS),
                "required_before_g1_exit": True,
                "required_outputs": list(_PROFILE_DECISION_REQUIREMENTS[decision]),
                "selected_profile": None,
                "production_authority": "NONE",
            }
            for decision in blocking_decisions
        ],
        "profile_option_shapes": _PROFILE_OPTION_SHAPES,
        "bdd_contract": {
            "status": "BLOCKED_NO_EXACT_SUBJECT_EXECUTABLE_SCENARIOS",
            "command_count": len(commands),
            "required_for_every_command": list(_REQUIRED_BDD_SCENARIO_CLASSES),
            "cancellation_required_for_workflow_families": ["sealed_bid"],
            "executable_scenario_count": 0,
            "nonclaim": "Scenario-class labels are coverage requirements, not executable BDD evidence.",
        },
        "g1_exit_gate": {
            "complete": False,
            "status": "BLOCKED_OPEN_PROFILE_DECISIONS",
            "blocking_decisions": blocking_decisions,
            "closed_command_count": 0,
            "commands_with_semantic_gap": len(commands),
            "claim": "No command has a complete production semantic contract.",
        },
        "nonclaims": [
            "This registry does not prove an economic invariant.",
            "This registry does not mount a runtime entrypoint or authorize settlement.",
            "The source disable-count reconciliation does not select a production profile.",
            "The global projection and delta algebra are research declarations until independently checked.",
            "Handler reachability establishes only frozen V1 dispatch, not production semantic correctness.",
            "BDD class labels do not constitute executable scenarios or independent oracles.",
        ],
    }


def _load(path: Path) -> dict[str, Any]:
    duplicates: list[str] = []

    def hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                duplicates.append(key)
            result[key] = value
        return result

    with path.open(encoding="utf-8") as stream:
        value = json.load(stream, object_pairs_hook=hook)
    if duplicates:
        raise ValueError(f"duplicate JSON keys: {sorted(set(duplicates))}")
    if not isinstance(value, dict):
        raise ValueError("artifact root must be an object")
    return value


def _encoded(value: Mapping[str, Any]) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _write_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
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
        ["git", "merge-base", "--is-ancestor", SOURCE_SUBJECT, "HEAD"],
        cwd=repo_root,
        check=False,
    )
    if ancestry.returncode != 0:
        errors.append("current HEAD does not descend from the frozen source subject")

    try:
        expected = build_document(repo_root)
        observed = _load(path)
        if observed != expected:
            errors.append("artifact differs from the exact-subject generated semantic mapping")
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        errors.append(str(exc))

    command_registry = observed.get("command_registry")
    command_count = len(command_registry) if isinstance(command_registry, list) else 0
    disabled_count = (
        sum(
            1
            for entry in command_registry
            if isinstance(entry, dict)
            and entry.get("production_enablement") == "RESEARCH_DISABLED_NO_PRODUCTION_WRITER"
        )
        if isinstance(command_registry, list)
        else 0
    )
    semantic_gap_count = (
        sum(
            1
            for entry in command_registry
            if isinstance(entry, dict)
            and entry.get("semantic_status") == "GAP_OPEN_PROFILE_DECISION"
        )
        if isinstance(command_registry, list)
        else 0
    )
    return {
        "schema": "zenodex/production-readiness-g1-semantics-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "command_count": command_count,
        "disabled_command_count": disabled_count,
        "semantic_gap_count": semantic_gap_count,
        "executable_bdd_scenario_count": 0,
        "profile_decision_count": len(_PROFILE_DECISIONS),
        "errors": errors,
        "nonclaim": "PASS means only that the research mapping is exact and source-bound; it does not promote G1 or production readiness.",
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
    else:
        print("PASS" if report["ok"] else "FAIL")
        if report["errors"]:
            for error in report["errors"]:
                print(f"error: {error}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
