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
    "external_in",
    "external_out",
    "refund",
    "slash",
)

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

    entries: list[dict[str, Any]] = []
    for command in sorted(EXPECTED_COMMANDS, key=lambda item: item.value):
        family_name = _COMMAND_FAMILY[command]
        family = _FAMILY_DEFINITIONS[family_name]
        disabled = command in EXPECTED_DISABLED
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
                "semantic_status": "MAPPED_RESEARCH_ONLY",
                "actor": family["actor"],
                "economic_owner": family["economic_owner"],
                "user_story": f"{command.value} has an explicit G1 semantic owner and terminal path.",
                "normative_spec": f"{SOURCE_PATH}:GlobalCommandKindV1.{command.name}",
                "core_transition": f"{TRANSITION_PATH}:{_HANDLER_BY_COMMAND[command]}",
                "terminal_path": family["terminal_path"],
                "formal_obligation_ids": list(family["formal_obligation_ids"]),
                "runtime_projection": "G1_GLOBAL_ECONOMIC_STATE_PROJECTION_ONLY",
                "mounted_entrypoint": "UNMOUNTED_RESEARCH_ONLY",
                "workflow_family": family_name,
                "bdd_scenario_classes": list(family["scenario_classes"]),
            }
        )
    return entries


def build_document(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    source_pins = _source_pins(repo_root)
    commands = _command_entries()
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
            "reconciliation": "EXACT_SOURCE_PARTITION_RECORDED_RECEIVED_COUNT_RETAINED_AS_NONAUTHORITATIVE",
            "source_authority": "GlobalCommandKindV1 and M6_RESEARCH_DISABLED_COMMANDS_V1 at the frozen subject",
        },
        "command_registry": commands,
        "global_state_projection": {
            "schema": "M6GlobalEconomicStateProjectionV1",
            "status": "DECLARED_RESEARCH_PROJECTION",
            "authority": "ZenoLedger_candidate_state_before_publication",
            "canonical_order": list(EXPECTED_STATE_FIELDS),
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
            "entry_key": ["asset", "owner", "custody", "economic_event"],
            "amount_representation": "nonnegative_integer_base_units",
            "delta_classes": list(EXPECTED_DELTA_CLASSES),
            "laws": [
                "internal_transfer_preserves_asset_supply",
                "issue_and_burn_require_explicit_authority_and_supply_delta",
                "liability_delta_names_both_owner_and_asset",
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
                "required_before_g1_exit": True,
                "production_authority": "NONE",
            }
            for decision in blocking_decisions
        ],
        "g1_exit_gate": {
            "complete": False,
            "status": "BLOCKED_OPEN_PROFILE_DECISIONS",
            "blocking_decisions": blocking_decisions,
            "claim": "No enabled command has a complete production semantic contract.",
        },
        "nonclaims": [
            "This registry does not prove an economic invariant.",
            "This registry does not mount a runtime entrypoint or authorize settlement.",
            "The source disable-count reconciliation does not select a production profile.",
            "The global projection and delta algebra are research declarations until independently checked.",
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
    return {
        "schema": "zenodex/production-readiness-g1-semantics-check/v1",
        "ok": not errors,
        "g1_complete": False,
        "production_ready": False,
        "command_count": command_count,
        "disabled_command_count": disabled_count,
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
