#!/usr/bin/env python3
"""Check a production-candidate live ZenoOracle reporter economics policy."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(1, str(TOOLS))

from zenodex_oracle_reporter_economics_replay import (  # noqa: E402
    sample_replay,
    verify_reporter_economics_replay,
)

POLICY_SCHEMA = "zenodex.oracle.live_economics_policy.v1"
REPORT_SCHEMA = "zenodex.oracle.live_economics_policy_check.v1"
RECEIPT_BUNDLE_SCHEMA = "zenodex.oracle.live_economics_receipt_bundle.v1"
RECEIPT_SCHEMA = "zenodex.oracle.live_economics_receipt.v1"
BPS_DENOM = 10_000
ADDRESS_RE = re.compile(r"^0x[0-9a-fA-F]{40}$")
TX_RE = re.compile(r"^0x[0-9a-fA-F]{64}$")
SHA_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_escrow_funded_onchain",
    "does_not_claim_onchain_settlement_executed",
    "does_not_claim_governance_vote_executed",
    "does_not_claim_reporter_honesty",
    "does_not_claim_market_price_truth",
}
GO_LIVE_BLOCKERS = [
    "onchain_receipts_not_replayed_against_live_chain_state",
    "escrow_funding_receipt_not_verified_onchain",
    "governance_execution_not_verified_onchain",
    "settlement_execution_receipt_not_verified_onchain",
    "settlement_contract_deployment_not_verified_by_this_checker",
    "public_reporting_soak_not_completed",
]
TOP_LEVEL_KEYS = {
    "schema",
    "policy_id",
    "policy_name",
    "settlement_mode",
    "settlement_asset",
    "token_contract",
    "escrow_contract",
    "governance_contract",
    "governance",
    "governance_approval_receipt",
    "governance_execution_receipt",
    "escrow_funding_receipt",
    "settlement_execution_receipt",
    "live_token_settlement_enabled",
    "required_reporter_bond_e8",
    "max_report_reward_e8",
    "min_dispute_bond_e8",
    "max_slash_bps",
    "withdrawal_delay_epochs",
    "fee_split_bps",
    "settlement_receipt_required",
    "not_claimed",
}
GOVERNANCE_KEYS = {
    "timelock_seconds",
    "dispute_window_epochs",
    "slash_delay_epochs",
    "emergency_pause_role",
}
FEE_SPLIT_KEYS = {"reporter_reward", "treasury", "burn"}
RECEIPT_BUNDLE_KEYS = {
    "schema",
    "policy_id",
    "policy_name",
    "chain_id",
    "observed_block_number",
    "observed_block_hash",
    "receipts",
    "not_claimed",
}
RECEIPT_KEYS = {
    "schema",
    "receipt_id",
    "kind",
    "chain_id",
    "contract_address",
    "tx_hash",
    "block_number",
    "block_hash",
    "log_index",
    "payload",
}
REQUIRED_RECEIPT_KINDS = {"governance_approval", "governance_execution", "escrow_funding", "settlement_execution"}
RECEIPT_NOT_CLAIMS = {
    "does_not_claim_receipts_verified_against_live_rpc",
    "does_not_claim_contract_code_verified_onchain",
}


def _canonical_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def policy_content_hash(policy: Mapping[str, Any]) -> str:
    payload = dict(policy)
    payload.pop("policy_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def policy_static_hash(policy: Mapping[str, Any]) -> str:
    payload = dict(policy)
    for key in (
        "policy_id",
        "governance_approval_receipt",
        "governance_execution_receipt",
        "escrow_funding_receipt",
        "settlement_execution_receipt",
        "not_claimed",
    ):
        payload.pop(key, None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def receipt_content_hash(receipt: Mapping[str, Any]) -> str:
    payload = dict(receipt)
    payload.pop("receipt_id", None)
    return "sha256:" + hashlib.sha256(_canonical_bytes(payload)).hexdigest()


def _sha(label: str) -> str:
    return "sha256:" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _tx(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("utf-8")).hexdigest()


def _is_address(value: Any) -> bool:
    return isinstance(value, str) and ADDRESS_RE.fullmatch(value) is not None


def _is_sha(value: Any) -> bool:
    return isinstance(value, str) and SHA_RE.fullmatch(value) is not None


def _is_tx(value: Any) -> bool:
    return isinstance(value, str) and TX_RE.fullmatch(value) is not None


def _int_field(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int,
    maximum: int | None = None,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        errors.append(f"{key}_must_be_int")
        return None
    if value < minimum:
        errors.append(f"{key}_below_min:{minimum}")
    if maximum is not None and value > maximum:
        errors.append(f"{key}_above_max:{maximum}")
    return int(value)


def _obj_field(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any]:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return {}
    return value


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj:
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _bool_true(obj: Mapping[str, Any], key: str, errors: list[str]) -> None:
    value = obj.get(key)
    if not isinstance(value, bool):
        errors.append(f"{key}_must_be_bool")
    elif value is not True:
        errors.append(f"{key}_must_be_true")


def _events_by_type(replay: Mapping[str, Any], event_type: str) -> list[Mapping[str, Any]]:
    raw = replay.get("events")
    if not isinstance(raw, list):
        return []
    return [event for event in raw if isinstance(event, Mapping) and event.get("type") == event_type]


def minimum_escrow_floor_e8(replay: Mapping[str, Any]) -> int:
    floor = 0
    initial_dispute_pool = replay.get("initial_dispute_reward_pool_e8")
    if isinstance(initial_dispute_pool, int) and not isinstance(initial_dispute_pool, bool):
        floor += max(0, int(initial_dispute_pool))
    for event in replay.get("events", []) if isinstance(replay.get("events"), list) else []:
        if not isinstance(event, Mapping):
            continue
        if event.get("type") == "deposit_bond":
            amount = event.get("amount_e8")
            if isinstance(amount, int) and not isinstance(amount, bool):
                floor += max(0, int(amount))
        if event.get("type") == "fee_split":
            fee_paid = event.get("fee_paid_e8")
            if isinstance(fee_paid, int) and not isinstance(fee_paid, bool):
                floor += max(0, int(fee_paid))
    return floor


def settlement_execution_totals(replay: Mapping[str, Any]) -> dict[str, int]:
    totals = {
        "report_reward_paid_e8": 0,
        "dispute_reward_paid_e8": 0,
        "bond_withdrawn_e8": 0,
        "slashed_e8": 0,
        "fee_paid_e8": 0,
        "treasury_delta_e8": 0,
        "burn_delta_e8": 0,
    }
    for event in replay.get("events", []) if isinstance(replay.get("events"), list) else []:
        if not isinstance(event, Mapping):
            continue
        event_type = event.get("type")
        if event_type == "submit_report":
            reward = event.get("reward_e8")
            if isinstance(reward, int) and not isinstance(reward, bool):
                totals["report_reward_paid_e8"] += max(0, int(reward))
        elif event_type == "pay_dispute_reward":
            amount = event.get("amount_e8")
            if isinstance(amount, int) and not isinstance(amount, bool):
                totals["dispute_reward_paid_e8"] += max(0, int(amount))
        elif event_type == "withdraw_bond":
            amount = event.get("amount_e8")
            if isinstance(amount, int) and not isinstance(amount, bool):
                totals["bond_withdrawn_e8"] += max(0, int(amount))
        elif event_type == "slash_reporter":
            amount = event.get("amount_e8")
            if isinstance(amount, int) and not isinstance(amount, bool):
                totals["slashed_e8"] += max(0, int(amount))
        elif event_type == "fee_split":
            for key in ("fee_paid_e8", "treasury_delta_e8", "burn_delta_e8"):
                amount = event.get(key)
                if isinstance(amount, int) and not isinstance(amount, bool):
                    totals[key] += max(0, int(amount))
    return totals


def _receipt(
    *,
    kind: str,
    chain_id: str,
    contract_address: str,
    tx_hash: str,
    block_number: int,
    block_hash: str,
    log_index: int,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "kind": kind,
        "chain_id": chain_id,
        "contract_address": contract_address,
        "tx_hash": tx_hash,
        "block_number": int(block_number),
        "block_hash": block_hash,
        "log_index": int(log_index),
        "payload": dict(payload),
    }
    receipt["receipt_id"] = receipt_content_hash(receipt)
    return receipt


def _sample_receipts_for_policy(policy: Mapping[str, Any], replay: Mapping[str, Any]) -> list[dict[str, Any]]:
    chain_id = "zenodex.oracle.mainnet-candidate-1"
    static_hash = policy_static_hash(policy)
    proposal_id = _sha(f"zenodex.oracle.live_economics.proposal.{static_hash}")
    queued_at = 1_800_000_000
    governance = policy.get("governance") if isinstance(policy.get("governance"), Mapping) else {}
    timelock_seconds = int(governance.get("timelock_seconds", 172_800))
    executable_after = queued_at + timelock_seconds
    executed_at = executable_after
    required_floor = minimum_escrow_floor_e8(replay)
    settlement_totals = settlement_execution_totals(replay)
    return [
        _receipt(
            kind="governance_approval",
            chain_id=chain_id,
            contract_address=str(policy.get("governance_contract")),
            tx_hash=_tx("zenodex.oracle.live_economics.governance_approval"),
            block_number=1_000,
            block_hash=_sha("zenodex.oracle.live_economics.block.1000"),
            log_index=0,
            payload={
                "approved": True,
                "executable_after_timestamp": executable_after,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "proposal_id": proposal_id,
                "queued_at_timestamp": queued_at,
                "timelock_seconds": timelock_seconds,
            },
        ),
        _receipt(
            kind="governance_execution",
            chain_id=chain_id,
            contract_address=str(policy.get("governance_contract")),
            tx_hash=_tx("zenodex.oracle.live_economics.governance_execution"),
            block_number=1_100,
            block_hash=_sha("zenodex.oracle.live_economics.block.1100"),
            log_index=0,
            payload={
                "executed": True,
                "executed_at_timestamp": executed_at,
                "executable_after_timestamp": executable_after,
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "proposal_id": proposal_id,
            },
        ),
        _receipt(
            kind="escrow_funding",
            chain_id=chain_id,
            contract_address=str(policy.get("escrow_contract")),
            tx_hash=_tx("zenodex.oracle.live_economics.escrow_funding"),
            block_number=1_200,
            block_hash=_sha("zenodex.oracle.live_economics.block.1200"),
            log_index=0,
            payload={
                "balance_e8": required_floor,
                "escrow_contract": str(policy.get("escrow_contract")),
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "required_escrow_floor_e8": required_floor,
                "token_contract": str(policy.get("token_contract")),
            },
        ),
        _receipt(
            kind="settlement_execution",
            chain_id=chain_id,
            contract_address=str(policy.get("escrow_contract")),
            tx_hash=_tx("zenodex.oracle.live_economics.settlement_execution"),
            block_number=1_300,
            block_hash=_sha("zenodex.oracle.live_economics.block.1300"),
            log_index=0,
            payload={
                "bond_withdrawn_e8": settlement_totals["bond_withdrawn_e8"],
                "burn_delta_e8": settlement_totals["burn_delta_e8"],
                "dispute_reward_paid_e8": settlement_totals["dispute_reward_paid_e8"],
                "escrow_contract": str(policy.get("escrow_contract")),
                "executed": True,
                "fee_paid_e8": settlement_totals["fee_paid_e8"],
                "policy_name": str(policy.get("policy_name")),
                "policy_static_hash": static_hash,
                "query_id": replay.get("query_id"),
                "report_reward_paid_e8": settlement_totals["report_reward_paid_e8"],
                "settlement_asset": policy.get("settlement_asset"),
                "slashed_e8": settlement_totals["slashed_e8"],
                "token_contract": str(policy.get("token_contract")),
                "treasury_delta_e8": settlement_totals["treasury_delta_e8"],
            },
        ),
    ]


def _sample_receipt_refs(policy: Mapping[str, Any], replay: Mapping[str, Any]) -> dict[str, str]:
    receipts = _sample_receipts_for_policy(policy, replay)
    by_kind = {str(receipt["kind"]): str(receipt["receipt_id"]) for receipt in receipts}
    return {
        "governance_approval_receipt": by_kind["governance_approval"],
        "governance_execution_receipt": by_kind["governance_execution"],
        "escrow_funding_receipt": by_kind["escrow_funding"],
        "settlement_execution_receipt": by_kind["settlement_execution"],
    }


def sample_receipt_bundle(
    policy: Mapping[str, Any] | None = None,
    replay: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if policy is None:
        policy = sample_policy()
    if replay is None:
        replay = sample_replay()
    receipts = _sample_receipts_for_policy(policy, replay)
    return {
        "schema": RECEIPT_BUNDLE_SCHEMA,
        "policy_id": policy.get("policy_id"),
        "policy_name": policy.get("policy_name"),
        "chain_id": "zenodex.oracle.mainnet-candidate-1",
        "observed_block_number": 1_300,
        "observed_block_hash": _sha("zenodex.oracle.live_economics.block.1300"),
        "receipts": receipts,
        "not_claimed": sorted(RECEIPT_NOT_CLAIMS),
    }


def sample_policy() -> dict[str, Any]:
    replay = sample_replay()
    policy: dict[str, Any] = {
        "schema": POLICY_SCHEMA,
        "policy_name": "zeno-oracle-live-economics-production-candidate-1",
        "settlement_mode": "production-candidate",
        "settlement_asset": "ZENO",
        "token_contract": "0x2222222222222222222222222222222222222222",
        "escrow_contract": "0x3333333333333333333333333333333333333333",
        "governance_contract": "0x4444444444444444444444444444444444444444",
        "governance": {
            "timelock_seconds": 172_800,
            "dispute_window_epochs": 32,
            "slash_delay_epochs": 2,
            "emergency_pause_role": "oracle-economics-guardian-1",
        },
        "live_token_settlement_enabled": True,
        "required_reporter_bond_e8": 250_000_000_000,
        "max_report_reward_e8": 30_000_000,
        "min_dispute_bond_e8": 10_000_000,
        "max_slash_bps": 5_000,
        "withdrawal_delay_epochs": 2,
        "fee_split_bps": {
            "reporter_reward": 9_000,
            "treasury": 700,
            "burn": 300,
        },
        "settlement_receipt_required": True,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }
    policy.update(_sample_receipt_refs(policy, replay))
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def check_receipt_bundle(
    policy: Mapping[str, Any],
    replay: Mapping[str, Any],
    receipt_bundle: Mapping[str, Any] | None,
) -> dict[str, Any]:
    errors: list[str] = []
    if receipt_bundle is None:
        return {
            "schema": RECEIPT_BUNDLE_SCHEMA,
            "ok": False,
            "status": "rejected",
            "error_count": 1,
            "errors": ["receipt_bundle_required"],
            "required_escrow_floor_e8": minimum_escrow_floor_e8(replay),
        }

    _unknown_fields(receipt_bundle, allowed=RECEIPT_BUNDLE_KEYS, label="receipt_bundle", errors=errors)
    if receipt_bundle.get("schema") != RECEIPT_BUNDLE_SCHEMA:
        errors.append("receipt_bundle_schema_mismatch")
    if receipt_bundle.get("policy_id") != policy.get("policy_id"):
        errors.append("receipt_bundle_policy_id_mismatch")
    if receipt_bundle.get("policy_name") != policy.get("policy_name"):
        errors.append("receipt_bundle_policy_name_mismatch")
    chain_id = receipt_bundle.get("chain_id")
    if not isinstance(chain_id, str) or not chain_id.strip():
        errors.append("receipt_bundle_chain_id_required")
    observed_block_number = receipt_bundle.get("observed_block_number")
    if not isinstance(observed_block_number, int) or isinstance(observed_block_number, bool) or observed_block_number <= 0:
        errors.append("observed_block_number_must_be_positive_int")
        observed_block_number = 0
    if not _is_sha(receipt_bundle.get("observed_block_hash")):
        errors.append("observed_block_hash_must_be_sha256")

    not_claimed = receipt_bundle.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("receipt_bundle_not_claimed_must_be_list")
    else:
        values = {str(item) for item in not_claimed if isinstance(item, str)}
        errors.extend(f"missing_receipt_not_claim:{item}" for item in sorted(RECEIPT_NOT_CLAIMS - values))

    raw_receipts = receipt_bundle.get("receipts")
    if not isinstance(raw_receipts, list):
        errors.append("receipts_must_be_list")
        raw_receipts = []

    by_kind: dict[str, Mapping[str, Any]] = {}
    static_hash = policy_static_hash(policy)
    expected_contract_by_kind = {
        "governance_approval": policy.get("governance_contract"),
        "governance_execution": policy.get("governance_contract"),
        "escrow_funding": policy.get("escrow_contract"),
        "settlement_execution": policy.get("escrow_contract"),
    }
    expected_receipt_id_by_kind = {
        "governance_approval": policy.get("governance_approval_receipt"),
        "governance_execution": policy.get("governance_execution_receipt"),
        "escrow_funding": policy.get("escrow_funding_receipt"),
        "settlement_execution": policy.get("settlement_execution_receipt"),
    }

    for idx, receipt in enumerate(raw_receipts):
        if not isinstance(receipt, Mapping):
            errors.append(f"receipt_{idx}_must_be_object")
            continue
        _unknown_fields(receipt, allowed=RECEIPT_KEYS, label=f"receipt_{idx}", errors=errors)
        if receipt.get("schema") != RECEIPT_SCHEMA:
            errors.append(f"receipt_{idx}_schema_mismatch")
        kind = receipt.get("kind")
        if not isinstance(kind, str) or kind not in REQUIRED_RECEIPT_KINDS:
            errors.append(f"receipt_{idx}_kind_invalid")
            continue
        if kind in by_kind:
            errors.append(f"duplicate_receipt_kind:{kind}")
        else:
            by_kind[kind] = receipt
        if receipt.get("receipt_id") != receipt_content_hash(receipt):
            errors.append(f"receipt_id_mismatch:{kind}")
        if receipt.get("receipt_id") != expected_receipt_id_by_kind.get(kind):
            errors.append(f"policy_receipt_id_mismatch:{kind}")
        if receipt.get("chain_id") != chain_id:
            errors.append(f"receipt_chain_id_mismatch:{kind}")
        if receipt.get("contract_address") != expected_contract_by_kind.get(kind):
            errors.append(f"receipt_contract_mismatch:{kind}")
        if not _is_tx(receipt.get("tx_hash")):
            errors.append(f"receipt_tx_hash_invalid:{kind}")
        if not _is_sha(receipt.get("block_hash")):
            errors.append(f"receipt_block_hash_invalid:{kind}")
        block_number = receipt.get("block_number")
        if not isinstance(block_number, int) or isinstance(block_number, bool) or block_number <= 0:
            errors.append(f"receipt_block_number_invalid:{kind}")
        elif isinstance(observed_block_number, int) and observed_block_number > 0 and block_number > observed_block_number:
            errors.append(f"receipt_after_observed_block:{kind}")
        log_index = receipt.get("log_index")
        if not isinstance(log_index, int) or isinstance(log_index, bool) or log_index < 0:
            errors.append(f"receipt_log_index_invalid:{kind}")
        payload = receipt.get("payload")
        if not isinstance(payload, Mapping):
            errors.append(f"receipt_payload_must_be_object:{kind}")
            continue
        if payload.get("policy_name") != policy.get("policy_name"):
            errors.append(f"receipt_policy_name_mismatch:{kind}")
        if payload.get("policy_static_hash") != static_hash:
            errors.append(f"receipt_policy_static_hash_mismatch:{kind}")

    for kind in sorted(REQUIRED_RECEIPT_KINDS - set(by_kind)):
        errors.append(f"missing_receipt_kind:{kind}")

    approval = by_kind.get("governance_approval")
    execution = by_kind.get("governance_execution")
    funding = by_kind.get("escrow_funding")
    settlement = by_kind.get("settlement_execution")
    approval_payload = approval.get("payload") if isinstance(approval, Mapping) and isinstance(approval.get("payload"), Mapping) else {}
    execution_payload = execution.get("payload") if isinstance(execution, Mapping) and isinstance(execution.get("payload"), Mapping) else {}
    funding_payload = funding.get("payload") if isinstance(funding, Mapping) and isinstance(funding.get("payload"), Mapping) else {}
    settlement_payload = (
        settlement.get("payload") if isinstance(settlement, Mapping) and isinstance(settlement.get("payload"), Mapping) else {}
    )

    def _receipt_position(kind: str) -> tuple[int, int] | None:
        receipt = by_kind.get(kind)
        if receipt is None:
            return None
        block_number = receipt.get("block_number")
        log_index = receipt.get("log_index")
        if (
            isinstance(block_number, int)
            and not isinstance(block_number, bool)
            and isinstance(log_index, int)
            and not isinstance(log_index, bool)
        ):
            return (block_number, log_index)
        return None

    def _require_receipt_order(before: str, after: str) -> None:
        before_pos = _receipt_position(before)
        after_pos = _receipt_position(after)
        if before_pos is not None and after_pos is not None and before_pos >= after_pos:
            errors.append(f"receipt_order_invalid:{before}->{after}")

    for before, after in (
        ("governance_approval", "governance_execution"),
        ("governance_execution", "escrow_funding"),
        ("escrow_funding", "settlement_execution"),
    ):
        _require_receipt_order(before, after)

    governance = policy.get("governance") if isinstance(policy.get("governance"), Mapping) else {}
    timelock_seconds = governance.get("timelock_seconds")
    if approval_payload:
        if approval_payload.get("approved") is not True:
            errors.append("governance_approval_not_true")
        if approval_payload.get("timelock_seconds") != timelock_seconds:
            errors.append("governance_approval_timelock_mismatch")
        queued_at = approval_payload.get("queued_at_timestamp")
        executable_after = approval_payload.get("executable_after_timestamp")
        if (
            isinstance(queued_at, int)
            and not isinstance(queued_at, bool)
            and isinstance(executable_after, int)
            and not isinstance(executable_after, bool)
            and isinstance(timelock_seconds, int)
            and not isinstance(timelock_seconds, bool)
        ):
            if executable_after - queued_at < timelock_seconds:
                errors.append("governance_timelock_not_satisfied")
        else:
            errors.append("governance_approval_timestamps_invalid")
    if execution_payload:
        if execution_payload.get("executed") is not True:
            errors.append("governance_execution_not_true")
        if execution_payload.get("proposal_id") != approval_payload.get("proposal_id"):
            errors.append("governance_execution_proposal_mismatch")
        executed_at = execution_payload.get("executed_at_timestamp")
        executable_after = approval_payload.get("executable_after_timestamp")
        if (
            isinstance(executed_at, int)
            and not isinstance(executed_at, bool)
            and isinstance(executable_after, int)
            and not isinstance(executable_after, bool)
        ):
            if executed_at < executable_after:
                errors.append("governance_execution_before_timelock")
        else:
            errors.append("governance_execution_timestamp_invalid")

    required_floor = minimum_escrow_floor_e8(replay)
    if funding_payload:
        if funding_payload.get("token_contract") != policy.get("token_contract"):
            errors.append("escrow_funding_token_contract_mismatch")
        if funding_payload.get("escrow_contract") != policy.get("escrow_contract"):
            errors.append("escrow_funding_contract_mismatch")
        if funding_payload.get("required_escrow_floor_e8") != required_floor:
            errors.append("escrow_funding_required_floor_mismatch")
        balance = funding_payload.get("balance_e8")
        if not isinstance(balance, int) or isinstance(balance, bool):
            errors.append("escrow_funding_balance_must_be_int")
        elif balance < required_floor:
            errors.append("escrow_funding_below_replay_floor")

    if settlement_payload:
        if settlement_payload.get("executed") is not True:
            errors.append("settlement_execution_not_true")
        if settlement_payload.get("token_contract") != policy.get("token_contract"):
            errors.append("settlement_execution_token_contract_mismatch")
        if settlement_payload.get("escrow_contract") != policy.get("escrow_contract"):
            errors.append("settlement_execution_escrow_contract_mismatch")
        if settlement_payload.get("settlement_asset") != policy.get("settlement_asset"):
            errors.append("settlement_execution_asset_mismatch")
        if settlement_payload.get("query_id") != replay.get("query_id"):
            errors.append("settlement_execution_query_id_mismatch")
        totals = settlement_execution_totals(replay)
        for key, expected in sorted(totals.items()):
            if settlement_payload.get(key) != expected:
                errors.append(f"settlement_execution_{key}_mismatch")

    status = "accepted" if not errors else "rejected"
    return {
        "schema": RECEIPT_BUNDLE_SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "error_count": len(errors),
        "errors": errors,
        "required_escrow_floor_e8": required_floor,
        "receipt_count": len(raw_receipts),
        "receipt_kinds": sorted(by_kind),
    }


def check_policy(
    policy: Mapping[str, Any],
    replay: Mapping[str, Any],
    receipt_bundle: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    _unknown_fields(policy, allowed=TOP_LEVEL_KEYS, label="policy", errors=errors)
    if policy.get("schema") != POLICY_SCHEMA:
        errors.append("policy_schema_mismatch")
    expected_policy_id = policy_content_hash(policy)
    if policy.get("policy_id") != expected_policy_id:
        errors.append("policy_id_mismatch")
    if policy.get("settlement_mode") != "production-candidate":
        errors.append("settlement_mode_must_be_production_candidate")
    if policy.get("settlement_asset") in {None, "", "DEV", "dev"}:
        errors.append("settlement_asset_must_be_production_asset")
    for key in ("token_contract", "escrow_contract", "governance_contract"):
        if not _is_address(policy.get(key)):
            errors.append(f"{key}_invalid")
    for key in (
        "governance_approval_receipt",
        "governance_execution_receipt",
        "escrow_funding_receipt",
        "settlement_execution_receipt",
    ):
        if not _is_sha(policy.get(key)):
            errors.append(f"{key}_must_be_sha256")
    _bool_true(policy, "live_token_settlement_enabled", errors)
    _bool_true(policy, "settlement_receipt_required", errors)

    governance = _obj_field(policy, "governance", errors)
    if governance:
        _unknown_fields(governance, allowed=GOVERNANCE_KEYS, label="governance", errors=errors)
        _int_field(governance, "timelock_seconds", errors, minimum=86_400)
        _int_field(governance, "dispute_window_epochs", errors, minimum=1)
        _int_field(governance, "slash_delay_epochs", errors, minimum=1)
        pause_role = governance.get("emergency_pause_role")
        if not isinstance(pause_role, str) or not pause_role.strip():
            errors.append("emergency_pause_role_required")

    required_bond = _int_field(policy, "required_reporter_bond_e8", errors, minimum=1)
    max_report_reward = _int_field(policy, "max_report_reward_e8", errors, minimum=1)
    min_dispute_bond = _int_field(policy, "min_dispute_bond_e8", errors, minimum=1)
    max_slash_bps = _int_field(policy, "max_slash_bps", errors, minimum=1, maximum=BPS_DENOM)
    withdrawal_delay = _int_field(policy, "withdrawal_delay_epochs", errors, minimum=1)
    fee_split = _obj_field(policy, "fee_split_bps", errors)
    if fee_split:
        _unknown_fields(fee_split, allowed=FEE_SPLIT_KEYS, label="fee_split_bps", errors=errors)
    reporter_bps = _int_field(fee_split, "reporter_reward", errors, minimum=0, maximum=BPS_DENOM) if fee_split else None
    treasury_bps = _int_field(fee_split, "treasury", errors, minimum=0, maximum=BPS_DENOM) if fee_split else None
    burn_bps = _int_field(fee_split, "burn", errors, minimum=0, maximum=BPS_DENOM) if fee_split else None
    if None not in (reporter_bps, treasury_bps, burn_bps):
        if int(reporter_bps) + int(treasury_bps) + int(burn_bps) != BPS_DENOM:
            errors.append("fee_split_bps_must_sum_to_10000")

    not_claimed = policy.get("not_claimed")
    if not isinstance(not_claimed, list):
        errors.append("not_claimed_must_be_list")
    else:
        values = {str(item) for item in not_claimed if isinstance(item, str)}
        errors.extend(f"missing_not_claim:{item}" for item in sorted(REQUIRED_NOT_CLAIMS - values))

    replay_result = verify_reporter_economics_replay(replay).to_json_obj()
    if replay_result["status"] != "accepted":
        errors.append("reporter_economics_replay_rejected")
        errors.extend(f"replay:{error}" for error in replay_result.get("errors", []))
    receipt_result = check_receipt_bundle(policy, replay, receipt_bundle)
    if receipt_result["status"] != "accepted":
        errors.append("receipt_bundle_rejected")
        errors.extend(f"receipt:{error}" for error in receipt_result.get("errors", []))

    if required_bond is not None and replay.get("required_reporter_bond_e8") != required_bond:
        errors.append("required_reporter_bond_mismatch")

    for event in _events_by_type(replay, "fee_split"):
        fee_paid = event.get("fee_paid_e8")
        if not isinstance(fee_paid, int) or isinstance(fee_paid, bool) or fee_paid <= 0:
            errors.append("fee_split_fee_paid_invalid")
            continue
        if None in (reporter_bps, treasury_bps, burn_bps):
            continue
        expected = {
            "reporter_reward_pool_delta_e8": int(reporter_bps),
            "treasury_delta_e8": int(treasury_bps),
            "burn_delta_e8": int(burn_bps),
        }
        total_delta = 0
        for key, bps in expected.items():
            actual = event.get(key)
            if not isinstance(actual, int) or isinstance(actual, bool):
                errors.append(f"fee_split_{key}_invalid")
                continue
            total_delta += int(actual)
            if int(actual) * BPS_DENOM != fee_paid * bps:
                errors.append(f"fee_split_{key}_policy_mismatch")
        if total_delta != fee_paid:
            errors.append("fee_split_total_policy_mismatch")

    for event in _events_by_type(replay, "submit_report"):
        reward = event.get("reward_e8")
        if isinstance(max_report_reward, int) and (
            not isinstance(reward, int) or isinstance(reward, bool) or reward > max_report_reward
        ):
            errors.append("report_reward_exceeds_policy")

    for event in _events_by_type(replay, "open_dispute"):
        bond = event.get("dispute_bond_e8")
        if isinstance(min_dispute_bond, int) and (
            not isinstance(bond, int) or isinstance(bond, bool) or bond < min_dispute_bond
        ):
            errors.append("dispute_bond_below_policy")

    slash_by_reporter: dict[str, int] = {}
    unregister_epoch: dict[str, int] = {}
    for event in replay.get("events", []) if isinstance(replay.get("events"), list) else []:
        if not isinstance(event, Mapping):
            continue
        if event.get("type") == "slash_reporter":
            reporter_id = str(event.get("reporter_id", ""))
            amount = event.get("amount_e8")
            if isinstance(amount, int) and not isinstance(amount, bool):
                slash_by_reporter[reporter_id] = slash_by_reporter.get(reporter_id, 0) + int(amount)
        if event.get("type") == "unregister_reporter":
            reporter_id = str(event.get("reporter_id", ""))
            epoch = event.get("epoch")
            if isinstance(epoch, int) and not isinstance(epoch, bool):
                unregister_epoch[reporter_id] = int(epoch)
        if event.get("type") == "withdraw_bond":
            reporter_id = str(event.get("reporter_id", ""))
            epoch = event.get("epoch")
            if isinstance(withdrawal_delay, int) and isinstance(epoch, int) and not isinstance(epoch, bool):
                if reporter_id not in unregister_epoch:
                    errors.append("withdraw_without_unregister")
                elif int(epoch) - int(unregister_epoch[reporter_id]) < withdrawal_delay:
                    errors.append("withdrawal_before_policy_delay")

    if isinstance(max_slash_bps, int) and isinstance(required_bond, int):
        max_slash = (required_bond * max_slash_bps) // BPS_DENOM
        for reporter_id, amount in slash_by_reporter.items():
            if amount > max_slash:
                errors.append(f"reporter_slash_exceeds_policy:{reporter_id}")

    status = "accepted" if not errors else "rejected"
    return {
        "schema": REPORT_SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "policy_id": expected_policy_id,
        "replay_status": replay_result["status"],
        "receipt_bundle_status": receipt_result["status"],
        "required_escrow_floor_e8": receipt_result["required_escrow_floor_e8"],
        "error_count": len(errors),
        "errors": errors,
        "settlement_controls": {
            "live_token_settlement_enabled": bool(policy.get("live_token_settlement_enabled") is True),
            "settlement_receipt_required": bool(policy.get("settlement_receipt_required") is True),
            "governance_approval_receipt": policy.get("governance_approval_receipt"),
            "governance_execution_receipt": policy.get("governance_execution_receipt"),
            "escrow_funding_receipt": policy.get("escrow_funding_receipt"),
            "settlement_execution_receipt": policy.get("settlement_execution_receipt"),
        },
        "go_live_blockers": list(GO_LIVE_BLOCKERS),
        "deployment_blockers": list(GO_LIVE_BLOCKERS),
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must be a JSON object")
    return obj


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--policy", type=Path, help="policy JSON; defaults to built-in sample policy")
    parser.add_argument("--replay", type=Path, help="reporter economics replay JSON; defaults to built-in sample replay")
    parser.add_argument("--receipts", type=Path, help="receipt bundle JSON; required when policy/replay is custom")
    parser.add_argument("--sample-policy", action="store_true", help="emit the built-in sample policy")
    parser.add_argument("--sample-receipts", action="store_true", help="emit the built-in sample receipt bundle")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--require-live", action="store_true", help="fail if go-live blockers remain")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.sample_policy:
        print(json.dumps(sample_policy(), indent=2, sort_keys=True))
        return 0
    if args.sample_receipts:
        policy = _load_json(args.policy) if args.policy else sample_policy()
        replay = _load_json(args.replay) if args.replay else sample_replay()
        print(json.dumps(sample_receipt_bundle(policy, replay), indent=2, sort_keys=True))
        return 0
    policy = _load_json(args.policy) if args.policy else sample_policy()
    replay = _load_json(args.replay) if args.replay else sample_replay()
    if args.receipts:
        receipts: Mapping[str, Any] | None = _load_json(args.receipts)
    elif args.policy is None and args.replay is None:
        receipts = sample_receipt_bundle(policy, replay)
    else:
        receipts = None
    result = check_policy(policy, replay, receipts)
    if args.require_live and result["go_live_blockers"]:
        result = dict(result)
        result["ok"] = False
        result["status"] = "rejected"
        result["errors"] = [*result["errors"], "go_live_blockers_present"]
        result["error_count"] = len(result["errors"])
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"status = {result['status']}")
        print(f"replay_status = {result['replay_status']}")
        print(f"receipt_bundle_status = {result['receipt_bundle_status']}")
        print(f"error_count = {result['error_count']}")
        print(f"go_live_blocker_count = {len(result['go_live_blockers'])}")
        print(f"policy_id = {result['policy_id']}")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
