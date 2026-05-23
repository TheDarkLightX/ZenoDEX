#!/usr/bin/env python3
"""Verify local token settlement for ZenoOracle reporter economics.

This verifier sits after ``zenodex_oracle_reporter_economics_replay.py``. The
economics replay proves the event ledger is valid. This verifier checks that the
accepted ledger is governed by an approved policy and that a concrete token
transfer receipt settles every value-moving flow without minting value.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from zenodex_oracle_reporter_economics_replay import (  # noqa: E402
    MAX_AMOUNT,
    verify_reporter_economics_replay,
)
from zenodex_oracle_reporter_economics_replay import (  # noqa: E402
    REPLAY_SCHEMA as ECONOMICS_REPLAY_SCHEMA,
)
from zenodex_oracle_reporter_economics_replay import (  # noqa: E402
    RESULT_SCHEMA as ECONOMICS_RESULT_SCHEMA,
)
from zenodex_oracle_reporter_economics_replay import (  # noqa: E402
    sample_replay as sample_economics_replay,
)

SETTLEMENT_SCHEMA = "zenodex.oracle.reporter_token_settlement_replay.v1"
RESULT_SCHEMA = "zenodex.oracle.reporter_token_settlement_replay_result.v1"
POLICY_SCHEMA = "zenodex.oracle.reporter_token_settlement_policy.v1"
MAX_REPLAY_BYTES = 750_000
MAX_TRANSFERS = 512
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
TOP_LEVEL_KEYS = {"schema", "policy", "economics_replay", "initial_balances_e8", "transfers"}
POLICY_KEYS = {
    "schema",
    "policy_id",
    "governance_receipt_id",
    "approved",
    "authority_id",
    "effective_epoch",
    "expires_epoch",
    "consumer_module",
    "action_kind",
    "required_reporter_bond_e8",
    "reporter_reward_fee_bps",
    "treasury_fee_bps",
    "burn_fee_bps",
    "max_report_reward_e8",
    "max_slash_bps",
    "withdrawal_requires_inactive",
    "withdrawal_requires_no_open_dispute",
}
TRANSFER_KEYS = {"debit", "credit", "amount_e8", "reason", "policy_id"}
ALLOWED_REASONS = {
    "bond_deposit",
    "fee_split_reporter_reward_pool",
    "fee_split_treasury",
    "fee_split_burn",
    "report_reward_payout",
    "reporter_slash",
    "dispute_reward_payout",
    "bond_withdrawal",
}
ORACLE_BOND_ESCROW = "oracle.bond_escrow"
ORACLE_REPORTER_REWARD_POOL = "oracle.reporter_reward_pool"
ORACLE_DISPUTE_REWARD_POOL = "oracle.dispute_reward_pool"
ORACLE_TREASURY = "oracle.treasury"
ORACLE_BURN = "oracle.burn"
ORACLE_SLASH_POOL = "oracle.slash_pool"
IDENTITY_BOUND_REASONS = {
    "bond_deposit",
    "report_reward_payout",
    "reporter_slash",
    "dispute_reward_payout",
    "bond_withdrawal",
}

REASON_TOTAL_FIELDS = {
    "bond_deposit": "bond_deposit_settled_e8",
    "fee_split_reporter_reward_pool": "fee_reward_pool_settled_e8",
    "fee_split_treasury": "fee_treasury_settled_e8",
    "fee_split_burn": "fee_burn_settled_e8",
    "report_reward_payout": "report_reward_settled_e8",
    "reporter_slash": "slash_settled_e8",
    "dispute_reward_payout": "dispute_reward_settled_e8",
    "bond_withdrawal": "withdrawal_settled_e8",
}
NOT_CLAIMED = [
    "does_not_claim_production_chain_execution",
    "does_not_claim_onchain_governance_live",
    "does_not_claim_reporter_honesty",
    "does_not_claim_oracle_truth",
]


@dataclass(frozen=True)
class TokenSettlementResult:
    status: str
    errors: list[str]
    governance_approved: bool = False
    source_replay_accepted: bool = False
    token_conservation_ok: bool = False
    transfer_count: int = 0
    account_count: int = 0
    total_debits_e8: int = 0
    total_credits_e8: int = 0
    bond_deposit_settled_e8: int = 0
    fee_reward_pool_settled_e8: int = 0
    fee_treasury_settled_e8: int = 0
    fee_burn_settled_e8: int = 0
    report_reward_settled_e8: int = 0
    slash_settled_e8: int = 0
    dispute_reward_settled_e8: int = 0
    withdrawal_settled_e8: int = 0
    final_balances_e8: Mapping[str, int] | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "governance_approved": self.governance_approved,
            "source_replay_accepted": self.source_replay_accepted,
            "token_conservation_ok": self.token_conservation_ok,
            "transfer_count": self.transfer_count,
            "account_count": self.account_count,
            "total_debits_e8": self.total_debits_e8,
            "total_credits_e8": self.total_credits_e8,
            "bond_deposit_settled_e8": self.bond_deposit_settled_e8,
            "fee_reward_pool_settled_e8": self.fee_reward_pool_settled_e8,
            "fee_treasury_settled_e8": self.fee_treasury_settled_e8,
            "fee_burn_settled_e8": self.fee_burn_settled_e8,
            "report_reward_settled_e8": self.report_reward_settled_e8,
            "slash_settled_e8": self.slash_settled_e8,
            "dispute_reward_settled_e8": self.dispute_reward_settled_e8,
            "withdrawal_settled_e8": self.withdrawal_settled_e8,
            "final_balances_e8": dict(self.final_balances_e8 or {}),
            "errors": list(self.errors),
            "not_claimed": list(NOT_CLAIMED),
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def _content_hash(obj: Mapping[str, Any]) -> str:
    payload = {key: value for key, value in obj.items() if key != "policy_id"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def sample_policy() -> dict[str, Any]:
    policy = {
        "schema": POLICY_SCHEMA,
        "policy_id": "",
        "governance_receipt_id": sample_hash("zenodex.oracle.governance.reporter-token-settlement.v1"),
        "approved": True,
        "authority_id": "governance.oracle-council.v1",
        "effective_epoch": 0,
        "expires_epoch": 100,
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "required_reporter_bond_e8": 250_000_000_000,
        "reporter_reward_fee_bps": 9000,
        "treasury_fee_bps": 700,
        "burn_fee_bps": 300,
        "max_report_reward_e8": 30_000_000,
        "max_slash_bps": 5000,
        "withdrawal_requires_inactive": True,
        "withdrawal_requires_no_open_dispute": True,
    }
    policy["policy_id"] = _content_hash(policy)
    return policy


def sample_settlement_replay() -> dict[str, Any]:
    policy = sample_policy()
    economics = sample_economics_replay()
    policy_id = policy["policy_id"]
    return {
        "schema": SETTLEMENT_SCHEMA,
        "policy": policy,
        "economics_replay": economics,
        "initial_balances_e8": {
            "reporter.alpha": 250_000_000_000,
            "reporter.beta": 250_000_000_000,
            "reporter.gamma": 250_000_000_000,
            "consumer.fee_payer": 100_000_000,
            ORACLE_DISPUTE_REWARD_POOL: 20_000_000,
            ORACLE_BOND_ESCROW: 0,
            ORACLE_REPORTER_REWARD_POOL: 0,
            ORACLE_TREASURY: 0,
            ORACLE_BURN: 0,
            ORACLE_SLASH_POOL: 0,
            "challenger.sample": 0,
        },
        "transfers": [
            {
                "debit": "reporter.alpha",
                "credit": ORACLE_BOND_ESCROW,
                "amount_e8": 250_000_000_000,
                "reason": "bond_deposit",
                "policy_id": policy_id,
            },
            {
                "debit": "reporter.beta",
                "credit": ORACLE_BOND_ESCROW,
                "amount_e8": 250_000_000_000,
                "reason": "bond_deposit",
                "policy_id": policy_id,
            },
            {
                "debit": "reporter.gamma",
                "credit": ORACLE_BOND_ESCROW,
                "amount_e8": 250_000_000_000,
                "reason": "bond_deposit",
                "policy_id": policy_id,
            },
            {
                "debit": "consumer.fee_payer",
                "credit": ORACLE_REPORTER_REWARD_POOL,
                "amount_e8": 90_000_000,
                "reason": "fee_split_reporter_reward_pool",
                "policy_id": policy_id,
            },
            {
                "debit": "consumer.fee_payer",
                "credit": ORACLE_TREASURY,
                "amount_e8": 7_000_000,
                "reason": "fee_split_treasury",
                "policy_id": policy_id,
            },
            {
                "debit": "consumer.fee_payer",
                "credit": ORACLE_BURN,
                "amount_e8": 3_000_000,
                "reason": "fee_split_burn",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_REPORTER_REWARD_POOL,
                "credit": "reporter.alpha",
                "amount_e8": 30_000_000,
                "reason": "report_reward_payout",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_REPORTER_REWARD_POOL,
                "credit": "reporter.beta",
                "amount_e8": 30_000_000,
                "reason": "report_reward_payout",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_REPORTER_REWARD_POOL,
                "credit": "reporter.gamma",
                "amount_e8": 30_000_000,
                "reason": "report_reward_payout",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_BOND_ESCROW,
                "credit": ORACLE_SLASH_POOL,
                "amount_e8": 125_000_000_000,
                "reason": "reporter_slash",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_DISPUTE_REWARD_POOL,
                "credit": "challenger.sample",
                "amount_e8": 10_000_000,
                "reason": "dispute_reward_payout",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_BOND_ESCROW,
                "credit": "reporter.alpha",
                "amount_e8": 125_000_000_000,
                "reason": "bond_withdrawal",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_BOND_ESCROW,
                "credit": "reporter.beta",
                "amount_e8": 250_000_000_000,
                "reason": "bond_withdrawal",
                "policy_id": policy_id,
            },
            {
                "debit": ORACLE_BOND_ESCROW,
                "credit": "reporter.gamma",
                "amount_e8": 250_000_000_000,
                "reason": "bond_withdrawal",
                "policy_id": policy_id,
            },
        ],
    }


def _unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], label: str, errors: list[str]) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _token(value: object, *, label: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{label}_must_be_token")
        return None
    return str(value)


def _amount(value: object, *, label: str, errors: list[str]) -> int | None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > MAX_AMOUNT:
        errors.append(f"{label}_must_be_int_between_0_and_{MAX_AMOUNT}")
        return None
    return int(value)


def _policy(obj: Mapping[str, Any], errors: list[str]) -> Mapping[str, Any] | None:
    raw = obj.get("policy")
    if not isinstance(raw, Mapping):
        errors.append("policy_must_be_object")
        return None
    _unknown_fields(raw, allowed=POLICY_KEYS, label="policy", errors=errors)
    if raw.get("schema") != POLICY_SCHEMA:
        errors.append("policy_schema_mismatch")
    if not _is_hash(raw.get("policy_id")):
        errors.append("policy_id_must_be_sha256")
    elif raw.get("policy_id") != _content_hash(raw):
        errors.append("policy_content_hash_mismatch")
    if not _is_hash(raw.get("governance_receipt_id")):
        errors.append("governance_receipt_id_must_be_sha256")
    if raw.get("approved") is not True:
        errors.append("policy_not_governance_approved")
    _token(raw.get("authority_id"), label="authority_id", errors=errors)
    for key in ("effective_epoch", "expires_epoch"):
        value = raw.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            errors.append(f"{key}_must_be_int_ge_0")
    _token(raw.get("consumer_module"), label="consumer_module", errors=errors)
    _token(raw.get("action_kind"), label="action_kind", errors=errors)
    _amount(raw.get("required_reporter_bond_e8"), label="required_reporter_bond_e8", errors=errors)
    for key in ("reporter_reward_fee_bps", "treasury_fee_bps", "burn_fee_bps", "max_slash_bps"):
        value = raw.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > 10_000:
            errors.append(f"{key}_must_be_int_between_0_and_10000")
    _amount(raw.get("max_report_reward_e8"), label="max_report_reward_e8", errors=errors)
    for key in ("withdrawal_requires_inactive", "withdrawal_requires_no_open_dispute"):
        if raw.get(key) is not True:
            errors.append(f"{key}_must_be_true")
    if all(isinstance(raw.get(key), int) and not isinstance(raw.get(key), bool) for key in ("effective_epoch", "expires_epoch")):
        if int(raw["expires_epoch"]) < int(raw["effective_epoch"]):
            errors.append("policy_expires_before_effective_epoch")
    if all(
        isinstance(raw.get(key), int) and not isinstance(raw.get(key), bool)
        for key in ("reporter_reward_fee_bps", "treasury_fee_bps", "burn_fee_bps")
    ):
        if int(raw["reporter_reward_fee_bps"]) + int(raw["treasury_fee_bps"]) + int(raw["burn_fee_bps"]) > 10_000:
            errors.append("policy_fee_bps_exceed_10000")
    return raw


def _balances(obj: Mapping[str, Any], errors: list[str]) -> dict[str, int]:
    raw = obj.get("initial_balances_e8")
    if not isinstance(raw, Mapping):
        errors.append("initial_balances_e8_must_be_object")
        return {}
    balances: dict[str, int] = {}
    for account, amount in raw.items():
        token = _token(account, label="account_id", errors=errors)
        parsed = _amount(amount, label=f"initial_balance:{account}", errors=errors)
        if token is not None and parsed is not None:
            balances[token] = parsed
    return balances


def _transfers(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("transfers")
    if not isinstance(raw, list):
        errors.append("transfers_must_be_list")
        return []
    if len(raw) > MAX_TRANSFERS:
        errors.append(f"transfers_exceed_max:{len(raw)}>{MAX_TRANSFERS}")
    transfers: list[Mapping[str, Any]] = []
    for index, transfer in enumerate(raw[:MAX_TRANSFERS]):
        if not isinstance(transfer, Mapping):
            errors.append(f"transfer_{index}_must_be_object")
            continue
        _unknown_fields(transfer, allowed=TRANSFER_KEYS, label="transfer", errors=errors)
        transfers.append(transfer)
    return transfers


def _add_amount(totals: dict[str, int], key: str, amount: object) -> None:
    if isinstance(amount, int) and not isinstance(amount, bool):
        totals[key] = totals.get(key, 0) + int(amount)


def _add_obligation(
    obligations: dict[tuple[str, str, str], int],
    reason: str,
    debit: object,
    credit: object,
    amount: object,
) -> None:
    """DbC: accepted obligations require token-like actors and positive integer amounts."""
    if not all(isinstance(value, str) for value in (debit, credit)):
        return
    if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
        return
    key = (reason, str(debit), str(credit))
    obligations[key] = obligations.get(key, 0) + int(amount)


def _event_reason_totals(replay: Mapping[str, Any]) -> dict[str, int]:
    totals = {reason: 0 for reason in ALLOWED_REASONS}
    for event in replay.get("events", []):
        if not isinstance(event, Mapping):
            continue
        _add_event_reason_total(totals, event)
    return totals


def _add_event_reason_total(totals: dict[str, int], event: Mapping[str, Any]) -> None:
    event_type = event.get("type")
    if event_type == "deposit_bond":
        _add_amount(totals, "bond_deposit", event.get("amount_e8"))
    if event_type == "fee_split":
        _add_amount(totals, "fee_split_reporter_reward_pool", event.get("reporter_reward_pool_delta_e8"))
        _add_amount(totals, "fee_split_treasury", event.get("treasury_delta_e8"))
        _add_amount(totals, "fee_split_burn", event.get("burn_delta_e8"))
    if event_type == "submit_report":
        _add_amount(totals, "report_reward_payout", event.get("reward_e8"))
    if event_type == "slash_reporter":
        _add_amount(totals, "reporter_slash", event.get("amount_e8"))
    if event_type == "pay_dispute_reward":
        _add_amount(totals, "dispute_reward_payout", event.get("amount_e8"))
    if event_type == "withdraw_bond":
        _add_amount(totals, "bond_withdrawal", event.get("amount_e8"))


def _event_identity_obligations(replay: Mapping[str, Any]) -> dict[tuple[str, str, str], int]:
    obligations: dict[tuple[str, str, str], int] = {}
    for event in replay.get("events", []):
        if isinstance(event, Mapping):
            _add_event_identity_obligation(obligations, event)
    return obligations


def _add_event_identity_obligation(obligations: dict[tuple[str, str, str], int], event: Mapping[str, Any]) -> None:
    event_type = event.get("type")
    if event_type == "deposit_bond":
        _add_obligation(obligations, "bond_deposit", event.get("reporter_id"), ORACLE_BOND_ESCROW, event.get("amount_e8"))
    if event_type == "submit_report":
        _add_obligation(
            obligations,
            "report_reward_payout",
            ORACLE_REPORTER_REWARD_POOL,
            event.get("reporter_id"),
            event.get("reward_e8"),
        )
    if event_type == "slash_reporter":
        _add_obligation(obligations, "reporter_slash", ORACLE_BOND_ESCROW, ORACLE_SLASH_POOL, event.get("amount_e8"))
    if event_type == "pay_dispute_reward":
        _add_obligation(
            obligations,
            "dispute_reward_payout",
            ORACLE_DISPUTE_REWARD_POOL,
            event.get("recipient_id"),
            event.get("amount_e8"),
        )
    if event_type == "withdraw_bond":
        _add_obligation(obligations, "bond_withdrawal", ORACLE_BOND_ESCROW, event.get("reporter_id"), event.get("amount_e8"))


def _transfer_identity_obligations(transfers: list[tuple[str, str, str, int]]) -> dict[tuple[str, str, str], int]:
    obligations: dict[tuple[str, str, str], int] = {}
    for reason, debit, credit, amount in transfers:
        if reason in IDENTITY_BOUND_REASONS:
            _add_obligation(obligations, reason, debit, credit, amount)
    return obligations


def _append_identity_obligation_errors(
    actual: Mapping[tuple[str, str, str], int],
    expected: Mapping[tuple[str, str, str], int],
    errors: list[str],
) -> None:
    for key in sorted(set(actual) | set(expected)):
        actual_amount = int(actual.get(key, 0))
        expected_amount = int(expected.get(key, 0))
        if actual_amount != expected_amount:
            reason, debit, credit = key
            errors.append(
                f"settlement_identity_mismatch:{reason}:{debit}->{credit}:{actual_amount}!={expected_amount}"
            )


def verify_reporter_token_settlement(obj: Mapping[str, Any]) -> TokenSettlementResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="settlement_replay", errors=errors)
    if obj.get("schema") != SETTLEMENT_SCHEMA:
        errors.append("settlement_replay_schema_mismatch")
    policy = _policy(obj, errors)
    economics = obj.get("economics_replay")
    if not isinstance(economics, Mapping):
        errors.append("economics_replay_must_be_object")
        economics = {}
    if economics.get("schema") != ECONOMICS_REPLAY_SCHEMA:
        errors.append("economics_replay_schema_mismatch")
    economics_result = verify_reporter_economics_replay(economics)
    economics_json = economics_result.to_json_obj()
    if economics_json.get("schema") != ECONOMICS_RESULT_SCHEMA:
        errors.append("economics_result_schema_mismatch")
    if economics_result.status != "accepted":
        errors.append("economics_replay_not_accepted")

    balances = _balances(obj, errors)
    transfers = _transfers(obj, errors)
    policy_id = policy.get("policy_id") if isinstance(policy, Mapping) else None
    if isinstance(policy, Mapping):
        if policy.get("consumer_module") != economics.get("consumer_module"):
            errors.append("policy_consumer_module_mismatch")
        if policy.get("action_kind") != economics.get("action_kind"):
            errors.append("policy_action_kind_mismatch")
        if policy.get("required_reporter_bond_e8") != economics.get("required_reporter_bond_e8"):
            errors.append("policy_required_bond_mismatch")
        if economics_result.status == "accepted":
            last_epoch = economics_result.last_epoch
            if isinstance(last_epoch, int):
                if isinstance(policy.get("effective_epoch"), int) and last_epoch < int(policy["effective_epoch"]):
                    errors.append("policy_not_yet_effective")
                if isinstance(policy.get("expires_epoch"), int) and last_epoch > int(policy["expires_epoch"]):
                    errors.append("policy_expired_before_last_event")
        for event in economics.get("events", []):
            if isinstance(event, Mapping) and event.get("type") == "submit_report":
                reward = event.get("reward_e8")
                if isinstance(reward, int) and isinstance(policy.get("max_report_reward_e8"), int):
                    if reward > int(policy["max_report_reward_e8"]):
                        errors.append("report_reward_exceeds_governance_policy")
        if isinstance(policy.get("max_slash_bps"), int):
            max_slash = int(economics.get("required_reporter_bond_e8", 0)) * int(policy["max_slash_bps"]) // 10_000
            for event in economics.get("events", []):
                if isinstance(event, Mapping) and event.get("type") == "slash_reporter":
                    amount = event.get("amount_e8")
                    if isinstance(amount, int) and amount > max_slash:
                        errors.append("slash_exceeds_governance_policy")

    reason_totals = {reason: 0 for reason in ALLOWED_REASONS}
    identity_bound_transfers: list[tuple[str, str, str, int]] = []
    total_debits = 0
    total_credits = 0
    for index, transfer in enumerate(transfers):
        debit = _token(transfer.get("debit"), label=f"transfer_{index}_debit", errors=errors)
        credit = _token(transfer.get("credit"), label=f"transfer_{index}_credit", errors=errors)
        amount = _amount(transfer.get("amount_e8"), label=f"transfer_{index}_amount_e8", errors=errors)
        reason = transfer.get("reason")
        if reason not in ALLOWED_REASONS:
            errors.append(f"transfer_{index}_reason_unsupported:{reason}")
            continue
        if policy_id is None or transfer.get("policy_id") != policy_id:
            errors.append(f"transfer_{index}_policy_id_mismatch")
        if debit is None or credit is None or amount is None:
            continue
        if debit == credit:
            errors.append(f"transfer_{index}_self_transfer")
            continue
        if amount == 0:
            errors.append(f"transfer_{index}_amount_required")
            continue
        balances.setdefault(debit, 0)
        balances.setdefault(credit, 0)
        if balances[debit] < amount:
            errors.append(f"transfer_{index}_insufficient_balance:{debit}")
            continue
        balances[debit] -= amount
        balances[credit] += amount
        total_debits += amount
        total_credits += amount
        reason_totals[str(reason)] += amount
        identity_bound_transfers.append((str(reason), debit, credit, amount))

    expected_reason_totals = _event_reason_totals(economics)
    for reason in sorted(ALLOWED_REASONS):
        if reason_totals[reason] != expected_reason_totals[reason]:
            errors.append(f"settlement_total_mismatch:{reason}:{reason_totals[reason]}!={expected_reason_totals[reason]}")

    expected_identity_obligations = _event_identity_obligations(economics)
    actual_identity_obligations = _transfer_identity_obligations(identity_bound_transfers)
    _append_identity_obligation_errors(actual_identity_obligations, expected_identity_obligations, errors)

    if economics_result.status == "accepted":
        expected_bond_escrow = (
            expected_reason_totals["bond_deposit"]
            - expected_reason_totals["reporter_slash"]
            - expected_reason_totals["bond_withdrawal"]
        )
        if reason_totals["bond_deposit"] != expected_reason_totals["bond_deposit"]:
            errors.append("bond_deposit_total_mismatch")
        if reason_totals["report_reward_payout"] != int(economics_result.total_rewards_paid_e8 or 0):
            errors.append("report_reward_total_mismatch")
        if reason_totals["reporter_slash"] != int(economics_result.total_slashed_e8 or 0):
            errors.append("slash_total_mismatch")
        if reason_totals["bond_withdrawal"] != int(economics_result.total_withdrawn_e8 or 0):
            errors.append("withdrawal_total_mismatch")
        fee_split_total = (
            reason_totals["fee_split_reporter_reward_pool"]
            + reason_totals["fee_split_treasury"]
            + reason_totals["fee_split_burn"]
        )
        if fee_split_total != int(economics_result.total_fees_paid_e8 or 0):
            errors.append("fee_split_total_mismatch")
        if balances.get(ORACLE_REPORTER_REWARD_POOL, 0) != int(economics_result.reward_pool_e8 or 0):
            errors.append("reward_pool_final_balance_mismatch")
        if balances.get(ORACLE_DISPUTE_REWARD_POOL, 0) != int(economics_result.dispute_reward_pool_e8 or 0):
            errors.append("dispute_reward_pool_final_balance_mismatch")
        if balances.get(ORACLE_TREASURY, 0) != int(economics_result.treasury_balance_e8 or 0):
            errors.append("treasury_final_balance_mismatch")
        if balances.get(ORACLE_BURN, 0) != int(economics_result.burn_balance_e8 or 0):
            errors.append("burn_final_balance_mismatch")
        if balances.get(ORACLE_BOND_ESCROW, 0) != expected_bond_escrow:
            errors.append("bond_escrow_final_balance_mismatch")

    token_conservation_ok = total_debits == total_credits
    if not token_conservation_ok:
        errors.append("token_conservation_mismatch")

    return TokenSettlementResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        governance_approved=bool(isinstance(policy, Mapping) and policy.get("approved") is True),
        source_replay_accepted=economics_result.status == "accepted",
        token_conservation_ok=token_conservation_ok,
        transfer_count=len(transfers),
        account_count=len(balances),
        total_debits_e8=total_debits,
        total_credits_e8=total_credits,
        bond_deposit_settled_e8=reason_totals["bond_deposit"],
        fee_reward_pool_settled_e8=reason_totals["fee_split_reporter_reward_pool"],
        fee_treasury_settled_e8=reason_totals["fee_split_treasury"],
        fee_burn_settled_e8=reason_totals["fee_split_burn"],
        report_reward_settled_e8=reason_totals["report_reward_payout"],
        slash_settled_e8=reason_totals["reporter_slash"],
        dispute_reward_settled_e8=reason_totals["dispute_reward_payout"],
        withdrawal_settled_e8=reason_totals["bond_withdrawal"],
        final_balances_e8=dict(sorted(balances.items())),
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_REPLAY_BYTES:
        raise ValueError(f"reporter_token_settlement_replay_file_too_large:{size}>{MAX_REPLAY_BYTES}")
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("reporter token settlement replay root must be a JSON object")
    return obj


def _write_json(payload: Mapping[str, Any], output: Path | None) -> None:
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        replay = _load_json(Path(args.replay))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = TokenSettlementResult(status="inconclusive", errors=[f"reporter_token_settlement_replay_load_failed:{exc}"])
        _write_json(result.to_json_obj(), Path(args.output) if args.output else None)
        return 3
    result = verify_reporter_token_settlement(replay)
    _write_json(result.to_json_obj(), Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    _write_json(sample_settlement_replay(), Path(args.output) if args.output else None)
    return 0


def cmd_self_test(args: argparse.Namespace) -> int:
    result = verify_reporter_token_settlement(sample_settlement_replay())
    _write_json(result.to_json_obj(), Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    verify = sub.add_parser("verify", help="verify a reporter token settlement replay JSON file")
    verify.add_argument("replay")
    verify.add_argument("--output")
    verify.set_defaults(func=cmd_verify)

    sample = sub.add_parser("sample", help="emit a sample accepted reporter token settlement replay")
    sample.add_argument("--output")
    sample.set_defaults(func=cmd_sample)

    self_test = sub.add_parser("self-test", help="run the built-in reporter token settlement replay check")
    self_test.add_argument("--output")
    self_test.set_defaults(func=cmd_self_test)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
