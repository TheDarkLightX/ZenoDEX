"""Derivative settlement receipt helpers.

These helpers give derivative lanes a common replay envelope for settlement
authority evidence. They are structural guards only: a receipt binds roots,
formula hashes, collateral bounds, witness hashes, and balance-transfer roots.
The lane-specific verifier still decides whether a transition is valid.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


DERIVATIVE_SETTLEMENT_RECEIPT_SCHEMA = "zenodex/derivative_settlement_receipt/v1"
DERIVATIVE_SETTLEMENT_RECEIPT_MAX_COLLATERAL = 1_000_000_000_000

_HEX_32_RE = re.compile(r"^(0x|sha256:)[0-9a-f]{64}$")
_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.:/-]{1,128}$")


@dataclass(frozen=True)
class DerivativeSettlementReceiptBody:
    """Hash-stable settlement receipt body."""

    market: str
    market_epoch: int
    action: str
    pre_state_root: str
    post_state_root: str
    reference_root: str
    payoff_formula_hash: str
    witness_hash: str
    collateral_bound: int
    balance_transfer_root: str
    accepted: bool
    rejection_code: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": DERIVATIVE_SETTLEMENT_RECEIPT_SCHEMA,
            "market": self.market,
            "market_epoch": int(self.market_epoch),
            "action": self.action,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "reference_root": self.reference_root,
            "payoff_formula_hash": self.payoff_formula_hash,
            "witness_hash": self.witness_hash,
            "collateral_bound": int(self.collateral_bound),
            "balance_transfer_root": self.balance_transfer_root,
            "accepted": bool(self.accepted),
            "rejection_code": self.rejection_code,
        }


def is_hash_ref(value: object) -> bool:
    """Return True for canonical 32-byte 0x or sha256 hash references."""

    return isinstance(value, str) and _HEX_32_RE.fullmatch(value) is not None


def derivative_settlement_receipt_hash(body: Mapping[str, Any]) -> str:
    """Hash a derivative settlement receipt body with domain separation."""

    return sha256_hex(
        domain_sep_bytes("zenodex.derivative_settlement_receipt/v1")
        + canonical_json_bytes(dict(body))
    )


def _valid_token(value: object) -> bool:
    return isinstance(value, str) and _TOKEN_RE.fullmatch(value) is not None


def validate_derivative_settlement_receipt_body(body: Mapping[str, Any]) -> tuple[bool, str]:
    """Validate the deterministic settlement receipt body contract."""

    if not isinstance(body, Mapping):
        return False, "body_type"
    if body.get("schema") != DERIVATIVE_SETTLEMENT_RECEIPT_SCHEMA:
        return False, "schema"
    if not _valid_token(body.get("market")):
        return False, "market"
    if not _valid_token(body.get("action")):
        return False, "action"
    epoch = body.get("market_epoch")
    if not isinstance(epoch, int) or isinstance(epoch, bool) or epoch < 0:
        return False, "market_epoch"

    for key in (
        "pre_state_root",
        "post_state_root",
        "reference_root",
        "payoff_formula_hash",
        "witness_hash",
        "balance_transfer_root",
    ):
        if not is_hash_ref(body.get(key)):
            return False, key

    collateral = body.get("collateral_bound")
    if (
        not isinstance(collateral, int)
        or isinstance(collateral, bool)
        or collateral < 0
        or collateral > DERIVATIVE_SETTLEMENT_RECEIPT_MAX_COLLATERAL
    ):
        return False, "collateral_bound"

    accepted = body.get("accepted")
    if not isinstance(accepted, bool):
        return False, "accepted"
    rejection_code = body.get("rejection_code")
    if not isinstance(rejection_code, str):
        return False, "rejection_code"
    if accepted and rejection_code:
        return False, "accepted_rejection_code"
    if not accepted:
        if not rejection_code or not _valid_token(rejection_code):
            return False, "missing_rejection_code"
        if body.get("post_state_root") != body.get("pre_state_root"):
            return False, "rejected_state_changed"
    return True, "ok"


def make_derivative_settlement_receipt(body: DerivativeSettlementReceiptBody) -> dict[str, Any]:
    """Build a hash-bound derivative settlement receipt envelope."""

    body_dict = body.to_dict()
    ok, reason = validate_derivative_settlement_receipt_body(body_dict)
    if not ok:
        raise ValueError(f"invalid derivative settlement receipt body: {reason}")
    return {
        "schema": DERIVATIVE_SETTLEMENT_RECEIPT_SCHEMA,
        "body": body_dict,
        "receipt_hash": derivative_settlement_receipt_hash(body_dict),
    }


def verify_derivative_settlement_receipt(receipt: Mapping[str, Any]) -> tuple[bool, str]:
    """Verify a hash-bound derivative settlement receipt envelope."""

    if not isinstance(receipt, Mapping):
        return False, "receipt_type"
    if receipt.get("schema") != DERIVATIVE_SETTLEMENT_RECEIPT_SCHEMA:
        return False, "schema"
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        return False, "body"
    ok, reason = validate_derivative_settlement_receipt_body(body)
    if not ok:
        return False, reason
    expected_hash = derivative_settlement_receipt_hash(body)
    if receipt.get("receipt_hash") != expected_hash:
        return False, "receipt_hash"
    return True, "ok"
