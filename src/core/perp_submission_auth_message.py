from __future__ import annotations

import hashlib
from typing import Any, Dict, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes
from .perp_submission_auth_field_selector_gate import (
    PERP_OP_AUTH_FIELD_SELECTOR_ACTION_TAGS_V1,
    PERP_OP_AUTH_FIELD_SELECTOR_CANDIDATE_KEYS_V1,
    select_perp_submission_auth_signed_field_keys_v1,
)


def _derive_signed_field_keys_v1() -> dict[str, tuple[str, ...]]:
    witness_op = {key: True for key in PERP_OP_AUTH_FIELD_SELECTOR_CANDIDATE_KEYS_V1}
    return {
        action: select_perp_submission_auth_signed_field_keys_v1(
            action=action,
            op=witness_op,
        ).signed_field_keys
        for action in PERP_OP_AUTH_FIELD_SELECTOR_ACTION_TAGS_V1
    }


PERP_OP_AUTH_SIGNED_FIELD_KEYS_V1: dict[str, tuple[str, ...]] = _derive_signed_field_keys_v1()


def _require_auth_nonce(nonce: int) -> int:
    if not isinstance(nonce, int) or isinstance(nonce, bool):
        raise TypeError("nonce must be an int")
    if nonce < 0:
        raise ValueError("nonce must be non-negative")
    return int(nonce)


def build_perp_op_auth_signing_dict_v1(
    op: Mapping[str, Any],
    *,
    signer_pubkey: str,
    nonce: int,
) -> Dict[str, Any]:
    """Build the canonical action-bound signing dict for perps op authorization."""
    nonce_int = _require_auth_nonce(nonce)
    module = op.get("module")
    version = op.get("version")
    market_id = op.get("market_id")
    action = op.get("action")
    if not isinstance(module, str) or not module:
        raise ValueError("signing dict missing module")
    if not isinstance(version, str) or not version:
        raise ValueError("signing dict missing version")
    if not isinstance(market_id, str) or not market_id:
        raise ValueError("signing dict missing market_id")
    if not isinstance(action, str) or not action:
        raise ValueError("signing dict missing action")

    selection = select_perp_submission_auth_signed_field_keys_v1(action=action, op=op)

    fields: Dict[str, Any] = {}
    for key in selection.signed_field_keys:
        fields[key] = op[key]

    return {
        "module": module,
        "version": version,
        "market_id": market_id,
        "action": action,
        "signer_pubkey": str(signer_pubkey),
        "nonce": nonce_int,
        "fields": fields,
    }


def build_perp_op_auth_message_v1(
    op: Mapping[str, Any],
    *,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> bytes:
    """Build the domain-separated message bytes for perps op authorization."""
    if not isinstance(chain_id, str) or not chain_id:
        raise ValueError("chain_id must be a non-empty string")
    signing_payload = canonical_json_bytes(
        build_perp_op_auth_signing_dict_v1(op, signer_pubkey=signer_pubkey, nonce=nonce)
    )
    return domain_sep_bytes(f"perp_op_sig:{chain_id}", version=1) + signing_payload


def hash_perp_op_auth_message_v1(
    op: Mapping[str, Any],
    *,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> bytes:
    """Hash the canonical perps auth message used by both the client and engine."""
    return hashlib.sha256(
        build_perp_op_auth_message_v1(
            op,
            chain_id=chain_id,
            signer_pubkey=signer_pubkey,
            nonce=nonce,
        )
    ).digest()
