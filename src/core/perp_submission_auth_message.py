from __future__ import annotations

import hashlib
from typing import Any, Dict, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes


PERP_OP_AUTH_SIGNED_FIELD_KEYS_V1: dict[str, tuple[str, ...]] = {
    "init_market_2p": ("quote_asset", "account_a_pubkey", "account_b_pubkey", "deadline"),
    "init_market_3p": ("quote_asset", "account_a_pubkey", "account_b_pubkey", "account_c_pubkey", "deadline"),
    "set_position_pair": (
        "account_a_pubkey",
        "account_b_pubkey",
        "new_position_base_a",
        "new_position_base_b",
        "deadline",
    ),
    "set_position_triplet": (
        "account_a_pubkey",
        "account_b_pubkey",
        "account_c_pubkey",
        "new_position_base_a",
        "new_position_base_b",
        "new_position_base_c",
        "deadline",
    ),
    "publish_clearing_price": ("price_e8", "deadline"),
}


def build_perp_op_auth_signing_dict_v1(
    op: Mapping[str, Any],
    *,
    signer_pubkey: str,
    nonce: int,
) -> Dict[str, Any]:
    """Build the canonical action-bound signing dict for perps op authorization."""
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

    keys = PERP_OP_AUTH_SIGNED_FIELD_KEYS_V1.get(action)
    if keys is None:
        raise ValueError(f"unsupported signed action: {action}")

    fields: Dict[str, Any] = {}
    for key in keys:
        if key not in op:
            raise ValueError(f"signing dict missing field: {key}")
        fields[key] = op[key]

    return {
        "module": module,
        "version": version,
        "market_id": market_id,
        "action": action,
        "signer_pubkey": str(signer_pubkey),
        "nonce": int(nonce),
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
