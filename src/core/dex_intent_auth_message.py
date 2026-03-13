from __future__ import annotations

import hashlib
from enum import Enum
from typing import Any, Dict, Mapping

from ..state.canonical import canonical_json_bytes, domain_sep_bytes
from ..state.intents import Intent


_DEX_INTENT_COMMON_KEYS = {"module", "version", "kind", "intent_id", "sender_pubkey", "deadline", "salt", "fields"}


def _normalize_intent_kind(kind: Any) -> Any:
    if isinstance(kind, Enum):
        kind = kind.value
    if isinstance(kind, str):
        return kind.lower()
    return kind


def build_dex_intent_signing_dict_v1(intent: Intent | Mapping[str, Any]) -> Dict[str, Any]:
    """Build the canonical signing dict for a DEX intent."""
    if isinstance(intent, Intent):
        fields = intent.fields or {}
        if not isinstance(fields, dict):
            raise TypeError("intent.fields must be a dict")
        fields = dict(fields)
        signing_dict: Dict[str, Any] = {
            "module": intent.module,
            "version": intent.version,
            "kind": _normalize_intent_kind(intent.kind),
            "intent_id": intent.intent_id,
            "sender_pubkey": intent.sender_pubkey,
            "deadline": intent.deadline,
            "fields": fields,
        }
        if intent.salt is not None:
            signing_dict["salt"] = intent.salt
        return signing_dict

    if not isinstance(intent, Mapping):
        raise TypeError("intent must be an Intent or mapping")

    explicit_fields = intent.get("fields")
    if explicit_fields is None:
        fields = {k: v for k, v in dict(intent).items() if k not in _DEX_INTENT_COMMON_KEYS and k != "signature"}
    else:
        if not isinstance(explicit_fields, Mapping):
            raise TypeError("intent.fields must be a mapping when present")
        fields = dict(explicit_fields)

    signing_dict = {
        "module": intent.get("module"),
        "version": intent.get("version"),
        "kind": _normalize_intent_kind(intent.get("kind")),
        "intent_id": intent.get("intent_id"),
        "sender_pubkey": intent.get("sender_pubkey"),
        "deadline": intent.get("deadline"),
        "fields": fields,
    }
    salt = intent.get("salt")
    if salt is not None:
        signing_dict["salt"] = salt
    return signing_dict


def build_dex_intent_auth_message_v1(intent: Intent | Mapping[str, Any], *, chain_id: str) -> bytes:
    """Build the domain-separated message bytes for DEX intent authorization."""
    if not isinstance(chain_id, str) or not chain_id:
        raise ValueError("chain_id must be a non-empty string")
    signing_payload = canonical_json_bytes(build_dex_intent_signing_dict_v1(intent))
    return domain_sep_bytes(f"dex_intent_sig:{chain_id}", version=1) + signing_payload


def hash_dex_intent_auth_message_v1(intent: Intent | Mapping[str, Any], *, chain_id: str) -> bytes:
    """Hash the canonical DEX intent auth message used by both engine and client."""
    return hashlib.sha256(build_dex_intent_auth_message_v1(intent, chain_id=chain_id)).digest()
