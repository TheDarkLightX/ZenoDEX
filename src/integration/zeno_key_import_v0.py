"""Tau-like key import helpers for ZenoKeyManager v0."""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_key_manager import KeyRef, TauNetKeyImportEvidence, import_tau_net_key_ref_with_evidence
from src.integration.zeno_ledger_v0 import hash_v0


TAU_IMPORT_CHALLENGE_SCHEMA_V0 = "zenodex/zeno_key_manager/tau_import_challenge/v0"
TAU_IMPORT_RECEIPT_SCHEMA_V0 = "zenodex/zeno_key_manager/tau_import_receipt/v0"


def build_tau_import_challenge_v0(
    *,
    key_id: str,
    tau_chain_id: str,
    policy_hash: str,
    nonce: str,
) -> dict[str, Any]:
    body = {
        "schema": TAU_IMPORT_CHALLENGE_SCHEMA_V0,
        "key_id": key_id,
        "tau_chain_id": tau_chain_id,
        "policy_hash": policy_hash,
        "nonce": nonce,
    }
    if not all(isinstance(body[name], str) and body[name] for name in ("key_id", "tau_chain_id", "policy_hash", "nonce")):
        raise ValueError("challenge fields must be non-empty strings")
    return {**body, "challenge_hash": hash_v0("zeno_tau_import_challenge_v0", body)}


def import_tau_bls_key_descriptor_v0(
    *,
    evidence: TauNetKeyImportEvidence,
    current_epoch: int,
    metadata: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    key_ref = import_tau_net_key_ref_with_evidence(
        evidence=evidence,
        current_epoch=current_epoch,
        metadata=metadata,
    )
    body = {
        "schema": TAU_IMPORT_RECEIPT_SCHEMA_V0,
        "key_ref": key_ref.public_dict(),
        "evidence": evidence.public_dict(),
        "current_epoch": current_epoch,
        "raw_private_key_imported": False,
    }
    return {**body, "receipt_hash": hash_v0("zeno_tau_import_receipt_v0", body)}


def key_ref_from_tau_import_receipt_v0(receipt: Mapping[str, Any]) -> KeyRef:
    if receipt.get("schema") != TAU_IMPORT_RECEIPT_SCHEMA_V0:
        raise ValueError("tau import receipt schema mismatch")
    if receipt.get("raw_private_key_imported") is not False:
        raise ValueError("tau import receipt must not import raw private keys")
    return KeyRef.from_public_dict(receipt.get("key_ref"))
