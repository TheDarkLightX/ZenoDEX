"""Proof-mining handlers for the DEX dispatch registry."""

from __future__ import annotations

import os
from typing import Any, Mapping

from src.integration.api_server_dex_dispatch import (
    DexRequestContext,
    DexResponse,
    _register,
)
from src.integration.proof_mining_claimability import evaluate_proof_mining_claimability

BOUNDARY_DOMAIN_ERRORS: tuple[type[Exception], ...] = (
    TypeError,
    ValueError,
    ArithmeticError,
)


def _handle_proof_mining_status(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    claim_artifact = obj.get("claim")
    chain_balances = obj.get("chain_balances", {})
    tx_sender_pubkey = str(obj.get("tx_sender_pubkey", ""))
    expected_proposal_hash = str(obj.get("expected_proposal_hash", ""))
    proof_mining_context = obj.get("proof_mining_context")
    app_state_json = obj.get("app_state_json", "")
    if not isinstance(claim_artifact, dict):
        return 400, {"ok": False, "error": "bad_claim"}
    if not isinstance(chain_balances, dict):
        return 400, {"ok": False, "error": "bad_chain_balances"}
    if proof_mining_context is not None and not isinstance(proof_mining_context, dict):
        return 400, {"ok": False, "error": "bad_proof_mining_context"}
    if not isinstance(app_state_json, str):
        return 400, {"ok": False, "error": "bad_app_state_json"}
    if not tx_sender_pubkey:
        return 400, {"ok": False, "error": "missing_tx_sender_pubkey"}
    if not expected_proposal_hash:
        return 400, {"ok": False, "error": "missing_expected_proposal_hash"}
    try:
        reward_pool_pubkey = (
            os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip()
            or str(obj.get("reward_pool_pubkey", "")).strip()
            or None
        )
        reward_asset_raw = obj.get("reward_asset_id")
        reward_asset_id = reward_asset_raw.strip() if isinstance(reward_asset_raw, str) else None
        status = evaluate_proof_mining_claimability(
            reward_pool_pubkey=reward_pool_pubkey,
            reward_asset_id=reward_asset_id or None,
            app_state_json=app_state_json,
            chain_balances=chain_balances,
            claim_artifact=claim_artifact,
            tx_sender_pubkey=tx_sender_pubkey,
            expected_proposal_hash=expected_proposal_hash,
            proof_mining_context_obj=proof_mining_context,
        )
        return 200, {"ok": True, "status": status.to_public_dict()}
    except BOUNDARY_DOMAIN_ERRORS:
        return 400, {"ok": False, "error": "proof_mining_status_error", "details": "request failed"}


def register_proof_mining_handlers() -> None:
    _register(
        "/api/dex/proof_mining_status",
        _handle_proof_mining_status,
        default_error_code="proof_mining_status_error",
    )


register_proof_mining_handlers()
