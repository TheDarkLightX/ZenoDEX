"""Proof-mining handlers for the DEX dispatch registry."""

from __future__ import annotations

import os
from typing import Any, Mapping

from src.integration import dex_dispatch_proof_mining_snapshots as _snapshot_helpers
from src.integration.api_server_dex_dispatch import (
    DexRequestContext,
    DexResponse,
    _register,
)
from src.integration.dex_dispatch_proof_mining_reward import (
    canonical_pubkey_48,
    proof_mining_reward_config,
)
from src.integration.dex_dispatch_proof_mining_templates import (
    BOUNDARY_DOMAIN_ERRORS,
    _template_block_timestamp,
    _template_faucet_mint,
    _template_intent,
    _template_proof_bundle,
    _template_state,
    _template_state_with_faucet,
    _template_state_with_native_reward_pool,
    _template_success_body,
    _TemplateAssembly,
    _TemplateReject,
)
from src.integration.proof_mining_claimability import evaluate_proof_mining_claimability

urllib = _snapshot_helpers.urllib
_load_latest_writer_snapshot_for_template = _snapshot_helpers._load_latest_writer_snapshot_for_template
_load_latest_writer_snapshot_from_file_for_template = (
    _snapshot_helpers._load_latest_writer_snapshot_from_file_for_template
)
_load_latest_writer_snapshot_from_url_for_template = (
    _snapshot_helpers._load_latest_writer_snapshot_from_url_for_template
)


def _handle_proof_mining_payout_template(obj: Mapping[str, Any], ctx: DexRequestContext) -> DexResponse:
    if os.environ.get("ZENODEX_ENV", "").strip().lower() not in {"local", "test", "local-testnet", ""}:
        return 403, {"ok": False, "error": "local_testnet_only"}
    try:
        sender = canonical_pubkey_48(obj.get("tx_sender_pubkey"), name="tx_sender_pubkey")
        template_intent = _template_intent(obj, sender=sender)
        chain_id = str(obj.get("chain_id") or os.environ.get("TAU_DEX_CHAIN_ID") or "zeno-ledger-localtest-v0")
        try:
            tx_block_timestamp = _template_block_timestamp(obj, template_intent.intent)
        except ValueError:
            return 400, {"ok": False, "error": "bad_block_timestamp"}

        state = _template_state(obj, ctx)
        faucet_mint = _template_faucet_mint(obj)
        reward = proof_mining_reward_config(obj, chain_id=chain_id, state=state)
        if reward.pool_before <= 0:
            return 409, {
                "ok": False,
                "error": "reward_pool_unfunded",
                "reward_pool_pubkey": reward.pool_pubkey,
                "reward_asset_id": reward.asset_id,
            }
        proof_state = _template_state_with_faucet(state, faucet_mint, sender=sender)
        proof_state = _template_state_with_native_reward_pool(proof_state, reward)
        bundle = _template_proof_bundle(
            proof_state=proof_state,
            template_intent=template_intent,
            tx_block_timestamp=tx_block_timestamp,
            chain_id=chain_id,
        )

        assembly = _TemplateAssembly(
            obj=obj,
            sender=sender,
            chain_id=chain_id,
            tx_block_timestamp=tx_block_timestamp,
            template_intent=template_intent,
            faucet_mint=faucet_mint,
            bundle=bundle,
            reward=reward,
        )
        return 200, dict(_template_success_body(assembly))
    except _TemplateReject as reject:
        return reject.response
    except BOUNDARY_DOMAIN_ERRORS as exc:
        return 400, {"ok": False, "error": "proof_mining_payout_template_error", "details": str(exc)}


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
        "/api/dex/proof_mining_payout_template",
        _handle_proof_mining_payout_template,
        default_error_code="proof_mining_payout_template_error",
    )
    _register(
        "/api/dex/proof_mining_status",
        _handle_proof_mining_status,
        default_error_code="proof_mining_status_error",
    )


register_proof_mining_handlers()
