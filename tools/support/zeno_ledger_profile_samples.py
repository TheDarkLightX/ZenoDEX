"""ZenoLedger profile constructors for repo-local tools and tests only."""

from __future__ import annotations

from typing import Any

from src.integration.zeno_ledger_profile import (
    DEPLOYMENT_MODE_LOCAL_SANDBOX_V0,
    DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
    DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
    TOKEN_SCOPE_NONE_V0,
    TOKEN_SCOPE_TAU_NET_EXCLUSIVE_V0,
    TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0,
    make_zeno_ledger_profile_v0,
)
from src.integration.zeno_ledger_v0 import ZERO_ROOT_V0


def sample_local_sandbox_profile_v0(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
) -> dict[str, Any]:
    return make_zeno_ledger_profile_v0(
        profile_name="ZenoLedger local sandbox",
        deployment_mode=DEPLOYMENT_MODE_LOCAL_SANDBOX_V0,
        chain_id=chain_id,
        accepted_config_digests=[config_digest],
        accepted_sequencer_set_hashes=[sequencer_set_hash],
        proof_required=False,
        body_required=True,
        tau_net_adapter_required=False,
        token_policy={
            "token_symbol": "",
            "token_asset_id": ZERO_ROOT_V0,
            "issuance_scope": TOKEN_SCOPE_NONE_V0,
            "tau_net_exclusive": False,
            "external_minting_allowed": False,
            "non_tau_deployment_allowed": False,
        },
        bridge_policy={
            "bridge_value_enabled": False,
            "requires_tau_checkpoint": False,
            "requires_proof_journal": False,
        },
    )


def sample_zeno_sovereign_testnet_profile_v0(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
    token_symbol: str,
    token_asset_id: str,
    proof_required: bool = False,
) -> dict[str, Any]:
    return make_zeno_ledger_profile_v0(
        profile_name="ZenoLedger sovereign testnet",
        deployment_mode=DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
        chain_id=chain_id,
        accepted_config_digests=[config_digest],
        accepted_sequencer_set_hashes=[sequencer_set_hash],
        proof_required=proof_required,
        body_required=True,
        tau_net_adapter_required=False,
        token_policy={
            "token_symbol": token_symbol,
            "token_asset_id": token_asset_id,
            "issuance_scope": TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0,
            "tau_net_exclusive": False,
            "external_minting_allowed": False,
            "non_tau_deployment_allowed": True,
        },
        bridge_policy={
            "bridge_value_enabled": False,
            "requires_tau_checkpoint": False,
            "requires_proof_journal": proof_required,
        },
    )


def sample_tau_exclusive_release_profile_v0(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
    token_symbol: str,
    token_asset_id: str,
) -> dict[str, Any]:
    return make_zeno_ledger_profile_v0(
        profile_name="ZenoLedger Tau-exclusive release",
        deployment_mode=DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
        chain_id=chain_id,
        accepted_config_digests=[config_digest],
        accepted_sequencer_set_hashes=[sequencer_set_hash],
        proof_required=True,
        body_required=True,
        tau_net_adapter_required=True,
        token_policy={
            "token_symbol": token_symbol,
            "token_asset_id": token_asset_id,
            "issuance_scope": TOKEN_SCOPE_TAU_NET_EXCLUSIVE_V0,
            "tau_net_exclusive": True,
            "external_minting_allowed": False,
            "non_tau_deployment_allowed": False,
        },
        bridge_policy={
            "bridge_value_enabled": True,
            "requires_tau_checkpoint": True,
            "requires_proof_journal": True,
        },
    )
