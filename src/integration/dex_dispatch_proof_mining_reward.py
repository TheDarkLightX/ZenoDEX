"""Reward-pool parsing for proof-mining dispatch helpers."""

from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import hash_v0


@dataclass(frozen=True)
class ProofMiningRewardConfig:
    pool_pubkey: str
    asset_id: str
    pool_before: int
    base_reward: int
    epoch: int
    proposal_slot: int
    prover_id: int
    improvement_u64: int


def canonical_asset_id(value: Any, *, name: str) -> str:
    text = str(value or "").strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if len(text) != 64 or any(ch not in "0123456789abcdef" for ch in text):
        raise ValueError(f"{name} must be a canonical 32-byte hex asset")
    return "0x" + text


def canonical_pubkey_48(value: Any, *, name: str) -> str:
    text = str(value or "").strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if len(text) != 96 or any(ch not in "0123456789abcdef" for ch in text):
        raise ValueError(f"{name} must be a canonical 48-byte hex pubkey")
    return "0x" + text


def _coerced_int(value: Any, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{name} must be an int")
    return int(value)


def proof_mining_reward_config(
    obj: Mapping[str, Any],
    *,
    chain_id: str,
    state: Any,
) -> ProofMiningRewardConfig:
    reward_pool = os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip()
    if not reward_pool:
        reward_pool = str(obj.get("reward_pool_pubkey", "")).strip()
    reward_pool = canonical_pubkey_48(reward_pool, name="reward_pool_pubkey")

    reward_asset = obj.get("reward_asset_id")
    if reward_asset is None:
        reward_asset = os.environ.get("TAU_DEX_PROOF_MINING_REWARD_ASSET_ID", "").strip()
    if not reward_asset:
        token_symbol = os.environ.get("TAU_DEX_TOKEN_SYMBOL", "ZDEX").strip() or "ZDEX"
        reward_asset = hash_v0("testnet_bundle_token_asset", {"chain_id": chain_id, "symbol": token_symbol})
    reward_asset = canonical_asset_id(reward_asset, name="reward_asset_id")

    return ProofMiningRewardConfig(
        pool_pubkey=reward_pool,
        asset_id=reward_asset,
        pool_before=int(state.balances.get(reward_pool, reward_asset)),
        base_reward=_coerced_int(obj.get("base_reward", 8), name="base_reward"),
        epoch=_coerced_int(obj.get("epoch", 1), name="epoch"),
        proposal_slot=_coerced_int(obj.get("proposal_slot", 0), name="proposal_slot"),
        prover_id=_coerced_int(obj.get("prover_id", 1), name="prover_id"),
        improvement_u64=_coerced_int(obj.get("improvement_u64", 1), name="improvement_u64"),
    )
