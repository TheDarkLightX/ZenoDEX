from __future__ import annotations

from types import SimpleNamespace

import pytest

from src.integration.dex_dispatch_proof_mining_reward import proof_mining_reward_config
from src.state.balances import BalanceTable

POOL_PUBKEY = "0x" + "11" * 48
REWARD_ASSET = "0x" + "22" * 32


def _state() -> SimpleNamespace:
    balances = BalanceTable()
    balances.set(POOL_PUBKEY, REWARD_ASSET, 1_000)
    return SimpleNamespace(balances=balances)


@pytest.mark.parametrize(
    "field",
    ("base_reward", "epoch", "proposal_slot", "prover_id", "improvement_u64"),
)
def test_reward_config_rejects_bool_numeric_fields(field: str) -> None:
    payload = {
        "reward_pool_pubkey": POOL_PUBKEY,
        "reward_asset_id": REWARD_ASSET,
        "base_reward": 8,
        "epoch": 1,
        "proposal_slot": 0,
        "prover_id": 1,
        "improvement_u64": 1,
    }
    payload[field] = True

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        proof_mining_reward_config(payload, chain_id="test-chain", state=_state())


@pytest.mark.parametrize(
    "field",
    ("base_reward", "epoch", "proposal_slot", "prover_id", "improvement_u64"),
)
def test_reward_config_rejects_numeric_string_fields(field: str) -> None:
    payload = {
        "reward_pool_pubkey": POOL_PUBKEY,
        "reward_asset_id": REWARD_ASSET,
        "base_reward": 8,
        "epoch": 1,
        "proposal_slot": 0,
        "prover_id": 1,
        "improvement_u64": 1,
    }
    payload[field] = "1"

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        proof_mining_reward_config(payload, chain_id="test-chain", state=_state())
