# [TESTER] v1

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any


def _import_kernel(module_name: str, rel_path: str) -> Any:
    try:
        return __import__(module_name, fromlist=["*"])
    except ModuleNotFoundError:
        root = Path(__file__).resolve().parents[2]
        abs_path = root / rel_path
        spec = importlib.util.spec_from_file_location(module_name, abs_path)
        assert spec and spec.loader, f"Could not load spec for {module_name} from {abs_path}"
        module = importlib.util.module_from_spec(spec)
        sys.modules[module_name] = module
        spec.loader.exec_module(module)
        return module


cpmm = _import_kernel("generated.cpmm_python.cpmm_swap_ref", "generated/cpmm_python/cpmm_swap_ref.py")
lp = _import_kernel("generated.liquidity_python.liquidity_pool_ref", "generated/liquidity_python/liquidity_pool_ref.py")
vault = _import_kernel("generated.vault_python.vault_manager_ref", "generated/vault_python/vault_manager_ref.py")

try:
    from src.core.nonce import Nonce  # type: ignore[attr-defined]
except Exception:

    class Nonce:
        def __init__(self, start: int = 0):
            self._value = start

        def next(self) -> int:
            self._value += 1
            return self._value


def _split_fee_60_20_20(total_fee: int) -> tuple[int, int, int]:
    lp_fee = (total_fee * 60) // 100
    vault_fee = (total_fee * 20) // 100
    treasury_fee = total_fee - lp_fee - vault_fee
    return lp_fee, vault_fee, treasury_fee


def test_full_lifecycle() -> None:
    # Init all states
    cpmm_state = cpmm.init_state()
    lp_state = lp.init_state()
    vault_state = vault.init_state()

    ok, failed = cpmm.check_invariants(cpmm_state)
    assert ok, failed
    ok, failed = lp.check_invariants(lp_state)
    assert ok, failed
    ok, failed = vault.check_invariants(vault_state)
    assert ok, failed

    nonce = Nonce()
    _intent_nonce = nonce.next()

    # Swap: User swaps X for Y (Validation: CPMM)
    amount_in_x = 10
    pre_swap = cpmm_state
    swap_res = cpmm.step(
        cpmm_state,
        cpmm.Command(tag="swap_x_for_y", args={"amount_in_x": amount_in_x, "min_amount_out": 0}),
    )
    assert swap_res.ok, swap_res.error
    assert swap_res.state is not None
    assert swap_res.effects is not None
    cpmm_state = swap_res.state

    amount_out_y = int(swap_res.effects["amount_out"])
    assert cpmm_state.reserve_x == pre_swap.reserve_x + amount_in_x
    assert cpmm_state.reserve_y == pre_swap.reserve_y - amount_out_y

    # Fee: Calculate fee (mock logic based on fee_distribution_v1.tau: 60/20/20).
    total_fee = amount_in_x  # mock fee sizing for deterministic integration test
    lp_fee, vault_fee, treasury_fee = _split_fee_60_20_20(total_fee)
    assert lp_fee + vault_fee + treasury_fee == total_fee
    assert vault_fee > 0

    # Liquidity: User adds liquidity (Validation: LP)
    lp_state = lp.State(
        reserve_a=cpmm_state.reserve_x,
        reserve_a_before=cpmm_state.reserve_x,
        reserve_b=cpmm_state.reserve_y,
        reserve_b_before=cpmm_state.reserve_y,
        total_lp_shares=lp_state.total_lp_shares,
        total_lp_shares_before=lp_state.total_lp_shares,
    )
    ok, failed = lp.check_invariants(lp_state)
    assert ok, failed

    amount_a_in = 5
    amount_b_in = 3
    pre_lp = lp_state
    add_res = lp.step(lp_state, lp.Command(tag="add_liquidity", args={"amount_a_in": amount_a_in, "amount_b_in": amount_b_in}))
    assert add_res.ok, add_res.error
    assert add_res.state is not None
    assert add_res.effects is not None
    lp_state = add_res.state

    lp_minted = int(add_res.effects["lp_shares_minted"])
    assert lp_state.reserve_a == pre_lp.reserve_a + amount_a_in
    assert lp_state.reserve_b == pre_lp.reserve_b + amount_b_in
    assert lp_minted >= 1

    # Keep CPMM reserves consistent with LP reserves after liquidity update.
    cpmm_state = cpmm.State(
        fee_bps=cpmm_state.fee_bps,
        reserve_x=lp_state.reserve_a,
        reserve_x_before=lp_state.reserve_a,
        reserve_y=lp_state.reserve_b,
        reserve_y_before=lp_state.reserve_b,
    )
    ok, failed = cpmm.check_invariants(cpmm_state)
    assert ok, failed

    # Stake: User stakes LP tokens (Validation: Vault)
    stake_amount = lp_minted
    stake_res = vault.step(vault_state, vault.Command(tag="stake", args={"amount": stake_amount}))
    assert stake_res.ok, stake_res.error
    assert stake_res.state is not None
    vault_state = stake_res.state

    # Assertions: LP shares minted = staked.
    assert vault_state.staked_lp_shares == stake_amount

    # Rewards: Distribute simulated fees to Vault.
    entry_acc = vault_state.acc_reward_per_share
    deposit_res = vault.step(vault_state, vault.Command(tag="deposit_rewards", args={"amount": vault_fee}))
    assert deposit_res.ok, deposit_res.error
    assert deposit_res.state is not None
    vault_state = deposit_res.state

    # Assertions: Vault rewards accumulator increases.
    assert vault_state.acc_reward_per_share > entry_acc

    # Harvest: User harvests.
    harvest_res = vault.step(vault_state, vault.Command(tag="harvest", args={"entry_acc": entry_acc}))
    assert harvest_res.ok, harvest_res.error
    assert harvest_res.state is not None
    assert harvest_res.effects is not None
    vault_state = harvest_res.state

    harvested = int(harvest_res.effects["harvested_reward"])
    assert harvested > 0
