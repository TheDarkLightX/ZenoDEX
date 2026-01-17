"""
Vault staking + reward distribution kernel.

This is a pure state machine intended for the functional core:
- Inputs are integers (already range-checked by the shell if desired).
- Outputs are (next_state, effects) or an error.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping


ACC_SCALE = 1_000_000


@dataclass(frozen=True)
class VaultState:
    """Vault state."""

    acc_reward_per_share: int
    last_update_acc: int
    pending_rewards: int
    reward_balance: int
    staked_lp_shares: int

    def __post_init__(self) -> None:
        if self.acc_reward_per_share < 0:
            raise ValueError("acc_reward_per_share must be non-negative")
        if self.last_update_acc < 0:
            raise ValueError("last_update_acc must be non-negative")
        if self.pending_rewards < 0:
            raise ValueError("pending_rewards must be non-negative")
        if self.reward_balance < 0:
            raise ValueError("reward_balance must be non-negative")
        if self.staked_lp_shares < 0:
            raise ValueError("staked_lp_shares must be non-negative")
        if self.acc_reward_per_share < self.last_update_acc:
            raise ValueError("acc_reward_per_share must be monotone >= last_update_acc")
        if self.pending_rewards > self.reward_balance:
            raise ValueError("pending_rewards must be <= reward_balance")


@dataclass(frozen=True)
class VaultCommand:
    tag: Literal["deposit_rewards", "harvest", "stake", "unstake"]
    args: Mapping[str, Any]


@dataclass(frozen=True)
class VaultStepResult:
    ok: bool
    state: VaultState | None = None
    effects: Mapping[str, Any] | None = None
    error: str | None = None


def init_vault_state() -> VaultState:
    return VaultState(
        acc_reward_per_share=0,
        last_update_acc=0,
        pending_rewards=0,
        reward_balance=0,
        staked_lp_shares=0,
    )


def step(state: VaultState, cmd: VaultCommand) -> VaultStepResult:
    """Execute a vault command."""
    try:
        if cmd.tag == "deposit_rewards":
            return _deposit_rewards(state, cmd.args)
        if cmd.tag == "harvest":
            return _harvest(state, cmd.args)
        if cmd.tag == "stake":
            return _stake(state, cmd.args)
        if cmd.tag == "unstake":
            return _unstake(state, cmd.args)
        return VaultStepResult(ok=False, error=f"unknown action: {cmd.tag}")
    except Exception as exc:
        return VaultStepResult(ok=False, error=str(exc))


def _deposit_rewards(state: VaultState, args: Mapping[str, Any]) -> VaultStepResult:
    amount = args.get("amount")
    if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
        return VaultStepResult(ok=False, error="invalid param amount")

    new_reward_balance = state.reward_balance + amount
    if new_reward_balance < state.reward_balance:
        return VaultStepResult(ok=False, error="overflow in reward_balance")

    if state.staked_lp_shares == 0:
        new_pending = state.pending_rewards + amount
        new_state = VaultState(
            acc_reward_per_share=state.acc_reward_per_share,
            last_update_acc=state.acc_reward_per_share,
            pending_rewards=new_pending,
            reward_balance=new_reward_balance,
            staked_lp_shares=state.staked_lp_shares,
        )
        return VaultStepResult(ok=True, state=new_state, effects={"delta_acc": 0, "harvested_reward": 0})

    total = state.pending_rewards + amount
    delta_acc = (total * ACC_SCALE) // state.staked_lp_shares
    distributed = (delta_acc * state.staked_lp_shares) // ACC_SCALE
    new_pending = total - distributed

    new_state = VaultState(
        acc_reward_per_share=state.acc_reward_per_share + delta_acc,
        last_update_acc=state.acc_reward_per_share,
        pending_rewards=new_pending,
        reward_balance=new_reward_balance,
        staked_lp_shares=state.staked_lp_shares,
    )
    return VaultStepResult(
        ok=True,
        state=new_state,
        effects={"delta_acc": new_state.acc_reward_per_share - new_state.last_update_acc, "harvested_reward": 0},
    )


def _harvest(state: VaultState, args: Mapping[str, Any]) -> VaultStepResult:
    entry_acc = args.get("entry_acc")
    if not isinstance(entry_acc, int) or isinstance(entry_acc, bool) or entry_acc < 0:
        return VaultStepResult(ok=False, error="invalid param entry_acc")
    if entry_acc > state.acc_reward_per_share:
        return VaultStepResult(ok=False, error="guard failed for harvest (entry_acc)")

    accrued_scaled = (state.acc_reward_per_share - entry_acc) * state.staked_lp_shares
    harvested = accrued_scaled // ACC_SCALE

    spendable = state.reward_balance - state.pending_rewards
    if harvested > spendable:
        return VaultStepResult(ok=False, error="guard failed for harvest (insufficient spendable)")

    new_state = VaultState(
        acc_reward_per_share=state.acc_reward_per_share,
        last_update_acc=state.acc_reward_per_share,
        pending_rewards=state.pending_rewards,
        reward_balance=state.reward_balance - harvested,
        staked_lp_shares=state.staked_lp_shares,
    )
    return VaultStepResult(
        ok=True,
        state=new_state,
        effects={"delta_acc": 0, "harvested_reward": harvested},
    )


def _stake(state: VaultState, args: Mapping[str, Any]) -> VaultStepResult:
    amount = args.get("amount")
    if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
        return VaultStepResult(ok=False, error="invalid param amount")

    new_staked = state.staked_lp_shares + amount
    if new_staked < state.staked_lp_shares:
        return VaultStepResult(ok=False, error="overflow in staked_lp_shares")

    if state.staked_lp_shares != 0 or state.pending_rewards == 0:
        new_state = VaultState(
            acc_reward_per_share=state.acc_reward_per_share,
            last_update_acc=state.acc_reward_per_share,
            pending_rewards=state.pending_rewards,
            reward_balance=state.reward_balance,
            staked_lp_shares=new_staked,
        )
        return VaultStepResult(ok=True, state=new_state, effects={"delta_acc": 0, "harvested_reward": 0})

    # First staker: distribute any pending rewards across the new stake.
    delta_acc = (state.pending_rewards * ACC_SCALE) // new_staked
    distributed = (delta_acc * new_staked) // ACC_SCALE
    new_pending = state.pending_rewards - distributed

    new_state = VaultState(
        acc_reward_per_share=state.acc_reward_per_share + delta_acc,
        last_update_acc=state.acc_reward_per_share,
        pending_rewards=new_pending,
        reward_balance=state.reward_balance,
        staked_lp_shares=new_staked,
    )
    return VaultStepResult(
        ok=True,
        state=new_state,
        effects={"delta_acc": new_state.acc_reward_per_share - new_state.last_update_acc, "harvested_reward": 0},
    )


def _unstake(state: VaultState, args: Mapping[str, Any]) -> VaultStepResult:
    amount = args.get("amount")
    if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
        return VaultStepResult(ok=False, error="invalid param amount")
    if amount > state.staked_lp_shares:
        return VaultStepResult(ok=False, error="guard failed for unstake")

    new_state = VaultState(
        acc_reward_per_share=state.acc_reward_per_share,
        last_update_acc=state.acc_reward_per_share,
        pending_rewards=state.pending_rewards,
        reward_balance=state.reward_balance,
        staked_lp_shares=state.staked_lp_shares - amount,
    )
    return VaultStepResult(ok=True, state=new_state, effects={"delta_acc": 0, "harvested_reward": 0})

