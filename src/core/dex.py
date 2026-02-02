"""
DEX step orchestration (functional core).

This module wires the verified kernels into a single pure step:
- Compute a settlement from intents + pre-state
- Validate the settlement (fail-closed)
- Apply it to produce (next_state, effects)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

from ..state.balances import BalanceTable
from ..state.intents import Intent
from ..state.lp import LPTable
from ..state.nonces import NonceTable
from ..state.pools import PoolState
from .batch_clearing import compute_settlement, validate_settlement, apply_settlement_pure
from .fees import FeeAccumulatorState, FeeSplitParams, FeeSplitResult, split_fee_with_dust_carry
from .oracle import OracleState
from .perps import PerpsState
from .settlement import Settlement
from .vault import VaultState


@dataclass(frozen=True)
class DexConfig:
    """Runtime config for the core step."""

    fee_split_params: Optional[FeeSplitParams] = None


@dataclass(frozen=True)
class DexState:
    balances: BalanceTable
    pools: Dict[str, PoolState]
    lp_balances: LPTable
    nonces: NonceTable = field(default_factory=NonceTable)

    # Optional modules (can be unused in early deployments).
    vault: Optional[VaultState] = None
    oracle: Optional[OracleState] = None
    fee_accumulator: FeeAccumulatorState = FeeAccumulatorState()
    perps: Optional[PerpsState] = None


@dataclass(frozen=True)
class DexEffects:
    settlement: Settlement
    total_swap_fees: int
    fee_split: Optional[FeeSplitResult] = None


@dataclass(frozen=True)
class DexStepResult:
    ok: bool
    state: Optional[DexState] = None
    effects: Optional[Dict[str, Any]] = None
    error: Optional[str] = None


def step(config: DexConfig, state: DexState, intents: List[Intent]) -> DexStepResult:
    """
    Execute one DEX step over a batch of intents.

    This function is pure: it returns a new DexState and structured effects.
    """
    try:
        settlement = compute_settlement(
            intents=intents,
            pools=state.pools,
            balances=state.balances,
            lp_balances=state.lp_balances,
        )
        ok, err = validate_settlement(
            settlement=settlement,
            pre_balances=state.balances,
            pre_pools=state.pools,
            pre_lp_balances=state.lp_balances,
        )
        if not ok:
            return DexStepResult(ok=False, error=err or "settlement invalid")

        next_balances, next_pools, next_lp = apply_settlement_pure(
            settlement=settlement,
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
        )

        total_fees = sum(int(fill.fee_paid or 0) for fill in settlement.fills)

        fee_split = None
        next_fee_state = state.fee_accumulator
        if config.fee_split_params is not None:
            fee_split, next_fee_state = split_fee_with_dust_carry(
                fee_amount=total_fees,
                params=config.fee_split_params,
                state=state.fee_accumulator,
            )

        next_state = DexState(
            balances=next_balances,
            pools=next_pools,
            lp_balances=next_lp,
            nonces=state.nonces,
            vault=state.vault,
            oracle=state.oracle,
            fee_accumulator=next_fee_state,
            perps=state.perps,
        )

        return DexStepResult(
            ok=True,
            state=next_state,
            effects={
                "settlement": settlement,
                "total_swap_fees": total_fees,
                "fee_split": fee_split,
            },
        )
    except Exception as exc:
        return DexStepResult(ok=False, error=str(exc))
