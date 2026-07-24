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
from ..state.nonces import NonceTable, validate_and_apply_intent_nonce_batch
from ..state.pools import PoolState
from ..state.state_snapshots import (
    freeze_balance_table,
    freeze_lp_table,
    freeze_nonce_table,
    freeze_optional_module_state,
    freeze_pool_mapping,
)
from .batch_clearing import (
    apply_settlement_pure,
    compute_settlement,
    is_cow_pair_netting_ordering,
    validate_settlement,
)
from .fees import FeeAccumulatorState, FeeSplitParams, FeeSplitResult, split_fee_with_dust_carry
from .oracle import OracleState
from .perps import PerpsState
from .settlement import Settlement, first_rejected_settlement_intent_error
from .settlement_strong_validator import validate_settlement_strong
from .vault import VaultState


@dataclass(frozen=True)
class DexConfig:
    """Runtime config for the core step."""

    fee_split_params: Optional[FeeSplitParams] = None
    # Promote chunked invariant-preserving greedy batch ordering by default.
    swap_ordering: str = "greedy_ab_refined"
    # Settlement acceptance gate:
    # - "legacy": conservation/nonnegativity only (not sufficient for AMM safety)
    # - "strong_replay": replay-check fills vs kernels/intents (no witness required)
    # - "strong_proof_carrying": require per-swap reserve witnesses and replay-check
    settlement_validation: str = "strong_proof_carrying"
    # Quote-bound snapshot markers are only accepted after a higher layer
    # validates and strips raw receipt transport metadata.
    allow_snapshot_bound_quote_bindings: bool = False
    # A transaction-level DEX step is accepted only when every submitted intent is
    # filled. Batch-clearing internals may represent unfillable intents as
    # REJECT fills, but the public execution boundary fails closed on them.
    reject_settlements_with_rejected_intents: bool = True
    # Replay protection is a core-boundary invariant: every public intent must
    # carry a valid nonce unless a caller deliberately enables the legacy
    # nonce-free compatibility mode for closed test harnesses.
    require_all_nonces: bool = True
    allow_legacy_nonce_free_steps: bool = False
    # Exact-in CPMM protocol-fee capture. A nonzero share removes that portion
    # of the swap fee from pool reserves and credits `protocol_fee_recipient_pubkey`.
    protocol_fee_share_bps: int = 0
    protocol_fee_recipient_pubkey: Optional[str] = None

    def requires_complete_nonce_coverage(self) -> bool:
        """Return the fail-closed nonce policy for public core step calls.

        Design by Contract:
        - Precondition: compatibility callers must set both
          `require_all_nonces=False` and `allow_legacy_nonce_free_steps=True`.
        - Invariant: the default policy rejects nonce-free intents at the core
          boundary, preventing signed-intent replay.
        - Postcondition: an ambiguous config (`require_all_nonces=False` without
          legacy opt-in) still fails closed.
        """
        if bool(self.require_all_nonces):
            return True
        return not bool(self.allow_legacy_nonce_free_steps)


@dataclass(frozen=True, slots=True)
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

    def __post_init__(self) -> None:
        """Own and seal every value reachable from committed state."""

        object.__setattr__(self, "balances", freeze_balance_table(self.balances))
        object.__setattr__(self, "pools", freeze_pool_mapping(self.pools))
        object.__setattr__(self, "lp_balances", freeze_lp_table(self.lp_balances))
        object.__setattr__(self, "nonces", freeze_nonce_table(self.nonces))

        frozen_vault = freeze_optional_module_state(self.vault)
        frozen_oracle = freeze_optional_module_state(self.oracle)
        frozen_fee_accumulator = freeze_optional_module_state(self.fee_accumulator)
        frozen_perps = freeze_optional_module_state(self.perps)
        if frozen_vault is not None and type(frozen_vault) is not VaultState:
            raise TypeError("vault must be an exact VaultState or None")
        if frozen_oracle is not None and type(frozen_oracle) is not OracleState:
            raise TypeError("oracle must be an exact OracleState or None")
        if type(frozen_fee_accumulator) is not FeeAccumulatorState:
            raise TypeError("fee_accumulator must be an exact FeeAccumulatorState")
        if frozen_perps is not None and type(frozen_perps) is not PerpsState:
            raise TypeError("perps must be an exact PerpsState or None")
        object.__setattr__(self, "vault", frozen_vault)
        object.__setattr__(self, "oracle", frozen_oracle)
        object.__setattr__(self, "fee_accumulator", frozen_fee_accumulator)
        object.__setattr__(self, "perps", frozen_perps)


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


def _validate_and_apply_settlement(
    config: DexConfig,
    state: DexState,
    intents: List[Intent],
    settlement: Settlement,
    next_nonces: NonceTable,
) -> DexStepResult:
    """Fail-closed settlement acceptance gate + pure application."""
    if config.settlement_validation == "legacy":
        ok, err = validate_settlement(
            settlement=settlement,
            pre_balances=state.balances,
            pre_pools=state.pools,
            pre_lp_balances=state.lp_balances,
        )
    else:
        allow_cow = is_cow_pair_netting_ordering(str(config.swap_ordering))
        ok, err = validate_settlement_strong(
            settlement=settlement,
            intents=intents,
            pre_balances=state.balances,
            pre_pools=state.pools,
            pre_lp_balances=state.lp_balances,
            mode=str(config.settlement_validation),
            allow_cow_netting=bool(allow_cow),
            allow_snapshot_bound_quote_bindings=bool(config.allow_snapshot_bound_quote_bindings),
            protocol_fee_share_bps=config.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=config.protocol_fee_recipient_pubkey,
        )
    if not ok:
        return DexStepResult(ok=False, error=err or "settlement invalid")

    if config.reject_settlements_with_rejected_intents:
        err = first_rejected_settlement_intent_error(settlement)
        if err is not None:
            return DexStepResult(ok=False, error=err)

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
        nonces=next_nonces,
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


def step_with_candidate_settlement(
    config: DexConfig,
    state: DexState,
    intents: List[Intent],
    *,
    candidate_settlement: Settlement,
) -> DexStepResult:
    """Verifier path: accept an externally proposed settlement (proof-carrying friendly)."""
    try:
        ok, err, next_nonces = validate_and_apply_intent_nonce_batch(
            nonces=state.nonces,
            intents=intents,
            require_all_nonces=config.requires_complete_nonce_coverage(),
        )
        if not ok:
            return DexStepResult(ok=False, error=err or "nonce policy rejected")
        return _validate_and_apply_settlement(
            config,
            state,
            intents,
            candidate_settlement,
            next_nonces or state.nonces,
        )
    except Exception as exc:
        return DexStepResult(ok=False, error=str(exc))


def step(config: DexConfig, state: DexState, intents: List[Intent]) -> DexStepResult:
    """
    Execute one DEX step over a batch of intents.

    This function is pure: it returns a new DexState and structured effects.
    """
    try:
        ok, err, next_nonces = validate_and_apply_intent_nonce_batch(
            nonces=state.nonces,
            intents=intents,
            require_all_nonces=config.requires_complete_nonce_coverage(),
        )
        if not ok:
            return DexStepResult(ok=False, error=err or "nonce policy rejected")
        settlement = compute_settlement(
            intents=intents,
            pools=state.pools,
            balances=state.balances,
            lp_balances=state.lp_balances,
            swap_ordering=str(config.swap_ordering),
            protocol_fee_share_bps=config.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=config.protocol_fee_recipient_pubkey,
        )
        return _validate_and_apply_settlement(
            config,
            state,
            intents,
            settlement,
            next_nonces or state.nonces,
        )
    except Exception as exc:
        return DexStepResult(ok=False, error=str(exc))
