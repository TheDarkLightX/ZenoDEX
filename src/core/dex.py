"""
DEX step orchestration (functional core).

This module wires the verified kernels into a single pure step:
- Compute a settlement from intents + pre-state
- Validate the settlement (fail-closed)
- Apply it to produce (next_state, effects)

Ownership contract:
- ``DexState`` admits mutable builders (``BalanceTable``, ``PoolState`` dicts,
  ``LPTable``, ``NonceTable``) but stores only owned immutable snapshots, so a
  committed table cannot be changed through its builder's aliases. Optional
  modules have separate ownership contracts; PerpsState is not yet immutable.
- ``DexEffects`` is the owned immutable effects value returned by a step; its
  settlement graph is a ``SettlementSnapshot``.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from dataclasses import dataclass, field
from typing import ClassVar, List, Optional

from ..state.balances import BalanceSnapshot, BalanceTable, snapshot_balances
from ..state.intents import Intent
from ..state.lp import LPSnapshot, LPTable, snapshot_lp_table
from ..state.nonces import (
    NonceSnapshot,
    NonceTable,
    snapshot_nonces,
    validate_and_apply_intent_nonce_batch,
)
from ..state.pools import (
    PoolSnapshot,
    PoolState,
    PoolTableSnapshot,
    snapshot_pool_table,
)
from .batch_clearing import apply_settlement_pure, compute_settlement, validate_settlement
from .domain_limits import is_strict_int
from .fees import FeeAccumulatorState, FeeSplitParams, FeeSplitResult, split_fee_with_dust_carry
from .oracle import OracleState
from .perps import PerpsState
from .settlement import FillAction, Settlement, SettlementSnapshot, snapshot_settlement
from .settlement_fill_fields import read_optional_non_negative_fill_int
from .settlement_strong_validator import validate_settlement_strong
from .vault import VaultState

_FAIL_CLOSED_STEP_ERRORS = (
    TypeError,
    ValueError,
    ArithmeticError,
    LookupError,
    AttributeError,
    RuntimeError,
    AssertionError,
)


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
    # Exact-in CPMM protocol-fee capture. A nonzero share removes that portion
    # of the swap fee from pool reserves and credits `protocol_fee_recipient_pubkey`.
    protocol_fee_share_bps: int = 0
    protocol_fee_recipient_pubkey: Optional[str] = None


@dataclass(frozen=True)
class DexState:
    """
    Committed DEX state.

    Constructor arguments may be mutable builders; ``__post_init__`` converts
    every table into an owned immutable snapshot (``BalanceSnapshot``,
    ``PoolTableSnapshot`` of ``PoolSnapshot`` values, ``LPSnapshot``,
    ``NonceSnapshot``). Callers that need a mutable working copy use the
    snapshots' ``to_table()`` helpers; commits go through ``DexState(...)`` or
    ``dataclasses.replace``.
    """

    balances: BalanceTable | BalanceSnapshot
    pools: Mapping[str, PoolState | PoolSnapshot] | PoolTableSnapshot
    lp_balances: LPTable | LPSnapshot
    nonces: NonceTable | NonceSnapshot = field(default_factory=NonceTable)

    # Optional modules (can be unused in early deployments).
    vault: Optional[VaultState] = None
    oracle: Optional[OracleState] = None
    fee_accumulator: FeeAccumulatorState = FeeAccumulatorState()
    perps: Optional[PerpsState] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "balances", snapshot_balances(self.balances))
        object.__setattr__(self, "pools", snapshot_pool_table(self.pools))
        object.__setattr__(self, "lp_balances", snapshot_lp_table(self.lp_balances))
        object.__setattr__(self, "nonces", snapshot_nonces(self.nonces))


@dataclass(frozen=True, slots=True)
class DexEffects(Mapping[str, object]):
    """
    Owned immutable effects of an accepted DEX step.

    Closed key set: ``settlement`` (a ``SettlementSnapshot``),
    ``total_swap_fees`` and ``fee_split``. The mapping interface keeps
    ``effects["settlement"]`` readers working; attribute access is typed.
    """

    settlement: Settlement | SettlementSnapshot
    total_swap_fees: int
    fee_split: Optional[FeeSplitResult] = None

    _KEYS: ClassVar[tuple[str, ...]] = ("settlement", "total_swap_fees", "fee_split")

    def __post_init__(self) -> None:
        object.__setattr__(self, "settlement", snapshot_settlement(self.settlement))
        if not is_strict_int(self.total_swap_fees) or self.total_swap_fees < 0:
            raise TypeError("total_swap_fees must be a non-negative int")
        object.__setattr__(self, "total_swap_fees", int(self.total_swap_fees))
        if self.fee_split is not None and type(self.fee_split) is not FeeSplitResult:
            raise TypeError("fee_split must be a FeeSplitResult or None")
        if self.fee_split is not None:
            split = self.fee_split
            object.__setattr__(self, "fee_split", FeeSplitResult(
                buyback_amount=int(split.buyback_amount),
                treasury_amount=int(split.treasury_amount),
                rewards_amount=int(split.rewards_amount),
                dust_carried=int(split.dust_carried),
            ))

    def __getitem__(self, key: str) -> object:
        if key in self._KEYS:
            return getattr(self, key)
        raise KeyError(key)

    def __iter__(self) -> Iterator[str]:
        return iter(self._KEYS)

    def __len__(self) -> int:
        return len(self._KEYS)


@dataclass(frozen=True)
class DexStepResult:
    ok: bool
    state: Optional[DexState] = None
    effects: Optional[DexEffects] = None
    error: Optional[str] = None

    def __post_init__(self) -> None:
        if self.state is not None and type(self.state) is not DexState:
            raise TypeError("state must be a DexState or None")
        if self.effects is not None and type(self.effects) is not DexEffects:
            raise TypeError("effects must be a DexEffects or None")


def _validate_and_apply_settlement(
    config: DexConfig,
    state: DexState,
    intents: List[Intent],
    settlement: Settlement,
    next_nonces: NonceTable | NonceSnapshot,
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
        allow_cow = str(config.swap_ordering) == "cow_pair_netting_v1"
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
    reject_error = reject_settlement_public_boundary_error(config, settlement)
    if reject_error is not None:
        return DexStepResult(ok=False, error=reject_error)

    next_balances, next_pools, next_lp = apply_settlement_pure(
        settlement=settlement,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
    )

    total_fees = _sum_settlement_swap_fees(settlement)

    fee_split = None
    next_fee_state = state.fee_accumulator
    if config.fee_split_params is not None:
        fee_split, next_fee_state = split_fee_with_dust_carry(
            fee_amount=total_fees,
            params=config.fee_split_params,
            state=state.fee_accumulator,
        )

    # The owned effects value is built before the next state is committed so a
    # malformed settlement graph rejects the whole step (pre-state unchanged).
    effects = DexEffects(
        settlement=settlement,
        total_swap_fees=total_fees,
        fee_split=fee_split,
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

    return DexStepResult(ok=True, state=next_state, effects=effects)


def reject_settlement_public_boundary_error(
    config: DexConfig,
    settlement: Settlement,
) -> Optional[str]:
    if not config.reject_settlements_with_rejected_intents:
        return None
    for intent_id, action in settlement.included_intents:
        if action == FillAction.REJECT:
            return (
                "settlement contains rejected intent at public DEX boundary: "
                f"{intent_id}"
            )
    for fill in settlement.fills:
        if fill.action == FillAction.REJECT:
            return (
                "settlement contains rejected fill at public DEX boundary: "
                f"{fill.intent_id}"
            )
    return None


def _sum_settlement_swap_fees(settlement: Settlement) -> int:
    total = 0
    for fill in settlement.fills:
        fee_paid, err = read_optional_non_negative_fill_int(
            fill.fee_paid,
            operation="SWAP",
            field_name="fee_paid",
            intent_id=fill.intent_id,
        )
        if err is not None:
            raise TypeError(err)
        total += int(fee_paid)
    return total


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
            require_all_nonces=False,
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
    except _FAIL_CLOSED_STEP_ERRORS as exc:
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
            require_all_nonces=False,
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
    except _FAIL_CLOSED_STEP_ERRORS as exc:
        return DexStepResult(ok=False, error=str(exc))
