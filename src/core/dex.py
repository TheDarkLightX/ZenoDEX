"""
DEX step orchestration (functional core).

This module wires the verified kernels into a single pure step:
- Compute a settlement from intents + pre-state
- Validate the settlement (fail-closed)
- Apply it to produce (next_state, effects)
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from dataclasses import dataclass, field, replace
from typing import List, Literal, Optional, overload

from ..state.balances import BalanceTable, FrozenBalanceTable, freeze_balance_table
from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.immutable import FrozenDict, SealedValue, seal_dataclass_init
from ..state.intents import Intent, require_exact_intent
from ..state.lp import FrozenLPTable, LPTable, freeze_lp_table
from ..state.nonces import (
    FrozenNonceTable,
    NonceTable,
    freeze_nonce_table,
    validate_and_apply_intent_nonce_batch,
)
from ..state.pools import FrozenPoolState, PoolState, freeze_pool_state
from .batch_clearing import apply_settlement_pure, compute_settlement, validate_settlement
from .fees import FeeAccumulatorState, FeeSplitParams, FeeSplitResult, split_fee_with_dust_carry
from .oracle import OracleState
from .perps import PerpsState
from .protocol_fee_policy import canonical_protocol_fee_policy
from .settlement import FillAction, Settlement
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


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class DexConfig(SealedValue):
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

    def __post_init__(self) -> None:
        if self.fee_split_params is not None and type(self.fee_split_params) is not FeeSplitParams:
            raise TypeError("fee_split_params must be an exact FeeSplitParams or None")
        for string_name, string_value in (
            ("swap_ordering", self.swap_ordering),
            ("settlement_validation", self.settlement_validation),
        ):
            if type(string_value) is not str or not string_value:
                raise TypeError(f"{string_name} must be a non-empty string")
        for bool_name, bool_value in (
            ("allow_snapshot_bound_quote_bindings", self.allow_snapshot_bound_quote_bindings),
            ("reject_settlements_with_rejected_intents", self.reject_settlements_with_rejected_intents),
        ):
            if type(bool_value) is not bool:
                raise TypeError(f"{bool_name} must be a bool")
        policy = canonical_protocol_fee_policy(
            share_bps=self.protocol_fee_share_bps,
            recipient_pubkey=self.protocol_fee_recipient_pubkey,
        )
        object.__setattr__(self, "protocol_fee_share_bps", policy.share_bps)
        object.__setattr__(
            self,
            "protocol_fee_recipient_pubkey",
            policy.recipient_pubkey,
        )


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class DexState(SealedValue):
    balances: BalanceTable
    pools: Mapping[str, PoolState]
    lp_balances: LPTable
    nonces: NonceTable = field(default_factory=NonceTable)

    # Optional modules (can be unused in early deployments).
    vault: Optional[VaultState] = None
    oracle: Optional[OracleState] = None
    fee_accumulator: FeeAccumulatorState = FeeAccumulatorState()
    perps: Optional[PerpsState] = None

    def __post_init__(self) -> None:
        if type(self.balances) not in (BalanceTable, FrozenBalanceTable):
            raise TypeError("balances must be an exact BalanceTable snapshot")
        if not isinstance(self.pools, Mapping):
            raise TypeError("pools must be a mapping")
        if type(self.lp_balances) not in (LPTable, FrozenLPTable):
            raise TypeError("lp_balances must be an exact LPTable snapshot")
        if type(self.nonces) not in (NonceTable, FrozenNonceTable):
            raise TypeError("nonces must be an exact NonceTable snapshot")
        if self.vault is not None and type(self.vault) is not VaultState:
            raise TypeError("vault must be an exact VaultState or None")
        if self.oracle is not None and type(self.oracle) is not OracleState:
            raise TypeError("oracle must be an exact OracleState or None")
        if type(self.fee_accumulator) is not FeeAccumulatorState:
            raise TypeError("fee_accumulator must be an exact FeeAccumulatorState")
        if self.perps is not None and type(self.perps) is not PerpsState:
            raise TypeError("perps must be an exact PerpsState or None")

        frozen_pools: dict[str, FrozenPoolState] = {}
        decoded_pool_ids: dict[str, str] = {}
        for pool_id, pool in self.pools.items():
            if type(pool_id) is not str:
                raise TypeError("pool ids must be strings")
            if pool_id in frozen_pools:
                raise ValueError("duplicate pool_id in pools mapping iteration")
            if type(pool) not in (PoolState, FrozenPoolState):
                raise TypeError(f"pool {pool_id!r} must be an exact PoolState snapshot")
            frozen_pool = freeze_pool_state(pool)
            if frozen_pool.pool_id != pool_id:
                raise ValueError(
                    f"pool_id mismatch: key={pool_id} pool.pool_id={frozen_pool.pool_id}"
                )
            try:
                decoded_pool_id = canonical_hex_fixed_allow_0x(
                    pool_id,
                    nbytes=32,
                    name="pool_id",
                )
            except ValueError:
                # Preserve symbolic IDs for non-production/test profiles. Their
                # canonical spelling requires an explicit snapshot migration.
                decoded_pool_id = pool_id
            prior_spelling = decoded_pool_ids.get(decoded_pool_id)
            if prior_spelling is not None and prior_spelling != pool_id:
                raise ValueError("duplicate decoded pool_id in pools")
            decoded_pool_ids[decoded_pool_id] = pool_id
            frozen_pools[pool_id] = frozen_pool

        object.__setattr__(self, "balances", freeze_balance_table(self.balances))
        object.__setattr__(self, "pools", FrozenDict(frozen_pools))
        object.__setattr__(self, "lp_balances", freeze_lp_table(self.lp_balances))
        object.__setattr__(self, "nonces", freeze_nonce_table(self.nonces))


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class DexEffects(SealedValue, Mapping[str, object]):
    """Immutable, backwards-compatible effect plan.

    ``Mapping`` preserves the historical read surface used by the shell and
    tests while preventing callers from changing an accepted plan after it has
    been hashed, cached, signed, or queued.
    """

    settlement: Settlement
    total_swap_fees: int
    fee_split: Optional[FeeSplitResult] = None

    _KEYS = ("settlement", "total_swap_fees", "fee_split")

    def __post_init__(self) -> None:
        if type(self.settlement) is not Settlement:
            raise TypeError("settlement must be an exact Settlement")
        if type(self.total_swap_fees) is not int:
            raise TypeError("total_swap_fees must be an int")
        if self.total_swap_fees < 0:
            raise ValueError("total_swap_fees must be non-negative")
        if self.fee_split is not None and type(self.fee_split) is not FeeSplitResult:
            raise TypeError("fee_split must be an exact FeeSplitResult or None")
        object.__setattr__(self, "settlement", replace(self.settlement))

    @overload
    def __getitem__(self, key: Literal["settlement"]) -> Settlement: ...

    @overload
    def __getitem__(self, key: Literal["total_swap_fees"]) -> int: ...

    @overload
    def __getitem__(self, key: Literal["fee_split"]) -> Optional[FeeSplitResult]: ...

    @overload
    def __getitem__(self, key: str) -> object: ...

    def __getitem__(self, key: str) -> object:
        if key == "settlement":
            return self.settlement
        if key == "total_swap_fees":
            return self.total_swap_fees
        if key == "fee_split":
            return self.fee_split
        raise KeyError(key)

    def __iter__(self) -> Iterator[str]:
        return iter(self._KEYS)

    def __len__(self) -> int:
        return len(self._KEYS)


@seal_dataclass_init
@dataclass(frozen=True, slots=True)
class DexStepResult(SealedValue):
    ok: bool
    state: Optional[DexState] = None
    effects: Optional[DexEffects] = None
    error: Optional[str] = None

    def __post_init__(self) -> None:
        if type(self.ok) is not bool:
            raise TypeError("ok must be a bool")
        if self.ok:
            if type(self.state) is not DexState:
                raise ValueError("accepted result requires an exact DexState")
            if type(self.effects) is not DexEffects:
                raise ValueError("accepted result requires exact DexEffects")
            if self.error is not None:
                raise ValueError("accepted result cannot carry an error")
            return
        if self.state is not None or self.effects is not None:
            raise ValueError("rejected result cannot carry state or effects")
        if type(self.error) is not str or not self.error:
            raise ValueError("rejected result requires a non-empty error")


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
        effects=DexEffects(
            settlement=settlement,
            total_swap_fees=total_fees,
            fee_split=fee_split,
        ),
    )


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
        if type(config) is not DexConfig:
            raise TypeError("config must be an exact DexConfig")
        if type(state) is not DexState:
            raise TypeError("state must be an exact DexState")
        for intent in intents:
            require_exact_intent(intent)
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
