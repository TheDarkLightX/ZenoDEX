"""Closed FCIS snapshot facades and the temporarily mounted legacy snapshots.

The ``snapshot_*`` functions are the target one-way admission boundary. The
legacy ``Frozen*`` implementations below remain only until their mounted
callers have migrated to exact committed values and return-new transitions.
New authority-core code must not depend on those compatibility classes.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, NoReturn, cast, final

from .balances import Amount, AssetId, BalanceTable, PubKey
from .immutable_collections import FrozenDict, deep_freeze
from .lp import LPTable, PoolId
from .nonces import NonceTable
from .owned_collections import OwnedMapV1
from .pools import PoolState, copy_pool_state
from .snapshot_combinators import (
    AdmissionLimitsV1,
    AdmitCode,
    AdmitOk,
    AdmitReject,
    FieldPath,
    ValidatedAdmissionLimitsV1,
    build_admission_limits_v1,
)

if TYPE_CHECKING:
    from ..core.fees import FeeAccumulatorState
    from ..core.oracle import OracleState
    from ..core.perps import PerpsState
    from ..core.vault import VaultState
    from .state_snapshot_values import (
        CommittedBalanceTableV1,
        CommittedFeeAccumulatorStateV1,
        CommittedLPTableV1,
        CommittedNonceTableV1,
        CommittedOracleStateV1,
        CommittedPerpsStateV1,
        CommittedPoolStateV1,
        CommittedVaultStateV1,
    )


_STATE_ADMISSION_LIMITS_V1 = build_admission_limits_v1(
    AdmissionLimitsV1(
        max_depth=64,
        max_nodes=200_000,
        max_canonical_bytes=4_000_000,
        max_collection_items=200_000,
    )
)
if type(_STATE_ADMISSION_LIMITS_V1) is not ValidatedAdmissionLimitsV1:
    raise RuntimeError("mounted FCIS state admission limits are invalid")


@final
@dataclass(frozen=True, slots=True)
class StateAdmissionError(ValueError):
    """Stable adapter error for one typed no-output admission rejection."""

    code: AdmitCode
    path: FieldPath

    def __str__(self) -> str:
        path = ".".join(str(part) for part in self.path)
        return self.code.value if not path else f"{self.code.value}:{path}"


def _raise_admission_reject(reject: AdmitReject) -> NoReturn:
    raise StateAdmissionError(reject.code, reject.path)


def _admit_state_value(schema_id: str, source: object) -> object:
    from .state_admission_profile import admit
    from .state_snapshot_values import FCIS_STATE_SCHEMA_REVISION_V1

    result = admit(
        FCIS_STATE_SCHEMA_REVISION_V1,
        schema_id,
        _STATE_ADMISSION_LIMITS_V1,
        source,
    )
    if type(result) is AdmitReject:
        _raise_admission_reject(result)
    if type(result) is not AdmitOk:
        raise RuntimeError("closed state admission returned an impossible result")
    return result.value


def snapshot_balance_table(
    source: BalanceTable | CommittedBalanceTableV1,
) -> CommittedBalanceTableV1:
    """Admit one exact balance source into a distinct owned committed value.

    Legacy source internals are inspected directly before any source behavior
    can execute. Already-committed inputs traverse the same closed admission
    relation and are reconstructed only after complete revalidation.
    """

    # These imports remain local because the full mounted state registry names
    # core domain source types. Keeping the leaf snapshot module importable
    # prevents the core package initializer from cycling back through DexState.
    from .state_snapshot_schema import BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import (
        CommittedBalanceTableV1,
        _BalanceSourceV1,
    )

    admission_source: object
    if type(source) is BalanceTable:
        try:
            raw_balances = object.__getattribute__(source, "_balances")
        except AttributeError:
            _raise_admission_reject(AdmitReject(AdmitCode.MISSING_FIELD, ("_balances",)))
        if type(raw_balances) is not dict:
            _raise_admission_reject(AdmitReject(AdmitCode.WRONG_CONTAINER, ("_balances",)))
        admission_source = _BalanceSourceV1(raw_balances)
    elif type(source) is CommittedBalanceTableV1:
        admission_source = source
    else:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))

    admitted = _admit_state_value(BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1, admission_source)
    if type(admitted) is not CommittedBalanceTableV1:
        raise RuntimeError("closed balance admission returned an impossible result")
    return cast(CommittedBalanceTableV1, admitted)


def snapshot_lp_table(source: LPTable | CommittedLPTableV1) -> CommittedLPTableV1:
    """Admit the five exact LP maps as one owned committed aggregate."""

    from .state_snapshot_schema import LP_TABLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedLPTableV1, _LPSourceV1

    admission_source: object
    if type(source) is LPTable:
        raw_fields: list[object] = []
        for field_name in (
            "_balances",
            "_last_mint_timestamps",
            "_last_remove_timestamps",
            "_churn_tiers",
            "_last_churn_update_timestamps",
        ):
            try:
                raw = object.__getattribute__(source, field_name)
            except AttributeError:
                _raise_admission_reject(AdmitReject(AdmitCode.MISSING_FIELD, (field_name,)))
            if type(raw) is not dict:
                _raise_admission_reject(AdmitReject(AdmitCode.WRONG_CONTAINER, (field_name,)))
            raw_fields.append(raw)
        admission_source = _LPSourceV1(*raw_fields)
    elif type(source) is CommittedLPTableV1:
        admission_source = source
    else:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))

    admitted = _admit_state_value(LP_TABLE_ADMISSION_SCHEMA_ID_V1, admission_source)
    if type(admitted) is not CommittedLPTableV1:
        raise RuntimeError("closed LP admission returned an impossible result")
    return cast(CommittedLPTableV1, admitted)


def snapshot_nonce_table(
    source: NonceTable | CommittedNonceTableV1,
) -> CommittedNonceTableV1:
    """Admit one exact nonce source without invoking source behavior."""

    from .state_snapshot_schema import NONCE_TABLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedNonceTableV1

    if type(source) is NonceTable:
        try:
            raw = object.__getattribute__(source, "_last")
        except AttributeError:
            _raise_admission_reject(AdmitReject(AdmitCode.MISSING_FIELD, ("_last",)))
        if type(raw) is not dict:
            _raise_admission_reject(AdmitReject(AdmitCode.WRONG_CONTAINER, ("_last",)))
        admission_source: object = source
    elif type(source) is CommittedNonceTableV1:
        admission_source = source
    else:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))

    admitted = _admit_state_value(NONCE_TABLE_ADMISSION_SCHEMA_ID_V1, admission_source)
    if type(admitted) is not CommittedNonceTableV1:
        raise RuntimeError("closed nonce admission returned an impossible result")
    return cast(CommittedNonceTableV1, admitted)


def snapshot_pool(source: PoolState | CommittedPoolStateV1) -> CommittedPoolStateV1:
    """Admit one exact pool through the closed field and invariant schema."""

    from .state_snapshot_schema import POOL_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedPoolStateV1

    if type(source) not in {PoolState, CommittedPoolStateV1}:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(POOL_ADMISSION_SCHEMA_ID_V1, source)
    if type(admitted) is not CommittedPoolStateV1:
        raise RuntimeError("closed pool admission returned an impossible result")
    return cast(CommittedPoolStateV1, admitted)


def snapshot_pool_map(
    source: dict[str, PoolState] | OwnedMapV1[str, CommittedPoolStateV1],
) -> OwnedMapV1[str, CommittedPoolStateV1]:
    """Admit a canonical pool map and bind each map key to its pool ID."""

    from .state_snapshot_schema import POOL_MAP_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedPoolStateV1

    if type(source) not in {dict, OwnedMapV1}:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(POOL_MAP_ADMISSION_SCHEMA_ID_V1, source)
    if type(admitted) is not OwnedMapV1:
        raise RuntimeError("closed pool-map admission returned an impossible result")
    return cast(OwnedMapV1[str, CommittedPoolStateV1], admitted)


def snapshot_vault(
    source: None | VaultState | CommittedVaultStateV1,
) -> None | CommittedVaultStateV1:
    """Admit the explicit optional vault state family."""

    from ..core.vault import VaultState
    from .state_snapshot_schema import VAULT_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedVaultStateV1

    if source is not None and type(source) not in {VaultState, CommittedVaultStateV1}:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(VAULT_ADMISSION_SCHEMA_ID_V1, source)
    if admitted is not None and type(admitted) is not CommittedVaultStateV1:
        raise RuntimeError("closed vault admission returned an impossible result")
    return cast(None | CommittedVaultStateV1, admitted)


def snapshot_oracle(
    source: None | OracleState | CommittedOracleStateV1,
) -> None | CommittedOracleStateV1:
    """Admit the explicit optional Oracle state family."""

    from ..core.oracle import OracleState
    from .state_snapshot_schema import ORACLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedOracleStateV1

    if source is not None and type(source) not in {OracleState, CommittedOracleStateV1}:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(ORACLE_ADMISSION_SCHEMA_ID_V1, source)
    if admitted is not None and type(admitted) is not CommittedOracleStateV1:
        raise RuntimeError("closed Oracle admission returned an impossible result")
    return cast(None | CommittedOracleStateV1, admitted)


def snapshot_fee_accumulator(
    source: FeeAccumulatorState | CommittedFeeAccumulatorStateV1,
) -> CommittedFeeAccumulatorStateV1:
    """Admit the exact fee-accumulator state family."""

    from ..core.fees import FeeAccumulatorState
    from .state_snapshot_schema import FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedFeeAccumulatorStateV1

    if type(source) not in {FeeAccumulatorState, CommittedFeeAccumulatorStateV1}:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1, source)
    if type(admitted) is not CommittedFeeAccumulatorStateV1:
        raise RuntimeError("closed fee admission returned an impossible result")
    return cast(CommittedFeeAccumulatorStateV1, admitted)


def snapshot_perps(
    source: None | PerpsState | CommittedPerpsStateV1,
) -> None | CommittedPerpsStateV1:
    """Admit every registered perps state variant through one closed schema."""

    from ..core.perps import PerpsState
    from .state_snapshot_schema import PERPS_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedPerpsStateV1

    if source is not None and type(source) not in {PerpsState, CommittedPerpsStateV1}:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(PERPS_ADMISSION_SCHEMA_ID_V1, source)
    if admitted is not None and type(admitted) is not CommittedPerpsStateV1:
        raise RuntimeError("closed perps admission returned an impossible result")
    return cast(None | CommittedPerpsStateV1, admitted)


def _immutable_state(*_args: object, **_kwargs: object) -> NoReturn:
    raise TypeError("committed state snapshot is immutable")


class FrozenBalanceTable(BalanceTable):
    """Read-compatible immutable ``BalanceTable`` snapshot."""

    __slots__ = ()

    def __init__(self, source: BalanceTable) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        BalanceTable.__init__(self)
        for (pubkey, asset), amount in source.get_all_balances().items():
            BalanceTable.set(self, pubkey, asset, amount)
        object.__setattr__(self, "_balances", FrozenDict(self._balances))
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_snapshot_sealed", False):
            raise TypeError("committed balance snapshot is immutable")
        object.__setattr__(self, name, value)

    def set(self, pubkey: PubKey, asset: AssetId, amount: Amount) -> None:
        _immutable_state(pubkey, asset, amount)

    def add(self, pubkey: PubKey, asset: AssetId, delta: Amount) -> None:
        _immutable_state(pubkey, asset, delta)

    def subtract(self, pubkey: PubKey, asset: AssetId, delta: Amount) -> None:
        _immutable_state(pubkey, asset, delta)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenBalanceTable:
        return self


class FrozenLPTable(LPTable):
    """Read-compatible immutable ``LPTable`` snapshot with metadata."""

    __slots__ = ()

    def __init__(self, source: LPTable) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        LPTable.__init__(self)
        for (pubkey, pool_id), amount in source.get_all_balances().items():
            LPTable.set(self, pubkey, pool_id, amount)
        for (pubkey, pool_id), timestamp in source.get_all_last_mint_timestamps().items():
            if LPTable.get(self, pubkey, pool_id) > 0:
                LPTable.set_last_mint_timestamp(self, pubkey, pool_id, timestamp)
        for (pubkey, pool_id), timestamp in source.get_all_last_remove_timestamps().items():
            LPTable.set_last_remove_timestamp(self, pubkey, pool_id, timestamp)
        for (pubkey, pool_id), tier in source.get_all_churn_tiers().items():
            LPTable.set_churn_tier(self, pubkey, pool_id, tier)
        for (
            pubkey,
            pool_id,
        ), timestamp in source.get_all_last_churn_update_timestamps().items():
            LPTable.set_last_churn_update_timestamp(self, pubkey, pool_id, timestamp)

        for name in (
            "_balances",
            "_last_mint_timestamps",
            "_last_remove_timestamps",
            "_churn_tiers",
            "_last_churn_update_timestamps",
        ):
            object.__setattr__(self, name, FrozenDict(getattr(self, name)))
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_snapshot_sealed", False):
            raise TypeError("committed LP snapshot is immutable")
        object.__setattr__(self, name, value)

    def set(self, pubkey: PubKey, pool_id: PoolId, amount: Amount) -> None:
        _immutable_state(pubkey, pool_id, amount)

    def add(self, pubkey: PubKey, pool_id: PoolId, delta: int) -> None:
        _immutable_state(pubkey, pool_id, delta)

    def subtract(self, pubkey: PubKey, pool_id: PoolId, delta: Amount) -> None:
        _immutable_state(pubkey, pool_id, delta)

    def set_last_mint_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
        timestamp: int,
    ) -> None:
        _immutable_state(pubkey, pool_id, timestamp)

    def clear_last_mint_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        _immutable_state(pubkey, pool_id)

    def set_last_remove_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
        timestamp: int,
    ) -> None:
        _immutable_state(pubkey, pool_id, timestamp)

    def clear_last_remove_timestamp(self, pubkey: PubKey, pool_id: PoolId) -> None:
        _immutable_state(pubkey, pool_id)

    def set_churn_tier(self, pubkey: PubKey, pool_id: PoolId, tier: int) -> None:
        _immutable_state(pubkey, pool_id, tier)

    def set_last_churn_update_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
        timestamp: int,
    ) -> None:
        _immutable_state(pubkey, pool_id, timestamp)

    def clear_last_churn_update_timestamp(
        self,
        pubkey: PubKey,
        pool_id: PoolId,
    ) -> None:
        _immutable_state(pubkey, pool_id)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenLPTable:
        return self


class FrozenNonceTable(NonceTable):
    """Read-compatible immutable replay-protection snapshot."""

    __slots__ = ()

    def __init__(self, source: NonceTable) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        NonceTable.__init__(self)
        for pubkey, nonce in source.get_all().items():
            NonceTable.set_last(self, pubkey, nonce)
        object.__setattr__(self, "_last", FrozenDict(self._last))
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_snapshot_sealed", False):
            raise TypeError("committed nonce snapshot is immutable")
        object.__setattr__(self, name, value)

    def set_last(self, pubkey: PubKey, last_nonce: int) -> None:
        _immutable_state(pubkey, last_nonce)

    def apply_accept(self, pubkey: PubKey, nonce: int) -> None:
        _immutable_state(pubkey, nonce)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenNonceTable:
        return self


class FrozenPoolState(PoolState):
    """A canonical ``PoolState`` whose economic fields cannot be reassigned."""

    __slots__ = ()

    def __post_init__(self) -> None:
        object.__setattr__(self, "_snapshot_sealed", False)
        PoolState.__post_init__(self)
        object.__setattr__(self, "_snapshot_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_snapshot_sealed", False):
            raise TypeError("committed pool snapshot is immutable")
        object.__setattr__(self, name, value)

    def __deepcopy__(self, _memo: dict[int, object]) -> FrozenPoolState:
        return self


def freeze_balance_table(source: BalanceTable) -> BalanceTable:
    if type(source) is FrozenBalanceTable:
        return source
    if type(source) is not BalanceTable:
        raise TypeError("balances must be an exact BalanceTable")
    return FrozenBalanceTable(source)


def freeze_lp_table(source: LPTable) -> LPTable:
    if type(source) is FrozenLPTable:
        return source
    if type(source) is not LPTable:
        raise TypeError("lp_balances must be an exact LPTable")
    return FrozenLPTable(source)


def freeze_nonce_table(source: NonceTable) -> NonceTable:
    if type(source) is FrozenNonceTable:
        return source
    if type(source) is not NonceTable:
        raise TypeError("nonces must be an exact NonceTable")
    return FrozenNonceTable(source)


def freeze_pool_state(source: PoolState) -> PoolState:
    if type(source) is FrozenPoolState:
        return source
    if type(source) is not PoolState:
        raise TypeError("pool values must be exact PoolState instances")
    scratch = copy_pool_state(source)
    return FrozenPoolState(
        pool_id=scratch.pool_id,
        asset0=scratch.asset0,
        asset1=scratch.asset1,
        reserve0=scratch.reserve0,
        reserve1=scratch.reserve1,
        fee_bps=scratch.fee_bps,
        lp_supply=scratch.lp_supply,
        status=scratch.status,
        created_at=scratch.created_at,
        curve_tag=scratch.curve_tag,
        curve_params=scratch.curve_params,
    )


def freeze_pool_mapping(source: Mapping[str, PoolState]) -> FrozenDict:
    if type(source) is FrozenDict:
        for pool_id, pool in source.items():
            if type(pool_id) is not str or not pool_id:
                raise TypeError("pool keys must be non-empty exact strings")
            if type(pool) is not FrozenPoolState:
                raise TypeError("frozen pool mappings must contain frozen pools")
        return source
    if type(source) is not dict:
        raise TypeError("pools must be an exact dict or owned FrozenDict")
    snapshot: dict[str, PoolState] = {}
    for pool_id, pool in source.items():
        if type(pool_id) is not str or not pool_id:
            raise TypeError("pool keys must be non-empty exact strings")
        snapshot[pool_id] = freeze_pool_state(pool)
    return FrozenDict(snapshot)


def _validate_exact_perps_types(source: PerpsState) -> None:
    """Reject behavior-bearing subclasses before committed-state admission."""

    from ..core.perps import (
        PerpAccountState,
        PerpClearinghouse2pMarketState,
        PerpClearinghouse3pTransferMarketState,
        PerpClearinghouseNpAccount,
        PerpClearinghouseNpMarketState,
        PerpClearinghouseNpPendingIntent,
        PerpMarketState,
        PerpsState,
    )

    if type(source) is not PerpsState:
        raise TypeError("perps must be an exact PerpsState")
    if type(source.version) is not int:
        raise TypeError("perps.version must be an exact int")
    if not isinstance(source.markets, Mapping):
        raise TypeError("perps.markets must be mapping-compatible")

    allowed_market_types = (
        PerpMarketState,
        PerpClearinghouse2pMarketState,
        PerpClearinghouse3pTransferMarketState,
        PerpClearinghouseNpMarketState,
    )
    for market_id, market in source.markets.items():
        if type(market_id) is not str or not market_id:
            raise TypeError("perps market ids must be non-empty exact strings")
        if type(market) not in allowed_market_types:
            raise TypeError("perps market must use an exact supported state type")
        if type(market) is PerpMarketState and any(
            type(account) is not PerpAccountState for account in market.accounts.values()
        ):
            raise TypeError("isolated perps accounts must be exact PerpAccountState values")
        if type(market) is PerpClearinghouseNpMarketState:
            if type(market.accounts) is not tuple or any(
                type(account) is not PerpClearinghouseNpAccount for account in market.accounts
            ):
                raise TypeError("N-party perps accounts must use exact tuple values")
            if type(market.pending_intents) is not tuple or any(
                type(intent) is not PerpClearinghouseNpPendingIntent
                for intent in market.pending_intents
            ):
                raise TypeError("N-party pending intents must use exact tuple values")


def freeze_perps_state(source: PerpsState) -> PerpsState:
    """Own perps state after excluding behavior-changing runtime subclasses."""

    from ..core.perps import PerpsState

    _validate_exact_perps_types(source)
    frozen = deep_freeze(source)
    if type(frozen) is not PerpsState:  # pragma: no cover
        raise AssertionError("perps snapshot lost its exact top-level type")
    _validate_exact_perps_types(frozen)
    return frozen


def freeze_optional_module_state(value: Any) -> Any:
    """Detach and recursively freeze an optional nested module state."""

    from ..core.perps import PerpsState

    if value is None:
        return None
    if isinstance(value, PerpsState):
        return freeze_perps_state(value)
    return deep_freeze(value)
