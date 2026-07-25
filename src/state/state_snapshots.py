"""Closed one-way admission facades for exact committed DEX state values.

Each public function accepts only the source and committed classes declared in
``PR477_STATE_SCHEMA.md``.  Validation and ownership are delegated to the sole
four-argument state admission profile.  The temporarily mounted ``Frozen*``
oracle lives in ``legacy_state_snapshots`` and is intentionally outside this
accepted language.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NoReturn, cast, final

from .balances import BalanceTable
from .lp import LPTable
from .nonces import NonceTable
from .owned_collections import OwnedMapV1
from .pools import PoolState
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
class StateAdmissionError(ValueError):
    """Stable shell-edge transport for one typed no-output rejection."""

    __slots__ = ("_code", "_path")

    _code: AdmitCode
    _path: FieldPath

    def __init__(self, code: AdmitCode, path: FieldPath) -> None:
        self._code = code
        self._path = path
        super().__init__(code, path)

    @property
    def code(self) -> AdmitCode:
        return self._code

    @property
    def path(self) -> FieldPath:
        return self._path

    def __str__(self) -> str:
        path = ".".join(str(part) for part in self.path)
        return self.code.value if not path else f"{self.code.value}:{path}"

    def __eq__(self, other: object) -> bool:
        return (
            type(other) is StateAdmissionError
            and self.code is other.code
            and self.path == other.path
        )

    # A process-randomized hash over field-path strings must never participate
    # in rejection precedence or consensus-visible output.
    __hash__ = None  # type: ignore[assignment]


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
    """Own one exact balance table without invoking source behavior."""

    from .state_snapshot_schema import BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import (
        CommittedBalanceTableV1,
        _BalanceSourceV1,
    )

    if type(source) is BalanceTable:
        try:
            raw_balances = object.__getattribute__(source, "_balances")
        except AttributeError:
            _raise_admission_reject(
                AdmitReject(AdmitCode.MISSING_FIELD, ("_balances",))
            )
        if type(raw_balances) is not dict:
            _raise_admission_reject(
                AdmitReject(AdmitCode.WRONG_CONTAINER, ("_balances",))
            )
        admission_source: object = _BalanceSourceV1(raw_balances)
    elif type(source) is CommittedBalanceTableV1:
        admission_source = source
    else:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))

    admitted = _admit_state_value(
        BALANCE_TABLE_ADMISSION_SCHEMA_ID_V1,
        admission_source,
    )
    if type(admitted) is not CommittedBalanceTableV1:
        raise RuntimeError("closed balance admission returned an impossible result")
    return admitted


def snapshot_lp_table(
    source: LPTable | CommittedLPTableV1,
) -> CommittedLPTableV1:
    """Own the five exact LP maps as one committed aggregate."""

    from .state_snapshot_schema import LP_TABLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedLPTableV1, _LPSourceV1

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
                _raise_admission_reject(
                    AdmitReject(AdmitCode.MISSING_FIELD, (field_name,))
                )
            if type(raw) is not dict:
                _raise_admission_reject(
                    AdmitReject(AdmitCode.WRONG_CONTAINER, (field_name,))
                )
            raw_fields.append(raw)
        admission_source: object = _LPSourceV1(*raw_fields)
    elif type(source) is CommittedLPTableV1:
        admission_source = source
    else:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))

    admitted = _admit_state_value(
        LP_TABLE_ADMISSION_SCHEMA_ID_V1,
        admission_source,
    )
    if type(admitted) is not CommittedLPTableV1:
        raise RuntimeError("closed LP admission returned an impossible result")
    return admitted


def snapshot_nonce_table(
    source: NonceTable | CommittedNonceTableV1,
) -> CommittedNonceTableV1:
    """Own one exact nonce table without invoking source behavior."""

    from .state_snapshot_schema import NONCE_TABLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedNonceTableV1, _NonceSourceV1

    if type(source) is NonceTable:
        try:
            raw = object.__getattribute__(source, "_last")
        except AttributeError:
            _raise_admission_reject(AdmitReject(AdmitCode.MISSING_FIELD, ("_last",)))
        if type(raw) is not dict:
            _raise_admission_reject(
                AdmitReject(AdmitCode.WRONG_CONTAINER, ("_last",))
            )
        admission_source: object = _NonceSourceV1(raw)
    elif type(source) is CommittedNonceTableV1:
        admission_source = source
    else:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))

    admitted = _admit_state_value(
        NONCE_TABLE_ADMISSION_SCHEMA_ID_V1,
        admission_source,
    )
    if type(admitted) is not CommittedNonceTableV1:
        raise RuntimeError("closed nonce admission returned an impossible result")
    return admitted


def snapshot_pool(
    source: PoolState | CommittedPoolStateV1,
) -> CommittedPoolStateV1:
    """Own one exact pool through the closed field and invariant schema."""

    from .state_snapshot_schema import POOL_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedPoolStateV1

    if type(source) not in {PoolState, CommittedPoolStateV1}:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(POOL_ADMISSION_SCHEMA_ID_V1, source)
    if type(admitted) is not CommittedPoolStateV1:
        raise RuntimeError("closed pool admission returned an impossible result")
    return admitted


def snapshot_pool_map(
    source: dict[str, PoolState] | OwnedMapV1[str, CommittedPoolStateV1],
) -> OwnedMapV1[str, CommittedPoolStateV1]:
    """Own a canonical pool map and bind every key to its pool ID."""

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
    """Own the explicit optional vault state family."""

    from ..core.vault import VaultState
    from .state_snapshot_schema import VAULT_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedVaultStateV1

    if source is not None and type(source) not in {
        VaultState,
        CommittedVaultStateV1,
    }:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(VAULT_ADMISSION_SCHEMA_ID_V1, source)
    if admitted is not None and type(admitted) is not CommittedVaultStateV1:
        raise RuntimeError("closed vault admission returned an impossible result")
    return admitted


def snapshot_oracle(
    source: None | OracleState | CommittedOracleStateV1,
) -> None | CommittedOracleStateV1:
    """Own the explicit optional Oracle state family."""

    from ..core.oracle import OracleState
    from .state_snapshot_schema import ORACLE_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedOracleStateV1

    if source is not None and type(source) not in {
        OracleState,
        CommittedOracleStateV1,
    }:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(ORACLE_ADMISSION_SCHEMA_ID_V1, source)
    if admitted is not None and type(admitted) is not CommittedOracleStateV1:
        raise RuntimeError("closed Oracle admission returned an impossible result")
    return admitted


def snapshot_fee_accumulator(
    source: FeeAccumulatorState | CommittedFeeAccumulatorStateV1,
) -> CommittedFeeAccumulatorStateV1:
    """Own the exact fee-accumulator state family."""

    from ..core.fees import FeeAccumulatorState
    from .state_snapshot_schema import FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedFeeAccumulatorStateV1

    if type(source) not in {
        FeeAccumulatorState,
        CommittedFeeAccumulatorStateV1,
    }:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(
        FEE_ACCUMULATOR_ADMISSION_SCHEMA_ID_V1,
        source,
    )
    if type(admitted) is not CommittedFeeAccumulatorStateV1:
        raise RuntimeError("closed fee admission returned an impossible result")
    return admitted


def snapshot_perps(
    source: None | PerpsState | CommittedPerpsStateV1,
) -> None | CommittedPerpsStateV1:
    """Own every registered perps variant through one closed schema."""

    from ..core.perps import PerpsState
    from .state_snapshot_schema import PERPS_ADMISSION_SCHEMA_ID_V1
    from .state_snapshot_values import CommittedPerpsStateV1

    if source is not None and type(source) not in {
        PerpsState,
        CommittedPerpsStateV1,
    }:
        _raise_admission_reject(AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ()))
    admitted = _admit_state_value(PERPS_ADMISSION_SCHEMA_ID_V1, source)
    if admitted is not None and type(admitted) is not CommittedPerpsStateV1:
        raise RuntimeError("closed perps admission returned an impossible result")
    return admitted


__all__ = [
    "StateAdmissionError",
    "snapshot_balance_table",
    "snapshot_fee_accumulator",
    "snapshot_lp_table",
    "snapshot_nonce_table",
    "snapshot_oracle",
    "snapshot_perps",
    "snapshot_pool",
    "snapshot_pool_map",
    "snapshot_vault",
]
