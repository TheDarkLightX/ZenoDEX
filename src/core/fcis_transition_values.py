"""Exact transition, patch, effect, replay, and commit-plan values for FCIS M5."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias, final

from ..state.canonical import canonical_hex_fixed_allow_0x
from ..state.state_snapshot_values import (
    MAX_BALANCES_V1,
    MAX_LP_ENTRIES_V1,
    MAX_NONCES_V1,
    MAX_POOLS_V1,
    CommittedFeeAccumulatorStateV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedVaultStateV1,
)
from ..state.state_transitions import (
    BalanceWriteV1,
    LPPositionWriteV1,
    NonceAdvanceV1,
    PoolWriteV1,
)
from .fcis_step_evaluation_values import FCISFeeAllocationV1
from .settlement_snapshots import OwnedSettlementV1

FCIS_DEX_PATCH_SCHEMA_ID_V1 = "zenodex/fcis/dex-patch/v1"
FCIS_EFFECTS_SCHEMA_ID_V1 = "zenodex/fcis/effects/v1"
FCIS_REPLAY_UPDATE_SCHEMA_ID_V1 = "zenodex/fcis/replay-update/v1"
FCIS_COMMIT_PLAN_SCHEMA_ID_V1 = "zenodex/fcis/commit-plan/v1"
MAX_FCIS_NULLIFIERS_V1 = 256


@final
@dataclass(frozen=True, slots=True)
class BalanceWriteSourceV1:
    key: object
    expected_old: object
    replacement: object


@final
@dataclass(frozen=True, slots=True)
class PoolWriteSourceV1:
    pool_id: object
    expected: object
    replacement: object


@final
@dataclass(frozen=True, slots=True)
class LPPositionValueSourceV1:
    balance: object
    last_mint_timestamp: object
    last_remove_timestamp: object
    churn_tier: object
    last_churn_update_timestamp: object


@final
@dataclass(frozen=True, slots=True)
class LPPositionWriteSourceV1:
    key: object
    expected: object
    replacement: object


@final
@dataclass(frozen=True, slots=True)
class NonceAdvanceSourceV1:
    pubkey: object
    expected_last: object
    new_last: object


@final
@dataclass(frozen=True, slots=True)
class FCISFeeAllocationSourceV1:
    buyback_amount: object
    treasury_amount: object
    rewards_amount: object
    dust_carried: object


@final
@dataclass(frozen=True, slots=True)
class FeeAccumulatorWriteSourceV1:
    expected: object
    replacement: object


@final
@dataclass(frozen=True, slots=True)
class VaultWriteSourceV1:
    expected: object
    replacement: object


@final
@dataclass(frozen=True, slots=True)
class OracleWriteSourceV1:
    expected: object
    replacement: object


@final
@dataclass(frozen=True, slots=True)
class PerpsWriteSourceV1:
    expected: object
    replacement: object


@final
@dataclass(frozen=True, slots=True)
class CanonicalDexPatchSourceV1:
    balance_writes: object
    pool_writes: object
    lp_writes: object
    fee_accumulator_write: object
    vault_write: object
    oracle_write: object
    perps_write: object


@final
@dataclass(frozen=True, slots=True)
class OwnedDexEffectsSourceV1:
    settlement: object
    total_swap_fees: object
    fee_allocation: object


@final
@dataclass(frozen=True, slots=True)
class NullifierRecordSourceV1:
    pubkey: object
    intent_id: object


@final
@dataclass(frozen=True, slots=True)
class ReplayUpdateSourceV1:
    nonce_advances: object
    nullifiers: object


@final
@dataclass(frozen=True, slots=True)
class CommitPlanSourceV1:
    patch: object
    effects: object
    replay: object


@final
@dataclass(frozen=True, slots=True)
class FeeAccumulatorWriteV1:
    expected: CommittedFeeAccumulatorStateV1
    replacement: CommittedFeeAccumulatorStateV1

    def __post_init__(self) -> None:
        if type(self.expected) is not CommittedFeeAccumulatorStateV1:
            raise TypeError("fee expected value must be exact")
        if type(self.replacement) is not CommittedFeeAccumulatorStateV1:
            raise TypeError("fee replacement value must be exact")
        if self.expected == self.replacement:
            raise ValueError("fee write must change its cell")


@final
@dataclass(frozen=True, slots=True)
class VaultWriteV1:
    expected: CommittedVaultStateV1 | None
    replacement: CommittedVaultStateV1 | None

    def __post_init__(self) -> None:
        for field_name in ("expected", "replacement"):
            value = object.__getattribute__(self, field_name)
            if value is not None and type(value) is not CommittedVaultStateV1:
                raise TypeError(f"vault {field_name} value must be exact or None")
        if self.expected == self.replacement:
            raise ValueError("vault write must change its cell")


@final
@dataclass(frozen=True, slots=True)
class OracleWriteV1:
    expected: CommittedOracleStateV1 | None
    replacement: CommittedOracleStateV1 | None

    def __post_init__(self) -> None:
        for field_name in ("expected", "replacement"):
            value = object.__getattribute__(self, field_name)
            if value is not None and type(value) is not CommittedOracleStateV1:
                raise TypeError(f"Oracle {field_name} value must be exact or None")
        if self.expected == self.replacement:
            raise ValueError("Oracle write must change its cell")


@final
@dataclass(frozen=True, slots=True)
class PerpsWriteV1:
    expected: CommittedPerpsStateV1 | None
    replacement: CommittedPerpsStateV1 | None

    def __post_init__(self) -> None:
        for field_name in ("expected", "replacement"):
            value = object.__getattribute__(self, field_name)
            if value is not None and type(value) is not CommittedPerpsStateV1:
                raise TypeError(f"perps {field_name} value must be exact or None")
        if self.expected == self.replacement:
            raise ValueError("perps write must change its cell")


def _strictly_increasing(items: tuple[object, ...], key_name: str) -> bool:
    keys = tuple(object.__getattribute__(item, key_name) for item in items)
    return all(keys[index - 1] < keys[index] for index in range(1, len(keys)))


def _validate_canonical_write_sequence_v1(
    field_name: str,
    values: object,
    expected_type: type[object],
    key_name: str,
    maximum: int,
) -> tuple[object, ...]:
    if type(values) is not tuple:
        raise TypeError(f"{field_name} must be an exact tuple")
    exact_values = values
    if any(type(value) is not expected_type for value in exact_values):
        raise TypeError(f"{field_name} contains a foreign write")
    if not _strictly_increasing(exact_values, key_name):
        raise ValueError(f"{field_name} must be in strict protocol order")
    if len(exact_values) > maximum:
        raise ValueError(f"{field_name} limit exceeded")
    return exact_values


def _validate_patch_no_ops_v1(
    balance_writes: tuple[BalanceWriteV1, ...],
    pool_writes: tuple[PoolWriteV1, ...],
    lp_writes: tuple[LPPositionWriteV1, ...],
) -> None:
    if any(
        write.expected_old == (0 if write.replacement is None else write.replacement)
        for write in balance_writes
    ):
        raise ValueError("balance patch contains a no-op write")
    if any(write.expected == write.replacement for write in pool_writes):
        raise ValueError("pool patch contains a no-op write")
    if any(write.expected == write.replacement for write in lp_writes):
        raise ValueError("LP patch contains a no-op write")


def _validate_optional_write_v1(
    field_name: str,
    value: object,
    expected_type: type[object],
) -> None:
    if value is not None and type(value) is not expected_type:
        raise TypeError(f"{field_name} must be exact or None")


@final
@dataclass(frozen=True, slots=True)
class CanonicalDexPatchV1:
    """Complete changed-cell normal form, excluding replay-owned nonce changes."""

    balance_writes: tuple[BalanceWriteV1, ...]
    pool_writes: tuple[PoolWriteV1, ...]
    lp_writes: tuple[LPPositionWriteV1, ...]
    fee_accumulator_write: FeeAccumulatorWriteV1 | None
    vault_write: VaultWriteV1 | None
    oracle_write: OracleWriteV1 | None
    perps_write: PerpsWriteV1 | None

    def __post_init__(self) -> None:
        _validate_canonical_write_sequence_v1(
            "balance_writes", self.balance_writes, BalanceWriteV1, "key", MAX_BALANCES_V1
        )
        _validate_canonical_write_sequence_v1(
            "pool_writes", self.pool_writes, PoolWriteV1, "pool_id", MAX_POOLS_V1
        )
        _validate_canonical_write_sequence_v1(
            "lp_writes", self.lp_writes, LPPositionWriteV1, "key", MAX_LP_ENTRIES_V1
        )
        _validate_patch_no_ops_v1(self.balance_writes, self.pool_writes, self.lp_writes)
        for field_name, value, expected_type in (
            ("fee_accumulator_write", self.fee_accumulator_write, FeeAccumulatorWriteV1),
            ("vault_write", self.vault_write, VaultWriteV1),
            ("oracle_write", self.oracle_write, OracleWriteV1),
            ("perps_write", self.perps_write, PerpsWriteV1),
        ):
            _validate_optional_write_v1(field_name, value, expected_type)


@final
@dataclass(frozen=True, slots=True)
class OwnedDexEffectsV1:
    """Canonical effects derived from the retained evaluated settlement."""

    settlement: OwnedSettlementV1
    total_swap_fees: int
    fee_allocation: FCISFeeAllocationV1 | None

    def __post_init__(self) -> None:
        if type(self.settlement) is not OwnedSettlementV1:
            raise TypeError("effects settlement must be exact")
        if type(self.total_swap_fees) is not int or self.total_swap_fees < 0:
            raise TypeError("total_swap_fees must be an exact nonnegative int")
        if self.fee_allocation is not None and type(self.fee_allocation) is not FCISFeeAllocationV1:
            raise TypeError("fee_allocation must be exact or None")
        derived_total = sum(
            0 if fill.fee_paid is None else fill.fee_paid for fill in self.settlement.fills
        )
        if self.total_swap_fees != derived_total:
            raise ValueError("effect total must equal the exact fill-fee sum")


@final
@dataclass(frozen=True, slots=True)
class NullifierRecordV1:
    pubkey: str
    intent_id: str

    def __post_init__(self) -> None:
        if type(self.pubkey) is not str:
            raise TypeError("nullifier pubkey must be an exact string")
        if canonical_hex_fixed_allow_0x(self.pubkey, nbytes=48, name="pubkey") != self.pubkey:
            raise ValueError("nullifier pubkey must be canonical")
        if type(self.intent_id) is not str:
            raise TypeError("nullifier intent_id must be an exact string")
        if (
            canonical_hex_fixed_allow_0x(
                self.intent_id,
                nbytes=32,
                name="intent_id",
            )
            != self.intent_id
        ):
            raise ValueError("nullifier intent_id must be canonical")


def _validate_nonce_advances_v1(nonce_advances: object) -> None:
    if type(nonce_advances) is not tuple or any(
        type(advance) is not NonceAdvanceV1 for advance in nonce_advances
    ):
        raise TypeError("nonce_advances must be an exact owned tuple")
    if len(nonce_advances) > MAX_NONCES_V1:
        raise ValueError("nonce advance limit exceeded")
    if not _strictly_increasing(nonce_advances, "pubkey"):
        raise ValueError("nonce advances must be in strict protocol order")


def _validate_nullifiers_v1(nullifiers: object) -> None:
    if type(nullifiers) is not tuple or any(
        type(record) is not NullifierRecordV1 for record in nullifiers
    ):
        raise TypeError("nullifiers must be an exact owned tuple")
    if len(nullifiers) > MAX_FCIS_NULLIFIERS_V1:
        raise ValueError("nullifier limit exceeded")
    nullifier_keys = tuple((record.pubkey, record.intent_id) for record in nullifiers)
    if any(
        nullifier_keys[index - 1] >= nullifier_keys[index]
        for index in range(1, len(nullifier_keys))
    ):
        raise ValueError("nullifiers must be in strict protocol order")


@final
@dataclass(frozen=True, slots=True)
class ReplayUpdateV1:
    """Exact replay-update data; authority requires a controlled decision lineage."""

    nonce_advances: tuple[NonceAdvanceV1, ...]
    nullifiers: tuple[NullifierRecordV1, ...]

    def __post_init__(self) -> None:
        _validate_nonce_advances_v1(self.nonce_advances)
        _validate_nullifiers_v1(self.nullifiers)


@final
@dataclass(frozen=True, slots=True)
class CommitPlanV1:
    """Exact plan data; controlled derivation later binds it to commit authority."""

    patch: CanonicalDexPatchV1
    effects: OwnedDexEffectsV1
    replay: ReplayUpdateV1

    def __post_init__(self) -> None:
        if type(self.patch) is not CanonicalDexPatchV1:
            raise TypeError("commit patch must be exact")
        if type(self.effects) is not OwnedDexEffectsV1:
            raise TypeError("commit effects must be exact")
        if type(self.replay) is not ReplayUpdateV1:
            raise TypeError("commit replay update must be exact")


FCISOptionalModuleWriteV1: TypeAlias = VaultWriteV1 | OracleWriteV1 | PerpsWriteV1


__all__ = (
    "BalanceWriteSourceV1",
    "CanonicalDexPatchSourceV1",
    "CanonicalDexPatchV1",
    "CommitPlanSourceV1",
    "CommitPlanV1",
    "FCIS_COMMIT_PLAN_SCHEMA_ID_V1",
    "FCIS_DEX_PATCH_SCHEMA_ID_V1",
    "FCIS_EFFECTS_SCHEMA_ID_V1",
    "FCIS_REPLAY_UPDATE_SCHEMA_ID_V1",
    "FCISFeeAllocationSourceV1",
    "FCISOptionalModuleWriteV1",
    "FeeAccumulatorWriteSourceV1",
    "FeeAccumulatorWriteV1",
    "LPPositionValueSourceV1",
    "LPPositionWriteSourceV1",
    "MAX_FCIS_NULLIFIERS_V1",
    "NonceAdvanceSourceV1",
    "NullifierRecordSourceV1",
    "NullifierRecordV1",
    "OracleWriteSourceV1",
    "OracleWriteV1",
    "OwnedDexEffectsSourceV1",
    "OwnedDexEffectsV1",
    "PerpsWriteSourceV1",
    "PerpsWriteV1",
    "PoolWriteSourceV1",
    "ReplayUpdateSourceV1",
    "ReplayUpdateV1",
    "VaultWriteSourceV1",
    "VaultWriteV1",
)
