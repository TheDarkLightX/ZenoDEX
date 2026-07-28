"""Exact per-asset, per-custodian fee values for the unmounted FCIS V2 path."""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import final

from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
    CommittedBalanceTableV1,
)
from ..state.state_transitions import CanonicalBalancePatchV1

FEE_CUSTODY_SCHEMA_REVISION_V2 = "zenodex/fcis/fee-custody/v2"
PROTOCOL_FEE_CREDIT_SCHEMA_ID_V2 = "zenodex/fcis/fee-custody/protocol-credit/v2"
PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2 = "zenodex/fcis/fee-custody/protocol-credit-batch/v2"
FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2 = "zenodex/fcis/fee-custody/distribution-policy/v2"
FEE_ACCUMULATOR_SCHEMA_ID_V2 = "zenodex/fcis/fee-custody/accumulator/v2"
ASSET_FEE_DISTRIBUTION_SCHEMA_ID_V2 = "zenodex/fcis/fee-custody/asset-distribution/v2"
ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2 = "zenodex/fcis/fee-custody/asset-distribution-batch/v2"
FEE_CUSTODY_TRANSITION_RESULT_SCHEMA_ID_V2 = "zenodex/fcis/fee-custody/transition-result/v2"
MAX_FEE_CREDITS_V2 = 256
MAX_FEE_CUSTODY_KEYS_V2 = 50_000
MAX_FEE_BALANCE_DELTAS_V2 = 200_000
MAX_FEE_AMOUNT_V2 = (1 << 256) - 1
BPS_DENOMINATOR_V2 = 10_000

_FEE_CUSTODY_RESULT_TOKEN_V2 = object()


class FCISFeeCustodyEnumTagV2(Enum):
    """This closed profile intentionally has no enum variants."""


class FCISFeeCustodyRecordTagV2(Enum):
    PROTOCOL_FEE_CREDIT = "protocol_fee_credit_v2"
    DISTRIBUTION_POLICY = "distribution_policy_v2"
    DUST_ENTRY = "dust_entry_v2"
    ACCUMULATOR = "accumulator_v2"
    ASSET_DISTRIBUTION = "asset_distribution_v2"


@final
@dataclass(frozen=True, slots=True)
class ProtocolFeeCreditSourceV2:
    source_custody_pubkey: object
    asset: object
    amount: object


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionPolicySourceV2:
    buyback_bps: object
    treasury_bps: object
    rewards_bps: object
    buyback_custody_pubkey: object
    treasury_custody_pubkey: object
    rewards_custody_pubkey: object


@final
@dataclass(frozen=True, slots=True)
class FeeDustEntrySourceV2:
    source_custody_pubkey: object
    asset: object
    amount: object


@final
@dataclass(frozen=True, slots=True)
class FeeAccumulatorSourceV2:
    entries: object


@final
@dataclass(frozen=True, slots=True)
class AssetFeeDistributionSourceV2:
    source_custody_pubkey: object
    asset: object
    buyback_custody_pubkey: object
    treasury_custody_pubkey: object
    rewards_custody_pubkey: object
    buyback_amount: object
    treasury_amount: object
    rewards_amount: object
    dust_carried: object


def _require_text_v2(name: str, value: object) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")
    if len(value) > MAX_STATE_STRING_CHARACTERS_V1:
        raise ValueError(f"{name} exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        raise ValueError(f"{name} exceeds its UTF-8 bound")
    return value


def _require_amount_v2(name: str, value: object, *, minimum: int) -> int:
    if type(value) is not int or not minimum <= value <= MAX_FEE_AMOUNT_V2:
        raise TypeError(f"{name} must be an exact bounded integer")
    return value


def _custody_key_v2(source_custody_pubkey: str, asset: str) -> tuple[str, str]:
    return source_custody_pubkey, asset


@final
@dataclass(frozen=True, slots=True)
class ProtocolFeeCreditV2:
    """One protocol-owned credit proven by exact swap replay."""

    source_custody_pubkey: str
    asset: str
    amount: int

    def __post_init__(self) -> None:
        _require_text_v2("protocol fee source custody", self.source_custody_pubkey)
        _require_text_v2("protocol fee asset", self.asset)
        _require_amount_v2("protocol fee amount", self.amount, minimum=1)

    @property
    def custody_key(self) -> tuple[str, str]:
        return _custody_key_v2(self.source_custody_pubkey, self.asset)


@final
@dataclass(frozen=True, slots=True)
class FeeDistributionPolicyV2:
    """Exact percentages and same-asset destination custody accounts."""

    buyback_bps: int
    treasury_bps: int
    rewards_bps: int
    buyback_custody_pubkey: str
    treasury_custody_pubkey: str
    rewards_custody_pubkey: str

    def __post_init__(self) -> None:
        shares = (self.buyback_bps, self.treasury_bps, self.rewards_bps)
        if any(type(share) is not int for share in shares):
            raise TypeError("fee distribution shares must be exact integers")
        if any(not 0 <= share <= BPS_DENOMINATOR_V2 for share in shares):
            raise ValueError("fee distribution shares must be in [0, 10000]")
        if sum(shares) != BPS_DENOMINATOR_V2:
            raise ValueError("fee distribution shares must sum to 10000")
        _require_text_v2("buyback custody", self.buyback_custody_pubkey)
        _require_text_v2("treasury custody", self.treasury_custody_pubkey)
        _require_text_v2("rewards custody", self.rewards_custody_pubkey)


@final
@dataclass(frozen=True, slots=True)
class FeeDustEntryV2:
    """Sparse retained dust under one exact custody and asset key."""

    source_custody_pubkey: str
    asset: str
    amount: int

    def __post_init__(self) -> None:
        _require_text_v2("fee dust source custody", self.source_custody_pubkey)
        _require_text_v2("fee dust asset", self.asset)
        _require_amount_v2("fee dust amount", self.amount, minimum=1)

    @property
    def custody_key(self) -> tuple[str, str]:
        return _custody_key_v2(self.source_custody_pubkey, self.asset)


def _validate_dust_entries_v2(entries: object) -> None:
    if type(entries) is not tuple:
        raise TypeError("fee accumulator entries must be an exact tuple")
    if len(entries) > MAX_FEE_CUSTODY_KEYS_V2:
        raise ValueError("fee accumulator entry limit exceeded")
    previous_key: tuple[str, str] | None = None
    for entry in entries:
        if type(entry) is not FeeDustEntryV2:
            raise TypeError("fee accumulator entry must be exact")
        entry.__post_init__()
        if previous_key is not None and previous_key >= entry.custody_key:
            raise ValueError("fee accumulator entries must be in strict protocol order")
        previous_key = entry.custody_key


@final
@dataclass(frozen=True, slots=True)
class CommittedFeeAccumulatorStateV2:
    """Canonical sparse dust state keyed by source custody and asset."""

    entries: tuple[FeeDustEntryV2, ...]

    def __post_init__(self) -> None:
        _validate_dust_entries_v2(self.entries)


@final
@dataclass(frozen=True, slots=True)
class AssetFeeDistributionV2:
    """One state-applied, same-asset fee distribution receipt."""

    source_custody_pubkey: str
    asset: str
    buyback_custody_pubkey: str
    treasury_custody_pubkey: str
    rewards_custody_pubkey: str
    buyback_amount: int
    treasury_amount: int
    rewards_amount: int
    dust_carried: int

    def __post_init__(self) -> None:
        for name, text_value in (
            ("fee distribution source custody", self.source_custody_pubkey),
            ("fee distribution asset", self.asset),
            ("fee distribution buyback custody", self.buyback_custody_pubkey),
            ("fee distribution treasury custody", self.treasury_custody_pubkey),
            ("fee distribution rewards custody", self.rewards_custody_pubkey),
        ):
            _require_text_v2(name, text_value)
        for name, amount_value in (
            ("buyback amount", self.buyback_amount),
            ("treasury amount", self.treasury_amount),
            ("rewards amount", self.rewards_amount),
            ("dust carried", self.dust_carried),
        ):
            _require_amount_v2(name, amount_value, minimum=0)
        total = self.distributed_amount + self.dust_carried
        if total > MAX_FEE_AMOUNT_V2:
            raise ValueError("fee distribution total exceeds its integer domain")

    @property
    def custody_key(self) -> tuple[str, str]:
        return _custody_key_v2(self.source_custody_pubkey, self.asset)

    @property
    def distributed_amount(self) -> int:
        return self.buyback_amount + self.treasury_amount + self.rewards_amount


def _validate_distributions_v2(distributions: object) -> None:
    if type(distributions) is not tuple:
        raise TypeError("fee distributions must be an exact tuple")
    if len(distributions) > MAX_FEE_CUSTODY_KEYS_V2:
        raise ValueError("fee distribution limit exceeded")
    previous_key: tuple[str, str] | None = None
    for distribution in distributions:
        if type(distribution) is not AssetFeeDistributionV2:
            raise TypeError("fee distribution must be exact")
        distribution.__post_init__()
        if previous_key is not None and previous_key >= distribution.custody_key:
            raise ValueError("fee distributions must be in strict protocol order")
        previous_key = distribution.custody_key


@final
@dataclass(frozen=True, slots=True)
class FeeCustodyTransitionOkV2:
    """One complete balance and accumulator candidate from the fee machine."""

    balances: CommittedBalanceTableV1
    balance_patch: CanonicalBalancePatchV1 | None
    accumulator: CommittedFeeAccumulatorStateV2
    distributions: tuple[AssetFeeDistributionV2, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _FEE_CUSTODY_RESULT_TOKEN_V2:
            raise TypeError("fee custody result requires controlled derivation")
        if type(self.balances) is not CommittedBalanceTableV1:
            raise TypeError("fee custody balances must be exact")
        self.balances.__post_init__()
        if self.balance_patch is not None:
            if type(self.balance_patch) is not CanonicalBalancePatchV1:
                raise TypeError("fee custody balance patch must be exact or None")
            self.balance_patch.__post_init__()
        if type(self.accumulator) is not CommittedFeeAccumulatorStateV2:
            raise TypeError("fee custody accumulator must be exact")
        self.accumulator.__post_init__()
        _validate_distributions_v2(self.distributions)


def _fee_custody_ok_v2(
    *,
    balances: CommittedBalanceTableV1,
    balance_patch: CanonicalBalancePatchV1 | None,
    accumulator: CommittedFeeAccumulatorStateV2,
    distributions: tuple[AssetFeeDistributionV2, ...],
) -> FeeCustodyTransitionOkV2:
    return FeeCustodyTransitionOkV2(
        balances,
        balance_patch,
        accumulator,
        distributions,
        _FEE_CUSTODY_RESULT_TOKEN_V2,
    )


__all__ = (
    "ASSET_FEE_DISTRIBUTION_BATCH_SCHEMA_ID_V2",
    "ASSET_FEE_DISTRIBUTION_SCHEMA_ID_V2",
    "AssetFeeDistributionSourceV2",
    "AssetFeeDistributionV2",
    "BPS_DENOMINATOR_V2",
    "CommittedFeeAccumulatorStateV2",
    "FCISFeeCustodyEnumTagV2",
    "FCISFeeCustodyRecordTagV2",
    "FEE_ACCUMULATOR_SCHEMA_ID_V2",
    "FEE_CUSTODY_SCHEMA_REVISION_V2",
    "FEE_CUSTODY_TRANSITION_RESULT_SCHEMA_ID_V2",
    "FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2",
    "FeeAccumulatorSourceV2",
    "FeeCustodyTransitionOkV2",
    "FeeDistributionPolicySourceV2",
    "FeeDistributionPolicyV2",
    "FeeDustEntrySourceV2",
    "FeeDustEntryV2",
    "MAX_FEE_AMOUNT_V2",
    "MAX_FEE_BALANCE_DELTAS_V2",
    "MAX_FEE_CREDITS_V2",
    "MAX_FEE_CUSTODY_KEYS_V2",
    "PROTOCOL_FEE_CREDIT_BATCH_SCHEMA_ID_V2",
    "PROTOCOL_FEE_CREDIT_SCHEMA_ID_V2",
    "ProtocolFeeCreditSourceV2",
    "ProtocolFeeCreditV2",
)
