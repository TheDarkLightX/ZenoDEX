"""Owned data values for one deterministic FCIS spot-step context."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from .dex_snapshot_profile import (
    DEX_SNAPSHOT_MAX_VERSION_V1,
    DEX_SNAPSHOT_MIN_VERSION_V1,
)
from .lp_duration_policy_values import LPDurationRiskPolicyV1
from .owned_collections import OwnedEnumV1

FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1 = "zenodex/fcis/context/spot-step/v1"
FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1 = "zenodex/fcis/context/settlement-value/v1"
FCIS_STEP_CONTEXT_SCHEMA_ID_V1 = "zenodex/fcis/context/step-value/v1"
FCIS_CONTEXT_STRING_MAX_CHARACTERS_V1 = 4_096
FCIS_CONTEXT_STRING_MAX_UTF8_BYTES_V1 = 16_384
BPS_DENOMINATOR_V1 = 10_000


class FCISSettlementModeV1(Enum):
    STRONG_REPLAY = "strong_replay"
    STRONG_PROOF_CARRYING = "strong_proof_carrying"


class FCISExecutionContextEnumTagV1(Enum):
    SETTLEMENT_MODE = "settlement_mode"


class FCISExecutionContextRecordTagV1(Enum):
    SETTLEMENT = "settlement"
    FEE_SPLIT = "fee_split"
    LP_DURATION_POLICY = "lp_duration_policy"
    STEP = "step"


@final
@dataclass(frozen=True, slots=True)
class FCISSettlementExecutionContextSourceV1:
    """Exact non-authoritative carrier; the closed profile decides admission."""

    now: object
    min_lp_position_age_seconds: object
    mode: object
    allow_cow_netting: object
    allow_snapshot_bound_quote_bindings: object
    protocol_fee_share_bps: object
    protocol_fee_recipient_pubkey: object


@final
@dataclass(frozen=True, slots=True)
class FCISFeeSplitPolicySourceV1:
    """Exact non-authoritative carrier for projected legacy fee policy fields."""

    buyback_bps: object
    treasury_bps: object
    rewards_bps: object


@final
@dataclass(frozen=True, slots=True)
class FCISStepExecutionContextSourceV1:
    """Exact carrier for every explicit policy value needed by one spot step."""

    settlement: object
    require_all_nonces: object
    reject_settlements_with_rejected_intents: object
    fee_split_policy: object
    lp_duration_policy: object
    snapshot_version: object


def settlement_mode_label_v1(mode: OwnedEnumV1) -> str:
    """Decode one admitted mode through the profile's fixed enum ordering."""

    if type(mode) is not OwnedEnumV1:
        raise TypeError("settlement mode must be an exact OwnedEnumV1")
    if (
        mode.schema_revision != FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1
        or mode.enum_tag_ordinal != 0
        or not 0 <= mode.member_ordinal < len(FCISSettlementModeV1)
    ):
        raise ValueError("settlement mode metadata does not match the context profile")
    return tuple(member.value for member in FCISSettlementModeV1)[mode.member_ordinal]


@final
@dataclass(frozen=True, slots=True)
class FCISSettlementExecutionContextV1:
    now: int
    min_lp_position_age_seconds: int
    mode: OwnedEnumV1
    allow_cow_netting: bool
    allow_snapshot_bound_quote_bindings: bool
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: str | None

    def __post_init__(self) -> None:
        if type(self.now) is not int or self.now < 0:
            raise TypeError("now must be an exact nonnegative int")
        if (
            type(self.min_lp_position_age_seconds) is not int
            or self.min_lp_position_age_seconds < 0
        ):
            raise TypeError("min_lp_position_age_seconds must be an exact nonnegative int")
        settlement_mode_label_v1(self.mode)
        if type(self.allow_cow_netting) is not bool:
            raise TypeError("allow_cow_netting must be an exact bool")
        if type(self.allow_snapshot_bound_quote_bindings) is not bool:
            raise TypeError("allow_snapshot_bound_quote_bindings must be an exact bool")
        if (
            type(self.protocol_fee_share_bps) is not int
            or not 0 <= self.protocol_fee_share_bps <= BPS_DENOMINATOR_V1
        ):
            raise TypeError("protocol_fee_share_bps must be an exact bounded int")
        recipient = self.protocol_fee_recipient_pubkey
        if recipient is not None and (type(recipient) is not str or not recipient):
            raise TypeError("protocol fee recipient must be None or an exact nonempty string")
        if self.protocol_fee_share_bps > 0 and recipient is None:
            raise ValueError("protocol fee recipient is required for a nonzero share")


@final
@dataclass(frozen=True, slots=True)
class FCISFeeSplitPolicyV1:
    buyback_bps: int
    treasury_bps: int
    rewards_bps: int

    def __post_init__(self) -> None:
        values = (self.buyback_bps, self.treasury_bps, self.rewards_bps)
        if any(type(value) is not int for value in values):
            raise TypeError("fee split values must be exact ints")
        if any(not 0 <= value <= BPS_DENOMINATOR_V1 for value in values):
            raise ValueError("fee split values must be in [0, 10000]")
        if sum(values) != BPS_DENOMINATOR_V1:
            raise ValueError("fee split values must sum to 10000")


@final
@dataclass(frozen=True, slots=True)
class FCISStepExecutionContextV1:
    settlement: FCISSettlementExecutionContextV1
    require_all_nonces: bool
    reject_settlements_with_rejected_intents: bool
    fee_split_policy: FCISFeeSplitPolicyV1 | None
    lp_duration_policy: LPDurationRiskPolicyV1 | None
    snapshot_version: int

    def __post_init__(self) -> None:
        if type(self.settlement) is not FCISSettlementExecutionContextV1:
            raise TypeError("settlement context must be exact")
        if type(self.require_all_nonces) is not bool:
            raise TypeError("require_all_nonces must be an exact bool")
        if type(self.reject_settlements_with_rejected_intents) is not bool:
            raise TypeError("rejected-intent policy must be an exact bool")
        if (
            self.fee_split_policy is not None
            and type(self.fee_split_policy) is not FCISFeeSplitPolicyV1
        ):
            raise TypeError("fee split policy must be None or exact")
        if (
            self.lp_duration_policy is not None
            and type(self.lp_duration_policy) is not LPDurationRiskPolicyV1
        ):
            raise TypeError("LP duration policy must be None or exact")
        if (
            type(self.snapshot_version) is not int
            or not DEX_SNAPSHOT_MIN_VERSION_V1
            <= self.snapshot_version
            <= DEX_SNAPSHOT_MAX_VERSION_V1
        ):
            raise TypeError("snapshot_version must be an exact supported int")


__all__ = (
    "BPS_DENOMINATOR_V1",
    "FCIS_CONTEXT_STRING_MAX_CHARACTERS_V1",
    "FCIS_CONTEXT_STRING_MAX_UTF8_BYTES_V1",
    "FCIS_EXECUTION_CONTEXT_SCHEMA_REVISION_V1",
    "FCIS_SETTLEMENT_CONTEXT_SCHEMA_ID_V1",
    "FCIS_STEP_CONTEXT_SCHEMA_ID_V1",
    "FCISExecutionContextEnumTagV1",
    "FCISExecutionContextRecordTagV1",
    "FCISFeeSplitPolicySourceV1",
    "FCISFeeSplitPolicyV1",
    "FCISSettlementExecutionContextSourceV1",
    "FCISSettlementExecutionContextV1",
    "FCISSettlementModeV1",
    "FCISStepExecutionContextSourceV1",
    "FCISStepExecutionContextV1",
    "settlement_mode_label_v1",
)
