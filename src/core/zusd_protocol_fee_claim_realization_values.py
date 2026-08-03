"""Public source and rejection values for zUSD fee-claim realization V1."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, final

ZUSD_PROTOCOL_FEE_CLAIM_REALIZATION_SCHEMA_V1: Final = (
    "zenodex/zusd/protocol-fee-claim-realization/v1"
)
ZUSD_LEDGER_UNIT_E8_V1: Final = 100_000_000


class ZUSDProtocolFeeClaimRealizationRejectCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_IDENTITY = "invalid_identity"
    INVALID_CLAIM_STATE = "invalid_claim_state"
    INVALID_PRESTATE = "invalid_prestate"
    NEGATIVE_VALUE = "negative_value"
    ZERO_AMOUNT = "zero_amount"
    NON_WHOLE_AMOUNT = "non_whole_amount"
    VALUE_EXCEEDS_U256 = "value_exceeds_u256"
    AMOUNT_EXCEEDS_OUTSTANDING = "amount_exceeds_outstanding"
    LEDGER_SUPPLY_OVERFLOW = "ledger_supply_overflow"
    CLAIM_TRANSITION = "claim_transition"
    BALANCE_TRANSITION = "balance_transition"
    DELTA_CERTIFICATE = "delta_certificate"
    EXTERNAL_INSTANCE_MISMATCH = "external_instance_mismatch"
    INVALID_REALIZATION = "invalid_realization"


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeClaimRealizationSourceV1:
    """Caller-constructible exact-source envelope carrying no authority."""

    asset_id: object
    custody_pubkey: object
    pre_claim: object
    pre_balances: object
    debt_e8: object
    amount_e8: object


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeClaimRealizationRejectV1:
    """Typed rejection carrying no successor, patch, credit, or certificate."""

    code: ZUSDProtocolFeeClaimRealizationRejectCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not ZUSDProtocolFeeClaimRealizationRejectCodeV1:
            raise TypeError("fee-claim realization reject code must be exact")
        if type(self.path) is not tuple or not self.path:
            raise TypeError("fee-claim realization reject path must be a nonempty tuple")
        if any(type(part) is not str or not part for part in self.path):
            raise TypeError("fee-claim realization reject path parts must be nonempty strings")


def _reject_v1(
    code: ZUSDProtocolFeeClaimRealizationRejectCodeV1,
    *path: str,
) -> ZUSDProtocolFeeClaimRealizationRejectV1:
    return ZUSDProtocolFeeClaimRealizationRejectV1(code, tuple(path))


__all__ = (
    "ZUSD_LEDGER_UNIT_E8_V1",
    "ZUSD_PROTOCOL_FEE_CLAIM_REALIZATION_SCHEMA_V1",
    "ZUSDProtocolFeeClaimRealizationRejectCodeV1",
    "ZUSDProtocolFeeClaimRealizationRejectV1",
    "ZUSDProtocolFeeClaimRealizationSourceV1",
)
