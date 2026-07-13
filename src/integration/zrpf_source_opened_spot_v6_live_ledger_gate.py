"""Fail-closed live-ledger boundary for authenticated Spot V6 evidence.

The current V6 capability authenticates state-root transitions, ledger-cell
hash transitions, and conserved per-asset totals.  It does not carry the raw
typed ledger-cell values or account/pool debit and credit destinations needed
to re-execute a ``DexState`` transition.  Its governed settlement capability
also permanently reports ``settlement_authority=False``.

Consequently this module can only emit a typed no-op.  It provides the sole
current bridge from the private receipt-authenticated V6 capability toward a
future live-ledger adapter, so proof-only result objects cannot accidentally be
used as value-movement authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import final

from src.core._zrpf_settlement_certificate_authority import (
    SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,
    _AuthenticatedSourceOpenedSpotV6SettlementV1,
)

SOURCE_OPENED_SPOT_V6_LIVE_LEDGER_AUTHORITY_BLOCKED_REASON_V1 = (
    "source_opened_spot_v6_missing_governed_live_ledger_value_preimages_and_authority"
)


class SourceOpenedSpotV6LiveLedgerDispositionV1(str, Enum):
    """Current live-ledger disposition after exact V6 authentication."""

    BLOCKED = "blocked_no_state_change"


class SourceOpenedSpotV6LiveLedgerRejectReasonV1(str, Enum):
    """Stable reason why authenticated V6 evidence cannot move value."""

    VALUE_MOVEMENT_AUTHORITY_UNAVAILABLE = (
        "zrpf.source_opened_spot_v6.live_ledger.value_movement_authority_unavailable"
    )


@final
@dataclass(frozen=True, slots=True)
class SourceOpenedSpotV6LiveLedgerBlockedV1:
    """Data-only receipt for a receipt-authenticated value-movement no-op."""

    disposition: SourceOpenedSpotV6LiveLedgerDispositionV1
    reject_reason: SourceOpenedSpotV6LiveLedgerRejectReasonV1
    authority_blocked_reason: str
    epoch_id: int
    pre_state_root: str
    post_state_root: str
    plan_commitment: str

    def __post_init__(self) -> None:
        if self.disposition is not SourceOpenedSpotV6LiveLedgerDispositionV1.BLOCKED:
            raise ValueError("Spot V6 live-ledger disposition must remain blocked")
        if (
            self.reject_reason
            is not SourceOpenedSpotV6LiveLedgerRejectReasonV1.VALUE_MOVEMENT_AUTHORITY_UNAVAILABLE
        ):
            raise ValueError("Spot V6 live-ledger reject reason mismatch")
        if (
            self.authority_blocked_reason
            != SOURCE_OPENED_SPOT_V6_LIVE_LEDGER_AUTHORITY_BLOCKED_REASON_V1
        ):
            raise ValueError("Spot V6 live-ledger blocked reason mismatch")
        if type(self.epoch_id) is not int or not 0 <= self.epoch_id <= (1 << 64) - 1:
            raise ValueError("Spot V6 live-ledger epoch is out of bounds")
        for name in ("pre_state_root", "post_state_root", "plan_commitment"):
            _require_prefixed_hash(getattr(self, name), name=name)

    @property
    def state_changed(self) -> bool:
        return False

    @property
    def replay_indexes_changed(self) -> bool:
        return False

    @property
    def proof_association_changed(self) -> bool:
        return False

    @property
    def live_ledger_prestate_cas_verified(self) -> bool:
        return False

    @property
    def typed_value_transition_verified(self) -> bool:
        return False

    @property
    def durable_atomic_value_commit_verified(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def signature_authority(self) -> bool:
        return False

    @property
    def grant_authority(self) -> bool:
        return False

    @property
    def provider_retrievability_verified(self) -> bool:
        return False

    @property
    def external_finality_verified(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _reject_authenticated_source_opened_spot_v6_live_ledger_value_movement(
    authenticated: _AuthenticatedSourceOpenedSpotV6SettlementV1,
) -> SourceOpenedSpotV6LiveLedgerBlockedV1:
    """Accept only the private V6 capability and deterministically do nothing."""

    if type(authenticated) is not _AuthenticatedSourceOpenedSpotV6SettlementV1:
        raise TypeError("live-ledger gate requires the receipt-authenticated V6 capability")
    if not authenticated._has_private_seal():
        raise TypeError("live-ledger gate requires the sealed V6 capability")
    certificate_capability = authenticated.certificate
    if certificate_capability.settlement_authority is not False:
        raise TypeError("authenticated V6 settlement authority must remain false")
    if (
        certificate_capability.authority_blocked_reason
        != SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1
    ):
        raise TypeError("authenticated V6 settlement blocked reason mismatch")
    plan = certificate_capability.plan
    return SourceOpenedSpotV6LiveLedgerBlockedV1(
        disposition=SourceOpenedSpotV6LiveLedgerDispositionV1.BLOCKED,
        reject_reason=(
            SourceOpenedSpotV6LiveLedgerRejectReasonV1.VALUE_MOVEMENT_AUTHORITY_UNAVAILABLE
        ),
        authority_blocked_reason=(SOURCE_OPENED_SPOT_V6_LIVE_LEDGER_AUTHORITY_BLOCKED_REASON_V1),
        epoch_id=plan.epoch_id,
        pre_state_root=plan.pre_state_root,
        post_state_root=plan.post_state_root,
        plan_commitment=plan.commitment,
    )


def _require_prefixed_hash(value: object, *, name: str) -> None:
    if type(value) is not str or len(value) != 66 or not value.startswith("0x"):
        raise ValueError(f"{name} must be a canonical 0x-prefixed hash")
    if any(character not in "0123456789abcdef" for character in value[2:]):
        raise ValueError(f"{name} must be a canonical 0x-prefixed hash")


__all__ = [
    "SOURCE_OPENED_SPOT_V6_LIVE_LEDGER_AUTHORITY_BLOCKED_REASON_V1",
    "SourceOpenedSpotV6LiveLedgerBlockedV1",
    "SourceOpenedSpotV6LiveLedgerDispositionV1",
    "SourceOpenedSpotV6LiveLedgerRejectReasonV1",
]
