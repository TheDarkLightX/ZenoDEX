"""Data-only views for the experimental atomic ZRPF settlement kernel."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from src.core._zrpf_settlement_certificate_authority import (
    SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1,
)
from src.core._zrpf_settlement_commit_authority import (
    SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
)
from src.core.recursive_stark_admission import RecursiveStarkAdmissionRejectReason
from src.integration.recursive_stark_admission_store_types import (
    DurableRecursiveStarkAdmissionCursor,
    DurableRecursiveStarkAdmissionReceipt,
    RecursiveStarkAdmissionStoreError,
    _hash_bytes,
)

MAX_SETTLEMENT_REVISION_V1 = 1_048_576


class ZrpfAtomicSettlementStoreErrorV1(RecursiveStarkAdmissionStoreError):
    """Stable fail-closed combined-store error."""


class ZrpfAtomicSettlementRejectReasonV1(str, Enum):
    """Settlement-specific reject reasons after recursive admission checks."""

    ADMISSION_CURSOR_MISMATCH = "zrpf.atomic_settlement.admission_cursor_mismatch"
    SETTLEMENT_CURSOR_MISMATCH = "zrpf.atomic_settlement.settlement_cursor_mismatch"
    PRE_STATE_ROOT_MISMATCH = "zrpf.atomic_settlement.pre_state_root_mismatch"
    DUPLICATE_ECONOMIC_ACTION = "zrpf.atomic_settlement.duplicate_economic_action"
    DUPLICATE_AUTHORIZATION_NULLIFIER = "zrpf.atomic_settlement.duplicate_authorization_nullifier"
    DUPLICATE_AUTHORIZATION_GRANT_SPEND = (
        "zrpf.atomic_settlement.duplicate_authorization_grant_spend"
    )
    DUPLICATE_ASSET_EFFECT = "zrpf.atomic_settlement.duplicate_asset_effect"
    DUPLICATE_MESSAGE_EFFECT = "zrpf.atomic_settlement.duplicate_message_effect"
    DUPLICATE_CARRY_EFFECT = "zrpf.atomic_settlement.duplicate_carry_effect"
    DUPLICATE_REWARD_EFFECT = "zrpf.atomic_settlement.duplicate_reward_effect"
    CERTIFICATE_IDENTITY_CONFLICT = (
        "zrpf.atomic_settlement.certificate_identity_conflict"
    )
    EPOCH_NOT_MONOTONIC = "zrpf.atomic_settlement.epoch_not_monotonic"
    DUPLICATE_ACTION_NULLIFIER = "zrpf.atomic_settlement.duplicate_action_nullifier"
    DUPLICATE_CONSUMED_OBJECT = "zrpf.atomic_settlement.duplicate_consumed_object"


class ZrpfAtomicSettlementDispositionV1(str, Enum):
    """Outcome of the atomicity-only transaction kernel."""

    TRANSACTION_COMMITTED = "transaction_committed_authority_false"
    IDEMPOTENT_REPLAY = "idempotent_replay_authority_false"
    REJECTED = "rejected"


@dataclass(frozen=True, slots=True)
class DurableZrpfSettlementCursorV1:
    """Compare-and-swap cursor for settlement-plan history."""

    revision: int
    state_root: str
    plan_count: int

    def __post_init__(self) -> None:
        if type(self.revision) is not int:
            raise TypeError("settlement cursor revision must be an int")
        if self.revision < 0 or self.revision > MAX_SETTLEMENT_REVISION_V1:
            raise ValueError(
                f"settlement cursor revision must be in 0..{MAX_SETTLEMENT_REVISION_V1}"
            )
        _hash_bytes(self.state_root, name="settlement cursor state_root")
        if type(self.plan_count) is not int:
            raise TypeError("settlement cursor plan_count must be an int")
        if self.plan_count != self.revision:
            raise ValueError("settlement cursor revision and plan_count must match")


@dataclass(frozen=True, slots=True)
class DurableZrpfSettlementReceiptV1:
    """Data-only stored receipt for an atomicity-test settlement plan."""

    plan_commitment: str
    root_journal_hash: str
    settlement_revision: int
    previous_state_root: str
    result_state_root: str
    economic_action_ids_root: str
    authorization_nullifiers_root: str
    authorization_grant_spend_nullifiers_root: str
    settlement_authority: bool
    authority_blocked_reason: str

    def __post_init__(self) -> None:
        for name in (
            "plan_commitment",
            "root_journal_hash",
            "previous_state_root",
            "result_state_root",
            "economic_action_ids_root",
            "authorization_nullifiers_root",
            "authorization_grant_spend_nullifiers_root",
        ):
            _hash_bytes(getattr(self, name), name=f"settlement receipt {name}")
        if type(self.settlement_revision) is not int:
            raise TypeError("settlement receipt revision must be an int")
        if not 1 <= self.settlement_revision <= MAX_SETTLEMENT_REVISION_V1:
            raise ValueError("settlement receipt revision is out of bounds")
        if self.settlement_authority is not False:
            raise ValueError("V1 settlement receipt authority must remain false")
        if self.authority_blocked_reason != SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1:
            raise ValueError("V1 settlement receipt blocked reason mismatch")


@dataclass(frozen=True, slots=True)
class DurableZrpfAtomicSettlementResultV1:
    """Combined replay-admission and settlement transaction result."""

    disposition: ZrpfAtomicSettlementDispositionV1
    admission_head: DurableRecursiveStarkAdmissionCursor
    settlement_head: DurableZrpfSettlementCursorV1
    admission_receipt: DurableRecursiveStarkAdmissionReceipt | None
    settlement_receipt: DurableZrpfSettlementReceiptV1 | None
    recursive_reject_reason: RecursiveStarkAdmissionRejectReason | None
    settlement_reject_reason: ZrpfAtomicSettlementRejectReasonV1 | None

    def __post_init__(self) -> None:
        if type(self.disposition) is not ZrpfAtomicSettlementDispositionV1:
            raise TypeError("atomic settlement disposition must be typed")
        if type(self.admission_head) is not DurableRecursiveStarkAdmissionCursor:
            raise TypeError("admission_head must be a durable admission cursor")
        if type(self.settlement_head) is not DurableZrpfSettlementCursorV1:
            raise TypeError("settlement_head must be a durable settlement cursor")
        rejected = self.disposition is ZrpfAtomicSettlementDispositionV1.REJECTED
        if rejected:
            if self.admission_receipt is not None or self.settlement_receipt is not None:
                raise ValueError("rejected atomic settlement cannot contain receipts")
            reasons = (
                self.recursive_reject_reason is not None,
                self.settlement_reject_reason is not None,
            )
            if reasons.count(True) != 1:
                raise ValueError("rejected atomic settlement requires exactly one typed reason")
            return
        if type(self.admission_receipt) is not DurableRecursiveStarkAdmissionReceipt:
            raise ValueError("committed atomic settlement requires an admission receipt")
        if type(self.settlement_receipt) is not DurableZrpfSettlementReceiptV1:
            raise ValueError("committed atomic settlement requires a settlement receipt")
        if self.recursive_reject_reason is not None or self.settlement_reject_reason is not None:
            raise ValueError("committed atomic settlement cannot contain a reject reason")

    @property
    def committed(self) -> bool:
        return self.disposition is ZrpfAtomicSettlementDispositionV1.TRANSACTION_COMMITTED

    @property
    def idempotent_replay(self) -> bool:
        return self.disposition is ZrpfAtomicSettlementDispositionV1.IDEMPOTENT_REPLAY

    @property
    def settlement_authority(self) -> bool:
        return False


@dataclass(frozen=True, slots=True)
class DurableAuthenticatedSettlementCertificateReceiptV1:
    """Exact persisted certificate identity with explicit authority non-claim."""

    certificate_journal_hash: str
    semantic_root_journal_hash: str
    normalized_plan_commitment: str
    effect_plan_commitment: str
    settlement_receipt_id: str
    settlement_claim_hash: str
    settlement_image_id: str
    settlement_profile_id: str
    settlement_revision: int
    epoch_id: int
    previous_state_root: str
    result_state_root: str
    settlement_authority: bool
    authority_blocked_reason: str

    def __post_init__(self) -> None:
        for name in (
            "certificate_journal_hash",
            "semantic_root_journal_hash",
            "normalized_plan_commitment",
            "effect_plan_commitment",
            "settlement_receipt_id",
            "settlement_claim_hash",
            "settlement_image_id",
            "previous_state_root",
            "result_state_root",
        ):
            _hash_bytes(getattr(self, name), name=f"certificate receipt {name}")
        if (
            type(self.settlement_revision) is not int
            or not 1 <= self.settlement_revision <= MAX_SETTLEMENT_REVISION_V1
        ):
            raise ValueError("certificate settlement_revision is out of bounds")
        if type(self.epoch_id) is not int or not 0 <= self.epoch_id <= (1 << 64) - 1:
            raise ValueError("certificate epoch_id is out of bounds")
        if type(self.settlement_profile_id) is not str or not self.settlement_profile_id:
            raise ValueError("certificate settlement_profile_id must be nonempty")
        if self.settlement_authority is not False:
            raise ValueError("certificate settlement authority must remain false")
        if (
            self.authority_blocked_reason
            != SETTLEMENT_CERTIFICATE_AUTHORITY_BLOCKED_REASON_V1
        ):
            raise ValueError("certificate authority blocked reason mismatch")


@dataclass(frozen=True, slots=True)
class DurableZrpfStateBoundSettlementResultV1:
    """Atomic base result paired with the authenticated certificate receipt."""

    atomic_result: DurableZrpfAtomicSettlementResultV1
    certificate_receipt: DurableAuthenticatedSettlementCertificateReceiptV1 | None

    def __post_init__(self) -> None:
        if type(self.atomic_result) is not DurableZrpfAtomicSettlementResultV1:
            raise TypeError("atomic_result must be exact durable atomic settlement result")
        accepted = self.atomic_result.disposition is not ZrpfAtomicSettlementDispositionV1.REJECTED
        if accepted:
            if (
                type(self.certificate_receipt)
                is not DurableAuthenticatedSettlementCertificateReceiptV1
            ):
                raise ValueError("accepted state-bound settlement requires a certificate receipt")
        elif self.certificate_receipt is not None:
            raise ValueError("rejected state-bound settlement cannot contain a certificate receipt")

    @property
    def disposition(self) -> ZrpfAtomicSettlementDispositionV1:
        return self.atomic_result.disposition

    @property
    def committed(self) -> bool:
        return self.atomic_result.committed

    @property
    def idempotent_replay(self) -> bool:
        return self.atomic_result.idempotent_replay

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def admission_head(self) -> DurableRecursiveStarkAdmissionCursor:
        return self.atomic_result.admission_head

    @property
    def settlement_head(self) -> DurableZrpfSettlementCursorV1:
        return self.atomic_result.settlement_head

    @property
    def admission_receipt(self) -> DurableRecursiveStarkAdmissionReceipt | None:
        return self.atomic_result.admission_receipt

    @property
    def settlement_receipt(self) -> DurableZrpfSettlementReceiptV1 | None:
        return self.atomic_result.settlement_receipt

    @property
    def recursive_reject_reason(self) -> RecursiveStarkAdmissionRejectReason | None:
        return self.atomic_result.recursive_reject_reason

    @property
    def settlement_reject_reason(self) -> ZrpfAtomicSettlementRejectReasonV1 | None:
        return self.atomic_result.settlement_reject_reason


__all__ = [
    "DurableAuthenticatedSettlementCertificateReceiptV1",
    "DurableZrpfAtomicSettlementResultV1",
    "DurableZrpfStateBoundSettlementResultV1",
    "DurableZrpfSettlementCursorV1",
    "DurableZrpfSettlementReceiptV1",
    "ZrpfAtomicSettlementDispositionV1",
    "ZrpfAtomicSettlementRejectReasonV1",
    "ZrpfAtomicSettlementStoreErrorV1",
]
