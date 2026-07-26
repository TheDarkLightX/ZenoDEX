"""Closed replay claims for the three-way M5 decision grammar.

These exact immutable values are safe to decode, store, compare, and
canonically encode.  They carry no commit authority.  Normative ``DecisionV1``
values are reserved for the controlled M5 derivation layer.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, final

from ..state.fcis_committed_state_values import FCISCommittedStateV1
from ..state.owned_collections import OwnedEnumV1
from .fcis_transition_values import CommitPlanV1

FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1 = "zenodex/fcis/receipt/accept/v1"
FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1 = "zenodex/fcis/receipt/reject/v1"
FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1 = "zenodex/fcis/receipt/committed-failure/v1"
FCIS_DECISION_SCHEMA_ID_V1 = "zenodex/fcis/decision/v1"
FCIS_AUTHORITY_SCHEMA_VERSION_V1 = 1
FCIS_AUTHORITY_CODEC_VERSION_V1 = 1


class FCISRejectCodeV1(Enum):
    """Closed union of aggregate rejection codes emitted by the spot profile."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    NONCANONICAL_SCALAR = "noncanonical_scalar"
    OUT_OF_RANGE = "out_of_range"
    WRONG_CONTAINER = "wrong_container"
    WRONG_KEY_TYPE = "wrong_key_type"
    UNKNOWN_FIELD = "unknown_field"
    MISSING_FIELD = "missing_field"
    UNSUPPORTED_VARIANT = "unsupported_variant"
    REGISTRY_DRIFT = "registry_drift"
    CYCLE = "cycle"
    DEPTH_LIMIT = "depth_limit"
    ITEM_LIMIT = "item_limit"
    BYTE_LIMIT = "byte_limit"
    DOMAIN_INVARIANT = "domain_invariant"
    ADMISSION_REJECTED = "admission_rejected"
    IMPOSSIBLE_RESULT = "impossible_result"
    CANONICAL_BINDING_REJECTED = "canonical_binding_rejected"
    INVALID_PRESTATE = "invalid_prestate"
    INVALID_NONCE = "invalid_nonce"
    INVALID_SENDER = "invalid_sender"
    MIXED_NONCE_PRESENCE = "mixed_nonce_presence"
    DUPLICATE_NONCE = "duplicate_nonce"
    INVALID_SEQUENCE = "invalid_sequence"
    PATCH_REJECTED = "patch_rejected"
    STRONG_SETTLEMENT_REJECTED = "strong_settlement_rejected"
    REJECTED_INTENT = "rejected_intent"
    INVALID_PARAMETERS = "invalid_parameters"
    CONSERVATION = "conservation"
    CANONICAL_EVIDENCE_REJECTED = "canonical_evidence_rejected"
    BUDGET_EXCEEDED = "budget_exceeded"


class FCISCommittedFailureCodeV1(Enum):
    """Grammar-reserved failure code; current spot derivation emits none."""

    RESERVED_UNMOUNTED = "reserved_unmounted"


def _is_digest_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value.startswith("0x")
        and all(character in "0123456789abcdef" for character in value[2:])
    )


@final
@dataclass(frozen=True, slots=True)
class RejectionPathTextPartSourceV1:
    text: object


@final
@dataclass(frozen=True, slots=True)
class RejectionPathIndexPartSourceV1:
    index: object


@final
@dataclass(frozen=True, slots=True)
class RejectionPathTextPartV1:
    text: str

    def __post_init__(self) -> None:
        if type(self.text) is not str or not self.text:
            raise TypeError("rejection path text must be exact and nonempty")


@final
@dataclass(frozen=True, slots=True)
class RejectionPathIndexPartV1:
    index: int

    def __post_init__(self) -> None:
        if type(self.index) is not int or self.index < 0:
            raise TypeError("rejection path index must be an exact nonnegative int")


RejectionPathPartV1: TypeAlias = RejectionPathTextPartV1 | RejectionPathIndexPartV1


@final
@dataclass(frozen=True, slots=True)
class ReceiptBindingSourceV1:
    algorithm_id: object
    algorithm_version: object
    schema_version: object
    codec_version: object
    execution_context_hash: object
    command_or_batch_root: object
    budget_hash: object
    pre_state_root: object
    next_state_root: object
    support_root_version: object
    support_root: object
    support_set_commitment: object
    snapshot_version: object
    snapshot_commitment: object
    patch_root: object
    commit_plan_root: object


@final
@dataclass(frozen=True, slots=True)
class AcceptanceReceiptSourceV1:
    binding: object


@final
@dataclass(frozen=True, slots=True)
class RejectionReceiptSourceV1:
    algorithm_id: object
    algorithm_version: object
    schema_version: object
    codec_version: object
    command_or_batch_root: object
    budget_hash: object
    execution_context_hash: object
    pre_state_root: object
    phase: object
    code: object
    path: object
    public_reason: object


@final
@dataclass(frozen=True, slots=True)
class CommittedFailureReceiptSourceV1:
    binding: object
    failure_code: object


@final
@dataclass(frozen=True, slots=True)
class AcceptSourceV1:
    next_state: object
    commit_plan: object
    receipt: object


@final
@dataclass(frozen=True, slots=True)
class RejectSourceV1:
    receipt: object


@final
@dataclass(frozen=True, slots=True)
class CommittedFailureSourceV1:
    next_state: object
    commit_plan: object
    receipt: object


@final
@dataclass(frozen=True, slots=True)
class ReceiptBindingClaimV1:
    """Decoded commitment fields awaiting same-lineage recomputation."""

    algorithm_id: str
    algorithm_version: int
    schema_version: int
    codec_version: int
    execution_context_hash: str
    command_or_batch_root: str
    budget_hash: str
    pre_state_root: str
    next_state_root: str
    support_root_version: int
    support_root: str
    support_set_commitment: str
    snapshot_version: int
    snapshot_commitment: str
    patch_root: str
    commit_plan_root: str

    def __post_init__(self) -> None:
        if type(self.algorithm_id) is not str or not self.algorithm_id:
            raise TypeError("receipt algorithm_id must be an exact nonempty string")
        for field_name in (
            "algorithm_version",
            "schema_version",
            "codec_version",
            "support_root_version",
            "snapshot_version",
        ):
            value = object.__getattribute__(self, field_name)
            if type(value) is not int or value <= 0:
                raise TypeError(f"{field_name} must be an exact positive int")
        for field_name in (
            "execution_context_hash",
            "command_or_batch_root",
            "budget_hash",
            "pre_state_root",
            "next_state_root",
            "support_root",
            "support_set_commitment",
            "snapshot_commitment",
            "patch_root",
            "commit_plan_root",
        ):
            if not _is_digest_v1(object.__getattribute__(self, field_name)):
                raise TypeError(f"{field_name} must be a canonical digest")


@final
@dataclass(frozen=True, slots=True)
class AcceptanceReceiptClaimV1:
    binding: ReceiptBindingClaimV1

    def __post_init__(self) -> None:
        if type(self.binding) is not ReceiptBindingClaimV1:
            raise TypeError("acceptance receipt claim binding must be exact")


def _validate_positive_rejection_versions_v1(receipt: object) -> None:
    for field_name in ("algorithm_version", "schema_version", "codec_version"):
        value = object.__getattribute__(receipt, field_name)
        if type(value) is not int or value <= 0:
            raise TypeError(f"{field_name} must be an exact positive int")


def _validate_optional_rejection_digests_v1(receipt: object) -> None:
    for field_name in (
        "command_or_batch_root",
        "budget_hash",
        "execution_context_hash",
        "pre_state_root",
    ):
        value = object.__getattribute__(receipt, field_name)
        if value is not None and not _is_digest_v1(value):
            raise TypeError(f"{field_name} must be None or a canonical digest")


def _validate_rejection_path_v1(path: object) -> None:
    if type(path) is not tuple or any(
        type(part) not in (RejectionPathTextPartV1, RejectionPathIndexPartV1) for part in path
    ):
        raise TypeError("rejection path must be an exact typed tuple")


@final
@dataclass(frozen=True, slots=True)
class RejectionReceiptClaimV1:
    """Decoded ordinary-rejection claim carrying no successor authority."""

    algorithm_id: str
    algorithm_version: int
    schema_version: int
    codec_version: int
    command_or_batch_root: str | None
    budget_hash: str | None
    execution_context_hash: str | None
    pre_state_root: str | None
    phase: OwnedEnumV1
    code: OwnedEnumV1
    path: tuple[RejectionPathPartV1, ...]
    public_reason: str

    def __post_init__(self) -> None:
        if type(self.algorithm_id) is not str or not self.algorithm_id:
            raise TypeError("rejection algorithm_id must be exact and nonempty")
        _validate_positive_rejection_versions_v1(self)
        _validate_optional_rejection_digests_v1(self)
        if type(self.phase) is not OwnedEnumV1:
            raise TypeError("rejection phase must be an exact owned enum")
        if type(self.code) is not OwnedEnumV1:
            raise TypeError("rejection code must be an exact owned enum")
        _validate_rejection_path_v1(self.path)
        if type(self.public_reason) is not str or not self.public_reason:
            raise TypeError("public_reason must be an exact nonempty string")


@final
@dataclass(frozen=True, slots=True)
class CommittedFailureReceiptClaimV1:
    binding: ReceiptBindingClaimV1
    failure_code: OwnedEnumV1

    def __post_init__(self) -> None:
        if type(self.binding) is not ReceiptBindingClaimV1:
            raise TypeError("committed-failure receipt claim binding must be exact")
        if type(self.failure_code) is not OwnedEnumV1:
            raise TypeError("failure_code must be an exact owned enum")


@final
@dataclass(frozen=True, slots=True)
class AcceptClaimV1:
    next_state: FCISCommittedStateV1
    commit_plan: CommitPlanV1
    receipt: AcceptanceReceiptClaimV1

    def __post_init__(self) -> None:
        if type(self.next_state) is not FCISCommittedStateV1:
            raise TypeError("accepted claim next_state must be exact")
        if type(self.commit_plan) is not CommitPlanV1:
            raise TypeError("accepted claim commit_plan must be exact")
        if type(self.receipt) is not AcceptanceReceiptClaimV1:
            raise TypeError("acceptance receipt claim must be exact")


@final
@dataclass(frozen=True, slots=True)
class RejectClaimV1:
    """Ordinary rejection claim contains only one exact receipt claim."""

    receipt: RejectionReceiptClaimV1

    def __post_init__(self) -> None:
        if type(self.receipt) is not RejectionReceiptClaimV1:
            raise TypeError("rejection receipt claim must be exact")


@final
@dataclass(frozen=True, slots=True)
class CommittedFailureClaimV1:
    next_state: FCISCommittedStateV1
    commit_plan: CommitPlanV1
    receipt: CommittedFailureReceiptClaimV1

    def __post_init__(self) -> None:
        if type(self.next_state) is not FCISCommittedStateV1:
            raise TypeError("committed-failure claim next_state must be exact")
        if type(self.commit_plan) is not CommitPlanV1:
            raise TypeError("committed-failure claim commit_plan must be exact")
        if type(self.receipt) is not CommittedFailureReceiptClaimV1:
            raise TypeError("committed-failure receipt claim must be exact")


DecisionClaimV1: TypeAlias = AcceptClaimV1 | RejectClaimV1 | CommittedFailureClaimV1
CommittableDecisionClaimV1: TypeAlias = AcceptClaimV1 | CommittedFailureClaimV1


__all__ = (
    "AcceptClaimV1",
    "AcceptSourceV1",
    "AcceptanceReceiptClaimV1",
    "AcceptanceReceiptSourceV1",
    "CommittedFailureClaimV1",
    "CommittedFailureReceiptClaimV1",
    "CommittedFailureReceiptSourceV1",
    "CommittedFailureSourceV1",
    "CommittableDecisionClaimV1",
    "DecisionClaimV1",
    "FCIS_ACCEPTANCE_RECEIPT_SCHEMA_ID_V1",
    "FCIS_AUTHORITY_CODEC_VERSION_V1",
    "FCIS_AUTHORITY_SCHEMA_VERSION_V1",
    "FCIS_COMMITTED_FAILURE_RECEIPT_SCHEMA_ID_V1",
    "FCIS_DECISION_SCHEMA_ID_V1",
    "FCIS_REJECTION_RECEIPT_SCHEMA_ID_V1",
    "FCISCommittedFailureCodeV1",
    "FCISRejectCodeV1",
    "ReceiptBindingClaimV1",
    "ReceiptBindingSourceV1",
    "RejectionPathIndexPartSourceV1",
    "RejectionPathIndexPartV1",
    "RejectionPathPartV1",
    "RejectionPathTextPartSourceV1",
    "RejectionPathTextPartV1",
    "RejectClaimV1",
    "RejectSourceV1",
    "RejectionReceiptClaimV1",
    "RejectionReceiptSourceV1",
)
