from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
from typing import Any

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

CROSS_SHARD_DECISION_CERTIFICATE_SCHEMA = "zenodex/cross_shard_decision_certificate/v1"
CROSS_SHARD_PARTICIPANT_IDS_SCHEMA = "zenodex/cross_shard_participant_ids/v1"

USER_STATUS_COMMIT_ACCEPTED = "global_cross_shard_commit_accepted"
USER_STATUS_COMMIT_REJECTED = "global_cross_shard_commit_rejected"
USER_STATUS_PENDING_DECISION = "pending_global_cross_shard_decision"

_CERTIFICATE_KEYS = frozenset(
    {
        "schema",
        "batch_id",
        "transfer_id",
        "sharded_settlement_certificate_hash",
        "participant_shard_ids_hash",
        "receipt_status",
        "decision",
        "participants",
        "decision_step",
        "deadline_step",
    }
)
_PARTICIPANT_KEYS = frozenset(
    {
        "shard_id",
        "prepare_state",
        "visibility_state",
    }
)


class CrossShardDecisionState(str, Enum):
    COMMIT = "commit"
    REJECT = "reject"
    PENDING = "pending"


class CrossShardReceiptStatus(str, Enum):
    MATCHED = "matched"
    REJECTED = "rejected"
    PENDING = "pending"


class ParticipantPrepareState(str, Enum):
    PREPARED = "prepared"
    UNPREPARED = "unprepared"


class ParticipantVisibilityState(str, Enum):
    VISIBLE = "visible"
    HIDDEN = "hidden"


@dataclass(frozen=True)
class CrossShardDecisionParticipantV1:
    shard_id: str
    prepare_state: ParticipantPrepareState
    visibility_state: ParticipantVisibilityState

    def __post_init__(self) -> None:
        _require_id(self.shard_id, name="participant.shard_id")
        if not isinstance(self.prepare_state, ParticipantPrepareState):
            raise TypeError("participant.prepare_state must be a ParticipantPrepareState")
        if not isinstance(self.visibility_state, ParticipantVisibilityState):
            raise TypeError("participant.visibility_state must be a ParticipantVisibilityState")

    def to_payload(self) -> dict[str, Any]:
        return {
            "shard_id": self.shard_id,
            "prepare_state": self.prepare_state.value,
            "visibility_state": self.visibility_state.value,
        }

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any]) -> "CrossShardDecisionParticipantV1":
        _reject_unknown_keys(payload, allowed=_PARTICIPANT_KEYS, name="participant")
        return cls(
            shard_id=_require_id(payload.get("shard_id"), name="participant.shard_id"),
            prepare_state=_require_enum(
                payload.get("prepare_state"),
                enum_cls=ParticipantPrepareState,
                name="participant.prepare_state",
            ),
            visibility_state=_require_enum(
                payload.get("visibility_state"),
                enum_cls=ParticipantVisibilityState,
                name="participant.visibility_state",
            ),
        )


@dataclass(frozen=True)
class CrossShardDecisionCertificateV1:
    batch_id: str
    transfer_id: str
    sharded_settlement_certificate_hash: str
    participant_shard_ids_hash: str
    receipt_status: CrossShardReceiptStatus
    decision: CrossShardDecisionState
    participants: tuple[CrossShardDecisionParticipantV1, ...]
    decision_step: int
    deadline_step: int
    schema: str = CROSS_SHARD_DECISION_CERTIFICATE_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != CROSS_SHARD_DECISION_CERTIFICATE_SCHEMA:
            raise ValueError("unsupported cross-shard decision certificate schema")
        _require_id(self.batch_id, name="certificate.batch_id")
        _require_id(self.transfer_id, name="certificate.transfer_id")
        _require_hash(
            self.sharded_settlement_certificate_hash,
            name="certificate.sharded_settlement_certificate_hash",
        )
        _require_hash(
            self.participant_shard_ids_hash,
            name="certificate.participant_shard_ids_hash",
        )
        if not isinstance(self.receipt_status, CrossShardReceiptStatus):
            raise TypeError("certificate.receipt_status must be a CrossShardReceiptStatus")
        if not isinstance(self.decision, CrossShardDecisionState):
            raise TypeError("certificate.decision must be a CrossShardDecisionState")
        if not isinstance(self.participants, tuple):
            raise TypeError("certificate.participants must be a tuple")
        decision_step = _require_non_negative_int(
            self.decision_step,
            name="certificate.decision_step",
        )
        deadline_step = _require_non_negative_int(
            self.deadline_step,
            name="certificate.deadline_step",
        )
        if decision_step > deadline_step:
            raise ValueError("certificate.decision_step must be <= certificate.deadline_step")
        if not self.participants:
            raise ValueError("certificate.participants must be non-empty")
        for participant in self.participants:
            if not isinstance(participant, CrossShardDecisionParticipantV1):
                raise TypeError("certificate.participants must contain participant records")

    def to_payload(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "batch_id": self.batch_id,
            "transfer_id": self.transfer_id,
            "sharded_settlement_certificate_hash": self.sharded_settlement_certificate_hash,
            "participant_shard_ids_hash": self.participant_shard_ids_hash,
            "receipt_status": self.receipt_status.value,
            "decision": self.decision.value,
            "participants": [participant.to_payload() for participant in self.participants],
            "decision_step": self.decision_step,
            "deadline_step": self.deadline_step,
        }

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any]) -> "CrossShardDecisionCertificateV1":
        _reject_unknown_keys(payload, allowed=_CERTIFICATE_KEYS, name="certificate")
        schema = _require_id(payload.get("schema"), name="certificate.schema")
        if schema != CROSS_SHARD_DECISION_CERTIFICATE_SCHEMA:
            raise ValueError("unsupported cross-shard decision certificate schema")
        return cls(
            schema=schema,
            batch_id=_require_id(payload.get("batch_id"), name="certificate.batch_id"),
            transfer_id=_require_id(payload.get("transfer_id"), name="certificate.transfer_id"),
            sharded_settlement_certificate_hash=_require_hash(
                payload.get("sharded_settlement_certificate_hash"),
                name="certificate.sharded_settlement_certificate_hash",
            ),
            participant_shard_ids_hash=_require_hash(
                payload.get("participant_shard_ids_hash"),
                name="certificate.participant_shard_ids_hash",
            ),
            receipt_status=_require_enum(
                payload.get("receipt_status"),
                enum_cls=CrossShardReceiptStatus,
                name="certificate.receipt_status",
            ),
            decision=_require_enum(
                payload.get("decision"),
                enum_cls=CrossShardDecisionState,
                name="certificate.decision",
            ),
            participants=_parse_participants(payload.get("participants")),
            decision_step=_require_non_negative_int(
                payload.get("decision_step"),
                name="certificate.decision_step",
            ),
            deadline_step=_require_non_negative_int(
                payload.get("deadline_step"),
                name="certificate.deadline_step",
            ),
        )

    def hash(self) -> str:
        return cross_shard_decision_certificate_hash(self)


@dataclass(frozen=True)
class CrossShardDecisionVerificationResult:
    ok: bool
    error: str | None
    certificate_hash: str | None = None
    participant_shard_ids_hash: str | None = None
    decision: str | None = None
    user_status: str | None = None
    participant_count: int | None = None
    visible_participant_count: int | None = None
    decision_step: int | None = None
    deadline_step: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be bool")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted cross-shard decision result cannot include error")
            _require_hash(self.certificate_hash, name="result.certificate_hash")
            _require_hash(self.participant_shard_ids_hash, name="result.participant_shard_ids_hash")
            _require_id(self.decision, name="result.decision")
            _require_id(self.user_status, name="result.user_status")
            _require_positive_int(self.participant_count, name="result.participant_count")
            _require_non_negative_int(
                self.visible_participant_count,
                name="result.visible_participant_count",
            )
            _require_non_negative_int(self.decision_step, name="result.decision_step")
            _require_non_negative_int(self.deadline_step, name="result.deadline_step")
            return
        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected cross-shard decision result must include error")
        if (
            self.certificate_hash is not None
            or self.participant_shard_ids_hash is not None
            or self.decision is not None
            or self.user_status is not None
            or self.participant_count is not None
            or self.visible_participant_count is not None
            or self.decision_step is not None
            or self.deadline_step is not None
        ):
            raise ValueError("rejected cross-shard decision result cannot include accepted artifacts")


def participant_shard_ids_hash(shard_ids: Sequence[str]) -> str:
    ids = _parse_expected_shard_ids(shard_ids)
    if tuple(sorted(ids)) != ids:
        raise ValueError("expected participant shard ids must be sorted")
    body = {
        "schema": CROSS_SHARD_PARTICIPANT_IDS_SCHEMA,
        "participant_shard_ids": list(ids),
    }
    return sha256_hex(
        domain_sep_bytes("cross_shard_participant_ids", version=1)
        + canonical_json_bytes(body)
    )


def cross_shard_decision_certificate_hash(
    certificate: CrossShardDecisionCertificateV1 | Mapping[str, Any],
) -> str:
    payload = (
        certificate.to_payload()
        if isinstance(certificate, CrossShardDecisionCertificateV1)
        else CrossShardDecisionCertificateV1.from_payload(certificate).to_payload()
    )
    return sha256_hex(
        domain_sep_bytes("cross_shard_decision_certificate", version=1)
        + canonical_json_bytes(payload)
    )


def build_cross_shard_decision_certificate(
    *,
    batch_id: str,
    transfer_id: str,
    sharded_settlement_certificate_hash: str,
    receipt_status: CrossShardReceiptStatus,
    decision: CrossShardDecisionState,
    participants: Sequence[CrossShardDecisionParticipantV1],
    decision_step: int,
    deadline_step: int,
) -> CrossShardDecisionCertificateV1:
    parsed_participants = tuple(participants)
    ids = tuple(participant.shard_id for participant in parsed_participants)
    return CrossShardDecisionCertificateV1(
        batch_id=batch_id,
        transfer_id=transfer_id,
        sharded_settlement_certificate_hash=sharded_settlement_certificate_hash,
        participant_shard_ids_hash=participant_shard_ids_hash(ids),
        receipt_status=receipt_status,
        decision=decision,
        participants=parsed_participants,
        decision_step=decision_step,
        deadline_step=deadline_step,
    )


def verify_cross_shard_decision_certificate_payload(
    payload: Mapping[str, Any],
    *,
    expected_participant_shard_ids: Sequence[str] | None = None,
    expected_participant_shard_ids_hash: str | None = None,
    expected_sharded_settlement_certificate_hash: str | None = None,
    current_step: int | None = None,
) -> CrossShardDecisionVerificationResult:
    try:
        certificate = CrossShardDecisionCertificateV1.from_payload(payload)
        _validate_bindings(
            certificate,
            expected_participant_shard_ids=expected_participant_shard_ids,
            expected_participant_shard_ids_hash=expected_participant_shard_ids_hash,
            expected_sharded_settlement_certificate_hash=(
                expected_sharded_settlement_certificate_hash
            ),
        )
        _validate_step_window(certificate, current_step=current_step)
        visible_count = _validate_decision(certificate)
    except (TypeError, ValueError) as exc:
        return CrossShardDecisionVerificationResult(ok=False, error=str(exc))

    return CrossShardDecisionVerificationResult(
        ok=True,
        error=None,
        certificate_hash=certificate.hash(),
        participant_shard_ids_hash=certificate.participant_shard_ids_hash,
        decision=certificate.decision.value,
        user_status=_user_status(certificate.decision),
        participant_count=len(certificate.participants),
        visible_participant_count=visible_count,
        decision_step=certificate.decision_step,
        deadline_step=certificate.deadline_step,
    )


def _validate_bindings(
    certificate: CrossShardDecisionCertificateV1,
    *,
    expected_participant_shard_ids: Sequence[str] | None,
    expected_participant_shard_ids_hash: str | None,
    expected_sharded_settlement_certificate_hash: str | None,
) -> None:
    shard_ids = tuple(participant.shard_id for participant in certificate.participants)
    if tuple(sorted(shard_ids)) != shard_ids:
        raise ValueError("certificate.participants must be sorted by shard_id")
    if len(set(shard_ids)) != len(shard_ids):
        raise ValueError("duplicate shard_id in certificate.participants")
    computed_hash = participant_shard_ids_hash(shard_ids)
    if computed_hash != certificate.participant_shard_ids_hash:
        raise ValueError("certificate.participant_shard_ids_hash mismatch")
    if (
        expected_participant_shard_ids is not None
        and tuple(_parse_expected_shard_ids(expected_participant_shard_ids)) != shard_ids
    ):
        raise ValueError("certificate participant shard ids do not match expected shard ids")
    if expected_participant_shard_ids_hash is not None:
        expected_hash = _require_hash(
            expected_participant_shard_ids_hash,
            name="expected_participant_shard_ids_hash",
        )
        if expected_hash != certificate.participant_shard_ids_hash:
            raise ValueError("certificate participant shard ids hash does not match expected hash")
    if expected_sharded_settlement_certificate_hash is not None:
        expected_hash = _require_hash(
            expected_sharded_settlement_certificate_hash,
            name="expected_sharded_settlement_certificate_hash",
        )
        if expected_hash != certificate.sharded_settlement_certificate_hash:
            raise ValueError("certificate settlement hash does not match expected hash")


def _validate_step_window(
    certificate: CrossShardDecisionCertificateV1,
    *,
    current_step: int | None,
) -> None:
    if (
        certificate.decision == CrossShardDecisionState.PENDING
        and certificate.decision_step >= certificate.deadline_step
    ):
        raise ValueError("pending decision requires decision_step < deadline_step")
    if current_step is None:
        return
    step = _require_non_negative_int(current_step, name="current_step")
    if certificate.decision_step > step:
        raise ValueError("certificate.decision_step must be <= current_step")
    if certificate.decision == CrossShardDecisionState.PENDING and step >= certificate.deadline_step:
        raise ValueError("pending decision expired at deadline_step")


def _validate_decision(certificate: CrossShardDecisionCertificateV1) -> int:
    visible_count = sum(
        1
        for participant in certificate.participants
        if participant.visibility_state == ParticipantVisibilityState.VISIBLE
    )
    if certificate.decision == CrossShardDecisionState.COMMIT:
        if certificate.receipt_status != CrossShardReceiptStatus.MATCHED:
            raise ValueError("commit decision requires matched receipt status")
        if any(
            participant.prepare_state != ParticipantPrepareState.PREPARED
            for participant in certificate.participants
        ):
            raise ValueError("commit decision requires every participant prepared")
        if visible_count != len(certificate.participants):
            raise ValueError("commit decision requires every participant visible")
        return visible_count

    if visible_count != 0:
        raise ValueError("non-commit decision requires every participant hidden")
    if (
        certificate.decision == CrossShardDecisionState.REJECT
        and certificate.receipt_status != CrossShardReceiptStatus.REJECTED
    ):
        raise ValueError("reject decision requires rejected receipt status")
    if (
        certificate.decision == CrossShardDecisionState.PENDING
        and certificate.receipt_status != CrossShardReceiptStatus.PENDING
    ):
        raise ValueError("pending decision requires pending receipt status")
    return visible_count


def _user_status(decision: CrossShardDecisionState) -> str:
    if decision == CrossShardDecisionState.COMMIT:
        return USER_STATUS_COMMIT_ACCEPTED
    if decision == CrossShardDecisionState.REJECT:
        return USER_STATUS_COMMIT_REJECTED
    return USER_STATUS_PENDING_DECISION


def _parse_participants(value: object) -> tuple[CrossShardDecisionParticipantV1, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError("certificate.participants must be a sequence")
    return tuple(
        CrossShardDecisionParticipantV1.from_payload(
            _require_mapping(row, name="certificate.participant")
        )
        for row in value
    )


def _parse_expected_shard_ids(value: Sequence[str]) -> tuple[str, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError("expected participant shard ids must be a sequence")
    return tuple(_require_id(item, name="expected_participant_shard_id") for item in value)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_hash(value: object, *, name: str) -> str:
    text = _require_id(value, name=name)
    if not text.startswith("0x") or len(text) != 66:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex digest")
    try:
        int(text[2:], 16)
    except ValueError as exc:
        raise ValueError(f"{name} must be a 0x-prefixed sha256 hex digest") from exc
    if text[2:].lower() != text[2:]:
        raise ValueError(f"{name} must use lowercase hex")
    return text


def _require_enum(value: object, *, enum_cls: type[Enum], name: str):
    text = _require_id(value, name=name)
    try:
        return enum_cls(text)
    except ValueError as exc:
        allowed = ", ".join(item.value for item in enum_cls)
        raise ValueError(f"{name} must be one of: {allowed}") from exc


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
    return out


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _reject_unknown_keys(
    payload: Mapping[str, Any],
    *,
    allowed: frozenset[str],
    name: str,
) -> None:
    unknown = sorted(set(payload) - set(allowed))
    if unknown:
        raise ValueError(f"{name} has unsupported fields: {', '.join(unknown)}")
