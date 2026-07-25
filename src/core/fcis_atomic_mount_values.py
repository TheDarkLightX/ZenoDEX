"""Closed immutable values for the unmounted FCIS M5 authority graph.

The module contains data only: all authoritative alternatives are exact frozen
records and the ordinary rejection variant has no successor, plan, replay, or
outbox fields. Canonical encoders and builders live in
``fcis_atomic_mount_codec``; the shell reference interpreter lives under
``src.integration``.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, final

from ..state.owned_collections import OwnedMapV1
from ..state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
)

FCIS_M5_CONTRACT_ID_V1 = "zenodex/fcis-m5-atomic-mount/v2"
FCIS_M5_ALGORITHM_ID_V1 = "zenodex/fcis/atomic-step/v1"
FCIS_M5_ALGORITHM_VERSION_V1 = 1
FCIS_M5_SCHEMA_VERSION_V1 = 1
FCIS_M5_CODEC_VERSION_V1 = 1
MAX_AUTHORITY_TEXT_UTF8_V1 = 4_096
MAX_AUTHORITY_PAYLOAD_BYTES_V1 = 4_000_000
MAX_REPLAY_UPDATES_V1 = 200_000
MAX_OUTBOX_RECORDS_V1 = 200_000
MAX_U32_V1 = 0xFFFF_FFFF


def require_digest_v1(value: object, field: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise TypeError(f"{field} must be a lowercase 32-byte 0x digest")
    return value


def require_text_v1(value: object, field: str, *, allow_empty: bool = False) -> str:
    if type(value) is not str or (not allow_empty and not value):
        raise TypeError(f"{field} must be an exact canonical string")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as error:
        raise ValueError(f"{field} must contain Unicode scalar values") from error
    if len(encoded) > MAX_AUTHORITY_TEXT_UTF8_V1:
        raise ValueError(f"{field} exceeds its UTF-8 bound")
    return value


def require_canonical_pubkey_v1(value: object) -> str:
    if (
        type(value) is not str
        or len(value) != 98
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise TypeError("replay pubkey must be canonical 48-byte lowercase hex")
    return value


class FCISAuthorityPayloadDomainV1(Enum):
    CANONICAL_PATCH = "fcis_m5_canonical_patch"
    VALUE_PLAN = "fcis_m5_value_plan"
    RECEIPT_DETAIL = "fcis_m5_receipt_detail"
    OUTBOX_PAYLOAD = "fcis_m5_outbox_payload"


@final
@dataclass(frozen=True, slots=True)
class FCISRootBoundPayloadV1:
    domain: FCISAuthorityPayloadDomainV1
    canonical_bytes: bytes
    root: str

    def __post_init__(self) -> None:
        if type(self.domain) is not FCISAuthorityPayloadDomainV1:
            raise TypeError("authority payload domain must be exact")
        if type(self.canonical_bytes) is not bytes:
            raise TypeError("authority payload bytes must be exact bytes")
        if len(self.canonical_bytes) > MAX_AUTHORITY_PAYLOAD_BYTES_V1:
            raise ValueError("authority payload exceeds its byte budget")
        require_digest_v1(self.root, "authority payload root")
        from .fcis_atomic_mount_codec import root_bound_payload_digest_v1

        if self.root != root_bound_payload_digest_v1(self.domain, self.canonical_bytes):
            raise ValueError("authority payload root does not bind its canonical bytes")


@final
@dataclass(frozen=True, slots=True)
class FCISCommittedDexStateV1:
    """All eight exact state fields in the frozen M5 admission order."""

    snapshot_version: int
    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    nonces: CommittedNonceTableV1
    vault: CommittedVaultStateV1 | None
    oracle: CommittedOracleStateV1 | None
    fee_accumulator: CommittedFeeAccumulatorStateV1
    perps: CommittedPerpsStateV1 | None

    def __post_init__(self) -> None:
        if type(self.snapshot_version) is not int or self.snapshot_version <= 0:
            raise TypeError("snapshot_version must be an exact positive int")
        required = (
            (self.balances, CommittedBalanceTableV1, "balances"),
            (self.pools, OwnedMapV1, "pools"),
            (self.lp_balances, CommittedLPTableV1, "lp_balances"),
            (self.nonces, CommittedNonceTableV1, "nonces"),
            (self.fee_accumulator, CommittedFeeAccumulatorStateV1, "fee_accumulator"),
        )
        for value, exact_type, field in required:
            if type(value) is not exact_type:
                raise TypeError(f"{field} must be exact committed state")
        optional = (
            (self.vault, CommittedVaultStateV1, "vault"),
            (self.oracle, CommittedOracleStateV1, "oracle"),
            (self.perps, CommittedPerpsStateV1, "perps"),
        )
        for value, exact_type, field in optional:
            if value is not None and type(value) is not exact_type:
                raise TypeError(f"{field} must be exact committed state or None")
        from .fcis_atomic_mount_codec import canonical_committed_state_bytes_v1

        canonical_committed_state_bytes_v1(self)


@final
@dataclass(frozen=True, slots=True)
class FCISReplayUpdateV1:
    pubkey: str
    expected_last: int
    new_last: int

    def __post_init__(self) -> None:
        require_canonical_pubkey_v1(self.pubkey)
        if type(self.expected_last) is not int or not 0 <= self.expected_last <= MAX_U32_V1:
            raise TypeError("expected_last must be an exact u32")
        if type(self.new_last) is not int or not 1 <= self.new_last <= MAX_U32_V1:
            raise TypeError("new_last must be an exact positive u32")
        if self.new_last <= self.expected_last:
            raise ValueError("new_last must strictly advance expected_last")


def require_replay_updates_v1(value: object) -> tuple[FCISReplayUpdateV1, ...]:
    if type(value) is not tuple:
        raise TypeError("replay updates must be an exact tuple")
    if len(value) > MAX_REPLAY_UPDATES_V1:
        raise ValueError("replay updates exceed their item budget")
    previous: str | None = None
    for update in value:
        if type(update) is not FCISReplayUpdateV1:
            raise TypeError("replay update must be exact")
        if previous is not None and previous >= update.pubkey:
            raise ValueError("replay updates must be duplicate-free protocol order")
        previous = update.pubkey
    return value


class FCISReceiptOutcomeV1(Enum):
    ACCEPT = "accept"
    REJECT = "reject"
    COMMITTED_FAILURE = "committed_failure"


@final
@dataclass(frozen=True, slots=True)
class FCISReceiptV1:
    outcome: FCISReceiptOutcomeV1
    candidate_root: str | None
    code: str
    public_reason: str
    detail: FCISRootBoundPayloadV1 | None = None

    def __post_init__(self) -> None:
        if type(self.outcome) is not FCISReceiptOutcomeV1:
            raise TypeError("receipt outcome must be exact")
        require_text_v1(self.code, "receipt code")
        require_text_v1(self.public_reason, "receipt public_reason")
        if self.outcome is FCISReceiptOutcomeV1.REJECT:
            if self.candidate_root is not None:
                raise ValueError("ordinary rejection receipt cannot bind a candidate")
        else:
            require_digest_v1(self.candidate_root, "receipt candidate root")
        if self.detail is not None:
            if type(self.detail) is not FCISRootBoundPayloadV1:
                raise TypeError("receipt detail must be exact or None")
            if self.detail.domain is not FCISAuthorityPayloadDomainV1.RECEIPT_DETAIL:
                raise ValueError("receipt detail uses the wrong payload domain")


@final
@dataclass(frozen=True, slots=True)
class FCISOutboxEffectV1:
    """Exact input used to construct one outbox record."""

    effect_identity: str
    canonical_payload: bytes

    def __post_init__(self) -> None:
        require_text_v1(self.effect_identity, "outbox effect identity")
        if type(self.canonical_payload) is not bytes:
            raise TypeError("outbox effect payload must be exact bytes")
        if len(self.canonical_payload) > MAX_AUTHORITY_PAYLOAD_BYTES_V1:
            raise ValueError("outbox effect payload exceeds its byte budget")


@final
@dataclass(frozen=True, slots=True)
class FCISOutboxRecordV1:
    candidate_root: str
    receipt_root: str
    effect_index: int
    effect_identity: str
    payload: FCISRootBoundPayloadV1
    idempotency_key: str

    def __post_init__(self) -> None:
        require_digest_v1(self.candidate_root, "outbox candidate root")
        require_digest_v1(self.receipt_root, "outbox receipt root")
        if type(self.effect_index) is not int or self.effect_index < 0:
            raise TypeError("outbox effect index must be an exact nonnegative int")
        require_text_v1(self.effect_identity, "outbox effect identity")
        if type(self.payload) is not FCISRootBoundPayloadV1:
            raise TypeError("outbox payload must be exact")
        if self.payload.domain is not FCISAuthorityPayloadDomainV1.OUTBOX_PAYLOAD:
            raise ValueError("outbox payload uses the wrong payload domain")
        require_digest_v1(self.idempotency_key, "outbox idempotency key")
        from .fcis_atomic_mount_codec import outbox_idempotency_key_v1

        expected = outbox_idempotency_key_v1(
            self.receipt_root,
            self.effect_index,
            self.effect_identity,
        )
        if self.idempotency_key != expected:
            raise ValueError("outbox idempotency key is not receipt-derived")


@final
@dataclass(frozen=True, slots=True)
class FCISOutboxPlanV1:
    candidate_root: str
    receipt_root: str
    records: tuple[FCISOutboxRecordV1, ...]

    def __post_init__(self) -> None:
        require_digest_v1(self.candidate_root, "outbox-plan candidate root")
        require_digest_v1(self.receipt_root, "outbox-plan receipt root")
        if type(self.records) is not tuple:
            raise TypeError("outbox records must be an exact tuple")
        if len(self.records) > MAX_OUTBOX_RECORDS_V1:
            raise ValueError("outbox records exceed their item budget")
        for index, record in enumerate(self.records):
            if type(record) is not FCISOutboxRecordV1:
                raise TypeError("outbox record must be exact")
            if record.effect_index != index:
                raise ValueError("outbox indices must be contiguous protocol order")
            if record.candidate_root != self.candidate_root:
                raise ValueError("outbox record candidate root mismatch")
            if record.receipt_root != self.receipt_root:
                raise ValueError("outbox record receipt root mismatch")


@final
@dataclass(frozen=True, slots=True)
class FCISCommitPlanV1:
    candidate_root: str
    canonical_patch: FCISRootBoundPayloadV1
    value_plan: FCISRootBoundPayloadV1
    replay_updates: tuple[FCISReplayUpdateV1, ...]
    outbox_plan: FCISOutboxPlanV1

    def __post_init__(self) -> None:
        require_digest_v1(self.candidate_root, "commit-plan candidate root")
        if type(self.canonical_patch) is not FCISRootBoundPayloadV1:
            raise TypeError("canonical patch must be exact")
        if self.canonical_patch.domain is not FCISAuthorityPayloadDomainV1.CANONICAL_PATCH:
            raise ValueError("canonical patch uses the wrong payload domain")
        if type(self.value_plan) is not FCISRootBoundPayloadV1:
            raise TypeError("value plan must be exact")
        if self.value_plan.domain is not FCISAuthorityPayloadDomainV1.VALUE_PLAN:
            raise ValueError("value plan uses the wrong payload domain")
        require_replay_updates_v1(self.replay_updates)
        if type(self.outbox_plan) is not FCISOutboxPlanV1:
            raise TypeError("outbox plan must be exact")
        if self.outbox_plan.candidate_root != self.candidate_root:
            raise ValueError("outbox plan belongs to a different candidate")


@final
@dataclass(frozen=True, slots=True)
class FCISAcceptV1:
    next_state: FCISCommittedDexStateV1
    commit_plan: FCISCommitPlanV1
    receipt: FCISReceiptV1

    def __post_init__(self) -> None:
        if type(self.next_state) is not FCISCommittedDexStateV1:
            raise TypeError("accepted next state must be exact")
        if type(self.commit_plan) is not FCISCommitPlanV1:
            raise TypeError("accepted commit plan must be exact")
        if type(self.receipt) is not FCISReceiptV1:
            raise TypeError("accepted receipt must be exact")
        if self.receipt.outcome is not FCISReceiptOutcomeV1.ACCEPT:
            raise ValueError("accepted decision requires an accept receipt")
        if self.receipt.candidate_root != self.commit_plan.candidate_root:
            raise ValueError("accepted receipt and plan belong to different candidates")


@final
@dataclass(frozen=True, slots=True)
class FCISRejectV1:
    reason: str
    rejection_receipt: FCISReceiptV1

    def __post_init__(self) -> None:
        require_text_v1(self.reason, "rejection reason")
        if type(self.rejection_receipt) is not FCISReceiptV1:
            raise TypeError("rejection receipt must be exact")
        if self.rejection_receipt.outcome is not FCISReceiptOutcomeV1.REJECT:
            raise ValueError("ordinary reject requires a rejection receipt")
        if self.rejection_receipt.candidate_root is not None:
            raise ValueError("ordinary reject cannot expose a candidate")


@final
@dataclass(frozen=True, slots=True)
class FCISCommittedFailureV1:
    reason: str
    next_state: FCISCommittedDexStateV1
    commit_plan: FCISCommitPlanV1
    receipt: FCISReceiptV1

    def __post_init__(self) -> None:
        require_text_v1(self.reason, "committed-failure reason")
        if type(self.next_state) is not FCISCommittedDexStateV1:
            raise TypeError("committed-failure next state must be exact")
        if type(self.commit_plan) is not FCISCommitPlanV1:
            raise TypeError("committed-failure plan must be exact")
        if type(self.receipt) is not FCISReceiptV1:
            raise TypeError("committed-failure receipt must be exact")
        if self.receipt.outcome is not FCISReceiptOutcomeV1.COMMITTED_FAILURE:
            raise ValueError("committed failure requires its exact receipt variant")
        if self.receipt.candidate_root != self.commit_plan.candidate_root:
            raise ValueError("failure receipt and plan belong to different candidates")


FCISDecisionV1: TypeAlias = FCISAcceptV1 | FCISRejectV1 | FCISCommittedFailureV1


@final
@dataclass(frozen=True, slots=True)
class FCISCommitBundleV1:
    expected_pre_root: str
    execution_context_hash: str
    command_or_batch_root: str
    algorithm_id: str
    algorithm_version: int
    schema_version: int
    codec_version: int
    next_state: FCISCommittedDexStateV1
    next_state_root: str
    canonical_patch: FCISRootBoundPayloadV1
    commit_plan: FCISCommitPlanV1
    commit_plan_root: str
    receipt: FCISReceiptV1
    receipt_root: str
    replay_updates: tuple[FCISReplayUpdateV1, ...]
    outbox_plan: FCISOutboxPlanV1

    def __post_init__(self) -> None:
        require_digest_v1(self.expected_pre_root, "bundle expected pre-root")
        require_digest_v1(self.execution_context_hash, "bundle context hash")
        require_digest_v1(self.command_or_batch_root, "bundle command root")
        if self.algorithm_id != FCIS_M5_ALGORITHM_ID_V1:
            raise ValueError("unexpected M5 algorithm id")
        if self.algorithm_version != FCIS_M5_ALGORITHM_VERSION_V1:
            raise ValueError("unexpected M5 algorithm version")
        if self.schema_version != FCIS_M5_SCHEMA_VERSION_V1:
            raise ValueError("unexpected M5 schema version")
        if self.codec_version != FCIS_M5_CODEC_VERSION_V1:
            raise ValueError("unexpected M5 codec version")
        if type(self.next_state) is not FCISCommittedDexStateV1:
            raise TypeError("bundle next state must be exact")
        if type(self.canonical_patch) is not FCISRootBoundPayloadV1:
            raise TypeError("bundle canonical patch must be exact")
        if type(self.commit_plan) is not FCISCommitPlanV1:
            raise TypeError("bundle commit plan must be exact")
        if type(self.receipt) is not FCISReceiptV1:
            raise TypeError("bundle receipt must be exact")
        if self.receipt.outcome is FCISReceiptOutcomeV1.REJECT:
            raise ValueError("ordinary rejection cannot produce a commit bundle")
        require_replay_updates_v1(self.replay_updates)
        if type(self.outbox_plan) is not FCISOutboxPlanV1:
            raise TypeError("bundle outbox plan must be exact")
        from .fcis_atomic_mount_codec import validate_commit_bundle_v1

        validate_commit_bundle_v1(self)


__all__ = (
    "FCISAcceptV1",
    "FCISAuthorityPayloadDomainV1",
    "FCISCommitBundleV1",
    "FCISCommitPlanV1",
    "FCISCommittedDexStateV1",
    "FCISCommittedFailureV1",
    "FCISDecisionV1",
    "FCISOutboxEffectV1",
    "FCISOutboxPlanV1",
    "FCISOutboxRecordV1",
    "FCISReceiptOutcomeV1",
    "FCISReceiptV1",
    "FCISRejectV1",
    "FCISReplayUpdateV1",
    "FCISRootBoundPayloadV1",
    "FCIS_M5_ALGORITHM_ID_V1",
    "FCIS_M5_ALGORITHM_VERSION_V1",
    "FCIS_M5_CODEC_VERSION_V1",
    "FCIS_M5_CONTRACT_ID_V1",
    "FCIS_M5_SCHEMA_VERSION_V1",
    "require_digest_v1",
    "require_replay_updates_v1",
    "require_text_v1",
)
