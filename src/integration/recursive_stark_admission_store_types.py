"""Data-only value types for durable recursive STARK replay admission."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from src.core.recursive_stark_admission import (
    MAX_ADMISSION_INDEX_ENTRIES,
    MAX_CHAIN_ID_BYTES,
    RecursiveStarkAdmissionRejectReason,
    RecursiveStarkAdmissionSlot,
)

MAX_SQLITE_REVISION = (1 << 63) - 1


class RecursiveStarkAdmissionStoreError(RuntimeError):
    """Stable fail-closed durable-store error."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


class DurableRecursiveStarkAdmissionDisposition(str, Enum):
    """Data-only durable outcome disposition."""

    COMMITTED = "committed"
    IDEMPOTENT_REPLAY = "idempotent_replay"
    REJECTED = "rejected"


@dataclass(frozen=True, slots=True)
class DurableRecursiveStarkAdmissionCursor:
    """Canonical compare-and-swap cursor for the replay-index database."""

    revision: int
    state_root: str
    chain_id: str | None
    root_count: int
    slot_count: int
    child_claim_count: int
    receipt_count: int
    message_count: int

    def __post_init__(self) -> None:
        _require_count(self.revision, name="cursor.revision", maximum=MAX_SQLITE_REVISION)
        _hash_bytes(self.state_root, name="cursor.state_root")
        if self.chain_id is not None:
            _require_token(
                self.chain_id,
                name="cursor.chain_id",
                maximum=MAX_CHAIN_ID_BYTES,
            )
        for name in (
            "root_count",
            "slot_count",
            "child_claim_count",
            "receipt_count",
            "message_count",
        ):
            _require_count(
                getattr(self, name),
                name=f"cursor.{name}",
                maximum=MAX_ADMISSION_INDEX_ENTRIES,
            )
        if self.root_count != self.slot_count:
            raise ValueError("cursor root and slot counts must match")
        if self.revision != self.root_count:
            raise ValueError("cursor revision and root count must match")
        if (self.revision == 0) != (self.chain_id is None):
            raise ValueError("cursor revision and chain scope disagree")


@dataclass(frozen=True, slots=True)
class DurableRecursiveStarkAdmissionReceipt:
    """Canonical stored outcome for retry reconciliation."""

    outcome_key: str
    slot: RecursiveStarkAdmissionSlot
    root_journal_hash: str
    committed_revision: int
    previous_state_root: str
    result_state_root: str
    result_root_count: int
    result_slot_count: int
    result_child_claim_count: int
    result_receipt_count: int
    result_message_count: int
    authority_manifest_sha256: str
    verifier_executable_sha256: str
    verification_request_sha256: str
    release_binding_config_digest: str
    replay_manifest_sha256: str

    def __post_init__(self) -> None:
        _hash_bytes(self.outcome_key, name="receipt.outcome_key")
        _hash_bytes(self.root_journal_hash, name="receipt.root_journal_hash")
        _hash_bytes(self.previous_state_root, name="receipt.previous_state_root")
        _hash_bytes(self.result_state_root, name="receipt.result_state_root")
        _require_count(
            self.committed_revision,
            name="receipt.committed_revision",
            maximum=MAX_SQLITE_REVISION,
            minimum=1,
        )
        for name in (
            "result_root_count",
            "result_slot_count",
            "result_child_claim_count",
            "result_receipt_count",
            "result_message_count",
        ):
            _require_count(
                getattr(self, name),
                name=f"receipt.{name}",
                maximum=MAX_ADMISSION_INDEX_ENTRIES,
            )
        if self.result_root_count != self.result_slot_count:
            raise ValueError("receipt root and slot counts must match")
        if self.committed_revision != self.result_root_count:
            raise ValueError("receipt revision and root count must match")
        for name in (
            "authority_manifest_sha256",
            "verifier_executable_sha256",
            "verification_request_sha256",
        ):
            _bare_sha256(getattr(self, name), name=f"receipt.{name}")
        _prefixed_sha256(
            self.release_binding_config_digest,
            prefix="0x",
            name="receipt.release_binding_config_digest",
        )
        _prefixed_sha256(
            self.replay_manifest_sha256,
            prefix="sha256:",
            name="receipt.replay_manifest_sha256",
        )


@dataclass(frozen=True, slots=True)
class DurableRecursiveStarkAdmissionResult:
    """Data-only result from one transactional replay-index evaluation."""

    disposition: DurableRecursiveStarkAdmissionDisposition
    head_cursor: DurableRecursiveStarkAdmissionCursor
    receipt: DurableRecursiveStarkAdmissionReceipt | None
    reject_reason: RecursiveStarkAdmissionRejectReason | None

    def __post_init__(self) -> None:
        if not isinstance(self.disposition, DurableRecursiveStarkAdmissionDisposition):
            raise TypeError("disposition must be DurableRecursiveStarkAdmissionDisposition")
        if not isinstance(self.head_cursor, DurableRecursiveStarkAdmissionCursor):
            raise TypeError("head_cursor must be DurableRecursiveStarkAdmissionCursor")
        if self.disposition is DurableRecursiveStarkAdmissionDisposition.REJECTED:
            if self.receipt is not None:
                raise ValueError("rejected durable admission cannot include a receipt")
            if not isinstance(self.reject_reason, RecursiveStarkAdmissionRejectReason):
                raise ValueError("rejected durable admission requires a typed reason")
            return
        if not isinstance(self.receipt, DurableRecursiveStarkAdmissionReceipt):
            raise ValueError("accepted durable admission requires a stored receipt")
        if self.reject_reason is not None:
            raise ValueError("accepted durable admission cannot include a reject reason")

    @property
    def accepted(self) -> bool:
        return self.disposition is not DurableRecursiveStarkAdmissionDisposition.REJECTED

    @property
    def committed(self) -> bool:
        return self.disposition is DurableRecursiveStarkAdmissionDisposition.COMMITTED

    @property
    def idempotent_replay(self) -> bool:
        return self.disposition is DurableRecursiveStarkAdmissionDisposition.IDEMPOTENT_REPLAY


def _hash_bytes(value: str, *, name: str) -> bytes:
    if type(value) is not str or len(value) != 66 or not value.startswith("0x"):
        raise ValueError(f"{name} must be canonical 0x-prefixed SHA-256")
    bare = value[2:]
    if any(character not in "0123456789abcdef" for character in bare):
        raise ValueError(f"{name} must be canonical lowercase hex")
    result = bytes.fromhex(bare)
    if result == bytes(32):
        raise ValueError(f"{name} must be nonzero")
    return result


def _hex_hash(value: bytes) -> str:
    if len(value) != 32 or value == bytes(32):
        raise ValueError("stored hash must be 32 nonzero bytes")
    return "0x" + value.hex()


def _bare_sha256(value: str, *, name: str) -> str:
    if type(value) is not str or len(value) != 64:
        raise ValueError(f"{name} must be lowercase 64-character hex")
    if any(character not in "0123456789abcdef" for character in value):
        raise ValueError(f"{name} must be lowercase 64-character hex")
    return value


def _prefixed_sha256(value: str, *, prefix: str, name: str) -> str:
    if type(value) is not str or not value.startswith(prefix):
        raise ValueError(f"{name} must start with {prefix}")
    _bare_sha256(value[len(prefix) :], name=name)
    return value


def _require_token(value: str, *, name: str, maximum: int) -> str:
    if type(value) is not str or not value:
        raise ValueError(f"{name} must be a non-empty string")
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must be ASCII") from exc
    if len(encoded) > maximum:
        raise ValueError(f"{name} exceeds {maximum} bytes")
    token_characters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:-"
    if any(character not in token_characters for character in value):
        raise ValueError(f"{name} contains unsupported characters")
    return value


def _require_count(
    value: int,
    *,
    name: str,
    maximum: int,
    minimum: int = 0,
) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < minimum or value > maximum:
        raise ValueError(f"{name} must be in {minimum}..{maximum}")
    return value
