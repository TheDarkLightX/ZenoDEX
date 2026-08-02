"""Typed E05 request and result boundary for the M6 atomic CAS port.

E05 is the linearizing boundary between the pure E04 retry classifier and a
datastore adapter.  The request owns a complete verified predecessor and
successor state, plus the fresh-reopen subject used by E04.  The adapter must
still compare the predecessor roots inside its write transaction.  A caller
holding an old request therefore receives a typed stale result after another
writer has advanced the database.

This module contains no I/O and makes no production-authentication claim.
The E04 values are verifier-owned research values; the SQLite experiment
provides the transaction and uniqueness refinement.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

from src.core.fcis_m6_e04_retry_classifier import (
    MAX_E04_REJECT_PATH_ITEMS_V1,
    E04AttemptV1,
    E04ReopenReceiptV1,
    E04StoredStateV1,
    is_verified_e04_attempt_v1,
    is_verified_e04_reopen_receipt_v1,
    is_verified_e04_stored_state_v1,
)
from src.state.canonical import canonical_json_bytes

FCIS_M6_E05_SCHEMA_V1: Final = "zenodex/fcis/m6/e05/expected-root-cas/v1"
FCIS_M6_E05_PUBLICATION_SET_SCHEMA_V1: Final = "zenodex/fcis/m6/e05/publication-set/v1"
MAX_E05_REJECT_PATH_ITEMS_V1: Final = MAX_E04_REJECT_PATH_ITEMS_V1


class E05Error(ValueError):
    """Raised when an E05 request or result is outside its closed domain."""


class E05CodeV1(Enum):
    """Typed outcomes of the E05 linearizing publication port."""

    COMMITTED = "committed"
    INVALID_REQUEST = "invalid_request"
    CLASSIFIER_REJECTED = "classifier_rejected"
    STALE_SNAPSHOT_CAS = "stale_snapshot_cas"
    STALE_STATE_CAS = "stale_state_cas"
    STALE_AUTHORITY_CAS = "stale_authority_cas"
    STALE_SEQUENCE_CAS = "stale_sequence_cas"
    CONSTRAINT_COLLISION = "constraint_collision"
    SQL_ROLLBACK = "sql_rollback"


@dataclass(frozen=True, slots=True)
class E05RejectV1:
    """Fail-closed E05 rejection with a bounded semantic path."""

    code: E05CodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not E05CodeV1:
            raise E05Error("E05 rejection code has the wrong exact type")
        if type(self.path) is not tuple or not self.path:
            raise E05Error("E05 rejection path must be a nonempty exact tuple")
        if len(self.path) > MAX_E05_REJECT_PATH_ITEMS_V1:
            raise E05Error("E05 rejection path exceeds the closed bound")
        if any(type(item) is not str or not item for item in self.path):
            raise E05Error("E05 rejection path contains an invalid item")


def _digest(value: object, name: str) -> None:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise E05Error(f"{name} must be a lowercase SHA-256 digest")


def _state_context_matches(left: E04StoredStateV1, right: E04StoredStateV1) -> bool:
    return bool(
        left.genesis_state_root == right.genesis_state_root
        and left.authority_epoch_index == right.authority_epoch_index
        and left.authority_state_root == right.authority_state_root
        and left.allowed_writer_roots == right.allowed_writer_roots
        and left.deployment_config_root == right.deployment_config_root
        and left.verifier_profile_root == right.verifier_profile_root
    )


@dataclass(frozen=True, slots=True)
class E05PublicationRequestV1:
    """One complete E04 successor request admitted to the CAS adapter.

    ``pre_state`` and ``post_state`` are verifier-owned canonical values.  The
    transaction must compare ``pre_state`` to the datastore head after it has
    begun, then install the exact ``post_state`` relation atomically.
    """

    attempt: E04AttemptV1
    pre_state: E04StoredStateV1
    post_state: E04StoredStateV1
    reopen_receipt: E04ReopenReceiptV1

    def __post_init__(self) -> None:
        if type(self.attempt) is not E04AttemptV1:
            raise E05Error("attempt has the wrong exact type")
        if not is_verified_e04_attempt_v1(self.attempt):
            raise E05Error("attempt lacks verifier provenance")
        if type(self.pre_state) is not E04StoredStateV1:
            raise E05Error("pre_state has the wrong exact type")
        if not is_verified_e04_stored_state_v1(self.pre_state):
            raise E05Error("pre_state lacks verifier provenance")
        if type(self.post_state) is not E04StoredStateV1:
            raise E05Error("post_state has the wrong exact type")
        if not is_verified_e04_stored_state_v1(self.post_state):
            raise E05Error("post_state lacks verifier provenance")
        if type(self.reopen_receipt) is not E04ReopenReceiptV1:
            raise E05Error("reopen_receipt has the wrong exact type")
        if not is_verified_e04_reopen_receipt_v1(self.reopen_receipt):
            raise E05Error("reopen_receipt lacks verifier provenance")

        attempt = self.attempt
        pre_state = self.pre_state
        post_state = self.post_state
        if attempt.expected_pre_root != pre_state.current_state_root:
            raise E05Error("attempt expected root is crossed with pre_state")
        if attempt.publication_sequence != len(pre_state.commits) + 1:
            raise E05Error("attempt sequence is not the next publication sequence")
        if not _state_context_matches(pre_state, post_state):
            raise E05Error("successor state changes immutable context")
        if len(post_state.commits) != len(pre_state.commits) + 1:
            raise E05Error("successor state does not append exactly one commit")
        successor = post_state.commits[-1]
        if successor.attempt != attempt:
            raise E05Error("successor state appends a different attempt")
        if successor.post_state_root != post_state.current_state_root:
            raise E05Error("successor commit does not name the successor head")
        if post_state.current_state_root == pre_state.current_state_root:
            raise E05Error("successor state does not advance the state root")

        identity = attempt.request_identity
        if identity.authority_epoch_index != pre_state.authority_epoch_index:
            raise E05Error("attempt authority epoch is crossed with pre_state")
        if attempt.authority_state_root != pre_state.authority_state_root:
            raise E05Error("attempt authority root is crossed with pre_state")
        if attempt.writer_profile_root not in pre_state.allowed_writer_roots:
            raise E05Error("attempt writer is not allowed by pre_state")
        if identity.deployment_config_root != pre_state.deployment_config_root:
            raise E05Error("attempt deployment profile is crossed with pre_state")
        if attempt.verifier_profile_root != pre_state.verifier_profile_root:
            raise E05Error("attempt verifier profile is crossed with pre_state")

        receipt = self.reopen_receipt
        if (
            receipt.snapshot_root != pre_state.snapshot_root
            or receipt.current_state_root != pre_state.current_state_root
            or receipt.authority_epoch_index != pre_state.authority_epoch_index
            or receipt.authority_state_root != pre_state.authority_state_root
            or receipt.deployment_config_root != pre_state.deployment_config_root
            or receipt.verifier_profile_root != pre_state.verifier_profile_root
        ):
            raise E05Error("reopen receipt is crossed with pre_state")


@dataclass(frozen=True, slots=True)
class E05CommitReceiptV1:
    """Receipt returned only after the complete E05 transaction commits."""

    attempt_root: str
    post_snapshot_root: str
    post_state_root: str
    authority_epoch_index: int
    publication_sequence: int
    publication_set_root: str

    def __post_init__(self) -> None:
        for name in (
            "attempt_root",
            "post_snapshot_root",
            "post_state_root",
            "publication_set_root",
        ):
            _digest(getattr(self, name), name)
        for name in ("authority_epoch_index", "publication_sequence"):
            value = getattr(self, name)
            if type(value) is not int or value < 0 or value > (1 << 32) - 1:
                raise E05Error(f"{name} is outside the closed u32 domain")
        if self.publication_sequence == 0:
            raise E05Error("publication_sequence must be positive")

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_E05_SCHEMA_V1,
            "attempt_root": self.attempt_root,
            "post_snapshot_root": self.post_snapshot_root,
            "post_state_root": self.post_state_root,
            "authority_epoch_index": self.authority_epoch_index,
            "publication_sequence": self.publication_sequence,
            "publication_set_root": self.publication_set_root,
        }


E05ResultV1: TypeAlias = E05CommitReceiptV1 | E05RejectV1


def e05_publication_set_root(rows: tuple[dict[str, object], ...]) -> str:
    """Derive the canonical root for the complete ordered E05 row set."""

    if type(rows) is not tuple:
        raise E05Error("publication rows must be an exact tuple")
    encoded = canonical_json_bytes(
        {
            "schema": FCIS_M6_E05_PUBLICATION_SET_SCHEMA_V1,
            "rows": list(rows),
        }
    )
    import hashlib

    return hashlib.sha256(
        FCIS_M6_E05_PUBLICATION_SET_SCHEMA_V1.encode("ascii") + b"\x00" + encoded
    ).hexdigest()


__all__ = (
    "E05CodeV1",
    "E05CommitReceiptV1",
    "E05Error",
    "E05PublicationRequestV1",
    "E05RejectV1",
    "E05ResultV1",
    "FCIS_M6_E05_PUBLICATION_SET_SCHEMA_V1",
    "FCIS_M6_E05_SCHEMA_V1",
    "MAX_E05_REJECT_PATH_ITEMS_V1",
    "e05_publication_set_root",
)
