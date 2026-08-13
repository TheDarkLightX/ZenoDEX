"""Durable attempt journal for the research-only M6 Tau delivery shell.

The journal carries no economic or acknowledgment authority. It records a
PENDING reservation before an external call, a RETRYABLE state only after a
typed pre-effect refusal, or a canonical delivery receipt. PENDING survives
restart and blocks automatic redelivery until explicit reconciliation.
"""

from __future__ import annotations

import fcntl
import json
import os
import stat
import tempfile
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Iterator, Mapping

from ..core.m6_safe_mount_types_v1 import (
    M6PromotionSubjectV1,
    _require_root,
    _require_token,
    canonical_bytes_v1,
    hash_v1,
)

_DELIVERY_JOURNAL_SCHEMA_V1 = "zenodex/m6-outbox-delivery-journal/v1"
_DELIVERY_ATTEMPT_SCHEMA_V1 = "zenodex/m6-outbox-delivery-attempt/v1"
_DELIVERY_JOURNAL_META_FILE_V1 = "journal.json"
_DELIVERY_JOURNAL_LOCK_FILE_V1 = ".m6-outbox-delivery.lock"
_DELIVERY_JOURNAL_ATTEMPTS_DIR_V1 = "attempts"
_DELIVERY_JOURNAL_MAX_BYTES_V1 = 1 << 20


class M6OutboxDeliveryJournalError(RuntimeError):
    """Durable delivery-attempt journal is missing, corrupt, or inconsistent."""


class M6OutboxDeliveryAttemptStatusV1(str, Enum):
    PENDING = "pending"
    RETRYABLE = "retryable"
    DELIVERED = "delivered"


@dataclass(frozen=True, slots=True)
class M6OutboxDeliveryAttemptV1:
    status: M6OutboxDeliveryAttemptStatusV1
    effect_id: str
    effect_root: str
    receipt_canonical: bytes | None

    def __post_init__(self) -> None:
        if not isinstance(self.status, M6OutboxDeliveryAttemptStatusV1):
            raise TypeError("delivery attempt status is not closed")
        _require_token(self.effect_id, name="delivery attempt effect id")
        _require_root(self.effect_root, name="delivery attempt effect root")
        if self.status is M6OutboxDeliveryAttemptStatusV1.DELIVERED:
            if type(self.receipt_canonical) is not bytes or not self.receipt_canonical:
                raise ValueError("delivered attempt requires canonical receipt bytes")
        elif self.receipt_canonical is not None:
            raise ValueError("unfinished delivery attempt cannot retain a receipt")

    def receipt_mapping(self) -> dict[str, object] | None:
        if self.receipt_canonical is None:
            return None
        try:
            decoded = json.loads(self.receipt_canonical.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise M6OutboxDeliveryJournalError(
                "delivery journal receipt is not canonical JSON"
            ) from exc
        if not isinstance(decoded, dict):
            raise M6OutboxDeliveryJournalError("delivery journal receipt is not an object")
        if canonical_bytes_v1(decoded) != self.receipt_canonical:
            raise M6OutboxDeliveryJournalError("delivery journal receipt is not canonical")
        return decoded


class M6OutboxDeliveryJournalV1:
    """Durable pre-effect reservation and outcome-quarantine journal."""

    def __init__(self, root: str | Path, subject: M6PromotionSubjectV1) -> None:
        if not isinstance(subject, M6PromotionSubjectV1):
            raise TypeError("delivery journal subject is not typed")
        self._root = Path(root)
        self._subject = subject
        try:
            metadata = os.stat(self._root, follow_symlinks=False)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("delivery journal root is unavailable") from exc
        if not stat.S_ISDIR(metadata.st_mode):
            raise M6OutboxDeliveryJournalError("delivery journal root is not a directory")
        self._root_identity = (metadata.st_dev, metadata.st_ino)
        with self._locked():
            self._validate_layout_unlocked()

    @classmethod
    def create(
        cls,
        root: str | Path,
        subject: M6PromotionSubjectV1,
    ) -> "M6OutboxDeliveryJournalV1":
        if not isinstance(subject, M6PromotionSubjectV1):
            raise TypeError("delivery journal subject is not typed")
        root_path = Path(root)
        if root_path.is_symlink():
            raise M6OutboxDeliveryJournalError("delivery journal root cannot be a symlink")
        if root_path.exists():
            if not root_path.is_dir():
                raise M6OutboxDeliveryJournalError("delivery journal root is not a directory")
            if any(root_path.iterdir()):
                raise FileExistsError("delivery journal root is not empty")
        else:
            root_path.mkdir(parents=True, mode=0o700)
        attempts = root_path / _DELIVERY_JOURNAL_ATTEMPTS_DIR_V1
        attempts.mkdir(mode=0o700)
        meta = canonical_bytes_v1(
            {
                "schema": _DELIVERY_JOURNAL_SCHEMA_V1,
                "subject_root": subject.subject_root,
            }
        )
        _write_new_durable_file(root_path / _DELIVERY_JOURNAL_META_FILE_V1, meta)
        _write_new_durable_file(root_path / _DELIVERY_JOURNAL_LOCK_FILE_V1, b"")
        _fsync_directory(attempts)
        _fsync_directory(root_path)
        _fsync_directory(root_path.parent)
        return cls(root_path, subject)

    @property
    def subject(self) -> M6PromotionSubjectV1:
        return self._subject

    @property
    def root(self) -> Path:
        return self._root

    def reserve(
        self,
        *,
        effect_id: str,
        effect_root: str,
    ) -> tuple[M6OutboxDeliveryAttemptV1, bool]:
        """Persist PENDING before transport; return whether this caller owns it."""

        _require_token(effect_id, name="delivery reservation effect id")
        _require_root(effect_root, name="delivery reservation effect root")
        with self._locked():
            self._validate_layout_unlocked()
            path = self._attempt_path(effect_id)
            if os.path.lexists(path):
                attempt = self._read_attempt_unlocked(path)
                self._require_attempt_binding(attempt, effect_id, effect_root)
                if attempt.status is not M6OutboxDeliveryAttemptStatusV1.RETRYABLE:
                    return attempt, False
                pending = M6OutboxDeliveryAttemptV1(
                    M6OutboxDeliveryAttemptStatusV1.PENDING,
                    effect_id,
                    effect_root,
                    None,
                )
                self._replace_attempt_unlocked(path, pending)
                return pending, True
            pending = M6OutboxDeliveryAttemptV1(
                M6OutboxDeliveryAttemptStatusV1.PENDING,
                effect_id,
                effect_root,
                None,
            )
            _write_new_durable_file(path, self._attempt_bytes(pending))
            _fsync_directory(path.parent)
            return pending, True

    def mark_retryable(self, *, effect_id: str, effect_root: str) -> None:
        self._replace_pending_status(
            M6OutboxDeliveryAttemptV1(
                M6OutboxDeliveryAttemptStatusV1.RETRYABLE,
                effect_id,
                effect_root,
                None,
            )
        )

    def mark_delivered(
        self,
        *,
        effect_id: str,
        effect_root: str,
        receipt: Mapping[str, object],
    ) -> M6OutboxDeliveryAttemptV1:
        delivered = M6OutboxDeliveryAttemptV1(
            M6OutboxDeliveryAttemptStatusV1.DELIVERED,
            effect_id,
            effect_root,
            canonical_bytes_v1(dict(receipt)),
        )
        self._replace_pending_status(delivered)
        return delivered

    def _replace_pending_status(self, replacement: M6OutboxDeliveryAttemptV1) -> None:
        with self._locked():
            self._validate_layout_unlocked()
            path = self._attempt_path(replacement.effect_id)
            current = self._read_attempt_unlocked(path)
            self._require_attempt_binding(
                current,
                replacement.effect_id,
                replacement.effect_root,
            )
            if current.status is not M6OutboxDeliveryAttemptStatusV1.PENDING:
                raise M6OutboxDeliveryJournalError(
                    "delivery attempt transition requires pending state"
                )
            self._replace_attempt_unlocked(path, replacement)

    @contextmanager
    def _locked(self) -> Iterator[None]:
        lock_path = self._root / _DELIVERY_JOURNAL_LOCK_FILE_V1
        flags = os.O_RDWR | getattr(os, "O_NOFOLLOW", 0)
        try:
            descriptor = os.open(lock_path, flags)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("delivery journal lock is unavailable") from exc
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            try:
                root_metadata = os.stat(self._root, follow_symlinks=False)
            except OSError as exc:
                raise M6OutboxDeliveryJournalError(
                    "delivery journal root cannot be revalidated"
                ) from exc
            if (
                not stat.S_ISDIR(root_metadata.st_mode)
                or (root_metadata.st_dev, root_metadata.st_ino) != self._root_identity
            ):
                raise M6OutboxDeliveryJournalError("delivery journal root identity changed")
            yield
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)

    def _validate_layout_unlocked(self) -> None:
        expected = {
            _DELIVERY_JOURNAL_META_FILE_V1,
            _DELIVERY_JOURNAL_LOCK_FILE_V1,
            _DELIVERY_JOURNAL_ATTEMPTS_DIR_V1,
        }
        try:
            entries = {entry.name: entry for entry in self._root.iterdir()}
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot enumerate delivery journal") from exc
        if set(entries) != expected:
            raise M6OutboxDeliveryJournalError("delivery journal root entries mismatch")
        for filename in (_DELIVERY_JOURNAL_META_FILE_V1, _DELIVERY_JOURNAL_LOCK_FILE_V1):
            entry = entries[filename]
            if entry.is_symlink() or not entry.is_file():
                raise M6OutboxDeliveryJournalError("delivery journal file type mismatch")
        attempts = entries[_DELIVERY_JOURNAL_ATTEMPTS_DIR_V1]
        if attempts.is_symlink() or not attempts.is_dir():
            raise M6OutboxDeliveryJournalError("delivery attempts path is not a directory")
        meta = _read_canonical_json_object(
            self._root / _DELIVERY_JOURNAL_META_FILE_V1
        )
        if set(meta) != {"schema", "subject_root"}:
            raise M6OutboxDeliveryJournalError("delivery journal metadata fields are not closed")
        if meta["schema"] != _DELIVERY_JOURNAL_SCHEMA_V1:
            raise M6OutboxDeliveryJournalError("delivery journal schema mismatch")
        if meta["subject_root"] != self._subject.subject_root:
            raise M6OutboxDeliveryJournalError("delivery journal subject mismatch")

    def _attempt_path(self, effect_id: str) -> Path:
        filename_root = hash_v1(
            "m6-outbox-delivery-attempt-filename-v1",
            {"effect_id": effect_id},
        )
        return (
            self._root
            / _DELIVERY_JOURNAL_ATTEMPTS_DIR_V1
            / f"{filename_root[2:]}.json"
        )

    def _read_attempt_unlocked(self, path: Path) -> M6OutboxDeliveryAttemptV1:
        obj = _read_canonical_json_object(path)
        expected = {
            "schema",
            "subject_root",
            "effect_id",
            "effect_root",
            "status",
            "receipt",
        }
        if set(obj) != expected:
            raise M6OutboxDeliveryJournalError("delivery attempt fields are not closed")
        if obj["schema"] != _DELIVERY_ATTEMPT_SCHEMA_V1:
            raise M6OutboxDeliveryJournalError("delivery attempt schema mismatch")
        if obj["subject_root"] != self._subject.subject_root:
            raise M6OutboxDeliveryJournalError("delivery attempt subject mismatch")
        try:
            status = M6OutboxDeliveryAttemptStatusV1(obj["status"])
            effect_id = _require_token(obj["effect_id"], name="journal effect id")
            effect_root = _require_root(obj["effect_root"], name="journal effect root")
        except (TypeError, ValueError) as exc:
            raise M6OutboxDeliveryJournalError("delivery attempt coordinates are invalid") from exc
        receipt_value = obj["receipt"]
        receipt_canonical = (
            None if receipt_value is None else canonical_bytes_v1(receipt_value)
        )
        return M6OutboxDeliveryAttemptV1(
            status,
            effect_id,
            effect_root,
            receipt_canonical,
        )

    def _replace_attempt_unlocked(
        self,
        path: Path,
        attempt: M6OutboxDeliveryAttemptV1,
    ) -> None:
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=".attempt-",
            dir=path.parent,
        )
        temporary_path = Path(temporary_name)
        try:
            data = self._attempt_bytes(attempt)
            _write_all(descriptor, data)
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        try:
            os.replace(temporary_path, path)
            _fsync_directory(path.parent)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot replace delivery attempt") from exc
        finally:
            if temporary_path.exists():
                temporary_path.unlink()

    def _attempt_bytes(self, attempt: M6OutboxDeliveryAttemptV1) -> bytes:
        return canonical_bytes_v1(
            {
                "schema": _DELIVERY_ATTEMPT_SCHEMA_V1,
                "subject_root": self._subject.subject_root,
                "effect_id": attempt.effect_id,
                "effect_root": attempt.effect_root,
                "status": attempt.status.value,
                "receipt": attempt.receipt_mapping(),
            }
        )

    @staticmethod
    def _require_attempt_binding(
        attempt: M6OutboxDeliveryAttemptV1,
        effect_id: str,
        effect_root: str,
    ) -> None:
        if attempt.effect_id != effect_id or attempt.effect_root != effect_root:
            raise M6OutboxDeliveryJournalError(
                "delivery attempt is bound to another committed effect"
            )


def _write_all(descriptor: int, data: bytes) -> None:
    offset = 0
    while offset < len(data):
        written = os.write(descriptor, data[offset:])
        if written <= 0:
            raise M6OutboxDeliveryJournalError("cannot write delivery journal bytes")
        offset += written


def _write_new_durable_file(path: Path, data: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except OSError as exc:
        raise M6OutboxDeliveryJournalError("cannot create delivery journal file") from exc
    try:
        _write_all(descriptor, data)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise M6OutboxDeliveryJournalError("cannot open delivery journal directory") from exc
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _read_canonical_json_object(path: Path) -> dict[str, object]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise M6OutboxDeliveryJournalError("cannot open delivery journal file") from exc
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_size > _DELIVERY_JOURNAL_MAX_BYTES_V1
        ):
            raise M6OutboxDeliveryJournalError("delivery journal file is invalid")
        chunks: list[bytes] = []
        remaining = _DELIVERY_JOURNAL_MAX_BYTES_V1 + 1
        while remaining > 0:
            chunk = os.read(descriptor, min(65536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
        if len(raw) > _DELIVERY_JOURNAL_MAX_BYTES_V1:
            raise M6OutboxDeliveryJournalError("delivery journal file exceeds size limit")
    finally:
        os.close(descriptor)
    try:
        decoded = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise M6OutboxDeliveryJournalError("cannot decode delivery journal file") from exc
    if not isinstance(decoded, dict):
        raise M6OutboxDeliveryJournalError("delivery journal file is not an object")
    if canonical_bytes_v1(decoded) != raw:
        raise M6OutboxDeliveryJournalError("delivery journal file is not canonical")
    return decoded


__all__ = [
    "M6OutboxDeliveryAttemptStatusV1",
    "M6OutboxDeliveryAttemptV1",
    "M6OutboxDeliveryJournalError",
    "M6OutboxDeliveryJournalV1",
]
