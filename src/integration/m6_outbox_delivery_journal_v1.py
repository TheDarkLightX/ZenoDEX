"""Durable attempt journal for the research-only M6 Tau delivery shell.

The journal carries no economic or acknowledgment authority. It records a
PENDING reservation before an external call or a canonical delivery receipt.
PENDING survives
restart and blocks automatic redelivery until explicit reconciliation. A
manifest detects isolated attempt loss and stale-record rollback. Coordinated
rollback of both records and manifest requires an external monotonic anchor and
remains outside this research adapter's safety claim.
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
from typing import TYPE_CHECKING, Iterator, Mapping

from ..core.m6_safe_mount_types_v1 import (
    M6PromotionSubjectV1,
    _require_root,
    _require_token,
    canonical_bytes_v1,
    hash_v1,
)

if TYPE_CHECKING:
    from .m6_durable_store_v1 import M6DurableLedgerStoreV1

_DELIVERY_JOURNAL_SCHEMA_V1 = "zenodex/m6-outbox-delivery-journal/v1"
_DELIVERY_ATTEMPT_SCHEMA_V1 = "zenodex/m6-outbox-delivery-attempt/v1"
_DELIVERY_JOURNAL_META_FILE_V1 = "journal.json"
_DELIVERY_JOURNAL_LOCK_FILE_V1 = ".m6-outbox-delivery.lock"
_DELIVERY_JOURNAL_ATTEMPTS_DIR_V1 = "attempts"
_DELIVERY_JOURNAL_SUBMISSION_LEASES_DIR_V1 = "submission-leases"
_DELIVERY_JOURNAL_ATTEMPT_MANIFEST_FILE_V1 = "attempt-manifest.json"
_DELIVERY_JOURNAL_ATTEMPT_MANIFEST_SCHEMA_V1 = (
    "zenodex/m6-outbox-delivery-attempt-manifest/v1"
)
_DELIVERY_JOURNAL_MAX_BYTES_V1 = 1 << 20
_DELIVERY_JOURNAL_MAX_ATTEMPTS_V1 = 7_000


class M6OutboxDeliveryJournalError(RuntimeError):
    """Durable delivery-attempt journal is missing, corrupt, or inconsistent."""


class M6OutboxDeliveryAttemptStatusV1(str, Enum):
    PENDING = "pending"
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
        except (
            UnicodeDecodeError,
            json.JSONDecodeError,
            RecursionError,
            TypeError,
            ValueError,
        ) as exc:
            raise M6OutboxDeliveryJournalError(
                "delivery journal receipt is not canonical JSON"
            ) from exc
        if not isinstance(decoded, dict):
            raise M6OutboxDeliveryJournalError("delivery journal receipt is not an object")
        try:
            canonical = canonical_bytes_v1(decoded)
        except (RecursionError, TypeError, ValueError) as exc:
            raise M6OutboxDeliveryJournalError(
                "delivery journal receipt is not canonical"
            ) from exc
        if canonical != self.receipt_canonical:
            raise M6OutboxDeliveryJournalError("delivery journal receipt is not canonical")
        return decoded


class M6OutboxDeliveryJournalV1:
    """Durable pre-effect reservation and outcome-quarantine journal."""

    def __init__(self, root: str | Path, subject: M6PromotionSubjectV1) -> None:
        if type(subject) is not M6PromotionSubjectV1:
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
            self._ledger_genesis_state_root = self._validate_layout_unlocked()

    @classmethod
    def create_for_store(
        cls,
        store: "M6DurableLedgerStoreV1",
    ) -> "M6OutboxDeliveryJournalV1":
        """Initialize the journal only while the bound ledger is at genesis."""

        from .m6_durable_store_v1 import M6DurableCorruptionError, M6DurableLedgerStoreV1

        if type(store) is not M6DurableLedgerStoreV1:
            raise TypeError("delivery journal creation requires an M6 durable ledger")
        try:
            with store.external_effect_submission_guard() as reopened:
                if reopened.records or reopened.chain_block_ids != ("genesis",):
                    raise M6OutboxDeliveryJournalError(
                        "delivery journal must be initialized before the first committed block"
                    )
                root_path = store.root.parent / f"{store.root.name}.outbox-delivery-v1"
                if root_path.is_symlink():
                    raise M6OutboxDeliveryJournalError(
                        "delivery journal root cannot be a symlink"
                    )
                if root_path.exists():
                    if not root_path.is_dir():
                        raise M6OutboxDeliveryJournalError(
                            "delivery journal root is not a directory"
                        )
                    if any(root_path.iterdir()):
                        raise FileExistsError("delivery journal root is not empty")
                else:
                    root_path.mkdir(parents=True, mode=0o700)
                attempts = root_path / _DELIVERY_JOURNAL_ATTEMPTS_DIR_V1
                attempts.mkdir(mode=0o700)
                leases = root_path / _DELIVERY_JOURNAL_SUBMISSION_LEASES_DIR_V1
                leases.mkdir(mode=0o700)
                meta = canonical_bytes_v1(
                    {
                        "schema": _DELIVERY_JOURNAL_SCHEMA_V1,
                        "subject_root": store.subject.subject_root,
                        "ledger_genesis_state_root": reopened.state.state_root,
                    }
                )
                _write_new_durable_file(root_path / _DELIVERY_JOURNAL_META_FILE_V1, meta)
                _write_new_durable_file(root_path / _DELIVERY_JOURNAL_LOCK_FILE_V1, b"")
                _write_new_durable_file(
                    root_path / _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_FILE_V1,
                    canonical_bytes_v1(
                        {
                            "schema": _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_SCHEMA_V1,
                            "subject_root": store.subject.subject_root,
                            "attempts": {},
                        }
                    ),
                )
                _fsync_directory(attempts)
                _fsync_directory(leases)
                _fsync_directory(root_path)
                _fsync_directory(root_path.parent)
        except M6DurableCorruptionError as exc:
            raise M6OutboxDeliveryJournalError(
                "delivery journal cannot reopen its durable ledger"
            ) from exc
        return cls(root_path, store.subject)

    @property
    def subject(self) -> M6PromotionSubjectV1:
        return self._subject

    @property
    def root(self) -> Path:
        return self._root

    @property
    def ledger_genesis_state_root(self) -> str:
        return self._ledger_genesis_state_root

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
                return attempt, False
            manifest = _read_canonical_json_object(
                self._root / _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_FILE_V1
            )
            recorded = manifest.get("attempts")
            if not isinstance(recorded, dict):
                raise M6OutboxDeliveryJournalError("delivery attempt manifest is invalid")
            if len(recorded) >= _DELIVERY_JOURNAL_MAX_ATTEMPTS_V1:
                raise M6OutboxDeliveryJournalError("delivery attempt capacity is exhausted")
            pending = M6OutboxDeliveryAttemptV1(
                M6OutboxDeliveryAttemptStatusV1.PENDING,
                effect_id,
                effect_root,
                None,
            )
            _write_new_durable_file(path, self._attempt_bytes(pending))
            _fsync_directory(path.parent)
            self._update_attempt_manifest_unlocked(path, pending)
            return pending, True

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
        locked = False
        try:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX)
                locked = True
            except OSError as exc:
                raise M6OutboxDeliveryJournalError(
                    "delivery journal lock cannot be acquired"
                ) from exc
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
            release_error: OSError | None = None
            if locked:
                try:
                    fcntl.flock(descriptor, fcntl.LOCK_UN)
                except OSError as exc:
                    release_error = exc
            try:
                os.close(descriptor)
            except OSError as exc:
                if release_error is None:
                    release_error = exc
            if release_error is not None:
                raise M6OutboxDeliveryJournalError(
                    "delivery journal lock cannot be released"
                ) from release_error

    def _validate_layout_unlocked(self) -> str:
        expected = {
            _DELIVERY_JOURNAL_META_FILE_V1,
            _DELIVERY_JOURNAL_LOCK_FILE_V1,
            _DELIVERY_JOURNAL_ATTEMPTS_DIR_V1,
            _DELIVERY_JOURNAL_SUBMISSION_LEASES_DIR_V1,
            _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_FILE_V1,
        }
        try:
            entries = {entry.name: entry for entry in self._root.iterdir()}
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot enumerate delivery journal") from exc
        if set(entries) != expected:
            raise M6OutboxDeliveryJournalError("delivery journal root entries mismatch")
        for filename in (
            _DELIVERY_JOURNAL_META_FILE_V1,
            _DELIVERY_JOURNAL_LOCK_FILE_V1,
            _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_FILE_V1,
        ):
            entry = entries[filename]
            if entry.is_symlink() or not entry.is_file():
                raise M6OutboxDeliveryJournalError("delivery journal file type mismatch")
        attempts = entries[_DELIVERY_JOURNAL_ATTEMPTS_DIR_V1]
        if attempts.is_symlink() or not attempts.is_dir():
            raise M6OutboxDeliveryJournalError("delivery attempts path is not a directory")
        leases = entries[_DELIVERY_JOURNAL_SUBMISSION_LEASES_DIR_V1]
        if leases.is_symlink() or not leases.is_dir():
            raise M6OutboxDeliveryJournalError("delivery leases path is not a directory")
        try:
            lease_entries = tuple(leases.iterdir())
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot enumerate delivery leases") from exc
        if any(
            entry.is_symlink()
            or not entry.is_file()
            or len(entry.name) != 69
            or not entry.name.endswith(".lock")
            or any(character not in "0123456789abcdef" for character in entry.name[:-5])
            for entry in lease_entries
        ):
            raise M6OutboxDeliveryJournalError("delivery lease inventory is invalid")
        meta = _read_canonical_json_object(
            self._root / _DELIVERY_JOURNAL_META_FILE_V1
        )
        if set(meta) != {"schema", "subject_root", "ledger_genesis_state_root"}:
            raise M6OutboxDeliveryJournalError("delivery journal metadata fields are not closed")
        if meta["schema"] != _DELIVERY_JOURNAL_SCHEMA_V1:
            raise M6OutboxDeliveryJournalError("delivery journal schema mismatch")
        if meta["subject_root"] != self._subject.subject_root:
            raise M6OutboxDeliveryJournalError("delivery journal subject mismatch")
        try:
            genesis_state_root = _require_root(
                meta["ledger_genesis_state_root"],
                name="delivery journal ledger genesis state root",
            )
        except (TypeError, ValueError) as exc:
            raise M6OutboxDeliveryJournalError(
                "delivery journal ledger genesis state root is invalid"
            ) from exc
        initialized_root = getattr(self, "_ledger_genesis_state_root", None)
        if initialized_root is not None and genesis_state_root != initialized_root:
            raise M6OutboxDeliveryJournalError(
                "delivery journal ledger genesis binding changed"
            )
        self._validate_attempt_manifest_unlocked()
        return genesis_state_root

    def _validate_attempt_manifest_unlocked(self) -> None:
        manifest = _read_canonical_json_object(
            self._root / _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_FILE_V1
        )
        if set(manifest) != {"schema", "subject_root", "attempts"}:
            raise M6OutboxDeliveryJournalError(
                "delivery attempt manifest fields are not closed"
            )
        if manifest["schema"] != _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_SCHEMA_V1:
            raise M6OutboxDeliveryJournalError("delivery attempt manifest schema mismatch")
        if manifest["subject_root"] != self._subject.subject_root:
            raise M6OutboxDeliveryJournalError("delivery attempt manifest subject mismatch")
        recorded = manifest["attempts"]
        if not isinstance(recorded, dict) or any(
            type(filename) is not str or type(attempt_root) is not str
            for filename, attempt_root in recorded.items()
        ):
            raise M6OutboxDeliveryJournalError("delivery attempt manifest is malformed")
        if len(recorded) > _DELIVERY_JOURNAL_MAX_ATTEMPTS_V1:
            raise M6OutboxDeliveryJournalError("delivery attempt capacity is exceeded")
        attempts_root = self._root / _DELIVERY_JOURNAL_ATTEMPTS_DIR_V1
        try:
            entries = {entry.name: entry for entry in attempts_root.iterdir()}
        except OSError as exc:
            raise M6OutboxDeliveryJournalError(
                "cannot enumerate delivery attempts"
            ) from exc
        if set(entries) != set(recorded):
            raise M6OutboxDeliveryJournalError("delivery attempt inventory mismatch")
        for filename, entry in entries.items():
            if entry.is_symlink() or not entry.is_file():
                raise M6OutboxDeliveryJournalError("delivery attempt file type mismatch")
            attempt = self._read_attempt_unlocked(entry)
            if self._attempt_path(attempt.effect_id).name != filename:
                raise M6OutboxDeliveryJournalError("delivery attempt filename mismatch")
            actual_root = self._attempt_manifest_root(attempt)
            try:
                expected_root = _require_root(
                    recorded[filename],
                    name="delivery attempt manifest root",
                )
            except (TypeError, ValueError) as exc:
                raise M6OutboxDeliveryJournalError(
                    "delivery attempt manifest root is invalid"
                ) from exc
            if actual_root != expected_root:
                raise M6OutboxDeliveryJournalError("delivery attempt manifest root mismatch")

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
        try:
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=".attempt-",
                dir=path.parent,
            )
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot stage delivery attempt") from exc
        temporary_path = Path(temporary_name)
        try:
            data = self._attempt_bytes(attempt)
            _write_all(descriptor, data)
            os.fsync(descriptor)
            os.close(descriptor)
            descriptor = -1
            os.replace(temporary_path, path)
            _fsync_directory(path.parent)
            self._update_attempt_manifest_unlocked(path, attempt)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot replace delivery attempt") from exc
        finally:
            if descriptor >= 0:
                try:
                    os.close(descriptor)
                except OSError as exc:
                    raise M6OutboxDeliveryJournalError(
                        "cannot close staged delivery attempt"
                    ) from exc
            try:
                temporary_path.unlink(missing_ok=True)
            except OSError as exc:
                raise M6OutboxDeliveryJournalError(
                    "cannot remove staged delivery attempt"
                ) from exc

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

    def _attempt_manifest_root(self, attempt: M6OutboxDeliveryAttemptV1) -> str:
        return hash_v1(
            "m6-outbox-delivery-attempt-manifest-entry-v1",
            {
                "subject_root": self._subject.subject_root,
                "attempt": json.loads(self._attempt_bytes(attempt).decode("utf-8")),
            },
        )

    def _update_attempt_manifest_unlocked(
        self,
        path: Path,
        attempt: M6OutboxDeliveryAttemptV1,
    ) -> None:
        manifest_path = self._root / _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_FILE_V1
        manifest = _read_canonical_json_object(manifest_path)
        if set(manifest) != {"schema", "subject_root", "attempts"}:
            raise M6OutboxDeliveryJournalError(
                "delivery attempt manifest fields are not closed"
            )
        recorded = manifest.get("attempts")
        if (
            manifest.get("schema") != _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_SCHEMA_V1
            or manifest.get("subject_root") != self._subject.subject_root
            or not isinstance(recorded, dict)
        ):
            raise M6OutboxDeliveryJournalError("delivery attempt manifest is invalid")
        updated = dict(recorded)
        updated[path.name] = self._attempt_manifest_root(attempt)
        replacement = canonical_bytes_v1(
            {
                "schema": _DELIVERY_JOURNAL_ATTEMPT_MANIFEST_SCHEMA_V1,
                "subject_root": self._subject.subject_root,
                "attempts": updated,
            }
        )
        if len(updated) > _DELIVERY_JOURNAL_MAX_ATTEMPTS_V1:
            raise M6OutboxDeliveryJournalError("delivery attempt capacity is exceeded")
        if len(replacement) > _DELIVERY_JOURNAL_MAX_BYTES_V1:
            raise M6OutboxDeliveryJournalError("delivery attempt manifest exceeds size limit")
        try:
            descriptor, temporary_name = tempfile.mkstemp(
                prefix=".attempt-manifest-",
                dir=self._root,
            )
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot stage delivery attempt manifest") from exc
        temporary_path = Path(temporary_name)
        try:
            _write_all(descriptor, replacement)
            os.fsync(descriptor)
            os.close(descriptor)
            descriptor = -1
            os.replace(temporary_path, manifest_path)
            _fsync_directory(self._root)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError(
                "cannot replace delivery attempt manifest"
            ) from exc
        finally:
            if descriptor >= 0:
                try:
                    os.close(descriptor)
                except OSError as exc:
                    raise M6OutboxDeliveryJournalError(
                        "cannot close staged delivery attempt manifest"
                    ) from exc
            try:
                temporary_path.unlink(missing_ok=True)
            except OSError as exc:
                raise M6OutboxDeliveryJournalError(
                    "cannot remove staged delivery attempt manifest"
                ) from exc

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
        try:
            written = os.write(descriptor, data[offset:])
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot write delivery journal bytes") from exc
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
    except OSError as exc:
        raise M6OutboxDeliveryJournalError("cannot persist delivery journal file") from exc
    finally:
        try:
            os.close(descriptor)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot close delivery journal file") from exc


def _fsync_directory(path: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise M6OutboxDeliveryJournalError("cannot open delivery journal directory") from exc
    try:
        os.fsync(descriptor)
    except OSError as exc:
        raise M6OutboxDeliveryJournalError("cannot persist delivery journal directory") from exc
    finally:
        try:
            os.close(descriptor)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot close delivery journal directory") from exc


def _read_canonical_json_object(path: Path) -> dict[str, object]:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise M6OutboxDeliveryJournalError("cannot open delivery journal file") from exc
    try:
        try:
            metadata = os.fstat(descriptor)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot inspect delivery journal file") from exc
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_size > _DELIVERY_JOURNAL_MAX_BYTES_V1
        ):
            raise M6OutboxDeliveryJournalError("delivery journal file is invalid")
        chunks: list[bytes] = []
        remaining = _DELIVERY_JOURNAL_MAX_BYTES_V1 + 1
        while remaining > 0:
            try:
                chunk = os.read(descriptor, min(65536, remaining))
            except OSError as exc:
                raise M6OutboxDeliveryJournalError("cannot read delivery journal file") from exc
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        raw = b"".join(chunks)
        if len(raw) > _DELIVERY_JOURNAL_MAX_BYTES_V1:
            raise M6OutboxDeliveryJournalError("delivery journal file exceeds size limit")
    finally:
        try:
            os.close(descriptor)
        except OSError as exc:
            raise M6OutboxDeliveryJournalError("cannot close delivery journal file") from exc
    try:
        decoded = json.loads(
            raw.decode("utf-8"),
            parse_constant=lambda _value: (_ for _ in ()).throw(
                ValueError("forbidden JSON constant")
            ),
            parse_float=lambda _value: (_ for _ in ()).throw(
                ValueError("floats are forbidden")
            ),
        )
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        RecursionError,
        TypeError,
        ValueError,
    ) as exc:
        raise M6OutboxDeliveryJournalError("cannot decode delivery journal file") from exc
    if not isinstance(decoded, dict):
        raise M6OutboxDeliveryJournalError("delivery journal file is not an object")
    try:
        canonical = canonical_bytes_v1(decoded)
    except (RecursionError, TypeError, ValueError) as exc:
        raise M6OutboxDeliveryJournalError(
            "delivery journal file is not canonical"
        ) from exc
    if canonical != raw:
        raise M6OutboxDeliveryJournalError("delivery journal file is not canonical")
    return decoded


__all__ = [
    "M6OutboxDeliveryAttemptStatusV1",
    "M6OutboxDeliveryAttemptV1",
    "M6OutboxDeliveryJournalError",
    "M6OutboxDeliveryJournalV1",
]
