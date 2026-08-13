"""Research-only durable shell for the M6 typed commit bundle.

The M6 transition and finality checks remain in the existing pure core and
commit port.  This module owns filesystem ordering only:

* canonical subject, state, and publication-record bytes are written into an
  immutable block directory;
* every file and directory is flushed before the directory is installed;
* the expected state root is checked under an inter-process file lock;
* the HEAD pointer is replaced atomically after block installation; and
* reopen reconstructs the typed state and publication records, checks the
  complete parent chain, rejects orphan or torn artifacts, and requires the
  canonical encode/reopen fixed point.

It intentionally has no validator networking, signature implementation, or
external effect delivery.  A crash after block installation and before HEAD
replacement leaves an orphan that reopen rejects, preserving fail-closed
behavior while leaving recovery policy explicit.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shutil
import stat
import tempfile
from contextlib import ExitStack, contextmanager
from contextvars import ContextVar
from copy import deepcopy
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Callable, Iterator, Mapping, TypeVar, cast

from src.core.m6_safe_mount_types_v1 import (
    DURABILITY_PROFILE_SCHEMA_V1,
    FINALITY_RECEIPT_RECORD_SCHEMA_V1,
    SCHEMA_V1,
    ZERO_ROOT_V1,
    ZRPF_RECEIPT_RECORD_SCHEMA_V1,
    AcceptCandidateV1,
    BusinessRejectReasonV1,
    BusinessStatusV1,
    CommandArgumentV1,
    DestinationAdapterRootV1,
    EconomicAtomKindV1,
    EconomicAtomV1,
    EscrowAtomV1,
    FinalityModeV1,
    GlobalCommandKindV1,
    GlobalCommandV1,
    HistoryAtomV1,
    M6ApplicationStateV1,
    M6DurabilityProfileV1,
    M6FinalityVerificationReceiptRecordV1,
    M6PromotionSubjectV1,
    M6ZRPFVerificationReceiptRecordV1,
    MigrationPhaseV1,
    MigrationStateV1,
    NonceAtomV1,
    OutboxAtomV1,
    PrivateSwapParticipantStateV1,
    PrivateSwapPhaseV1,
    PublicationAtomV1,
    SellerAuctionBidStateV1,
    SellerAuctionPhaseV1,
    TauBatchCertificateV1,
    TauWithdrawalIntentV1,
    TauWithdrawalStatusV1,
    VerifiedZenoLedgerFinalityV1,
    VerifiedZRPFRootV1,
    WithdrawalAcknowledgmentV1,
    ZenoLedgerFinalityCertificateV1,
    ZRPFRootJournalV1,
    canonical_bytes_v1,
    hash_v1,
    ordered_root_v1,
    validate_economic_state_v1,
    validate_state_commitments_v1,
    verify_finality_certificate_v1,
)
from src.core.m6_zrpf_v1 import (
    DirectBatchCandidateV1,
    ZRPFBatchCandidateV1,
    direct_batch_publication_root_v1,
)
from src.integration.m6_commit_port_v1 import (
    CommitResultV1,
    CommitStatusV1,
    DirectExecutionReplayV1,
    M6CommitPortV1,
    M6FinalityVerifierV1,
    M6PublishedRecordV1,
    _record_nonce_root,
    _require_bounded_json_depth_v1,
    candidate_matches_published_record_v1,
    direct_batch_data_availability_root_v1,
    direct_batch_matches_published_record_v1,
    finality_evidence_matches_published_record_v1,
    reverify_zrpf_handle_v1,
)
from src.state.canonical import canonical_hex_fixed_allow_0x

DURABLE_SCHEMA_V1 = "zenodex/m6-durable-block/v1"
HEAD_FILE_V1 = "HEAD.json"
GENESIS_BLOCK_ID_V1 = "genesis"
BLOCKS_DIR_V1 = "blocks"
GENESIS_DIR_V1 = "genesis"
LOCK_FILE_V1 = ".m6-durable.lock"
SUBJECT_FILE_V1 = "subject.json"
STATE_FILE_V1 = "state.json"
RECORD_FILE_V1 = "record.json"
MANIFEST_FILE_V1 = "manifest.json"
_OUTBOX_DELIVERY_ROOT_SUFFIX_V1 = ".outbox-delivery-v1"
_OUTBOX_SUBMISSION_LEASES_DIR_V1 = "submission-leases"
_OUTBOX_SUBMISSION_LEASE_DOMAIN_V1 = "m6-outbox-submission-lease-filename-v1"

_ACTIVE_DURABLE_ROOT: ContextVar[Path | None] = ContextVar(
    "m6_active_durable_root",
    default=None,
)
_ACTIVE_DURABLE_ROOT_FD: ContextVar[int | None] = ContextVar(
    "m6_active_durable_root_fd",
    default=None,
)
class M6DurableCorruptionError(RuntimeError):
    """The on-disk M6 layout cannot be reconstructed without ambiguity."""


class _M6ExternalEffectLeaseBusy(M6DurableCorruptionError):
    """Another process or callback currently owns this effect lease."""


@dataclass(frozen=True, slots=True)
class M6DurableReopenV1:
    subject: M6PromotionSubjectV1
    state: M6ApplicationStateV1
    head_block_id: str
    chain_block_ids: tuple[str, ...]
    records: tuple[M6PublishedRecordV1, ...]


@dataclass(frozen=True, slots=True)
class M6DurableCommitResultV1:
    status: CommitStatusV1
    state: M6ApplicationStateV1
    candidate_id: str
    block_id: str | None = None
    record: M6PublishedRecordV1 | None = None
    reason: str | None = None


@dataclass(frozen=True, slots=True)
class _LoadedBlockV1:
    block_id: str
    manifest: Mapping[str, object]
    state: M6ApplicationStateV1
    record: M6PublishedRecordV1


@dataclass(slots=True)
class _PublicationObservationV1:
    """Capture publication progress across shell-cleanup failure boundaries."""

    result: M6DurableCommitResultV1 | None = None


def _reject_json_constant(value: str) -> object:
    raise ValueError(f"JSON constant is forbidden: {value}")


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _object(value: object, *, name: str, keys: set[str]) -> dict[str, object]:
    if not isinstance(value, dict):
        raise M6DurableCorruptionError(f"{name} must be an object")
    if set(value) != keys:
        raise M6DurableCorruptionError(f"{name} keys mismatch")
    return value


def _list(value: object, *, name: str) -> list[object]:
    if not isinstance(value, list):
        raise M6DurableCorruptionError(f"{name} must be a list")
    return value


def _text(value: object, *, name: str, allow_none: bool = False) -> str | None:
    if value is None and allow_none:
        return None
    if not isinstance(value, str) or not value:
        raise M6DurableCorruptionError(f"{name} must be a non-empty string")
    return value


_EnumT = TypeVar("_EnumT", bound=Enum)


def _decode_enum(enum_type: type[_EnumT], value: object, *, name: str) -> _EnumT:
    text = _text(value, name=name)
    if text is None:
        raise M6DurableCorruptionError(f"{name} must be a non-empty string")
    try:
        return enum_type(text)
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"{name} is invalid") from exc


def _root(value: object, *, name: str, allow_zero: bool = False) -> str:
    if not isinstance(value, str):
        raise M6DurableCorruptionError(f"{name} must be a root string")
    try:
        canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(str(exc)) from exc
    if value != canonical or (not allow_zero and canonical == ZERO_ROOT_V1):
        raise M6DurableCorruptionError(f"{name} is not an allowed canonical root")
    return canonical


def _nonnegative_int(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise M6DurableCorruptionError(f"{name} must be a non-negative integer")
    return value


def _active_relative_parts(path: Path) -> tuple[int, tuple[str, ...]] | None:
    """Return a pinned root fd and safe relative components for active IO."""

    active_root = _ACTIVE_DURABLE_ROOT.get()
    active_fd = _ACTIVE_DURABLE_ROOT_FD.get()
    if active_root is None or active_fd is None:
        return None
    try:
        relative = path.relative_to(active_root)
    except ValueError:
        return None
    parts = tuple(relative.parts)
    if any(part in {"", ".", ".."} for part in parts):
        raise M6DurableCorruptionError(f"unsafe durable path component: {path}")
    return active_fd, parts


def _open_bound_directory(path: Path, *, create: bool = False) -> int:
    """Open every active-root directory component with O_NOFOLLOW."""

    bound = _active_relative_parts(path)
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
    if bound is None:
        if create:
            path.mkdir(parents=True, exist_ok=True)
        try:
            return os.open(path, directory_flags)
        except OSError as exc:
            raise M6DurableCorruptionError(f"cannot open directory {path}: {exc}") from exc

    root_fd, parts = bound
    current_fd = os.dup(root_fd)
    try:
        for part in parts:
            if create:
                try:
                    os.mkdir(part, 0o700, dir_fd=current_fd)
                except FileExistsError:
                    pass
            try:
                next_fd = os.open(part, directory_flags, dir_fd=current_fd)
            except OSError as exc:
                raise M6DurableCorruptionError(
                    f"cannot open pinned durable directory {path}: {exc}"
                ) from exc
            os.close(current_fd)
            current_fd = next_fd
        return current_fd
    except BaseException:
        os.close(current_fd)
        raise


def _open_bound_parent(path: Path) -> tuple[int, str]:
    """Open a pinned parent directory and return its final component."""

    bound = _active_relative_parts(path)
    if bound is None:
        directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
        try:
            return os.open(path.parent, directory_flags), path.name
        except OSError as exc:
            raise M6DurableCorruptionError(
                f"cannot open durable parent directory {path.parent}: {exc}"
            ) from exc
    root_fd, parts = bound
    if not parts:
        raise M6DurableCorruptionError(f"durable root is not a file path: {path}")
    active_root = _ACTIVE_DURABLE_ROOT.get()
    if active_root is None:
        raise M6DurableCorruptionError("active durable root disappeared")
    parent_fd = _open_bound_directory(
        active_root / Path(*parts[:-1]),
        create=False,
    )
    return parent_fd, parts[-1]


def _read_nofollow(path: Path, *, max_bytes: int) -> bytes:
    bound = _active_relative_parts(path)
    parent_fd = -1
    target: str | Path = path
    open_kwargs: dict[str, int] = {}
    if bound is not None:
        parent_fd, target_name = _open_bound_parent(path)
        target = target_name
        open_kwargs["dir_fd"] = parent_fd
    elif path.is_symlink() or not path.is_file():
        raise M6DurableCorruptionError(f"expected regular file: {path}")
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    nonblock = getattr(os, "O_NONBLOCK", 0)
    try:
        fd = os.open(target, os.O_RDONLY | nofollow | nonblock, **open_kwargs)
    except OSError as exc:
        if parent_fd >= 0:
            os.close(parent_fd)
        raise M6DurableCorruptionError(f"cannot open {path}: {exc}") from exc
    try:
        try:
            metadata = os.fstat(fd)
        except OSError as exc:
            raise M6DurableCorruptionError(f"cannot stat {path}: {exc}") from exc
        if not stat.S_ISREG(metadata.st_mode):
            raise M6DurableCorruptionError(f"expected regular file: {path}")
        size = metadata.st_size
        if size > max_bytes:
            raise M6DurableCorruptionError(
                f"{path} exceeds durable file limit of {max_bytes} bytes"
            )
        try:
            with os.fdopen(fd, "rb") as handle:
                fd = -1
                data = handle.read(max_bytes + 1)
        except OSError as exc:
            raise M6DurableCorruptionError(f"cannot read {path}: {exc}") from exc
        if len(data) > max_bytes:
            raise M6DurableCorruptionError(
                f"{path} exceeds durable file limit of {max_bytes} bytes"
            )
        return data
    finally:
        if fd >= 0:
            os.close(fd)
        if parent_fd >= 0:
            os.close(parent_fd)


def _read_canonical_json(path: Path, *, max_bytes: int) -> tuple[dict[str, object], bytes]:
    data = _read_nofollow(path, max_bytes=max_bytes)
    try:
        raw = json.loads(
            data.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
            parse_float=lambda _value: (_ for _ in ()).throw(ValueError("floats are forbidden")),
        )
        _require_bounded_json_depth_v1(raw, name=f"canonical JSON in {path}")
    except (
        UnicodeDecodeError,
        json.JSONDecodeError,
        RecursionError,
        TypeError,
        ValueError,
    ) as exc:
        raise M6DurableCorruptionError(f"invalid canonical JSON in {path}: {exc}") from exc
    if not isinstance(raw, dict):
        raise M6DurableCorruptionError(f"canonical JSON root must be an object: {path}")
    try:
        canonical = canonical_bytes_v1(raw)
    except (RecursionError, TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid canonical JSON in {path}: {exc}") from exc
    if canonical != data:
        raise M6DurableCorruptionError(f"non-canonical JSON bytes: {path}")
    return raw, data


def _file_digest(data: bytes) -> str:
    digest = hashlib.sha256(data).hexdigest()
    return "0x" + digest


def _canonical_data(value: object) -> bytes:
    return canonical_bytes_v1(value)


def _fsync_directory(path: Path) -> None:
    fd = -1
    try:
        fd = _open_bound_directory(path)
    except OSError as exc:
        raise M6DurableCorruptionError(f"cannot open directory for fsync: {path}: {exc}") from exc
    primary: M6DurableCorruptionError | None = None
    try:
        os.fsync(fd)
    except OSError as exc:
        primary = M6DurableCorruptionError(f"cannot fsync durable directory {path}: {exc}")
    try:
        os.close(fd)
    except OSError as exc:
        close_error = M6DurableCorruptionError(
            f"cannot close durable directory descriptor for {path}"
        )
        if primary is None:
            raise close_error from exc
    if primary is not None:
        raise primary


def _ensure_durable_file_bound(path: Path, data: bytes, *, max_bytes: int) -> None:
    if len(data) > max_bytes:
        raise M6DurableCorruptionError(
            f"{path} exceeds durable file limit of {max_bytes} bytes"
        )


def _write_new_file(path: Path, data: bytes, *, max_bytes: int) -> None:
    _ensure_durable_file_bound(path, data, max_bytes=max_bytes)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    parent_fd = -1
    target: str | Path = path
    open_kwargs: dict[str, int] = {}
    bound = _active_relative_parts(path)
    if bound is not None:
        parent_fd, target_name = _open_bound_parent(path)
        target = target_name
        open_kwargs["dir_fd"] = parent_fd
    try:
        fd = os.open(target, flags, 0o600, **open_kwargs)
    except OSError as exc:
        if parent_fd >= 0:
            os.close(parent_fd)
        raise M6DurableCorruptionError(f"cannot create durable file {path}: {exc}") from exc
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise M6DurableCorruptionError(f"created durable file is not regular: {path}")
        with os.fdopen(fd, "wb") as handle:
            fd = -1
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
    except OSError as exc:
        raise M6DurableCorruptionError(f"cannot fsync durable file {path}: {exc}") from exc
    finally:
        if fd >= 0:
            os.close(fd)
        if parent_fd >= 0:
            os.close(parent_fd)


def _atomic_replace_file(path: Path, data: bytes, *, max_bytes: int) -> None:
    bound = _active_relative_parts(path)
    if bound is not None:
        _ensure_durable_file_bound(path, data, max_bytes=max_bytes)
        parent_fd, target_name = _open_bound_parent(path)
        temp_name: str | None = None
        temp_path: Path | None = None
        try:
            try:
                current = os.stat(target_name, dir_fd=parent_fd, follow_symlinks=False)
            except FileNotFoundError:
                current = None
            if current is not None and stat.S_ISLNK(current.st_mode):
                raise M6DurableCorruptionError(f"refusing to replace symlink: {path}")
            fd, temp_path_value = tempfile.mkstemp(
                prefix=f".{path.name}.",
                suffix=".tmp",
                dir=f"/proc/self/fd/{parent_fd}",
            )
            temp_path = Path(temp_path_value)
            temp_name = temp_path.name
            with os.fdopen(fd, "wb") as handle:
                handle.write(data)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(
                temp_name,
                target_name,
                src_dir_fd=parent_fd,
                dst_dir_fd=parent_fd,
            )
            active_root = _ACTIVE_DURABLE_ROOT.get()
            if active_root is None:
                raise M6DurableCorruptionError("active durable root disappeared")
            _fsync_directory(active_root)
        except OSError as exc:
            raise M6DurableCorruptionError(f"cannot atomically replace {path}: {exc}") from exc
        finally:
            if temp_name is not None:
                try:
                    os.unlink(temp_name, dir_fd=parent_fd)
                except FileNotFoundError:
                    pass
            os.close(parent_fd)
        return
    if path.is_symlink():
        raise M6DurableCorruptionError(f"refusing to replace symlink: {path}")
    _ensure_durable_file_bound(path, data, max_bytes=max_bytes)
    fd, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    temp_path = Path(temp_name)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_path, path)
        _fsync_directory(path.parent)
    finally:
        if temp_path.exists() or temp_path.is_symlink():
            temp_path.unlink()


def _ensure_directory(path: Path) -> None:
    if _active_relative_parts(path) is not None:
        fd = _open_bound_directory(path, create=True)
        os.close(fd)
        return
    if path.exists() and (path.is_symlink() or not path.is_dir()):
        raise M6DurableCorruptionError(f"expected directory: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _require_directory_layout(
    path: Path,
    *,
    files: set[str],
    directories: set[str],
    name: str,
) -> None:
    if _active_relative_parts(path) is not None:
        directory_fd = _open_bound_directory(path)
        try:
            try:
                active_names = {entry.name for entry in os.scandir(directory_fd)}
            except OSError as exc:
                raise M6DurableCorruptionError(f"cannot enumerate {name}: {exc}") from exc
            expected = files | directories
            if active_names != expected:
                raise M6DurableCorruptionError(
                    f"{name} entries mismatch: expected={sorted(expected)}, actual={sorted(active_names)}"
                )
            for entry_name in files:
                try:
                    metadata = os.stat(entry_name, dir_fd=directory_fd, follow_symlinks=False)
                except OSError as exc:
                    raise M6DurableCorruptionError(
                        f"cannot stat {name} file {entry_name}: {exc}"
                    ) from exc
                if not stat.S_ISREG(metadata.st_mode):
                    raise M6DurableCorruptionError(f"{name} file is not regular: {entry_name}")
            for entry_name in directories:
                try:
                    metadata = os.stat(entry_name, dir_fd=directory_fd, follow_symlinks=False)
                except OSError as exc:
                    raise M6DurableCorruptionError(
                        f"cannot stat {name} directory {entry_name}: {exc}"
                    ) from exc
                if not stat.S_ISDIR(metadata.st_mode):
                    raise M6DurableCorruptionError(
                        f"{name} directory is not regular: {entry_name}"
                    )
        finally:
            os.close(directory_fd)
        return
    if path.is_symlink() or not path.is_dir():
        raise M6DurableCorruptionError(f"{name} must be a regular directory")
    try:
        entries = {entry.name: entry for entry in path.iterdir()}
    except OSError as exc:
        raise M6DurableCorruptionError(f"cannot enumerate {name}: {exc}") from exc
    expected = files | directories
    if set(entries) != expected:
        raise M6DurableCorruptionError(
            f"{name} entries mismatch: expected={sorted(expected)}, actual={sorted(entries)}"
        )
    for entry_name in files:
        entry = entries[entry_name]
        if entry.is_symlink() or not entry.is_file():
            raise M6DurableCorruptionError(f"{name} file is not regular: {entry_name}")
    for entry_name in directories:
        entry = entries[entry_name]
        if entry.is_symlink() or not entry.is_dir():
            raise M6DurableCorruptionError(f"{name} directory is not regular: {entry_name}")


def _block_identifier(value: object, *, name: str, allow_genesis: bool) -> str:
    if allow_genesis and value == GENESIS_BLOCK_ID_V1:
        return GENESIS_BLOCK_ID_V1
    return _root(value, name=name)


def _write_bundle_directory(
    final_dir: Path,
    files: Mapping[str, bytes],
    parent_dir: Path,
    *,
    max_bytes: int,
) -> None:
    bound = _active_relative_parts(final_dir)
    if bound is not None:
        _ensure_directory(parent_dir)
        parent_fd, final_name = _open_bound_parent(final_dir)
        temp_dir: Path | None = None
        temp_name: str | None = None
        try:
            try:
                os.stat(final_name, dir_fd=parent_fd, follow_symlinks=False)
            except FileNotFoundError:
                pass
            else:
                raise M6DurableCorruptionError(f"durable block already exists: {final_dir}")
            temp_dir_value = tempfile.mkdtemp(
                prefix=".m6-block-",
                dir=f"/proc/self/fd/{parent_fd}",
            )
            temp_dir = Path(temp_dir_value)
            temp_name = temp_dir.name
            for name, data in files.items():
                if Path(name).name != name:
                    raise ValueError(f"bundle file name is not flat: {name}")
                _write_new_file(temp_dir / name, data, max_bytes=max_bytes)
            _fsync_directory(temp_dir)
            os.replace(
                temp_name,
                final_name,
                src_dir_fd=parent_fd,
                dst_dir_fd=parent_fd,
            )
            _fsync_directory(parent_dir)
        except OSError as exc:
            raise M6DurableCorruptionError(
                f"cannot install durable bundle {final_dir}: {exc}"
            ) from exc
        finally:
            if temp_dir is not None and (temp_dir.exists() or temp_dir.is_symlink()):
                shutil.rmtree(temp_dir)
            os.close(parent_fd)
        return
    if final_dir.exists() or final_dir.is_symlink():
        raise M6DurableCorruptionError(f"durable block already exists: {final_dir}")
    _ensure_directory(parent_dir)
    temp_dir = Path(tempfile.mkdtemp(prefix=".m6-block-", dir=parent_dir))
    try:
        for name, data in files.items():
            if Path(name).name != name:
                raise ValueError(f"bundle file name is not flat: {name}")
            _write_new_file(temp_dir / name, data, max_bytes=max_bytes)
        _fsync_directory(temp_dir)
        os.replace(temp_dir, final_dir)
        _fsync_directory(parent_dir)
    finally:
        if temp_dir.exists():
            shutil.rmtree(temp_dir)


def _decode_durability_profile(raw: object) -> M6DurabilityProfileV1:
    obj = _object(
        raw,
        name="durability profile",
        keys={"schema", "max_json_bytes", "max_chain_blocks"},
    )
    if obj["schema"] != DURABILITY_PROFILE_SCHEMA_V1:
        raise M6DurableCorruptionError("durability profile schema mismatch")
    try:
        return M6DurabilityProfileV1(
            max_json_bytes=_nonnegative_int(obj["max_json_bytes"], name="durability max JSON bytes"),
            max_chain_blocks=_nonnegative_int(obj["max_chain_blocks"], name="durability max chain blocks"),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid durability profile: {exc}") from exc


def _decode_subject(raw: object) -> M6PromotionSubjectV1:
    obj = _object(
        raw,
        name="promotion subject",
        keys={
            "schema",
            "source",
            "proof",
            "build",
            "schema_root",
            "deployment",
            "chain_id",
            "verifier",
            "tau_profile",
            "validator_set",
            "writer_epoch",
            "managed_asset_policy",
            "risc0_image",
            "destination_adapter_roots",
            "durability_profile",
        },
    )
    if obj["schema"] != SCHEMA_V1:
        raise M6DurableCorruptionError("promotion subject schema mismatch")
    adapters: list[object] = _list(obj["destination_adapter_roots"], name="destination adapter roots")
    try:
        decoded_adapters = []
        for index, item in enumerate(adapters):
            adapter = _object(item, name=f"destination adapter {index}", keys={"adapter", "root"})
            decoded_adapters.append(
                DestinationAdapterRootV1(
                    adapter=str(_text(adapter["adapter"], name=f"destination adapter {index}.adapter")),
                    root=_root(adapter["root"], name=f"destination adapter {index}.root"),
                )
            )
        return M6PromotionSubjectV1(
            source=_root(obj["source"], name="promotion source"),
            proof=_root(obj["proof"], name="promotion proof"),
            build=_root(obj["build"], name="promotion build"),
            schema=_root(obj["schema_root"], name="promotion schema root"),
            deployment=_root(obj["deployment"], name="promotion deployment"),
            chain_id=_root(obj["chain_id"], name="promotion chain id"),
            verifier=_root(obj["verifier"], name="promotion verifier"),
            tau_profile=_root(obj["tau_profile"], name="promotion Tau profile"),
            validator_set=_root(obj["validator_set"], name="promotion validator set"),
            writer_epoch=_nonnegative_int(obj["writer_epoch"], name="promotion writer epoch"),
            managed_asset_policy=_root(obj["managed_asset_policy"], name="promotion asset policy"),
            risc0_image=_root(obj["risc0_image"], name="promotion RISC0 image"),
            destination_adapter_roots=tuple(decoded_adapters),
            durability_profile=_decode_durability_profile(obj["durability_profile"]),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid promotion subject: {exc}") from exc


def _decode_finality(raw: object) -> ZenoLedgerFinalityCertificateV1:
    obj = _object(
        raw,
        name="finality certificate",
        keys={
            "finality_id",
            "candidate_head",
            "publication_root",
            "chain_id",
            "validator_set_root",
            "writer_epoch",
            "signer_ids",
            "quorum",
            "mode",
            "signature_root",
            "execution_receipt_root",
        },
    )
    signers = tuple(
        cast(str, _text(item, name="finality signer"))
        for item in _list(obj["signer_ids"], name="finality signers")
    )
    try:
        return ZenoLedgerFinalityCertificateV1(
            finality_id=str(_text(obj["finality_id"], name="finality id")),
            candidate_head=_root(obj["candidate_head"], name="finality candidate head"),
            publication_root=_root(obj["publication_root"], name="finality publication root"),
            chain_id=_root(obj["chain_id"], name="finality chain id"),
            validator_set_root=_root(obj["validator_set_root"], name="finality validator set"),
            writer_epoch=_nonnegative_int(obj["writer_epoch"], name="finality writer epoch"),
            signer_ids=signers,
            quorum=_nonnegative_int(obj["quorum"], name="finality quorum"),
            mode=_decode_enum(FinalityModeV1, obj["mode"], name="finality mode"),
            signature_root=_root(obj["signature_root"], name="finality signature root"),
            execution_receipt_root=(
                None
                if obj["execution_receipt_root"] is None
                else _root(obj["execution_receipt_root"], name="finality execution receipt root")
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid finality certificate: {exc}") from exc


def _decode_finality_receipt_record(
    raw: object,
) -> M6FinalityVerificationReceiptRecordV1 | None:
    if raw is None:
        return None
    obj = _object(
        raw,
        name="finality verification receipt record",
        keys={
            "schema",
            "subject_root",
            "candidate_parent_head",
            "candidate_head",
            "publication_root",
            "writer_epoch",
            "certificate_root",
            "attestation_root",
            "receipt_root",
        },
    )
    if obj["schema"] != FINALITY_RECEIPT_RECORD_SCHEMA_V1:
        raise M6DurableCorruptionError("finality verification receipt record schema mismatch")
    try:
        receipt = M6FinalityVerificationReceiptRecordV1(
            subject_root=_root(obj["subject_root"], name="finality receipt record subject root"),
            candidate_parent_head=_root(
                obj["candidate_parent_head"],
                name="finality receipt record parent head",
                allow_zero=True,
            ),
            candidate_head=_root(obj["candidate_head"], name="finality receipt record candidate head"),
            publication_root=_root(
                obj["publication_root"],
                name="finality receipt record publication root",
            ),
            writer_epoch=_nonnegative_int(
                obj["writer_epoch"],
                name="finality receipt record writer epoch",
            ),
            certificate_root=_root(
                obj["certificate_root"],
                name="finality receipt record certificate root",
            ),
            attestation_root=_root(
                obj["attestation_root"],
                name="finality receipt record attestation root",
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(
            f"invalid finality verification receipt record: {exc}"
        ) from exc
    if obj["receipt_root"] != receipt.receipt_root:
        raise M6DurableCorruptionError("finality verification receipt record root mismatch")
    return receipt


def _decode_tau_certificate(raw: object) -> TauBatchCertificateV1 | None:
    if raw is None:
        return None
    obj = _object(
        raw,
        name="Tau batch certificate",
        keys={
            "batch_id",
            "tau_profile_root",
            "chain_id",
            "ordered_command_hashes",
            "ordered_nonce_identities",
            "candidate_parent_head",
            "certificate_root",
        },
    )
    try:
        return TauBatchCertificateV1(
            batch_id=str(_text(obj["batch_id"], name="Tau batch id")),
            tau_profile_root=_root(obj["tau_profile_root"], name="Tau batch profile"),
            chain_id=_root(obj["chain_id"], name="Tau batch chain id"),
            ordered_command_hashes=tuple(
                _root(item, name="Tau command hash")
                for item in _list(obj["ordered_command_hashes"], name="Tau command hashes")
            ),
            ordered_nonce_identities=tuple(
                str(_text(item, name="Tau nonce identity"))
                for item in _list(obj["ordered_nonce_identities"], name="Tau nonce identities")
            ),
            candidate_parent_head=_root(obj["candidate_parent_head"], name="Tau parent head", allow_zero=True),
            certificate_root=_root(obj["certificate_root"], name="Tau certificate root"),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid Tau batch certificate: {exc}") from exc


def _decode_zrpf_journal(raw: object) -> ZRPFRootJournalV1 | None:
    if raw is None:
        return None
    obj = _object(
        raw,
        name="ZRPF root journal",
        keys={
            "profile",
            "promotion_subject_root",
            "writer_epoch",
            "pre_state_root",
            "post_state_root",
            "command_count",
            "chunk_statement_roots",
            "aggregate_statement_roots",
            "command_root",
            "nonce_root",
            "value_delta_root",
            "history_root",
            "nullifier_root",
            "outbox_root",
            "data_availability_root",
            "verifier_image",
        },
    )
    try:
        return ZRPFRootJournalV1(
            profile=str(_text(obj["profile"], name="ZRPF journal profile")),
            promotion_subject_root=_root(obj["promotion_subject_root"], name="ZRPF journal subject"),
            writer_epoch=_nonnegative_int(obj["writer_epoch"], name="ZRPF journal writer epoch"),
            pre_state_root=_root(obj["pre_state_root"], name="ZRPF journal pre-state", allow_zero=True),
            post_state_root=_root(obj["post_state_root"], name="ZRPF journal post-state"),
            command_count=_nonnegative_int(obj["command_count"], name="ZRPF journal command count"),
            chunk_statement_roots=tuple(
                _root(item, name="ZRPF journal chunk root")
                for item in _list(obj["chunk_statement_roots"], name="ZRPF journal chunk roots")
            ),
            aggregate_statement_roots=tuple(
                _root(item, name="ZRPF journal aggregate root")
                for item in _list(obj["aggregate_statement_roots"], name="ZRPF journal aggregate roots")
            ),
            command_root=_root(obj["command_root"], name="ZRPF journal command root"),
            nonce_root=_root(obj["nonce_root"], name="ZRPF journal nonce root"),
            value_delta_root=_root(obj["value_delta_root"], name="ZRPF journal value delta root"),
            history_root=_root(obj["history_root"], name="ZRPF journal history root"),
            nullifier_root=_root(obj["nullifier_root"], name="ZRPF journal nullifier root"),
            outbox_root=_root(obj["outbox_root"], name="ZRPF journal outbox root"),
            data_availability_root=_root(
                obj["data_availability_root"],
                name="ZRPF journal data availability root",
            ),
            verifier_image=_root(obj["verifier_image"], name="ZRPF journal verifier image"),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid ZRPF root journal: {exc}") from exc


def _decode_zrpf_receipt_record(raw: object) -> M6ZRPFVerificationReceiptRecordV1 | None:
    if raw is None:
        return None
    obj = _object(
        raw,
        name="ZRPF verification receipt record",
        keys={
            "schema",
            "promotion_subject_root",
            "profile",
            "verifier_image",
            "journal_root",
            "data_availability_root",
            "attestation_root",
            "receipt_root",
        },
    )
    if obj["schema"] != ZRPF_RECEIPT_RECORD_SCHEMA_V1:
        raise M6DurableCorruptionError("ZRPF verification receipt record schema mismatch")
    try:
        receipt = M6ZRPFVerificationReceiptRecordV1(
            promotion_subject_root=_root(
                obj["promotion_subject_root"],
                name="ZRPF receipt record subject root",
            ),
            profile=str(_text(obj["profile"], name="ZRPF receipt record profile")),
            verifier_image=_root(
                obj["verifier_image"],
                name="ZRPF receipt record verifier image",
            ),
            journal_root=_root(obj["journal_root"], name="ZRPF receipt record journal root"),
            data_availability_root=_root(
                obj["data_availability_root"],
                name="ZRPF receipt record DA root",
            ),
            attestation_root=_root(
                obj["attestation_root"],
                name="ZRPF receipt record attestation root",
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(
            f"invalid ZRPF verification receipt record: {exc}"
        ) from exc
    if obj["receipt_root"] != receipt.receipt_root:
        raise M6DurableCorruptionError("ZRPF verification receipt record root mismatch")
    return receipt


def _decode_outbox(raw: object, *, name: str = "outbox") -> tuple[OutboxAtomV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name=name)):
        obj = _object(
            item,
            name=f"{name}[{index}]",
            keys={"effect_id", "effect_type", "destination", "asset", "amount_atoms", "source_state_root"},
        )
        decoded.append(
            OutboxAtomV1(
                effect_id=str(_text(obj["effect_id"], name="outbox effect id")),
                effect_type=str(_text(obj["effect_type"], name="outbox effect type")),
                destination=str(_text(obj["destination"], name="outbox destination")),
                asset=str(_text(obj["asset"], name="outbox asset")),
                amount_atoms=_nonnegative_int(obj["amount_atoms"], name="outbox amount"),
                source_state_root=_root(obj["source_state_root"], name="outbox source root"),
            )
        )
    return tuple(decoded)


def _decode_nonces(raw: object) -> tuple[NonceAtomV1, ...]:
    return tuple(
        NonceAtomV1(
            sender=str(_text(value["sender"], name="nonce sender")),
            last_nonce=_nonnegative_int(value["last_nonce"], name="last nonce"),
        )
        for index, item in enumerate(_list(raw, name="ingress nonces"))
        for value in [_object(item, name=f"ingress nonce {index}", keys={"sender", "last_nonce"})]
    )


def _decode_atoms(raw: object) -> tuple[EconomicAtomV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name="economic atoms")):
        value = _object(item, name=f"economic atom {index}", keys={"kind", "owner", "asset", "custody", "amount_atoms"})
        decoded.append(
            EconomicAtomV1(
                kind=_decode_enum(EconomicAtomKindV1, value["kind"], name="economic atom kind"),
                owner=str(_text(value["owner"], name="economic atom owner")),
                asset=str(_text(value["asset"], name="economic atom asset")),
                custody=str(_text(value["custody"], name="economic atom custody")),
                amount_atoms=_nonnegative_int(value["amount_atoms"], name="economic atom amount"),
            )
        )
    return tuple(decoded)


def _decode_migration(raw: object) -> MigrationStateV1:
    value = _object(
        raw,
        name="migration",
        keys={"phase", "authority_epoch", "previous_authority_root", "checkpoint_root", "quiescent"},
    )
    if type(value["quiescent"]) is not bool:
        raise M6DurableCorruptionError("migration quiescent must be bool")
    try:
        return MigrationStateV1(
            phase=_decode_enum(MigrationPhaseV1, value["phase"], name="migration phase"),
            authority_epoch=_nonnegative_int(value["authority_epoch"], name="migration epoch"),
            previous_authority_root=_root(value["previous_authority_root"], name="previous authority root", allow_zero=True),
            checkpoint_root=_root(value["checkpoint_root"], name="checkpoint root", allow_zero=True),
            quiescent=value["quiescent"],
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid migration: {exc}") from exc


def _decode_escrows(raw: object) -> tuple[EscrowAtomV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name="escrows")):
        value = _object(item, name=f"escrow {index}", keys={"escrow_id", "owner", "asset", "amount_atoms", "terminal_state"})
        decoded.append(
            EscrowAtomV1(
                escrow_id=str(_text(value["escrow_id"], name="escrow id")),
                owner=str(_text(value["owner"], name="escrow owner")),
                asset=str(_text(value["asset"], name="escrow asset")),
                amount_atoms=_nonnegative_int(value["amount_atoms"], name="escrow amount"),
                terminal_state=str(_text(value["terminal_state"], name="escrow terminal state")),
            )
        )
    return tuple(decoded)


def _decode_withdrawals(raw: object) -> tuple[TauWithdrawalIntentV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name="withdrawals")):
        value = _object(item, name=f"withdrawal {index}", keys={"withdrawal_id", "beneficiary", "asset", "amount_atoms", "source_state_root", "candidate_id", "status"})
        decoded.append(
            TauWithdrawalIntentV1(
                withdrawal_id=str(_text(value["withdrawal_id"], name="withdrawal id")),
                beneficiary=str(_text(value["beneficiary"], name="withdrawal beneficiary")),
                asset=str(_text(value["asset"], name="withdrawal asset")),
                amount_atoms=_nonnegative_int(value["amount_atoms"], name="withdrawal amount"),
                source_state_root=_root(value["source_state_root"], name="withdrawal source root"),
                candidate_id=str(_text(value["candidate_id"], name="withdrawal candidate id")),
                status=_decode_enum(TauWithdrawalStatusV1, value["status"], name="withdrawal status"),
            )
        )
    return tuple(decoded)


def _decode_acknowledgments(raw: object) -> tuple[WithdrawalAcknowledgmentV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name="acknowledgments")):
        value = _object(
            item,
            name=f"acknowledgment {index}",
            keys={
                "withdrawal_id",
                "provenance_root",
                "tau_receipt_root",
                "acknowledged_state_root",
                "tau_receipt_height",
            },
        )
        decoded.append(
            WithdrawalAcknowledgmentV1(
                withdrawal_id=str(_text(value["withdrawal_id"], name="ack withdrawal id")),
                provenance_root=_root(value["provenance_root"], name="ack provenance root"),
                tau_receipt_root=_root(value["tau_receipt_root"], name="ack Tau receipt root"),
                acknowledged_state_root=_root(value["acknowledged_state_root"], name="ack state root"),
                tau_receipt_height=_nonnegative_int(
                    value["tau_receipt_height"],
                    name="ack Tau receipt height",
                ),
            )
        )
    return tuple(decoded)


def _optional_nonnegative_int(value: object, *, name: str) -> int | None:
    if value is None:
        return None
    return _nonnegative_int(value, name=name)


def _decode_seller_auction_bids(raw: object) -> tuple[SellerAuctionBidStateV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name="seller auction bids")):
        value = _object(
            item,
            name=f"seller auction bid {index}",
            keys={
                "auction_id", "bidder", "escrow_id", "bond_asset", "bond_atoms", "commitment",
                "commit_height", "reveal_deadline_height", "settle_deadline_height", "inventory_asset",
                "quantity_atoms", "price_e8", "reveal_nonce", "filled_quantity_atoms", "paid_atoms",
                "rounding_remainder_e8", "phase",
            },
        )
        decoded.append(
            SellerAuctionBidStateV1(
                auction_id=str(_text(value["auction_id"], name="auction id")),
                bidder=str(_text(value["bidder"], name="auction bidder")),
                escrow_id=str(_text(value["escrow_id"], name="auction escrow id")),
                bond_asset=str(_text(value["bond_asset"], name="auction bond asset")),
                bond_atoms=_nonnegative_int(value["bond_atoms"], name="auction bond atoms"),
                commitment=_root(value["commitment"], name="auction commitment"),
                commit_height=_nonnegative_int(value["commit_height"], name="auction commit height"),
                reveal_deadline_height=_nonnegative_int(value["reveal_deadline_height"], name="auction reveal deadline"),
                settle_deadline_height=_nonnegative_int(value["settle_deadline_height"], name="auction settle deadline"),
                inventory_asset=_text(value["inventory_asset"], name="auction inventory asset", allow_none=True),
                quantity_atoms=_optional_nonnegative_int(value["quantity_atoms"], name="auction quantity"),
                price_e8=_optional_nonnegative_int(value["price_e8"], name="auction price"),
                reveal_nonce=_optional_nonnegative_int(value["reveal_nonce"], name="auction reveal nonce"),
                filled_quantity_atoms=_nonnegative_int(value["filled_quantity_atoms"], name="auction filled quantity"),
                paid_atoms=_nonnegative_int(value["paid_atoms"], name="auction paid atoms"),
                rounding_remainder_e8=_nonnegative_int(value["rounding_remainder_e8"], name="auction rounding remainder"),
                phase=_decode_enum(SellerAuctionPhaseV1, value["phase"], name="auction phase"),
            )
        )
    return tuple(decoded)


def _decode_private_swap_participants(raw: object) -> tuple[PrivateSwapParticipantStateV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name="private swap participants")):
        value = _object(
            item,
            name=f"private swap participant {index}",
            keys={
                "batch_id", "trader", "escrow_id", "bond_asset", "bond_atoms", "commitment",
                "commit_height", "reveal_deadline_height", "settle_deadline_height", "asset_in",
                "amount_in_atoms", "asset_out", "amount_out_atoms", "reveal_nonce", "phase",
            },
        )
        decoded.append(
            PrivateSwapParticipantStateV1(
                batch_id=str(_text(value["batch_id"], name="private batch id")),
                trader=str(_text(value["trader"], name="private trader")),
                escrow_id=str(_text(value["escrow_id"], name="private escrow id")),
                bond_asset=str(_text(value["bond_asset"], name="private bond asset")),
                bond_atoms=_nonnegative_int(value["bond_atoms"], name="private bond atoms"),
                commitment=_root(value["commitment"], name="private commitment"),
                commit_height=_nonnegative_int(value["commit_height"], name="private commit height"),
                reveal_deadline_height=_nonnegative_int(value["reveal_deadline_height"], name="private reveal deadline"),
                settle_deadline_height=_nonnegative_int(value["settle_deadline_height"], name="private settle deadline"),
                asset_in=_text(value["asset_in"], name="private input asset", allow_none=True),
                amount_in_atoms=_optional_nonnegative_int(value["amount_in_atoms"], name="private input amount"),
                asset_out=_text(value["asset_out"], name="private output asset", allow_none=True),
                amount_out_atoms=_optional_nonnegative_int(value["amount_out_atoms"], name="private output amount"),
                reveal_nonce=_optional_nonnegative_int(value["reveal_nonce"], name="private reveal nonce"),
                phase=_decode_enum(PrivateSwapPhaseV1, value["phase"], name="private phase"),
            )
        )
    return tuple(decoded)


def _decode_history(raw: object) -> tuple[HistoryAtomV1, ...]:
    decoded = []
    for index, item in enumerate(_list(raw, name="history")):
        value = _object(
            item,
            name=f"history {index}",
            keys={
                "sequence",
                "command_hash",
                "sender",
                "nonce",
                "pre_state_root",
                "post_state_root",
                "outcome",
                "value_delta_root",
                "nullifier",
                "business_reject_reason",
            },
        )
        raw_reject_reason = value["business_reject_reason"]
        decoded.append(
            HistoryAtomV1(
                sequence=_nonnegative_int(value["sequence"], name="history sequence"),
                command_hash=_root(value["command_hash"], name="history command hash"),
                sender=str(_text(value["sender"], name="history sender")),
                nonce=_nonnegative_int(value["nonce"], name="history nonce"),
                pre_state_root=_root(value["pre_state_root"], name="history pre-state", allow_zero=True),
                post_state_root=_root(value["post_state_root"], name="history post-state"),
                outcome=_decode_enum(BusinessStatusV1, value["outcome"], name="history outcome"),
                value_delta_root=_root(value["value_delta_root"], name="history delta root"),
                nullifier=_root(value["nullifier"], name="history nullifier"),
                business_reject_reason=(
                    None
                    if raw_reject_reason is None
                    else _decode_enum(
                        BusinessRejectReasonV1,
                        raw_reject_reason,
                        name="history business reject reason",
                    )
                ),
            )
        )
    return tuple(decoded)


def _decode_state(raw: object) -> M6ApplicationStateV1:
    obj = _object(
        raw,
        name="application state",
        keys={
            "schema", "deployment", "writer_epoch", "ingress_nonces", "economic_atoms", "migration",
            "escrows", "withdrawals", "outbox", "acknowledgments", "head", "history", "nullifiers",
            "seller_auction_bids", "private_swap_participants", "finality_certificates", "history_root_cache",
            "nullifier_root_cache", "outbox_root_cache",
        },
    )
    if obj["schema"] != SCHEMA_V1:
        raise M6DurableCorruptionError("application state schema mismatch")
    try:
        return M6ApplicationStateV1(
            deployment=_root(obj["deployment"], name="state deployment"),
            head=_root(obj["head"], name="state head", allow_zero=True),
            writer_epoch=_nonnegative_int(obj["writer_epoch"], name="state writer epoch"),
            ingress_nonces=_decode_nonces(obj["ingress_nonces"]),
            economic_atoms=_decode_atoms(obj["economic_atoms"]),
            history=_decode_history(obj["history"]),
            nullifiers=tuple(_root(item, name="nullifier") for item in _list(obj["nullifiers"], name="nullifiers")),
            finality_certificates=tuple(_decode_finality(item) for item in _list(obj["finality_certificates"], name="finality certificates")),
            migration=_decode_migration(obj["migration"]),
            escrows=_decode_escrows(obj["escrows"]),
            withdrawals=_decode_withdrawals(obj["withdrawals"]),
            outbox=_decode_outbox(obj["outbox"]),
            acknowledgments=_decode_acknowledgments(obj["acknowledgments"]),
            seller_auction_bids=_decode_seller_auction_bids(obj["seller_auction_bids"]),
            private_swap_participants=_decode_private_swap_participants(obj["private_swap_participants"]),
            history_root_cache=_root(obj["history_root_cache"], name="history root cache"),
            nullifier_root_cache=_root(obj["nullifier_root_cache"], name="nullifier root cache"),
            outbox_root_cache=_root(obj["outbox_root_cache"], name="outbox root cache"),
        )
    except M6DurableCorruptionError:
        raise
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid application state: {exc}") from exc


def _decode_direct_replay(raw: object) -> DirectExecutionReplayV1:
    obj = _object(
        raw,
        name="direct execution replay",
        keys={
            "command_body_hex",
            "context_body_hex",
            "candidate_body_hex",
            "data_availability_root",
        },
    )
    try:
        return DirectExecutionReplayV1(
            command_body_hex=cast(str, _text(obj["command_body_hex"], name="direct command body")),
            context_body_hex=cast(str, _text(obj["context_body_hex"], name="direct context body")),
            candidate_body_hex=cast(
                str | None,
                _text(
                    obj["candidate_body_hex"],
                    name="direct candidate projection body",
                    allow_none=True,
                ),
            ),
            data_availability_root=_root(
                obj["data_availability_root"],
                name="direct data-availability root",
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid direct execution replay: {exc}") from exc


def _decode_direct_replay_batch(
    raw: object,
) -> tuple[DirectExecutionReplayV1, ...] | None:
    if raw is None:
        return None
    return tuple(
        _decode_direct_replay(item)
        for item in _list(raw, name="direct batch replay")
    )


def _decode_record(raw: object) -> M6PublishedRecordV1:
    obj = _object(
        raw,
        name="published record",
        keys={
            "candidate_id",
            "parent_head",
            "pre_state_root",
            "post_state_root",
            "publication_root",
            "command_root",
            "value_delta_root",
            "history_root",
            "nullifier_root",
            "outbox_root",
            "outbox_atoms",
            "finality",
            "finality_receipt",
            "tau_certificate",
            "business_status",
            "business_reject_reason",
            "zrpf_journal",
            "zrpf_receipt",
            "direct_replay",
            "direct_batch_replay",
            "direct_batch_data_availability_root",
        },
    )
    candidate_id = _root(obj["candidate_id"], name="record candidate id")
    finality = _decode_finality(obj["finality"])
    raw_status = obj["business_status"]
    business_status = (
        None
        if raw_status is None
        else _decode_enum(BusinessStatusV1, raw_status, name="record business status")
    )
    raw_reject_reason = obj["business_reject_reason"]
    business_reject_reason = (
        None
        if raw_reject_reason is None
        else _decode_enum(
            BusinessRejectReasonV1,
            raw_reject_reason,
            name="record business reject reason",
        )
    )
    try:
        record = M6PublishedRecordV1(
            candidate_id=candidate_id,
            parent_head=_root(obj["parent_head"], name="record parent head", allow_zero=True),
            pre_state_root=_root(obj["pre_state_root"], name="record pre-state"),
            post_state_root=_root(obj["post_state_root"], name="record post-state"),
            publication_root=_root(obj["publication_root"], name="record publication root"),
            command_root=_root(obj["command_root"], name="record command root"),
            value_delta_root=_root(obj["value_delta_root"], name="record delta root"),
            history_root=_root(obj["history_root"], name="record history root"),
            nullifier_root=_root(obj["nullifier_root"], name="record nullifier root"),
            outbox_root=_root(obj["outbox_root"], name="record outbox root"),
            outbox_atoms=_decode_outbox(obj["outbox_atoms"], name="record outbox atoms"),
            finality=finality,
            finality_receipt=_decode_finality_receipt_record(obj["finality_receipt"]),
            tau_certificate=_decode_tau_certificate(obj["tau_certificate"]),
            business_status=business_status,
            business_reject_reason=business_reject_reason,
            zrpf_journal=_decode_zrpf_journal(obj["zrpf_journal"]),
            zrpf_receipt=_decode_zrpf_receipt_record(obj["zrpf_receipt"]),
            direct_replay=(
                None
                if obj["direct_replay"] is None
                else _decode_direct_replay(obj["direct_replay"])
            ),
            direct_batch_replay=_decode_direct_replay_batch(obj["direct_batch_replay"]),
            direct_batch_data_availability_root=(
                None
                if obj["direct_batch_data_availability_root"] is None
                else _root(
                    obj["direct_batch_data_availability_root"],
                    name="direct batch data-availability root",
                )
            ),
        )
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"invalid published record: {exc}") from exc
    if record.receipt_root != _root(record.receipt_root, name="record receipt root"):
        raise M6DurableCorruptionError("record receipt root is not canonical")
    return record


def _manifest_keys() -> set[str]:
    return {
        "schema",
        "kind",
        "block_id",
        "subject_root",
        "parent_block_id",
        "parent_state_root",
        "parent_head",
        "candidate_id",
        "pre_state_root",
        "post_state_root",
        "publication_root",
        "record_root",
        "writer_epoch",
        "files",
    }


def _head_payload(*, subject: M6PromotionSubjectV1, block_id: str, state: M6ApplicationStateV1) -> dict[str, object]:
    return {
        "schema": DURABLE_SCHEMA_V1,
        "subject_root": subject.subject_root,
        "block_id": block_id,
        "head_root": state.state_root,
        "economic_head": state.head,
        "writer_epoch": state.writer_epoch,
    }


def _head_keys() -> set[str]:
    return {"schema", "subject_root", "block_id", "head_root", "economic_head", "writer_epoch"}


def _block_id(
    subject: M6PromotionSubjectV1,
    *,
    parent_block_id: str,
    parent_state_root: str,
    parent_head: str,
    record: M6PublishedRecordV1,
) -> str:
    return hash_v1(
        "m6-durable-block-v1",
        {
            "subject_root": subject.subject_root,
            "parent_block_id": parent_block_id,
            "parent_state_root": parent_state_root,
            "parent_head": parent_head,
            "candidate_id": record.candidate_id,
            "post_state_root": record.post_state_root,
            "receipt_root": record.receipt_root,
        },
    )


class M6DurableLedgerStoreV1:
    """Filesystem-backed M6 shell with fail-closed reopen behavior."""

    def __init__(
        self,
        root: str | Path,
        subject: M6PromotionSubjectV1,
        finality_verifier: M6FinalityVerifierV1 | None = None,
    ) -> None:
        if type(subject) is not M6PromotionSubjectV1:
            raise TypeError("durable ledger subject must be the exact owned type")
        self._root = Path(root)
        self._subject = deepcopy(subject)
        self._finality_verifier = finality_verifier
        self._parent_lock_name = f".{self._root.name}.m6-root.lock"
        try:
            root_stat = os.stat(self._root, follow_symlinks=False)
        except FileNotFoundError:
            self._root_identity: tuple[int, int] | None = None
        except OSError as exc:
            raise M6DurableCorruptionError(f"cannot stat durable root: {exc}") from exc
        else:
            if not stat.S_ISDIR(root_stat.st_mode):
                raise M6DurableCorruptionError(
                    f"durable root must be a directory: {self._root}"
                )
            self._root_identity = (root_stat.st_dev, root_stat.st_ino)

    @classmethod
    def create(
        cls,
        root: str | Path,
        subject: M6PromotionSubjectV1,
        initial_state: M6ApplicationStateV1,
        *,
        finality_verifier: M6FinalityVerifierV1 | None = None,
    ) -> M6DurableLedgerStoreV1:
        if type(subject) is not M6PromotionSubjectV1:
            raise TypeError("durable ledger subject must be the exact owned type")
        if type(initial_state) is not M6ApplicationStateV1:
            raise TypeError("durable genesis state must be the exact owned type")
        root_path = Path(root)
        if root_path.is_symlink():
            raise M6DurableCorruptionError(f"durable M6 root must not be a symlink: {root_path}")
        if root_path.exists() and not root_path.is_dir():
            raise M6DurableCorruptionError(f"durable M6 root must be a directory: {root_path}")
        if root_path.exists() and any(root_path.iterdir()):
            raise FileExistsError(f"durable M6 root is not empty: {root_path}")

        # Validate the complete immutable genesis bundle before creating the
        # shell directory or its lock file.  An invalid candidate must leave
        # no durable authority artifact behind, so a caller can correct the
        # input and retry against the same path.
        if initial_state.deployment != subject.deployment:
            raise ValueError("genesis state deployment does not match subject")
        if initial_state.writer_epoch != subject.writer_epoch:
            raise ValueError("genesis state epoch does not match subject")
        validate_economic_state_v1(initial_state)
        if initial_state.history or initial_state.nullifiers or initial_state.finality_certificates:
            raise ValueError("genesis state must have empty history, nullifiers, and finality")

        _ensure_directory(root_path)
        instance = cls(root_path, subject, finality_verifier)
        with instance._file_lock(create_lock=True):
            io_root = instance._io_root()
            if any(entry.name != LOCK_FILE_V1 for entry in io_root.iterdir()):
                raise FileExistsError(f"durable M6 root was populated during create: {root_path}")
            _ensure_directory(io_root / BLOCKS_DIR_V1)
            instance._install_genesis_unlocked(initial_state)
            instance._write_head_unlocked(GENESIS_BLOCK_ID_V1, initial_state)
        return instance

    @property
    def root(self) -> Path:
        return self._root

    @property
    def subject(self) -> M6PromotionSubjectV1:
        return deepcopy(self._subject)

    def _io_root(self) -> Path:
        """Return the root directory identity held by the active lock."""

        return _ACTIVE_DURABLE_ROOT.get() or self._root

    def _assert_configured_root_is_bound(self, root_fd: int) -> None:
        """Reject a commit acknowledgment after the configured path was replaced.

        Descriptor-relative I/O keeps the operation on the locked inode.  The
        configured pathname is still the discovery point used by fresh
        processes, so returning a successful durable result while that name
        points elsewhere would acknowledge a store that new readers cannot
        reach.  The parent-directory lock narrows the race for cooperative
        writers; this final check closes the observable path/inode split for
        the operation itself.  A hostile actor that ignores filesystem locks
        remains outside this research shell's trust model.
        """

        try:
            path_stat = os.stat(self._root, follow_symlinks=False)
        except OSError as exc:
            raise M6DurableCorruptionError(
                f"cannot revalidate configured durable root: {exc}"
            ) from exc
        if not os.path.samestat(os.fstat(root_fd), path_stat):
            raise M6DurableCorruptionError(
                "configured durable root changed before commit acknowledgment"
            )

    def reopen(self) -> M6DurableReopenV1:
        with self._file_lock():
            return self._load_reopened_unlocked()

    @contextmanager
    def external_effect_submission_guard(self) -> Iterator[M6DurableReopenV1]:
        """Linearize short local setup against ledger publication.

        The caller receives one canonical snapshot while the same lock used by
        ``publish`` remains held. External callbacks must not run under this
        guard because they would block unrelated ledger work.
        """

        with self._file_lock():
            yield self._load_reopened_unlocked()

    @contextmanager
    def external_effect_submission_lease(self, effect_id: str) -> Iterator[None]:
        """Serialize one effect submission with its acknowledgment commit."""

        if type(effect_id) is not str or not effect_id or len(effect_id.encode("utf-8")) > 256:
            raise M6DurableCorruptionError("external effect lease id is invalid")
        if any(ord(character) < 0x21 or ord(character) > 0x7E for character in effect_id):
            raise M6DurableCorruptionError("external effect lease id is invalid")
        journal_root = self._root.parent / f"{self._root.name}{_OUTBOX_DELIVERY_ROOT_SUFFIX_V1}"
        lease_name = (
            hash_v1(_OUTBOX_SUBMISSION_LEASE_DOMAIN_V1, {"effect_id": effect_id})[2:]
            + ".lock"
        )
        directory_flags = (
            os.O_RDONLY
            | getattr(os, "O_DIRECTORY", 0)
            | getattr(os, "O_NOFOLLOW", 0)
        )
        file_flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0)
        journal_fd: int | None = None
        lease_directory_fd: int | None = None
        lease_fd: int | None = None
        try:
            journal_fd = os.open(journal_root, directory_flags)
            lease_directory_fd = os.open(
                _OUTBOX_SUBMISSION_LEASES_DIR_V1,
                directory_flags,
                dir_fd=journal_fd,
            )
            lease_fd = os.open(lease_name, file_flags, 0o600, dir_fd=lease_directory_fd)
        except OSError as exc:
            cleanup_failed = False
            for descriptor in (lease_fd, lease_directory_fd, journal_fd):
                if descriptor is not None:
                    try:
                        os.close(descriptor)
                    except OSError:
                        cleanup_failed = True
            if cleanup_failed:
                raise M6DurableCorruptionError(
                    "external effect lease setup cleanup failed"
                ) from exc
            raise M6DurableCorruptionError("external effect lease is unavailable") from exc
        locked = False
        try:
            os.fsync(lease_directory_fd)
            try:
                fcntl.flock(lease_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise _M6ExternalEffectLeaseBusy(
                    "external effect submission is already in progress"
                ) from exc
            locked = True
            configured = os.stat(journal_root, follow_symlinks=False)
            if not os.path.samestat(os.fstat(journal_fd), configured):
                raise M6DurableCorruptionError("external effect journal root changed")
            current_lease = os.stat(
                lease_name,
                dir_fd=lease_directory_fd,
                follow_symlinks=False,
            )
            if not stat.S_ISREG(current_lease.st_mode) or not os.path.samestat(
                os.fstat(lease_fd), current_lease
            ):
                raise M6DurableCorruptionError("external effect lease changed")
            yield
        except OSError as exc:
            raise M6DurableCorruptionError("external effect lease failed") from exc
        finally:
            cleanup_failed = False
            if locked:
                try:
                    fcntl.flock(lease_fd, fcntl.LOCK_UN)
                except OSError:
                    cleanup_failed = True
            for descriptor in (lease_fd, lease_directory_fd, journal_fd):
                try:
                    os.close(descriptor)
                except OSError:
                    cleanup_failed = True
            if cleanup_failed:
                raise M6DurableCorruptionError(
                    "external effect lease cleanup failed"
                )

    @contextmanager
    def _acknowledgment_submission_leases(
        self,
        commands: tuple[GlobalCommandV1, ...],
    ) -> Iterator[bool]:
        if type(commands) is not tuple or any(
            type(command) is not GlobalCommandV1
            or type(command.payload) is not tuple
            or any(
                type(argument) is not CommandArgumentV1
                or type(argument.key) is not str
                or type(argument.value) not in (str, int)
                for argument in command.payload
            )
            for command in commands
        ):
            raise TypeError(
                "acknowledgment lease extraction requires exact owned commands"
            )
        effect_ids = sorted(
            {
                value
                for command in commands
                if command.kind is GlobalCommandKindV1.TAU_WITHDRAWAL_ACK
                for value in (command.payload_value("withdrawal_id"),)
                if isinstance(value, str)
            }
        )
        with ExitStack() as stack:
            try:
                for effect_id in effect_ids:
                    stack.enter_context(self.external_effect_submission_lease(effect_id))
            except _M6ExternalEffectLeaseBusy:
                stack.close()
                yield False
                return
            yield True

    def _verify_publication_outside_durable_lock(
        self,
        *,
        expected: M6DurableReopenV1,
        candidate_id: str,
        publish: Callable[[M6CommitPortV1], CommitResultV1],
    ) -> CommitResultV1:
        """Run external finality verification against one immutable snapshot."""

        port = M6CommitPortV1(
            self._subject,
            expected.state,
            self._finality_verifier,
        )
        result = publish(port)
        if result.candidate_id != candidate_id:
            raise M6DurableCorruptionError("commit port returned a foreign candidate id")
        return result

    def _persist_verified_publication_locked(
        self,
        *,
        expected: M6DurableReopenV1,
        candidate_id: str,
        result: CommitResultV1,
        head_error: str,
        changed_head_replay: Callable[
            [M6DurableReopenV1],
            M6DurableCommitResultV1 | None,
        ],
    ) -> M6DurableCommitResultV1:
        """CAS-install an already verified proposal after reacquiring the lock."""

        reopened = self._load_reopened_unlocked()
        if (
            reopened.head_block_id != expected.head_block_id
            or reopened.state != expected.state
            or reopened.records != expected.records
            or reopened.chain_block_ids != expected.chain_block_ids
        ):
            if self._existing_record(reopened, candidate_id) is not None:
                replay = changed_head_replay(reopened)
                if replay is not None:
                    return replay
            return M6DurableCommitResultV1(
                status=CommitStatusV1.STALE_HEAD,
                state=reopened.state,
                candidate_id=candidate_id,
                reason="durable head changed during external finality verification",
            )
        if result.status is not CommitStatusV1.COMMITTED or result.record is None:
            return M6DurableCommitResultV1(
                status=result.status,
                state=reopened.state,
                candidate_id=candidate_id,
                record=result.record,
                reason=result.reason,
            )
        try:
            block_id = self._install_commit_unlocked(reopened, result.record, result.state)
            self._write_head_unlocked(
                block_id,
                result.state,
                expected_block_id=reopened.head_block_id,
                expected_state_root=reopened.state.state_root,
            )
        except M6DurableCorruptionError as cause:
            try:
                recovered = self._load_reopened_unlocked()
            except M6DurableCorruptionError as recovery_error:
                raise cause from recovery_error
            if self._existing_record(recovered, candidate_id) is not None:
                replay = changed_head_replay(recovered)
                if replay is not None:
                    return replay
            raise cause
        verified = self._load_reopened_unlocked()
        if verified.head_block_id != block_id:
            raise M6DurableCorruptionError(head_error)
        return M6DurableCommitResultV1(
            status=CommitStatusV1.COMMITTED,
            state=verified.state,
            candidate_id=candidate_id,
            block_id=block_id,
            record=result.record,
        )

    @staticmethod
    def _lease_busy_commit_result(
        reopened: M6DurableReopenV1,
        candidate_id: str,
    ) -> M6DurableCommitResultV1:
        return M6DurableCommitResultV1(
            status=CommitStatusV1.FINALITY_REJECTED,
            state=reopened.state,
            candidate_id=candidate_id,
            reason="external effect submission is already in progress",
        )

    def _durable_direct_replay_or_limit(
        self,
        *,
        reopened: M6DurableReopenV1,
        candidate: AcceptCandidateV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
        leases_available: bool,
    ) -> M6DurableCommitResultV1 | None:
        if not leases_available:
            return self._lease_busy_commit_result(reopened, candidate.candidate_id)
        existing = self._existing_record(reopened, candidate.candidate_id)
        if existing is not None:
            if _candidate_matches_record(
                candidate,
                existing,
            ) and finality_evidence_matches_published_record_v1(
                self._subject,
                existing,
                finality,
                tau_certificate,
            ):
                return M6DurableCommitResultV1(
                    status=CommitStatusV1.ALREADY_COMMITTED,
                    state=reopened.state,
                    candidate_id=candidate.candidate_id,
                    block_id=self._block_for_record(reopened, existing),
                    record=existing,
                )
            return M6DurableCommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=reopened.state,
                candidate_id=candidate.candidate_id,
                reason="candidate or finality replay identity conflicts with durable record",
            )
        if len(reopened.chain_block_ids[1:]) >= self._subject.durability_profile.max_chain_blocks:
            return M6DurableCommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=reopened.state,
                candidate_id=candidate.candidate_id,
                reason="durable chain limit reached for promotion profile",
            )
        return None

    def _recover_commit_after_lease_cleanup_failure(
        self,
        *,
        candidate_id: str,
        observed: _PublicationObservationV1,
        cause: M6DurableCorruptionError,
        replay: Callable[
            [M6DurableReopenV1],
            M6DurableCommitResultV1 | None,
        ],
    ) -> M6DurableCommitResultV1:
        """Return durable truth when shell cleanup fails after publication."""

        try:
            reopened = self.reopen()
        except M6DurableCorruptionError as recovery_error:
            raise cause from recovery_error
        if self._existing_record(reopened, candidate_id) is not None:
            recovered = replay(reopened)
            if recovered is not None:
                return recovered
        if observed.result is not None and observed.result.status is not CommitStatusV1.COMMITTED:
            return observed.result
        raise cause

    def _durable_zrpf_replay_or_limit(
        self,
        *,
        reopened: M6DurableReopenV1,
        verified_root: VerifiedZRPFRootV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
        leases_available: bool,
    ) -> M6DurableCommitResultV1 | None:
        if not leases_available:
            return self._lease_busy_commit_result(reopened, verified_root.candidate_id)
        existing = self._existing_record(reopened, verified_root.candidate_id)
        if existing is not None:
            if _zrpf_matches_record(
                verified_root,
                existing,
            ) and finality_evidence_matches_published_record_v1(
                self._subject,
                existing,
                finality,
                tau_certificate,
            ):
                return M6DurableCommitResultV1(
                    status=CommitStatusV1.ALREADY_COMMITTED,
                    state=reopened.state,
                    candidate_id=verified_root.candidate_id,
                    block_id=self._block_for_record(reopened, existing),
                    record=existing,
                )
            return M6DurableCommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=reopened.state,
                candidate_id=verified_root.candidate_id,
                reason="ZRPF or finality replay identity conflicts with durable record",
            )
        if len(reopened.chain_block_ids[1:]) >= self._subject.durability_profile.max_chain_blocks:
            return M6DurableCommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=reopened.state,
                candidate_id=verified_root.candidate_id,
                reason="durable chain limit reached for promotion profile",
            )
        return None

    def _durable_batch_replay_or_limit(
        self,
        *,
        reopened: M6DurableReopenV1,
        direct: DirectBatchCandidateV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
        leases_available: bool,
    ) -> M6DurableCommitResultV1 | None:
        if not leases_available:
            return self._lease_busy_commit_result(reopened, direct.candidate_id)
        existing = self._existing_record(reopened, direct.candidate_id)
        if existing is not None:
            if direct_batch_matches_published_record_v1(
                direct,
                existing,
            ) and finality_evidence_matches_published_record_v1(
                self._subject,
                existing,
                finality,
                tau_certificate,
            ):
                return M6DurableCommitResultV1(
                    status=CommitStatusV1.ALREADY_COMMITTED,
                    state=reopened.state,
                    candidate_id=direct.candidate_id,
                    block_id=self._block_for_record(reopened, existing),
                    record=existing,
                )
            return M6DurableCommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=reopened.state,
                candidate_id=direct.candidate_id,
                reason="direct batch or finality replay identity conflicts with durable record",
            )
        if len(reopened.chain_block_ids[1:]) >= self._subject.durability_profile.max_chain_blocks:
            return M6DurableCommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=reopened.state,
                candidate_id=direct.candidate_id,
                reason="durable chain limit reached for promotion profile",
            )
        return None

    def publish(
        self,
        candidate: AcceptCandidateV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
    ) -> M6DurableCommitResultV1:
        if type(candidate) is not AcceptCandidateV1:
            raise TypeError("durable publication candidate is not the exact owned type")
        commands = (candidate.command,)
        with self._acknowledgment_submission_leases(commands) as leases_available:
            with self._file_lock():
                reopened = self._load_reopened_unlocked()
                early = self._durable_direct_replay_or_limit(
                    reopened=reopened,
                    candidate=candidate,
                    finality=finality,
                    tau_certificate=tau_certificate,
                    leases_available=leases_available,
                )
                if early is not None:
                    return early
                expected = reopened
        result = self._verify_publication_outside_durable_lock(
            expected=expected,
            candidate_id=candidate.candidate_id,
            publish=lambda port: port.publish(candidate, finality, tau_certificate),
        )
        observed = _PublicationObservationV1()

        def replay(reopened: M6DurableReopenV1) -> M6DurableCommitResultV1 | None:
            return self._durable_direct_replay_or_limit(
                reopened=reopened,
                candidate=candidate,
                finality=finality,
                tau_certificate=tau_certificate,
                leases_available=True,
            )
        try:
            with self._acknowledgment_submission_leases(commands) as leases_available:
                with self._file_lock():
                    if not leases_available:
                        reopened = self._load_reopened_unlocked()
                        observed.result = self._lease_busy_commit_result(
                            reopened,
                            candidate.candidate_id,
                        )
                    else:
                        observed.result = self._persist_verified_publication_locked(
                            expected=expected,
                            candidate_id=candidate.candidate_id,
                            result=result,
                            head_error="HEAD did not advance to installed block",
                            changed_head_replay=replay,
                        )
        except M6DurableCorruptionError as exc:
            if observed.result is None:
                raise
            return self._recover_commit_after_lease_cleanup_failure(
                candidate_id=candidate.candidate_id,
                observed=observed,
                cause=exc,
                replay=replay,
            )
        if observed.result is None:
            raise M6DurableCorruptionError("durable publication produced no result")
        return observed.result

    def publish_zrpf(
        self,
        verified_root: VerifiedZRPFRootV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
    ) -> M6DurableCommitResultV1:
        if type(verified_root) is not VerifiedZRPFRootV1:
            raise TypeError("ZRPF publication handle is not the exact verified type")
        try:
            checked_root = reverify_zrpf_handle_v1(self._subject, verified_root)
        except ValueError as exc:
            with self._file_lock():
                reopened = self._load_reopened_unlocked()
                return M6DurableCommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=reopened.state,
                    candidate_id=verified_root.candidate_id,
                    reason=str(exc),
                )
        batch = checked_root.execution_batch
        if type(batch) is not ZRPFBatchCandidateV1:
            raise M6DurableCorruptionError("ZRPF publication batch is invalid")
        commands = batch.direct.commands
        with self._acknowledgment_submission_leases(commands) as leases_available:
            with self._file_lock():
                reopened = self._load_reopened_unlocked()
                early = self._durable_zrpf_replay_or_limit(
                    reopened=reopened,
                    verified_root=checked_root,
                    finality=finality,
                    tau_certificate=tau_certificate,
                    leases_available=leases_available,
                )
                if early is not None:
                    return early
                expected = reopened
        result = self._verify_publication_outside_durable_lock(
            expected=expected,
            candidate_id=checked_root.candidate_id,
            publish=lambda port: port.publish_zrpf(
                checked_root,
                finality,
                tau_certificate,
            ),
        )
        observed = _PublicationObservationV1()

        def replay(reopened: M6DurableReopenV1) -> M6DurableCommitResultV1 | None:
            return self._durable_zrpf_replay_or_limit(
                reopened=reopened,
                verified_root=checked_root,
                finality=finality,
                tau_certificate=tau_certificate,
                leases_available=True,
            )
        try:
            with self._acknowledgment_submission_leases(commands) as leases_available:
                with self._file_lock():
                    if not leases_available:
                        reopened = self._load_reopened_unlocked()
                        observed.result = self._lease_busy_commit_result(
                            reopened,
                            checked_root.candidate_id,
                        )
                    else:
                        observed.result = self._persist_verified_publication_locked(
                            expected=expected,
                            candidate_id=checked_root.candidate_id,
                            result=result,
                            head_error="HEAD did not advance to installed ZRPF block",
                            changed_head_replay=replay,
                        )
        except M6DurableCorruptionError as exc:
            if observed.result is None:
                raise
            return self._recover_commit_after_lease_cleanup_failure(
                candidate_id=checked_root.candidate_id,
                observed=observed,
                cause=exc,
                replay=replay,
            )
        if observed.result is None:
            raise M6DurableCorruptionError("durable ZRPF publication produced no result")
        return observed.result

    def publish_direct_batch(
        self,
        direct: DirectBatchCandidateV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
    ) -> M6DurableCommitResultV1:
        """Persist a direct multi-command candidate during proof degradation."""

        if type(direct) is not DirectBatchCandidateV1:
            raise TypeError("durable direct batch is not the exact owned type")
        commands = direct.commands
        with self._acknowledgment_submission_leases(commands) as leases_available:
            with self._file_lock():
                reopened = self._load_reopened_unlocked()
                early = self._durable_batch_replay_or_limit(
                    reopened=reopened,
                    direct=direct,
                    finality=finality,
                    tau_certificate=tau_certificate,
                    leases_available=leases_available,
                )
                if early is not None:
                    return early
                expected = reopened
        result = self._verify_publication_outside_durable_lock(
            expected=expected,
            candidate_id=direct.candidate_id,
            publish=lambda port: port.publish_direct_batch(
                direct,
                finality,
                tau_certificate,
            ),
        )
        observed = _PublicationObservationV1()

        def replay(reopened: M6DurableReopenV1) -> M6DurableCommitResultV1 | None:
            return self._durable_batch_replay_or_limit(
                reopened=reopened,
                direct=direct,
                finality=finality,
                tau_certificate=tau_certificate,
                leases_available=True,
            )
        try:
            with self._acknowledgment_submission_leases(commands) as leases_available:
                with self._file_lock():
                    if not leases_available:
                        reopened = self._load_reopened_unlocked()
                        observed.result = self._lease_busy_commit_result(
                            reopened,
                            direct.candidate_id,
                        )
                    else:
                        observed.result = self._persist_verified_publication_locked(
                            expected=expected,
                            candidate_id=direct.candidate_id,
                            result=result,
                            head_error="HEAD did not advance to installed direct batch block",
                            changed_head_replay=replay,
                        )
        except M6DurableCorruptionError as exc:
            if observed.result is None:
                raise
            return self._recover_commit_after_lease_cleanup_failure(
                candidate_id=direct.candidate_id,
                observed=observed,
                cause=exc,
                replay=replay,
            )
        if observed.result is None:
            raise M6DurableCorruptionError("durable direct batch publication produced no result")
        return observed.result

    def _install_genesis_unlocked(self, state: M6ApplicationStateV1) -> None:
        subject_data = _canonical_data(self._subject)
        state_data = _canonical_data(state)
        manifest = {
            "schema": DURABLE_SCHEMA_V1,
            "kind": "genesis",
            "block_id": GENESIS_BLOCK_ID_V1,
            "subject_root": self._subject.subject_root,
            "parent_block_id": None,
            "parent_state_root": None,
            "parent_head": ZERO_ROOT_V1,
            "candidate_id": None,
            "pre_state_root": state.state_root,
            "post_state_root": state.state_root,
            "publication_root": ZERO_ROOT_V1,
            "record_root": ZERO_ROOT_V1,
            "writer_epoch": state.writer_epoch,
            "files": {
                SUBJECT_FILE_V1: _file_digest(subject_data),
                STATE_FILE_V1: _file_digest(state_data),
            },
        }
        _write_bundle_directory(
            self._io_root() / GENESIS_DIR_V1,
            {
                SUBJECT_FILE_V1: subject_data,
                STATE_FILE_V1: state_data,
                MANIFEST_FILE_V1: _canonical_data(manifest),
            },
            self._io_root(),
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )

    def _install_commit_unlocked(
        self,
        reopened: M6DurableReopenV1,
        record: M6PublishedRecordV1,
        post_state: M6ApplicationStateV1,
    ) -> str:
        parent_block_id = reopened.head_block_id
        block_id = _block_id(
            self._subject,
            parent_block_id=parent_block_id,
            parent_state_root=reopened.state.state_root,
            parent_head=reopened.state.head,
            record=record,
        )
        subject_data = _canonical_data(self._subject)
        state_data = _canonical_data(post_state)
        record_data = _canonical_data(record)
        manifest = {
            "schema": DURABLE_SCHEMA_V1,
            "kind": "commit",
            "block_id": block_id,
            "subject_root": self._subject.subject_root,
            "parent_block_id": parent_block_id,
            "parent_state_root": reopened.state.state_root,
            "parent_head": reopened.state.head,
            "candidate_id": record.candidate_id,
            "pre_state_root": record.pre_state_root,
            "post_state_root": record.post_state_root,
            "publication_root": record.publication_root,
            "record_root": record.receipt_root,
            "writer_epoch": post_state.writer_epoch,
            "files": {
                SUBJECT_FILE_V1: _file_digest(subject_data),
                STATE_FILE_V1: _file_digest(state_data),
                RECORD_FILE_V1: _file_digest(record_data),
            },
        }
        _write_bundle_directory(
            self._io_root() / BLOCKS_DIR_V1 / block_id,
            {
                SUBJECT_FILE_V1: subject_data,
                STATE_FILE_V1: state_data,
                RECORD_FILE_V1: record_data,
                MANIFEST_FILE_V1: _canonical_data(manifest),
            },
            self._io_root() / BLOCKS_DIR_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        return block_id

    def _write_head_unlocked(
        self,
        block_id: str,
        state: M6ApplicationStateV1,
        *,
        expected_block_id: str | None = None,
        expected_state_root: str | None = None,
    ) -> None:
        if (expected_block_id is None) != (expected_state_root is None):
            raise ValueError("HEAD compare-and-swap requires both expected values")
        if expected_block_id is not None and expected_state_root is not None:
            current_raw, _ = _read_canonical_json(
                self._io_root() / HEAD_FILE_V1,
                max_bytes=self._subject.durability_profile.max_json_bytes,
            )
            current = _object(current_raw, name="HEAD", keys=_head_keys())
            if current["schema"] != DURABLE_SCHEMA_V1:
                raise M6DurableCorruptionError("HEAD schema mismatch during compare-and-swap")
            current_subject_root = _root(current["subject_root"], name="HEAD subject root")
            current_block_id = _block_identifier(
                current["block_id"], name="HEAD block id", allow_genesis=True
            )
            current_state_root = _root(current["head_root"], name="HEAD state root")
            if (
                current_subject_root != self._subject.subject_root
                or current_block_id != expected_block_id
                or current_state_root != expected_state_root
            ):
                raise M6DurableCorruptionError("HEAD compare-and-swap expectation failed")
        _atomic_replace_file(
            self._io_root() / HEAD_FILE_V1,
            _canonical_data(_head_payload(subject=self._subject, block_id=block_id, state=state)),
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )

    @contextmanager
    def _file_lock(self, *, create_lock: bool = False) -> Iterator[None]:
        if self._root.is_symlink() or not self._root.is_dir():
            raise M6DurableCorruptionError(
                f"durable root must be an existing regular directory: {self._root}"
            )
        parent_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
        root_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_NOFOLLOW", 0)
        flags = os.O_RDWR | getattr(os, "O_NOFOLLOW", 0)
        if create_lock:
            flags |= os.O_CREAT
        try:
            parent_fd = os.open(self._root.parent, parent_flags)
        except OSError as exc:
            raise M6DurableCorruptionError(f"cannot open durable root parent: {exc}") from exc
        parent_locked = False
        parent_lock_fd: int | None = None
        root_fd: int | None = None
        root_locked = False
        try:
            try:
                parent_lock_fd = os.open(
                    self._parent_lock_name,
                    flags,
                    0o600,
                    dir_fd=parent_fd,
                )
                fcntl.flock(parent_lock_fd, fcntl.LOCK_EX)
                parent_locked = True
                current_parent_stat = os.fstat(parent_fd)
                configured_parent_stat = os.stat(self._root.parent, follow_symlinks=False)
                if not os.path.samestat(current_parent_stat, configured_parent_stat):
                    raise M6DurableCorruptionError("durable root parent changed during lock acquisition")
                try:
                    current_root_path_stat = os.stat(self._root, follow_symlinks=False)
                except OSError as exc:
                    raise M6DurableCorruptionError(
                        f"root changed during lock acquisition: {exc}"
                    ) from exc
                if self._root_identity is not None and (
                    current_root_path_stat.st_dev,
                    current_root_path_stat.st_ino,
                ) != self._root_identity:
                    raise M6DurableCorruptionError("root changed during lock acquisition")
                root_fd = os.open(self._root, root_flags)
            except OSError as exc:
                raise M6DurableCorruptionError(f"cannot open durable root: {exc}") from exc
            current_root_stat = os.fstat(root_fd)
            current_root_identity = (current_root_stat.st_dev, current_root_stat.st_ino)
            if self._root_identity is None:
                # A read-only handle may be constructed before its root is
                # created.  Bind that handle to the first successfully opened
                # inode so a later path replacement cannot redirect it.
                self._root_identity = current_root_identity
            elif current_root_identity != self._root_identity:
                raise M6DurableCorruptionError("durable root changed after initialization")
            try:
                # The directory inode is the authoritative inter-process lock.
                # The stable parent lock serializes replacement-path attempts;
                # the directory inode then binds all later I/O to this root.
                fcntl.flock(root_fd, fcntl.LOCK_EX)
                root_locked = True
            except OSError as exc:
                raise M6DurableCorruptionError(f"cannot lock durable root: {exc}") from exc
            root_stat = os.fstat(root_fd)
            try:
                fd = os.open(LOCK_FILE_V1, flags, 0o600, dir_fd=root_fd)
            except OSError as exc:
                raise M6DurableCorruptionError(f"cannot open durable lock: {exc}") from exc
            try:
                lock_stat = os.fstat(fd)
                try:
                    current_root_stat = os.stat(self._root, follow_symlinks=False)
                except OSError as exc:
                    raise M6DurableCorruptionError(
                        f"cannot restat durable root during lock acquisition: {exc}"
                    ) from exc
                if not os.path.samestat(root_stat, current_root_stat):
                    raise M6DurableCorruptionError("root changed during lock acquisition")
                try:
                    current_lock_stat = os.stat(
                        LOCK_FILE_V1,
                        dir_fd=root_fd,
                        follow_symlinks=False,
                    )
                except OSError as exc:
                    raise M6DurableCorruptionError(
                        f"cannot restat durable lock during lock acquisition: {exc}"
                    ) from exc
                if not os.path.samestat(lock_stat, current_lock_stat):
                    raise M6DurableCorruptionError("lock changed during lock acquisition")
                bound_root = Path(f"/proc/self/fd/{root_fd}")
                root_token = _ACTIVE_DURABLE_ROOT.set(bound_root)
                root_fd_token = _ACTIVE_DURABLE_ROOT_FD.set(root_fd)
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX)
                    yield
                finally:
                    try:
                        self._assert_configured_root_is_bound(root_fd)
                    finally:
                        _ACTIVE_DURABLE_ROOT_FD.reset(root_fd_token)
                        _ACTIVE_DURABLE_ROOT.reset(root_token)
            finally:
                lock_cleanup_error: OSError | None = None
                try:
                    fcntl.flock(fd, fcntl.LOCK_UN)
                except OSError as exc:
                    lock_cleanup_error = exc
                try:
                    os.close(fd)
                except OSError as exc:
                    if lock_cleanup_error is None:
                        lock_cleanup_error = exc
                if lock_cleanup_error is not None:
                    raise M6DurableCorruptionError(
                        "durable lock cleanup failed"
                    ) from lock_cleanup_error
        finally:
            root_cleanup_error: OSError | None = None
            if root_locked and root_fd is not None:
                try:
                    fcntl.flock(root_fd, fcntl.LOCK_UN)
                except OSError as exc:
                    root_cleanup_error = exc
            if root_fd is not None:
                try:
                    os.close(root_fd)
                except OSError as exc:
                    if root_cleanup_error is None:
                        root_cleanup_error = exc
            if parent_locked and parent_lock_fd is not None:
                try:
                    fcntl.flock(parent_lock_fd, fcntl.LOCK_UN)
                except OSError as exc:
                    if root_cleanup_error is None:
                        root_cleanup_error = exc
            if parent_lock_fd is not None:
                try:
                    os.close(parent_lock_fd)
                except OSError as exc:
                    if root_cleanup_error is None:
                        root_cleanup_error = exc
            try:
                os.close(parent_fd)
            except OSError as exc:
                if root_cleanup_error is None:
                    root_cleanup_error = exc
            if root_cleanup_error is not None:
                raise M6DurableCorruptionError(
                    "durable root lock cleanup failed"
                ) from root_cleanup_error

    def _load_reopened_unlocked(self) -> M6DurableReopenV1:
        _require_directory_layout(
            self._io_root(),
            files={HEAD_FILE_V1, LOCK_FILE_V1},
            directories={GENESIS_DIR_V1, BLOCKS_DIR_V1},
            name="durable root",
        )
        head_raw, _ = _read_canonical_json(
            self._io_root() / HEAD_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        head = _object(head_raw, name="HEAD", keys=_head_keys())
        if head["schema"] != DURABLE_SCHEMA_V1:
            raise M6DurableCorruptionError("HEAD schema mismatch")
        subject_root = _root(head["subject_root"], name="HEAD subject root")
        if subject_root != self._subject.subject_root:
            raise M6DurableCorruptionError("HEAD promotion subject mismatch")
        head_block_id = _block_identifier(head["block_id"], name="HEAD block id", allow_genesis=True)
        if head_block_id == GENESIS_BLOCK_ID_V1:
            genesis = self._load_genesis_unlocked()
            loaded_blocks: list[_LoadedBlockV1] = []
        else:
            loaded_blocks = []
            current_id = head_block_id
            seen: set[str] = set()
            while current_id != GENESIS_BLOCK_ID_V1:
                if current_id in seen:
                    raise M6DurableCorruptionError("durable block chain contains a cycle")
                seen.add(current_id)
                if len(seen) > self._subject.durability_profile.max_chain_blocks:
                    raise M6DurableCorruptionError(
                        "durable block chain exceeds the configured block limit"
                    )
                loaded = self._load_block_unlocked(current_id)
                loaded_blocks.append(loaded)
                parent = _block_identifier(
                    loaded.manifest["parent_block_id"],
                    name="commit parent block id",
                    allow_genesis=True,
                )
                current_id = parent
            genesis = self._load_genesis_unlocked()

        chain_newest = loaded_blocks
        chain_oldest = list(reversed(chain_newest))
        previous_state = genesis.state
        previous_block_id = GENESIS_BLOCK_ID_V1
        for loaded in chain_oldest:
            if loaded.manifest["parent_block_id"] != previous_block_id:
                raise M6DurableCorruptionError("durable parent block binding mismatch")
            if loaded.manifest["parent_state_root"] != previous_state.state_root:
                raise M6DurableCorruptionError("durable parent state root mismatch")
            if loaded.manifest["parent_head"] != previous_state.head:
                raise M6DurableCorruptionError("durable parent economic head mismatch")
            if loaded.state.writer_epoch < previous_state.writer_epoch:
                raise M6DurableCorruptionError("durable writer epoch regressed")
            _validate_cross_block_publication(
                previous_state,
                loaded.state,
                loaded.record,
                subject=self._subject,
            )
            previous_state = loaded.state
            previous_block_id = loaded.block_id

        latest_state = previous_state
        expected_head_root = _root(head["head_root"], name="HEAD state root")
        expected_economic_head = _root(head["economic_head"], name="HEAD economic head", allow_zero=True)
        if latest_state.state_root != expected_head_root:
            raise M6DurableCorruptionError("HEAD state root mismatch")
        if latest_state.head != expected_economic_head:
            raise M6DurableCorruptionError("HEAD economic head mismatch")
        if latest_state.writer_epoch != _nonnegative_int(head["writer_epoch"], name="HEAD writer epoch"):
            raise M6DurableCorruptionError("HEAD writer epoch mismatch")

        expected_block_ids = {loaded.block_id for loaded in loaded_blocks}
        actual_block_ids = set()
        for entry in (self._io_root() / BLOCKS_DIR_V1).iterdir():
            if entry.is_symlink() or not entry.is_dir():
                raise M6DurableCorruptionError(f"unexpected block entry: {entry.name}")
            actual_block_ids.add(entry.name)
        if actual_block_ids != expected_block_ids:
            raise M6DurableCorruptionError(
                f"unreachable or missing durable blocks: expected={sorted(expected_block_ids)}, actual={sorted(actual_block_ids)}"
            )
        records = tuple(loaded.record for loaded in chain_oldest)
        chain_ids = (GENESIS_BLOCK_ID_V1,) + tuple(loaded.block_id for loaded in chain_oldest)
        return M6DurableReopenV1(
            subject=self._subject,
            state=latest_state,
            head_block_id=head_block_id,
            chain_block_ids=chain_ids,
            records=records,
        )

    def _load_genesis_unlocked(self) -> _LoadedBlockV1:
        directory = self._io_root() / GENESIS_DIR_V1
        _require_directory_layout(
            directory,
            files={SUBJECT_FILE_V1, STATE_FILE_V1, MANIFEST_FILE_V1},
            directories=set(),
            name="genesis block",
        )
        manifest_raw, _ = _read_canonical_json(
            directory / MANIFEST_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        manifest = _validate_manifest(manifest_raw, kind="genesis", block_id=GENESIS_BLOCK_ID_V1)
        subject_raw, subject_data = _read_canonical_json(
            directory / SUBJECT_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        state_raw, state_data = _read_canonical_json(
            directory / STATE_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        _validate_file_hashes(manifest, {SUBJECT_FILE_V1: subject_data, STATE_FILE_V1: state_data})
        subject = _decode_subject(subject_raw)
        if subject != self._subject:
            raise M6DurableCorruptionError("genesis subject differs from requested subject")
        state = _decode_state(state_raw)
        _require_state_fixed_point(state, state_data)
        _validate_state_commitments_at_reopen(state)
        try:
            validate_economic_state_v1(state)
        except (TypeError, ValueError) as exc:
            raise M6DurableCorruptionError(f"durable economic state invalid: {exc}") from exc
        if state.deployment != self._subject.deployment or state.writer_epoch != self._subject.writer_epoch:
            raise M6DurableCorruptionError("genesis authority binding mismatch")
        if state.state_root != manifest["post_state_root"] or state.state_root != manifest["pre_state_root"]:
            raise M6DurableCorruptionError("genesis state root mismatch")
        if state.head != ZERO_ROOT_V1:
            raise M6DurableCorruptionError("genesis economic head must be zero")
        if manifest["subject_root"] != subject.subject_root:
            raise M6DurableCorruptionError("genesis subject root mismatch")
        if _file_digest(subject_data) != _file_digest(_canonical_data(subject)):
            raise M6DurableCorruptionError("genesis subject canonical fixed point mismatch")
        return _LoadedBlockV1(
            block_id=GENESIS_BLOCK_ID_V1,
            manifest=manifest,
            state=state,
            record=_genesis_record(subject, state),
        )

    def _load_block_unlocked(self, block_id: str) -> _LoadedBlockV1:
        block_id = _block_identifier(block_id, name="commit block id", allow_genesis=False)
        directory = self._io_root() / BLOCKS_DIR_V1 / block_id
        if directory.is_symlink() or not directory.is_dir():
            raise M6DurableCorruptionError(f"missing durable block directory: {block_id}")
        _require_directory_layout(
            directory,
            files={SUBJECT_FILE_V1, STATE_FILE_V1, RECORD_FILE_V1, MANIFEST_FILE_V1},
            directories=set(),
            name=f"commit block {block_id}",
        )
        manifest_raw, _ = _read_canonical_json(
            directory / MANIFEST_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        manifest = _validate_manifest(manifest_raw, kind="commit", block_id=block_id)
        subject_raw, subject_data = _read_canonical_json(
            directory / SUBJECT_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        state_raw, state_data = _read_canonical_json(
            directory / STATE_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        record_raw, record_data = _read_canonical_json(
            directory / RECORD_FILE_V1,
            max_bytes=self._subject.durability_profile.max_json_bytes,
        )
        _validate_file_hashes(
            manifest,
            {SUBJECT_FILE_V1: subject_data, STATE_FILE_V1: state_data, RECORD_FILE_V1: record_data},
        )
        subject = _decode_subject(subject_raw)
        if subject != self._subject or manifest["subject_root"] != subject.subject_root:
            raise M6DurableCorruptionError("commit subject binding mismatch")
        state = _decode_state(state_raw)
        record = _decode_record(record_raw)
        _require_state_fixed_point(state, state_data)
        _require_record_fixed_point(record, record_data)
        _validate_state_commitments_at_reopen(state)
        try:
            validate_economic_state_v1(state)
        except (TypeError, ValueError) as exc:
            raise M6DurableCorruptionError(f"durable economic state invalid: {exc}") from exc
        if state.deployment != self._subject.deployment:
            raise M6DurableCorruptionError("commit deployment binding mismatch")
        if manifest["candidate_id"] != record.candidate_id or manifest["record_root"] != record.receipt_root:
            raise M6DurableCorruptionError("commit record binding mismatch")
        if manifest["pre_state_root"] != record.pre_state_root or manifest["post_state_root"] != record.post_state_root:
            raise M6DurableCorruptionError("commit state endpoint mismatch")
        if manifest["parent_state_root"] != record.pre_state_root:
            raise M6DurableCorruptionError("commit parent/pre-state binding mismatch")
        if state.state_root != record.post_state_root or state.state_root != manifest["post_state_root"]:
            raise M6DurableCorruptionError("commit post-state root mismatch")
        if state.writer_epoch != manifest["writer_epoch"]:
            raise M6DurableCorruptionError("commit writer epoch mismatch")
        if record.parent_head != manifest["parent_head"]:
            raise M6DurableCorruptionError("commit parent head mismatch")
        if record.publication_root != manifest["publication_root"]:
            raise M6DurableCorruptionError("commit publication root mismatch")
        if (
            record.outbox_root != state.outbox_root
            or record.history_root != state.history_root
            or record.nullifier_root != state.nullifier_root
        ):
            raise M6DurableCorruptionError("commit archive root mismatch")
        if record.finality_receipt is None:
            raise M6DurableCorruptionError("commit finality verification receipt is missing")
        if (
            record.finality_receipt.subject_root != subject.subject_root
            or record.finality_receipt.candidate_parent_head != record.parent_head
            or record.finality_receipt.candidate_head != record.post_state_root
            or record.finality_receipt.publication_root != record.publication_root
            or record.finality_receipt.writer_epoch != record.finality.writer_epoch
            or record.finality_receipt.certificate_root != record.finality.certificate_root
        ):
            raise M6DurableCorruptionError("commit finality verification receipt binding mismatch")
        try:
            expected_nonce_root = _record_nonce_root(record)
            verify_finality_certificate_v1(
                self._subject,
                candidate_head=record.post_state_root,
                publication_root=record.publication_root,
                current_writer_epoch=state.writer_epoch,
                candidate_parent_head=record.parent_head,
                expected_command_root=record.command_root,
                expected_nonce_root=expected_nonce_root,
                expected_execution_receipt_root=(
                    None if record.zrpf_receipt is None else record.zrpf_receipt.receipt_root
                ),
                certificate=record.finality,
                tau_certificate=record.tau_certificate,
            )
        except ValueError as exc:
            raise M6DurableCorruptionError(f"durable finality binding failed: {exc}") from exc
        expected_id = _block_id(
            self._subject,
            parent_block_id=str(manifest["parent_block_id"]),
            parent_state_root=str(manifest["parent_state_root"]),
            parent_head=str(manifest["parent_head"]),
            record=record,
        )
        if expected_id != block_id:
            raise M6DurableCorruptionError("durable block id mismatch")
        return _LoadedBlockV1(block_id=block_id, manifest=manifest, state=state, record=record)

    @staticmethod
    def _existing_record(reopened: M6DurableReopenV1, candidate_id: str) -> M6PublishedRecordV1 | None:
        for record in reopened.records:
            if record.candidate_id == candidate_id:
                return record
        return None

    @staticmethod
    def _block_for_record(reopened: M6DurableReopenV1, record: M6PublishedRecordV1) -> str:
        for block_id in reopened.chain_block_ids[1:]:
            if _record_candidate_id(reopened, block_id) == record.candidate_id:
                return block_id
        raise M6DurableCorruptionError("durable record has no block")


def _validate_cross_block_publication(
    previous_state: M6ApplicationStateV1,
    state: M6ApplicationStateV1,
    record: M6PublishedRecordV1,
    *,
    subject: M6PromotionSubjectV1 | None = None,
) -> None:
    """Bind each receipt's parallel archives to one parent-to-child append."""

    try:
        validate_economic_state_v1(previous_state)
        validate_economic_state_v1(state)
    except ValueError as exc:
        raise M6DurableCorruptionError(f"durable economic state mismatch: {exc}") from exc
    if record.pre_state_root != previous_state.state_root:
        raise M6DurableCorruptionError("durable record pre-state root mismatch")
    if record.post_state_root != state.state_root:
        raise M6DurableCorruptionError("durable record post-state root mismatch")
    if record.finality_receipt is None:
        raise M6DurableCorruptionError("durable finality verification receipt is missing")
    if subject is not None and record.finality_receipt.subject_root != subject.subject_root:
        raise M6DurableCorruptionError("durable finality verification receipt subject mismatch")
    if (
        record.finality_receipt.candidate_parent_head != record.parent_head
        or record.finality_receipt.candidate_head != record.post_state_root
        or record.finality_receipt.publication_root != record.publication_root
        or record.finality_receipt.writer_epoch != record.finality.writer_epoch
        or record.finality_receipt.certificate_root != record.finality.certificate_root
    ):
        raise M6DurableCorruptionError("durable finality verification receipt binding mismatch")
    if state.history[: len(previous_state.history)] != previous_state.history:
        raise M6DurableCorruptionError("durable history prefix mismatch")
    history_suffix = state.history[len(previous_state.history) :]
    if not history_suffix:
        raise M6DurableCorruptionError("durable history receipt suffix is empty")
    if tuple(atom.sequence for atom in history_suffix) != tuple(
        range(len(previous_state.history), len(state.history))
    ):
        raise M6DurableCorruptionError("durable history sequence suffix mismatch")
    if state.nullifiers[: len(previous_state.nullifiers)] != previous_state.nullifiers:
        raise M6DurableCorruptionError("durable nullifier prefix mismatch")
    nullifier_suffix = state.nullifiers[len(previous_state.nullifiers) :]
    if tuple(atom.nullifier for atom in history_suffix) != nullifier_suffix:
        raise M6DurableCorruptionError("durable history/nullifier binding mismatch")
    if record.nullifier_root != state.nullifier_root:
        raise M6DurableCorruptionError("durable nullifier receipt mismatch")
    if record.history_root != state.history_root:
        raise M6DurableCorruptionError("durable history receipt mismatch")
    expected_command_root = ordered_root_v1(
        "m6-direct-command-root-v1",
        tuple(atom.command_hash for atom in history_suffix),
    )
    if record.command_root != expected_command_root:
        raise M6DurableCorruptionError("durable command receipt mismatch")
    expected_nonce_root = ordered_root_v1(
        "m6-direct-nonce-root-v1",
        tuple(f"{atom.sender}:{atom.nonce}" for atom in history_suffix),
    )
    if record.tau_certificate is not None:
        tau_nonce_root = ordered_root_v1(
            "m6-direct-nonce-root-v1",
            record.tau_certificate.ordered_nonce_identities,
        )
        if tau_nonce_root != expected_nonce_root:
            raise M6DurableCorruptionError("durable Tau nonce identity binding mismatch")
    expected_value_delta_root = (
        history_suffix[0].value_delta_root
        if len(history_suffix) == 1
        else ordered_root_v1(
            "m6-direct-value-delta-root-v1",
            tuple(atom.value_delta_root for atom in history_suffix),
        )
    )
    if record.value_delta_root != expected_value_delta_root:
        raise M6DurableCorruptionError("durable value-delta receipt mismatch")
    if len(history_suffix) == 1:
        atom = history_suffix[0]
        if record.business_status is not atom.outcome:
            raise M6DurableCorruptionError("durable business status receipt mismatch")
        if record.business_reject_reason is not atom.business_reject_reason:
            raise M6DurableCorruptionError("durable business reject reason receipt mismatch")
        replay = record.direct_replay
        if replay is None:
            raise M6DurableCorruptionError("durable direct execution body is missing")
        if replay.command_hash != atom.command_hash:
            raise M6DurableCorruptionError("durable direct command body binding mismatch")
        if replay.context_parent_head != previous_state.head:
            raise M6DurableCorruptionError("durable direct context parent binding mismatch")
        if replay.context_sender != atom.sender or replay.context_nonce != atom.nonce:
            raise M6DurableCorruptionError("durable direct context nonce binding mismatch")
        if replay.context_deployment != state.deployment:
            raise M6DurableCorruptionError("durable direct context deployment binding mismatch")
        if subject is not None and replay.context_chain_id != subject.chain_id:
            raise M6DurableCorruptionError("durable direct context chain identity mismatch")
        expected_publication = PublicationAtomV1(
            candidate_id=record.candidate_id,
            pre_state_root=record.pre_state_root,
            post_state_root=record.post_state_root,
            history_root=record.history_root,
            nullifier_root=record.nullifier_root,
            value_delta_root=record.value_delta_root,
            outbox_root=record.outbox_root,
            execution_context_root=replay.context_root,
            writer_epoch=state.writer_epoch,
            business_status=record.business_status,
            business_reject_reason=record.business_reject_reason,
        )
        if expected_publication.publication_root != record.publication_root:
            raise M6DurableCorruptionError(
                "durable direct execution context root is not bound to publication"
            )
    elif record.business_status is not None or record.business_reject_reason is not None:
        raise M6DurableCorruptionError("durable batch business decision projection is not canonical")
    if len(history_suffix) > 1:
        if record.direct_batch_replay is not None:
            replays = record.direct_batch_replay
            if len(replays) != len(history_suffix):
                raise M6DurableCorruptionError("durable direct batch replay count mismatch")
            if record.direct_batch_data_availability_root is None:
                raise M6DurableCorruptionError("durable direct batch data-availability root is missing")
            try:
                expected_data_availability_root = direct_batch_data_availability_root_v1(replays)
            except (TypeError, ValueError, RecursionError) as exc:
                raise M6DurableCorruptionError(
                    f"durable direct batch data-availability bodies are invalid: {exc}"
                ) from exc
            if record.direct_batch_data_availability_root != expected_data_availability_root:
                raise M6DurableCorruptionError(
                    "durable direct batch data-availability root mismatch"
                )
            for index, (replay, atom) in enumerate(zip(replays, history_suffix, strict=True)):
                expected_parent_head = previous_state.head if index == 0 else history_suffix[index - 1].post_state_root
                if (
                    replay.command_hash != atom.command_hash
                    or replay.context_parent_head != expected_parent_head
                    or replay.context_sender != atom.sender
                    or replay.context_nonce != atom.nonce
                    or replay.context_deployment != state.deployment
                    or (subject is not None and replay.context_chain_id != subject.chain_id)
                ):
                    raise M6DurableCorruptionError("durable direct batch replay binding mismatch")
            expected_publication = direct_batch_publication_root_v1(
                pre_head=record.parent_head,
                pre_state_root=record.pre_state_root,
                post_state_root=record.post_state_root,
                candidate_id=record.candidate_id,
                command_root=record.command_root,
                nonce_root=expected_nonce_root,
                value_delta_root=record.value_delta_root,
                history_root=record.history_root,
                nullifier_root=record.nullifier_root,
                outbox_root=record.outbox_root,
                data_availability_root=record.direct_batch_data_availability_root,
            )
            if record.publication_root != expected_publication:
                raise M6DurableCorruptionError("durable direct batch publication binding mismatch")
        elif record.zrpf_journal is not None:
            journal = record.zrpf_journal
            receipt = record.zrpf_receipt
            if receipt is None:
                raise M6DurableCorruptionError("durable ZRPF verification receipt is missing")
            if subject is not None:
                if journal.promotion_subject_root != subject.subject_root:
                    raise M6DurableCorruptionError("durable ZRPF journal subject binding mismatch")
                if journal.verifier_image != subject.risc0_image:
                    raise M6DurableCorruptionError("durable ZRPF journal verifier image binding mismatch")
                if receipt.promotion_subject_root != subject.subject_root:
                    raise M6DurableCorruptionError("durable ZRPF receipt subject binding mismatch")
                if receipt.verifier_image != subject.risc0_image:
                    raise M6DurableCorruptionError("durable ZRPF receipt verifier image binding mismatch")
            if (
                journal.journal_root != record.publication_root
                or journal.command_count != len(history_suffix)
                or journal.writer_epoch != state.writer_epoch
                or journal.writer_epoch != record.finality.writer_epoch
                or journal.pre_state_root != record.pre_state_root
                or journal.post_state_root != record.post_state_root
                or journal.command_root != record.command_root
                or journal.nonce_root != expected_nonce_root
                or journal.value_delta_root != record.value_delta_root
                or journal.history_root != record.history_root
                or journal.nullifier_root != record.nullifier_root
                or journal.outbox_root != record.outbox_root
            ):
                raise M6DurableCorruptionError("durable ZRPF journal publication binding mismatch")
            if (
                receipt.profile != journal.profile
                or receipt.verifier_image != journal.verifier_image
                or receipt.journal_root != journal.journal_root
                or receipt.data_availability_root != journal.data_availability_root
            ):
                raise M6DurableCorruptionError("durable ZRPF verification receipt binding mismatch")
        else:
            raise M6DurableCorruptionError("durable multi-command execution proof is missing")
    elif record.zrpf_journal is not None:
        raise M6DurableCorruptionError("durable single-command publication cannot carry a ZRPF journal")
    elif record.zrpf_receipt is not None:
        raise M6DurableCorruptionError("durable single-command publication cannot carry a ZRPF receipt")
    if record.finality.candidate_head != record.post_state_root:
        raise M6DurableCorruptionError("durable finality candidate-head binding mismatch")
    if record.finality.publication_root != record.publication_root:
        raise M6DurableCorruptionError("durable finality publication binding mismatch")
    if state.outbox[: len(previous_state.outbox)] != previous_state.outbox:
        raise M6DurableCorruptionError("durable outbox prefix mismatch")
    if state.outbox[len(previous_state.outbox) :] != record.outbox_atoms:
        raise M6DurableCorruptionError("durable outbox receipt suffix mismatch")
    if state.finality_certificates[: len(previous_state.finality_certificates)] != previous_state.finality_certificates:
        raise M6DurableCorruptionError("durable finality archive prefix mismatch")
    if state.finality_certificates[len(previous_state.finality_certificates) :] != (record.finality,):
        raise M6DurableCorruptionError("durable finality receipt suffix mismatch")


def _validate_manifest(raw: object, *, kind: str, block_id: str) -> dict[str, object]:
    manifest = _object(raw, name=f"{kind} manifest", keys=_manifest_keys())
    if manifest["schema"] != DURABLE_SCHEMA_V1 or manifest["kind"] != kind or manifest["block_id"] != block_id:
        raise M6DurableCorruptionError(f"{kind} manifest identity mismatch")
    _block_identifier(manifest["block_id"], name=f"{kind} block id", allow_genesis=kind == "genesis")
    _root(manifest["subject_root"], name="manifest subject root")
    _root(manifest["parent_state_root"], name="manifest parent state root", allow_zero=True) if kind == "commit" else None
    _root(manifest["parent_head"], name="manifest parent head", allow_zero=True)
    _root(manifest["pre_state_root"], name="manifest pre-state root")
    _root(manifest["post_state_root"], name="manifest post-state root")
    _root(manifest["publication_root"], name="manifest publication root", allow_zero=kind == "genesis")
    _root(manifest["record_root"], name="manifest record root", allow_zero=kind == "genesis")
    _nonnegative_int(manifest["writer_epoch"], name="manifest writer epoch")
    files = manifest["files"]
    if not isinstance(files, dict):
        raise M6DurableCorruptionError("manifest files must be an object")
    expected_files = {SUBJECT_FILE_V1, STATE_FILE_V1} | ({RECORD_FILE_V1} if kind == "commit" else set())
    if set(files) != expected_files:
        raise M6DurableCorruptionError("manifest file set mismatch")
    for name, digest in files.items():
        _root(digest, name=f"manifest file digest {name}")
    if kind == "genesis":
        if manifest["parent_block_id"] is not None or manifest["parent_state_root"] is not None or manifest["candidate_id"] is not None:
            raise M6DurableCorruptionError("genesis parent/candidate fields must be null")
    else:
        _block_identifier(manifest["parent_block_id"], name="manifest parent block id", allow_genesis=True)
        _root(manifest["candidate_id"], name="manifest candidate id")
    return manifest


def _validate_file_hashes(manifest: Mapping[str, object], files: Mapping[str, bytes]) -> None:
    expected = manifest["files"]
    if not isinstance(expected, dict):
        raise M6DurableCorruptionError("manifest file hashes are not an object")
    for name, data in files.items():
        if expected.get(name) != _file_digest(data):
            raise M6DurableCorruptionError(f"durable file digest mismatch: {name}")


def _require_state_fixed_point(state: M6ApplicationStateV1, data: bytes) -> None:
    if _canonical_data(state) != data:
        raise M6DurableCorruptionError("state canonical encode/reopen fixed point failed")


def _validate_state_commitments_at_reopen(state: M6ApplicationStateV1) -> None:
    try:
        validate_state_commitments_v1(state)
    except (TypeError, ValueError) as exc:
        raise M6DurableCorruptionError(f"durable state commitment invalid: {exc}") from exc


def _require_record_fixed_point(record: M6PublishedRecordV1, data: bytes) -> None:
    if _canonical_data(record) != data:
        raise M6DurableCorruptionError("record canonical encode/reopen fixed point failed")


def _genesis_record(subject: M6PromotionSubjectV1, state: M6ApplicationStateV1) -> M6PublishedRecordV1:
    from src.core.m6_safe_mount_types_v1 import ZenoLedgerFinalityCertificateV1

    return M6PublishedRecordV1(
        candidate_id=hash_v1("m6-genesis-record-v1", {"subject_root": subject.subject_root, "state_root": state.state_root}),
        parent_head=ZERO_ROOT_V1,
        pre_state_root=state.state_root,
        post_state_root=state.state_root,
        publication_root=hash_v1("m6-genesis-publication-v1", {"state_root": state.state_root}),
        command_root=hash_v1("m6-genesis-command-v1", {"commands": ()}),
        value_delta_root=hash_v1("m6-genesis-delta-v1", {"entries": ()}),
        history_root=state.history_root,
        nullifier_root=state.nullifier_root,
        outbox_root=state.outbox_root,
        outbox_atoms=(),
        finality=ZenoLedgerFinalityCertificateV1(
            finality_id=hash_v1("m6-genesis-finality-v1", {"state_root": state.state_root}),
            candidate_head=state.state_root,
            publication_root=hash_v1("m6-genesis-publication-v1", {"state_root": state.state_root}),
            chain_id=subject.chain_id,
            validator_set_root=subject.validator_set,
            writer_epoch=subject.writer_epoch,
            signer_ids=("genesis", "genesis-2", "genesis-3", "genesis-4", "genesis-5"),
            quorum=5,
            mode=FinalityModeV1.FALLBACK_FORCED_INCLUSION,
            signature_root=hash_v1("m6-genesis-signature-v1", {"state_root": state.state_root}),
        ),
        tau_certificate=None,
    )


def _candidate_matches_record(candidate: AcceptCandidateV1, record: M6PublishedRecordV1) -> bool:
    return candidate_matches_published_record_v1(candidate, record)


def _zrpf_matches_record(verified_root: VerifiedZRPFRootV1, record: M6PublishedRecordV1) -> bool:
    journal = verified_root.journal
    receipt = record.zrpf_receipt
    proof_receipt = verified_root.proof_receipt
    if record.zrpf_journal != journal or receipt is None or record.direct_replay is not None:
        return False
    return (
        journal.pre_state_root == record.pre_state_root
        and journal.post_state_root == record.post_state_root
        and journal.journal_root == record.publication_root
        and journal.command_root == record.command_root
        and journal.value_delta_root == record.value_delta_root
        and journal.history_root == record.history_root
        and journal.outbox_root == record.outbox_root
        and record.finality.execution_receipt_root == proof_receipt.receipt_root
        and receipt.receipt_root == proof_receipt.receipt_root
        and receipt.promotion_subject_root == proof_receipt.promotion_subject_root
        and receipt.profile == proof_receipt.profile
        and receipt.verifier_image == proof_receipt.verifier_image
        and receipt.journal_root == proof_receipt.journal_root
        and receipt.data_availability_root == proof_receipt.data_availability_root
        and receipt.attestation_root == proof_receipt.attestation_root
    )


def _record_candidate_id(reopened: M6DurableReopenV1, block_id: str) -> str:
    index = reopened.chain_block_ids.index(block_id) - 1
    return reopened.records[index].candidate_id


__all__ = [
    "DURABLE_SCHEMA_V1",
    "M6DurableCorruptionError",
    "M6DurableReopenV1",
    "M6DurableCommitResultV1",
    "M6DurableLedgerStoreV1",
]
