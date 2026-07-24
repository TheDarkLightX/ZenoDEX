"""One-shot Store V3 to unified V7 release-history cutover.

The source and destination must be private regular files on one filesystem.
SQLite's attached-database transaction imports the exact authenticated history,
marks the V3 ``user_version`` retired, and activates the V7 release writer in
one commit.  The imported external watermark is structurally checked and kept
authority-neutral.
"""

from __future__ import annotations

import os
import sqlite3
import stat
from contextlib import closing
from pathlib import Path
from typing import Final

from src.integration import _zrpf_spot_v7_release_state_engine_v7 as engine_v7
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3

DEFAULT_CUTOVER_BUSY_TIMEOUT_MS_V1: Final = 15_000
MAX_CUTOVER_BUSY_TIMEOUT_MS_V1: Final = 60_000


class SpotV7ReleaseStoreCutoverRejectV1(RuntimeError):
    """Stable fail-closed cutover error."""

    def __init__(
        self,
        code: str,
        detail: str,
        *,
        cutover_committed: bool = False,
        cutover_outcome_known: bool = True,
        durability_sync_complete: bool = False,
    ) -> None:
        self.code = code
        self.detail = detail
        self.cutover_committed = cutover_committed
        self.cutover_outcome_known = cutover_outcome_known
        self.durability_sync_complete = durability_sync_complete
        super().__init__(f"{code}: {detail}")


def cutover_spot_v7_release_store_v1(
    source_store: store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
    *,
    destination_path: Path,
    exact_watermark_bytes: bytes,
    busy_timeout_ms: int = DEFAULT_CUTOVER_BUSY_TIMEOUT_MS_V1,
) -> engine_v7._AuthorityNeutralSpotV7ReleaseCutoverV7:
    """Atomically import, retire, and activate one release-event writer."""

    if type(source_store) is not store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3:
        raise TypeError("release cutover requires the exact Store V3 type")
    if type(exact_watermark_bytes) is not bytes:
        raise TypeError("release cutover watermark must be exact bytes")
    timeout = _require_timeout(busy_timeout_ms)
    source_path = source_store.path
    source_descriptor = _open_stable_private_file(source_path, name="source Store V3")
    try:
        destination = _validate_new_destination(destination_path)
    except Exception:
        os.close(source_descriptor)
        raise
    if source_path == destination:
        os.close(source_descriptor)
        raise _reject("PATH_ALIAS", "source and destination paths must differ")
    try:
        same_filesystem = os.fstat(source_descriptor).st_dev == destination.parent.stat().st_dev
    except OSError:
        os.close(source_descriptor)
        raise
    if not same_filesystem:
        os.close(source_descriptor)
        raise _reject(
            "FILESYSTEM_MISMATCH",
            "source and destination must share one filesystem for atomic cutover",
        )
    try:
        _require_path_matches_descriptor(source_path, source_descriptor, name="source Store V3")
        source_store.read_cursor()
    except store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3 as exc:
        os.close(source_descriptor)
        raise _reject("SOURCE_REPLAY_REJECTED", str(exc)) from exc
    except Exception:
        os.close(source_descriptor)
        raise
    try:
        _require_path_matches_descriptor(
            source_path,
            source_descriptor,
            name="source Store V3",
        )
        created = _create_private_database_file(destination)
    except Exception:
        os.close(source_descriptor)
        raise
    connection: sqlite3.Connection | None = None
    preserve_destination_on_exit = False
    try:
        connection = sqlite3.connect(
            destination,
            timeout=timeout / 1_000,
            isolation_level=None,
        )
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("PRAGMA trusted_schema = OFF")
        connection.execute("PRAGMA journal_mode = DELETE")
        connection.execute("PRAGMA synchronous = EXTRA")
        connection.execute(f"PRAGMA busy_timeout = {timeout}")
        connection.execute(
            "ATTACH DATABASE ? AS source_v3",
            (f"/proc/self/fd/{source_descriptor}",),
        )
        _require_attached_source_matches_descriptor(connection, source_descriptor)
        _require_delete_journal(connection, "main")
        _require_delete_journal(connection, "source_v3")
        connection.execute("BEGIN IMMEDIATE")
        # This no-op write ensures the source participates as a write database
        # before any bytes are copied into the destination.
        updated = connection.execute(
            """
            UPDATE source_v3.spot_v7_authenticated_release_state_meta_v3
            SET singleton = singleton
            WHERE singleton = 1
            """
        )
        if updated.rowcount != 1:
            raise _reject("SOURCE_WRITE_LOCK", "source Store V3 row is absent")
        result = engine_v7._cutover_attached_v3_history_locked_v7(
            connection,
            source_alias="source_v3",
            identity=source_store.identity,
            exact_watermark_bytes=exact_watermark_bytes,
        )
        _require_path_matches_descriptor(source_path, source_descriptor, name="source Store V3")
        connection.execute("PRAGMA main.user_version = 7")
        try:
            _commit_cutover_transaction(connection)
        except (OSError, sqlite3.Error) as exc:
            if connection.in_transaction:
                raise
            committed = _committed_cutover_visible_on_connection(connection)
            if committed is True:
                raise _reject(
                    "CUTOVER_COMMITTED_SYNC_UNCERTAIN",
                    f"commit completed before an error was reported: {exc}",
                    cutover_committed=True,
                    durability_sync_complete=False,
                ) from exc
            preserve_destination_on_exit = True
            raise _reject(
                "CUTOVER_COMMIT_OUTCOME_UNCERTAIN",
                f"commit ended without a conclusive committed-state probe: {exc}",
                cutover_outcome_known=False,
                durability_sync_complete=False,
            ) from exc
        try:
            _require_path_matches_descriptor(
                source_path,
                source_descriptor,
                name="source Store V3",
            )
        except SpotV7ReleaseStoreCutoverRejectV1 as exc:
            raise _reject(
                "CUTOVER_COMMITTED_SOURCE_IDENTITY_CHANGED",
                exc.detail,
                cutover_committed=True,
                durability_sync_complete=False,
            ) from exc
        try:
            os.fsync(source_descriptor)
            _fsync_file(destination)
            _fsync_directory(destination.parent)
            if source_path.parent != destination.parent:
                _fsync_directory(source_path.parent)
        except OSError as exc:
            raise _reject(
                "CUTOVER_COMMITTED_SYNC_UNCERTAIN",
                str(exc),
                cutover_committed=True,
                durability_sync_complete=False,
            ) from exc
        return result
    except engine_v7.SpotV7ReleaseStateEngineRejectV7 as exc:
        if connection is not None and connection.in_transaction:
            connection.rollback()
        raise _reject(exc.code, exc.detail) from exc
    except (OSError, sqlite3.Error, TypeError, ValueError) as exc:
        if connection is not None and connection.in_transaction:
            connection.rollback()
        raise _reject("CUTOVER_FAILED", str(exc)) from exc
    finally:
        if connection is not None:
            try:
                if connection.in_transaction:
                    connection.rollback()
                connection.execute("DETACH DATABASE source_v3")
            except sqlite3.Error:
                pass
            connection.close()
        os.close(source_descriptor)
        if (
            created
            and not preserve_destination_on_exit
            and not _cutover_committed(destination)
        ):
            destination.unlink(missing_ok=True)


def open_unified_release_store_v7_for_maintenance_v1(
    path: Path,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    busy_timeout_ms: int = DEFAULT_CUTOVER_BUSY_TIMEOUT_MS_V1,
) -> sqlite3.Connection:
    """Open and fully replay one V7 release store for scoped maintenance/tests."""

    timeout = _require_timeout(busy_timeout_ms)
    _validate_existing_private_file(path, name="V7 release store")
    connection = sqlite3.connect(
        path,
        timeout=timeout / 1_000,
        isolation_level=None,
    )
    connection.row_factory = sqlite3.Row
    try:
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("PRAGMA trusted_schema = OFF")
        connection.execute(f"PRAGMA busy_timeout = {timeout}")
        connection.execute("BEGIN IMMEDIATE")
        engine_v7._validate_complete_release_history_locked_v7(
            connection,
            identity=identity,
        )
        connection.rollback()
        return connection
    except (sqlite3.Error, TypeError, ValueError):
        if connection.in_transaction:
            connection.rollback()
        connection.close()
        raise


def _cutover_committed(path: Path) -> bool:
    if not path.exists():
        return False
    try:
        with closing(sqlite3.connect(path)) as connection:
            row = connection.execute(
                "SELECT old_store_retired, new_release_writer_active "
                "FROM main.spot_v7_release_cutover_v7 WHERE singleton = 1"
            ).fetchone()
            return row is not None and tuple(row) == (1, 1)
    except sqlite3.Error:
        return False


def _commit_cutover_transaction(connection: sqlite3.Connection) -> None:
    """Commit seam retained for deterministic outcome-boundary fault injection."""

    connection.commit()


def _committed_cutover_visible_on_connection(
    connection: sqlite3.Connection,
) -> bool | None:
    """Classify an ended transaction without converting uncertainty to rollback."""

    try:
        cutover = connection.execute(
            "SELECT old_store_retired, new_release_writer_active "
            "FROM main.spot_v7_release_cutover_v7 WHERE singleton = 1"
        ).fetchone()
        source_version = connection.execute("PRAGMA source_v3.user_version").fetchone()
    except sqlite3.Error:
        return None
    if cutover is None or source_version is None:
        return False
    return tuple(cutover) == (1, 1) and int(source_version[0]) == 307


def _validate_new_destination(path: Path) -> Path:
    if not isinstance(path, Path):
        raise TypeError("destination_path must be a Path")
    if not path.is_absolute() or path != path.resolve(strict=False):
        raise _reject("DESTINATION_PATH", "destination path must be canonical and absolute")
    if path.exists() or path.is_symlink():
        raise _reject("DESTINATION_EXISTS", "destination must not already exist")
    parent = path.parent
    if not parent.is_dir() or parent.is_symlink():
        raise _reject("DESTINATION_PARENT", "destination parent must be a real directory")
    parent_stat = parent.stat()
    if parent_stat.st_uid != os.getuid() or stat.S_IMODE(parent_stat.st_mode) != 0o700:
        raise _reject("DESTINATION_PARENT_MODE", "destination parent must be owned mode 0700")
    return path


def _validate_existing_private_file(path: Path, *, name: str) -> None:
    if not isinstance(path, Path) or not path.is_absolute() or path != path.resolve(strict=True):
        raise _reject("STORE_PATH", f"{name} path must be canonical and absolute")
    value = path.lstat()
    if not stat.S_ISREG(value.st_mode) or value.st_nlink != 1:
        raise _reject("STORE_FILE_TYPE", f"{name} must be one regular file with one link")
    if value.st_uid != os.getuid() or stat.S_IMODE(value.st_mode) != 0o600:
        raise _reject("STORE_FILE_MODE", f"{name} must be owned mode 0600")
    parent = path.parent.stat()
    if parent.st_uid != os.getuid() or stat.S_IMODE(parent.st_mode) != 0o700:
        raise _reject("STORE_PARENT_MODE", f"{name} parent must be owned mode 0700")


def _open_stable_private_file(path: Path, *, name: str) -> int:
    """Open and retain the exact inode used by SQLite ATTACH."""

    _validate_existing_private_file(path, name=name)
    try:
        descriptor = os.open(path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError as exc:
        raise _reject("STORE_OPEN", f"{name} could not be opened safely") from exc
    try:
        _require_private_descriptor(descriptor, name=name)
        _require_path_matches_descriptor(path, descriptor, name=name)
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def _require_private_descriptor(descriptor: int, *, name: str) -> None:
    value = os.fstat(descriptor)
    if not stat.S_ISREG(value.st_mode) or value.st_nlink != 1:
        raise _reject("STORE_FILE_TYPE", f"{name} must be one regular file with one link")
    if value.st_uid != os.getuid() or stat.S_IMODE(value.st_mode) != 0o600:
        raise _reject("STORE_FILE_MODE", f"{name} must be owned mode 0600")


def _require_path_matches_descriptor(path: Path, descriptor: int, *, name: str) -> None:
    """Reject persistent source-path substitution around the locked cutover."""

    _require_private_descriptor(descriptor, name=name)
    try:
        observed = path.lstat()
    except OSError as exc:
        raise _reject("STORE_INODE_CHANGED", f"{name} path disappeared") from exc
    expected = os.fstat(descriptor)
    if not stat.S_ISREG(observed.st_mode) or (
        observed.st_dev,
        observed.st_ino,
    ) != (expected.st_dev, expected.st_ino):
        raise _reject("STORE_INODE_CHANGED", f"{name} path changed inode")


def _require_attached_source_matches_descriptor(
    connection: sqlite3.Connection,
    descriptor: int,
) -> None:
    rows = connection.execute("PRAGMA database_list").fetchall()
    attached = [str(row[2]) for row in rows if str(row[1]) == "source_v3"]
    if len(attached) != 1:
        raise _reject("SOURCE_ATTACHMENT", "source_v3 attachment is absent or ambiguous")
    try:
        observed = os.stat(attached[0])
    except OSError as exc:
        raise _reject("SOURCE_ATTACHMENT", "source_v3 attachment cannot be inspected") from exc
    expected = os.fstat(descriptor)
    if (observed.st_dev, observed.st_ino) != (expected.st_dev, expected.st_ino):
        raise _reject("SOURCE_ATTACHMENT", "source_v3 differs from the pinned source inode")


def _create_private_database_file(path: Path) -> bool:
    descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR | os.O_CLOEXEC, 0o600)
    try:
        os.fchmod(descriptor, 0o600)
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    return True


def _require_delete_journal(connection: sqlite3.Connection, alias: str) -> None:
    mode = str(connection.execute(f"PRAGMA {alias}.journal_mode").fetchone()[0]).lower()
    if mode != "delete":
        raise _reject("JOURNAL_MODE", f"{alias} must use DELETE journal mode")


def _fsync_file(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _require_timeout(value: object) -> int:
    if type(value) is not int or not 1 <= value <= MAX_CUTOVER_BUSY_TIMEOUT_MS_V1:
        raise ValueError("busy_timeout_ms must be a positive bounded integer")
    return value


def _reject(
    code: str,
    detail: str,
    *,
    cutover_committed: bool = False,
    cutover_outcome_known: bool = True,
    durability_sync_complete: bool = False,
) -> SpotV7ReleaseStoreCutoverRejectV1:
    return SpotV7ReleaseStoreCutoverRejectV1(
        code,
        detail,
        cutover_committed=cutover_committed,
        cutover_outcome_known=cutover_outcome_known,
        durability_sync_complete=durability_sync_complete,
    )


__all__ = [
    "DEFAULT_CUTOVER_BUSY_TIMEOUT_MS_V1",
    "SpotV7ReleaseStoreCutoverRejectV1",
    "cutover_spot_v7_release_store_v1",
    "open_unified_release_store_v7_for_maintenance_v1",
]
