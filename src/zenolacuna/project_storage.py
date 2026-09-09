"""Atomic local publication of signed events and immutable source snapshots.

SQLite owns crash atomicity. No cached workflow state or verdict is stored.
The host must protect this cooperative filesystem and its external owner pin.
"""

import base64
import hashlib
import os
import sqlite3
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

from .codec import _array, _object, _parse, _string, encode
from .filesystem import _checked_directory, _read_regular
from .model import LacunaError, Scope
from .project_types import sha_field

MAX_EVENTS = 64
MAX_BLOBS = 256
MAX_BYTES = 32 * 1024 * 1024
MAX_SOURCE = 512 * 1024
SCHEMA = "zenolacuna/project-bundle/v1"

# Only these two owned tables may participate in persistence.
_CREATE = (
    "CREATE TABLE events (position INTEGER PRIMARY KEY, signed BLOB NOT NULL, evidence BLOB)",
    "CREATE TABLE sources (sha256 TEXT PRIMARY KEY, content BLOB NOT NULL)",
)


@contextmanager
def database(path: Path, *, create: bool = False) -> Iterator[sqlite3.Connection]:
    _checked_directory(path.parent, "PROJECT_MISSING")
    if not path.exists():
        if not create:
            raise LacunaError("PROJECT_MISSING")
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0), 0o600)
        os.close(descriptor)
    _read_regular(path, "PROJECT_MISSING", MAX_BYTES * 3)
    connection = None
    try:
        connection = sqlite3.connect(str(path), timeout=0, isolation_level=None)
        connection.execute("PRAGMA trusted_schema=OFF")
        connection.execute("PRAGMA foreign_keys=ON")
        connection.execute("PRAGMA synchronous=FULL")
        if connection.execute("PRAGMA journal_mode=DELETE").fetchone() != ("delete",):
            raise LacunaError("UNSUPPORTED_PERSISTENCE")
        connection.execute("BEGIN IMMEDIATE")
        existing = connection.execute("SELECT name, type, sql FROM sqlite_master ORDER BY name").fetchall()
        if not existing and create:
            for statement in _CREATE:
                connection.execute(statement)
            connection.execute("PRAGMA user_version=1")
            existing = connection.execute("SELECT name, type, sql FROM sqlite_master ORDER BY name").fetchall()
        expected = [("events", "table", _CREATE[0]), ("sources", "table", _CREATE[1]),
                    ("sqlite_autoindex_sources_1", "index", None)]
        if existing != expected or connection.execute("PRAGMA user_version").fetchone() != (1,):
            raise LacunaError("CORRUPT_PROJECT")
        yield connection
    except sqlite3.OperationalError as exc:
        code = "PROJECT_BUSY" if "locked" in str(exc) else "PROJECT_IO_ERROR"
        raise LacunaError(code) from exc
    except sqlite3.DatabaseError as exc:
        raise LacunaError("CORRUPT_PROJECT") from exc
    finally:
        if connection is not None:
            if connection.in_transaction:
                connection.rollback()
            connection.close()


def read_events(db: sqlite3.Connection) -> tuple[tuple[bytes, bytes | None], ...]:
    count, cost = db.execute("SELECT count(*), coalesce(sum(length(signed) + coalesce(length(evidence),0)),0) FROM events").fetchone()
    if type(count) is not int or count > MAX_EVENTS or type(cost) is not int or cost > MAX_BYTES:
        raise LacunaError("PROJECT_BUDGET_EXCEEDED")
    rows = db.execute("SELECT position, signed, evidence FROM events ORDER BY position").fetchall()
    events = []
    for index, (position, signed, evidence) in enumerate(rows):
        if position != index or type(signed) is not bytes or (evidence is not None and type(evidence) is not bytes):
            raise LacunaError("CORRUPT_PROJECT")
        events.append((signed, evidence))
    return tuple(events)


def read_blobs(db: sqlite3.Connection) -> dict[str, bytes]:
    count, cost = db.execute("SELECT count(*), coalesce(sum(length(content)),0) FROM sources").fetchone()
    if type(count) is not int or count > MAX_BLOBS or type(cost) is not int or cost > MAX_BYTES:
        raise LacunaError("PROJECT_BUDGET_EXCEEDED")
    result = {}
    for digest, content in db.execute("SELECT sha256, content FROM sources ORDER BY sha256"):
        sha_field(digest)
        if type(content) is not bytes or len(content) > MAX_SOURCE or hashlib.sha256(content).hexdigest() != digest:
            raise LacunaError("SOURCE_DRIFT")
        result[digest] = content
    return result


def snapshot_sources(scope: Scope, source_root: Path) -> dict[str, bytes]:
    root = _checked_directory(source_root, "SOURCE_MISSING")
    result = {}
    for source in scope.sources:
        path = root / source.path
        _checked_directory(path.parent, "SOURCE_MISSING")
        raw = _read_regular(path, "SOURCE_MISSING", MAX_SOURCE)
        if hashlib.sha256(raw).hexdigest() != source.sha256:
            raise LacunaError("SOURCE_DRIFT")
        result[source.sha256] = raw
    return result


def require_sources(scope: Scope, blobs: dict[str, bytes]) -> None:
    for source in scope.sources:
        raw = blobs.get(source.sha256)
        if raw is None or hashlib.sha256(raw).hexdigest() != source.sha256:
            raise LacunaError("SOURCE_DRIFT")


def _chunks(raw: bytes) -> list[str]:
    return [base64.b64encode(raw[i:i + 2048]).decode("ascii") for i in range(0, len(raw), 2048)]


def _unchunk(value: object) -> bytes:
    chunks = _array(value)
    if len(chunks) > MAX_BYTES // 2048:
        raise LacunaError("PROJECT_BUDGET_EXCEEDED")
    try:
        result = b"".join(base64.b64decode(_string(part), validate=True) for part in chunks)
    except ValueError as exc:
        raise LacunaError("CORRUPT_BUNDLE") from exc
    if _chunks(result) != chunks:
        raise LacunaError("CORRUPT_BUNDLE")
    return result


def bundle_bytes(events: tuple[tuple[bytes, bytes | None], ...], blobs: dict[str, bytes], revision: str) -> bytes:
    return encode({"schema": SCHEMA, "revision": revision,
                   "events": [{"signed": _chunks(s), "evidence": None if e is None else _chunks(e)} for s, e in events],
                   "sources": [{"sha256": sha, "content": _chunks(raw)} for sha, raw in sorted(blobs.items())]})


def decode_bundle(raw: bytes) -> tuple[tuple[tuple[bytes, bytes | None], ...], dict[str, bytes], str]:
    item = _object(_parse(raw), frozenset({"schema", "revision", "events", "sources"}))
    if item["schema"] != SCHEMA:
        raise LacunaError("CORRUPT_BUNDLE")
    events = []
    for value in _array(item["events"]):
        event = _object(value, frozenset({"signed", "evidence"}))
        events.append((_unchunk(event["signed"]), None if event["evidence"] is None else _unchunk(event["evidence"])))
    blobs = {}
    for value in _array(item["sources"]):
        source = _object(value, frozenset({"sha256", "content"}))
        sha, content = sha_field(source["sha256"]), _unchunk(source["content"])
        if sha in blobs or len(content) > MAX_SOURCE or hashlib.sha256(content).hexdigest() != sha:
            raise LacunaError("SOURCE_DRIFT")
        blobs[sha] = content
    if len(events) > MAX_EVENTS or len(blobs) > MAX_BLOBS:
        raise LacunaError("PROJECT_BUDGET_EXCEEDED")
    revision = sha_field(item["revision"])
    if bundle_bytes(tuple(events), blobs, revision) != raw:
        raise LacunaError("CORRUPT_BUNDLE")
    return tuple(events), blobs, revision
