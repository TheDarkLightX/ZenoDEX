"""SQLite schema, connection policy, and local-file controls for ZRPF admission."""

from __future__ import annotations

import hashlib
import os
import sqlite3
import stat
from pathlib import Path

STORE_SCHEMA_VERSION = 1
STORE_APPLICATION_ID = 0x5A525046
DEFAULT_BUSY_TIMEOUT_MS = 5_000
MAX_BUSY_TIMEOUT_MS = 60_000

_GENESIS_DOMAIN = b"zenodex.zrpf.durable_admission.genesis.v1"
GENESIS_STATE_ROOT = hashlib.sha256(
    _GENESIS_DOMAIN + STORE_SCHEMA_VERSION.to_bytes(4, "big")
).digest()

_SCHEMA_STATEMENTS = (
    """
    CREATE TABLE zrpf_store_meta (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 1),
        revision INTEGER NOT NULL CHECK (revision BETWEEN 0 AND 1048576),
        chain_id TEXT,
        state_root BLOB NOT NULL CHECK (typeof(state_root) = 'blob' AND length(state_root) = 32),
        root_count INTEGER NOT NULL CHECK (root_count BETWEEN 0 AND 1048576),
        slot_count INTEGER NOT NULL CHECK (slot_count BETWEEN 0 AND 1048576),
        child_claim_count INTEGER NOT NULL CHECK (child_claim_count BETWEEN 0 AND 1048576),
        receipt_count INTEGER NOT NULL CHECK (receipt_count BETWEEN 0 AND 1048576),
        message_count INTEGER NOT NULL CHECK (message_count BETWEEN 0 AND 1048576),
        CHECK (root_count = slot_count),
        CHECK ((revision = 0 AND chain_id IS NULL) OR (revision > 0 AND chain_id IS NOT NULL))
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_admissions (
        root_journal_hash BLOB NOT NULL PRIMARY KEY CHECK (length(root_journal_hash) = 32),
        outcome_key BLOB NOT NULL UNIQUE CHECK (length(outcome_key) = 32),
        facts_digest BLOB NOT NULL CHECK (length(facts_digest) = 32),
        revision INTEGER NOT NULL UNIQUE CHECK (revision BETWEEN 1 AND 1048576),
        chain_id TEXT NOT NULL,
        epoch_id_be BLOB NOT NULL CHECK (length(epoch_id_be) = 8),
        proof_profile TEXT NOT NULL,
        verifier_set_root BLOB NOT NULL CHECK (length(verifier_set_root) = 32),
        public_policy_hash BLOB NOT NULL CHECK (length(public_policy_hash) = 32),
        child_claims_root BLOB NOT NULL CHECK (length(child_claims_root) = 32),
        accepted_receipts_root BLOB NOT NULL CHECK (length(accepted_receipts_root) = 32),
        message_ids_root BLOB NOT NULL CHECK (length(message_ids_root) = 32),
        authority_manifest_sha256 BLOB NOT NULL CHECK (length(authority_manifest_sha256) = 32),
        verifier_executable_sha256 BLOB NOT NULL CHECK (length(verifier_executable_sha256) = 32),
        verification_request_sha256 BLOB NOT NULL CHECK (length(verification_request_sha256) = 32),
        release_binding_config_digest BLOB NOT NULL CHECK (length(release_binding_config_digest) = 32),
        replay_manifest_sha256 BLOB NOT NULL CHECK (length(replay_manifest_sha256) = 32),
        previous_state_root BLOB NOT NULL CHECK (length(previous_state_root) = 32),
        result_state_root BLOB NOT NULL UNIQUE CHECK (length(result_state_root) = 32),
        result_root_count INTEGER NOT NULL CHECK (result_root_count BETWEEN 1 AND 1048576),
        result_slot_count INTEGER NOT NULL CHECK (result_slot_count BETWEEN 1 AND 1048576),
        result_child_claim_count INTEGER NOT NULL CHECK (result_child_claim_count BETWEEN 0 AND 1048576),
        result_receipt_count INTEGER NOT NULL CHECK (result_receipt_count BETWEEN 0 AND 1048576),
        result_message_count INTEGER NOT NULL CHECK (result_message_count BETWEEN 0 AND 1048576),
        CHECK (result_root_count = result_slot_count),
        UNIQUE (chain_id, epoch_id_be, proof_profile)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_child_claims (
        identifier BLOB NOT NULL PRIMARY KEY CHECK (length(identifier) = 32),
        root_journal_hash BLOB NOT NULL REFERENCES zrpf_admissions(root_journal_hash) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 4095),
        UNIQUE (root_journal_hash, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_accepted_receipts (
        identifier BLOB NOT NULL PRIMARY KEY CHECK (length(identifier) = 32),
        root_journal_hash BLOB NOT NULL REFERENCES zrpf_admissions(root_journal_hash) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 65535),
        UNIQUE (root_journal_hash, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE zrpf_cross_shard_messages (
        identifier BLOB NOT NULL PRIMARY KEY CHECK (length(identifier) = 32),
        root_journal_hash BLOB NOT NULL REFERENCES zrpf_admissions(root_journal_hash) ON DELETE RESTRICT,
        ordinal INTEGER NOT NULL CHECK (ordinal BETWEEN 0 AND 65535),
        UNIQUE (root_journal_hash, ordinal)
    ) STRICT, WITHOUT ROWID
    """,
)

_EXPECTED_SCHEMA_SQL = {
    "zrpf_store_meta": _SCHEMA_STATEMENTS[0],
    "zrpf_admissions": _SCHEMA_STATEMENTS[1],
    "zrpf_child_claims": _SCHEMA_STATEMENTS[2],
    "zrpf_accepted_receipts": _SCHEMA_STATEMENTS[3],
    "zrpf_cross_shard_messages": _SCHEMA_STATEMENTS[4],
}


def _connect_database(path: Path, *, busy_timeout_ms: int) -> sqlite3.Connection:
    timeout_seconds = max(1, (busy_timeout_ms + 999) // 1_000)
    connection = sqlite3.connect(path, timeout=timeout_seconds, isolation_level=None)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    journal_mode = connection.execute("PRAGMA journal_mode = DELETE").fetchone()[0]
    if str(journal_mode).lower() != "delete":
        connection.close()
        raise ValueError("durable admission journal_mode must be DELETE")
    connection.execute("PRAGMA synchronous = EXTRA")
    connection.execute(f"PRAGMA busy_timeout = {busy_timeout_ms}")
    connection.execute("PRAGMA trusted_schema = OFF")
    connection.execute("PRAGMA temp_store = MEMORY")
    if connection.execute("PRAGMA foreign_keys").fetchone()[0] != 1:
        connection.close()
        raise ValueError("durable admission foreign_keys must be enabled")
    if connection.execute("PRAGMA synchronous").fetchone()[0] != 3:
        connection.close()
        raise ValueError("durable admission synchronous must be EXTRA")
    if connection.execute("PRAGMA trusted_schema").fetchone()[0] != 0:
        connection.close()
        raise ValueError("durable admission trusted_schema must be disabled")
    if connection.execute("PRAGMA busy_timeout").fetchone()[0] != busy_timeout_ms:
        connection.close()
        raise ValueError("durable admission busy_timeout mismatch")
    return connection


def _initialize_or_validate(connection: sqlite3.Connection) -> None:
    if not connection.in_transaction:
        raise ValueError("store initialization requires an existing transaction")
    existing_objects = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing_objects:
        if connection.execute("PRAGMA application_id").fetchone()[0] != 0:
            raise ValueError("empty durable admission database has an application_id")
        if connection.execute("PRAGMA user_version").fetchone()[0] != 0:
            raise ValueError("empty durable admission database has a user_version")
        connection.execute(f"PRAGMA application_id = {STORE_APPLICATION_ID}")
        connection.execute(f"PRAGMA user_version = {STORE_SCHEMA_VERSION}")
        for statement in _SCHEMA_STATEMENTS:
            connection.execute(statement)
        connection.execute(
            """
            INSERT INTO zrpf_store_meta (
                singleton, schema_version, revision, chain_id, state_root,
                root_count, slot_count, child_claim_count, receipt_count,
                message_count
            ) VALUES (1, 1, 0, NULL, ?, 0, 0, 0, 0, 0)
            """,
            (GENESIS_STATE_ROOT,),
        )
    _validate_schema(connection)
    _validate_database_content(connection)


def _validate_schema(connection: sqlite3.Connection) -> None:
    if connection.execute("PRAGMA application_id").fetchone()[0] != STORE_APPLICATION_ID:
        raise ValueError("durable admission application_id mismatch")
    if connection.execute("PRAGMA user_version").fetchone()[0] != STORE_SCHEMA_VERSION:
        raise ValueError("durable admission user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _EXPECTED_SCHEMA_SQL}
    if observed != expected:
        raise ValueError("durable admission schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        actual_sql = _normalize_sql(str(row["sql"]))
        expected_sql = _normalize_sql(_EXPECTED_SCHEMA_SQL[name])
        if actual_sql != expected_sql:
            raise ValueError(f"durable admission schema SQL mismatch for {name}")


def _validate_database_content(connection: sqlite3.Connection) -> None:
    quick_check = connection.execute("PRAGMA quick_check").fetchall()
    if len(quick_check) != 1 or quick_check[0][0] != "ok":
        raise ValueError("durable admission quick_check failed")
    if connection.execute("PRAGMA foreign_key_check").fetchone() is not None:
        raise ValueError("durable admission foreign_key_check failed")
    meta = connection.execute(
        """
        SELECT revision, chain_id, state_root, root_count, slot_count,
               child_claim_count, receipt_count, message_count
        FROM zrpf_store_meta WHERE singleton = 1
        """
    ).fetchone()
    if meta is None:
        raise ValueError("durable admission metadata row is missing")
    admission_count = connection.execute("SELECT count(*) FROM zrpf_admissions").fetchone()[0]
    observed_counts = (
        admission_count,
        admission_count,
        connection.execute("SELECT count(*) FROM zrpf_child_claims").fetchone()[0],
        connection.execute("SELECT count(*) FROM zrpf_accepted_receipts").fetchone()[0],
        connection.execute("SELECT count(*) FROM zrpf_cross_shard_messages").fetchone()[0],
    )
    committed_counts = tuple(
        int(meta[name])
        for name in (
            "root_count",
            "slot_count",
            "child_claim_count",
            "receipt_count",
            "message_count",
        )
    )
    if observed_counts != committed_counts:
        raise ValueError("durable admission metadata counts disagree with indexes")
    revision = int(meta["revision"])
    if revision != committed_counts[0]:
        raise ValueError("durable admission revision disagrees with root count")
    if revision == 0:
        if meta["chain_id"] is not None or bytes(meta["state_root"]) != GENESIS_STATE_ROOT:
            raise ValueError("durable admission genesis metadata mismatch")
        return
    latest = connection.execute(
        "SELECT chain_id, result_state_root FROM zrpf_admissions WHERE revision = ?",
        (revision,),
    ).fetchone()
    if latest is None:
        raise ValueError("durable admission latest receipt is missing")
    if latest["chain_id"] != meta["chain_id"]:
        raise ValueError("durable admission latest chain scope mismatch")
    if bytes(latest["result_state_root"]) != bytes(meta["state_root"]):
        raise ValueError("durable admission latest state root mismatch")


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())


def _require_private_parent(parent: Path) -> None:
    info = parent.stat(follow_symlinks=False)
    if not stat.S_ISDIR(info.st_mode):
        raise ValueError("durable admission parent must be a directory")
    if info.st_uid != os.geteuid():
        raise ValueError("durable admission parent must be owned by the effective uid")
    if stat.S_IMODE(info.st_mode) & 0o077:
        raise ValueError("durable admission parent must not grant group or world access")


def _create_private_database_file(path: Path) -> bool:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError:
        info = path.stat(follow_symlinks=False)
        if not stat.S_ISREG(info.st_mode):
            raise ValueError("durable admission database must be a regular file") from None
        if info.st_uid != os.geteuid() or info.st_nlink != 1:
            raise ValueError("durable admission database ownership or link count invalid") from None
        if stat.S_IMODE(info.st_mode) != 0o600:
            raise ValueError("durable admission database mode must be 0600") from None
        return False
    else:
        os.close(descriptor)
        return True


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
