"""Deterministic SQLite transaction mechanics for ZRPF replay admission."""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass

from src.core.recursive_stark_admission import (
    MAX_ADMISSION_INDEX_ENTRIES,
    RecursiveStarkRootFacts,
    _AuthenticatedRecursiveStarkRootFacts,
    _RecursiveStarkAdmissionIndexSnapshot,
)
from src.integration._recursive_stark_admission_store_hashes import (
    _OUTCOME_DOMAIN,
    _domain_hash,
    _epoch_blob,
    _state_root,
    _StateRootInput,
)
from src.integration.recursive_stark_admission_store_types import (
    MAX_SQLITE_REVISION,
    DurableRecursiveStarkAdmissionCursor,
    DurableRecursiveStarkAdmissionReceipt,
    RecursiveStarkAdmissionStoreError,
    _hash_bytes,
    _hex_hash,
)


@dataclass(frozen=True, slots=True)
class _StoredRootStatus:
    seen: bool
    idempotent_outcome: bool

    def __post_init__(self) -> None:
        if self.idempotent_outcome and not self.seen:
            raise ValueError("idempotent stored root must be seen")


@dataclass(frozen=True, slots=True)
class _AdmissionCommitContext:
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts
    facts_digest: bytes
    outcome_key: bytes
    previous_cursor: DurableRecursiveStarkAdmissionCursor
    next_cursor: DurableRecursiveStarkAdmissionCursor


def _database_snapshot(
    connection: sqlite3.Connection,
    cursor: DurableRecursiveStarkAdmissionCursor,
    facts: RecursiveStarkRootFacts,
    root_status: _StoredRootStatus,
) -> _RecursiveStarkAdmissionIndexSnapshot:
    _stage_incoming_identifiers(connection, facts)
    return _RecursiveStarkAdmissionIndexSnapshot(
        chain_id=cursor.chain_id,
        root_seen=root_status.seen,
        root_is_idempotent_outcome=root_status.idempotent_outcome,
        slot_seen=_slot_seen(connection, facts),
        child_claim_overlap=_incoming_overlap(
            connection,
            table="zrpf_child_claims",
            kind=1,
        ),
        receipt_overlap=_incoming_overlap(
            connection,
            table="zrpf_accepted_receipts",
            kind=2,
        ),
        message_overlap=_incoming_overlap(
            connection,
            table="zrpf_cross_shard_messages",
            kind=3,
        ),
        root_count=cursor.root_count,
        slot_count=cursor.slot_count,
        child_claim_count=cursor.child_claim_count,
        receipt_count=cursor.receipt_count,
        message_count=cursor.message_count,
    )


def _stage_incoming_identifiers(
    connection: sqlite3.Connection,
    facts: RecursiveStarkRootFacts,
) -> None:
    connection.execute(
        "CREATE TEMP TABLE IF NOT EXISTS zrpf_incoming_ids "
        "(kind INTEGER NOT NULL, identifier BLOB NOT NULL, PRIMARY KEY (kind, identifier)) "
        "WITHOUT ROWID"
    )
    connection.execute("DELETE FROM temp.zrpf_incoming_ids")
    incoming_rows = [
        (1, _hash_bytes(value, name="child claim"))
        for value in facts.child_verification_claim_hashes
    ]
    incoming_rows.extend(
        (2, _hash_bytes(value, name="accepted receipt")) for value in facts.accepted_receipt_ids
    )
    incoming_rows.extend(
        (3, _hash_bytes(value, name="cross-shard message"))
        for value in facts.cross_shard_message_ids
    )
    connection.executemany(
        "INSERT INTO temp.zrpf_incoming_ids (kind, identifier) VALUES (?, ?)",
        incoming_rows,
    )


def _slot_seen(connection: sqlite3.Connection, facts: RecursiveStarkRootFacts) -> bool:
    return (
        connection.execute(
            """
            SELECT 1 FROM zrpf_admissions
            WHERE chain_id = ? AND epoch_id_be = ? AND proof_profile = ? LIMIT 1
            """,
            (facts.chain_id, _epoch_blob(facts.epoch_id), facts.proof_profile),
        ).fetchone()
        is not None
    )


def _incoming_overlap(
    connection: sqlite3.Connection,
    *,
    table: str,
    kind: int,
) -> bool:
    if table not in {
        "zrpf_child_claims",
        "zrpf_accepted_receipts",
        "zrpf_cross_shard_messages",
    }:
        raise ValueError("unsupported replay-index table")
    return (
        connection.execute(
            f"""
            SELECT 1
            FROM temp.zrpf_incoming_ids AS incoming
            JOIN {table} AS stored ON stored.identifier = incoming.identifier
            WHERE incoming.kind = ?
            LIMIT 1
            """,
            (kind,),
        ).fetchone()
        is not None
    )


def _persist_admission_rows(
    connection: sqlite3.Connection,
    context: _AdmissionCommitContext,
) -> None:
    root = _insert_admission(connection, context)
    facts = context.authenticated_root.facts
    _insert_identifier_rows(
        connection,
        kind="child",
        identifiers=facts.child_verification_claim_hashes,
        root=root,
    )
    _insert_identifier_rows(
        connection,
        kind="receipt",
        identifiers=facts.accepted_receipt_ids,
        root=root,
    )
    _insert_identifier_rows(
        connection,
        kind="message",
        identifiers=facts.cross_shard_message_ids,
        root=root,
    )


def _insert_admission(
    connection: sqlite3.Connection,
    context: _AdmissionCommitContext,
) -> bytes:
    facts = context.authenticated_root.facts
    provenance = context.authenticated_root.provenance
    root = _hash_bytes(facts.root_journal_hash, name="facts.root_journal_hash")
    if (
        provenance.release_binding_config_digest is None
        or provenance.replay_manifest_sha256 is None
    ):
        raise TypeError("durable admission requires release provenance")
    connection.execute(
        """
        INSERT INTO zrpf_admissions (
            root_journal_hash, outcome_key, facts_digest, revision, chain_id,
            epoch_id_be, proof_profile, verifier_set_root, public_policy_hash,
            child_claims_root, accepted_receipts_root, message_ids_root,
            authority_manifest_sha256, verifier_executable_sha256,
            verification_request_sha256, release_binding_config_digest,
            replay_manifest_sha256, previous_state_root, result_state_root,
            result_root_count, result_slot_count, result_child_claim_count,
            result_receipt_count, result_message_count
        ) VALUES (
            ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?
        )
        """,
        _admission_values(context),
    )
    return root


def _admission_values(context: _AdmissionCommitContext) -> tuple[object, ...]:
    facts = context.authenticated_root.facts
    provenance = context.authenticated_root.provenance
    previous = context.previous_cursor
    result = context.next_cursor
    if (
        provenance.release_binding_config_digest is None
        or provenance.replay_manifest_sha256 is None
    ):
        raise TypeError("durable admission values require release provenance")
    return (
        _hash_bytes(facts.root_journal_hash, name="facts.root_journal_hash"),
        context.outcome_key,
        context.facts_digest,
        result.revision,
        facts.chain_id,
        _epoch_blob(facts.epoch_id),
        facts.proof_profile,
        _hash_bytes(facts.verifier_set_root, name="facts.verifier_set_root"),
        _hash_bytes(facts.public_policy_hash, name="facts.public_policy_hash"),
        _hash_bytes(facts.child_verification_claims_root, name="facts child root"),
        _hash_bytes(facts.accepted_receipts_root, name="facts receipt root"),
        _hash_bytes(facts.cross_shard_message_ids_root, name="facts message root"),
        bytes.fromhex(provenance.authority_manifest_sha256),
        bytes.fromhex(provenance.verifier_executable_sha256),
        bytes.fromhex(provenance.verification_request_sha256),
        bytes.fromhex(provenance.release_binding_config_digest.removeprefix("0x")),
        bytes.fromhex(provenance.replay_manifest_sha256.removeprefix("sha256:")),
        _hash_bytes(previous.state_root, name="previous state root"),
        _hash_bytes(result.state_root, name="result state root"),
        result.root_count,
        result.slot_count,
        result.child_claim_count,
        result.receipt_count,
        result.message_count,
    )


def _insert_identifier_rows(
    connection: sqlite3.Connection,
    *,
    kind: str,
    identifiers: tuple[str, ...],
    root: bytes,
) -> None:
    table_and_label = {
        "child": ("zrpf_child_claims", "child claim"),
        "receipt": ("zrpf_accepted_receipts", "accepted receipt"),
        "message": ("zrpf_cross_shard_messages", "cross-shard message"),
    }.get(kind)
    if table_and_label is None:
        raise ValueError("unsupported replay-index identifier kind")
    table, label = table_and_label
    connection.executemany(
        f"INSERT INTO {table} (identifier, root_journal_hash, ordinal) VALUES (?, ?, ?)",
        (
            (_hash_bytes(identifier, name=label), root, ordinal)
            for ordinal, identifier in enumerate(identifiers)
        ),
    )


def _cas_meta(
    connection: sqlite3.Connection,
    previous: DurableRecursiveStarkAdmissionCursor,
    result: DurableRecursiveStarkAdmissionCursor,
) -> None:
    cursor = connection.execute(
        """
        UPDATE zrpf_store_meta
        SET revision = ?, chain_id = ?, state_root = ?, root_count = ?,
            slot_count = ?, child_claim_count = ?, receipt_count = ?, message_count = ?
        WHERE singleton = 1 AND revision = ? AND state_root = ?
        """,
        (
            result.revision,
            result.chain_id,
            _hash_bytes(result.state_root, name="result state root"),
            result.root_count,
            result.slot_count,
            result.child_claim_count,
            result.receipt_count,
            result.message_count,
            previous.revision,
            _hash_bytes(previous.state_root, name="previous state root"),
        ),
    )
    if cursor.rowcount != 1:
        raise RecursiveStarkAdmissionStoreError(
            "INTERNAL_CAS_FAILED",
            "serialized metadata compare-and-swap changed no row",
        )


def _next_cursor(
    previous: DurableRecursiveStarkAdmissionCursor,
    facts: RecursiveStarkRootFacts,
    outcome_key: bytes,
    facts_digest: bytes,
) -> DurableRecursiveStarkAdmissionCursor:
    revision = previous.revision + 1
    if revision > min(MAX_SQLITE_REVISION, MAX_ADMISSION_INDEX_ENTRIES):
        raise ValueError("durable admission revision capacity exceeded")
    counts = (
        previous.root_count + 1,
        previous.slot_count + 1,
        previous.child_claim_count + len(facts.child_verification_claim_hashes),
        previous.receipt_count + len(facts.accepted_receipt_ids),
        previous.message_count + len(facts.cross_shard_message_ids),
    )
    state_root = _state_root(
        _StateRootInput(
            previous=previous,
            revision=revision,
            facts=facts,
            outcome_key=outcome_key,
            facts_digest=facts_digest,
            counts=counts,
        )
    )
    return DurableRecursiveStarkAdmissionCursor(
        revision=revision,
        state_root=_hex_hash(state_root),
        chain_id=facts.chain_id,
        root_count=counts[0],
        slot_count=counts[1],
        child_claim_count=counts[2],
        receipt_count=counts[3],
        message_count=counts[4],
    )


def _read_cursor(connection: sqlite3.Connection) -> DurableRecursiveStarkAdmissionCursor:
    row = connection.execute(
        """
        SELECT revision, chain_id, state_root, root_count, slot_count,
               child_claim_count, receipt_count, message_count
        FROM zrpf_store_meta WHERE singleton = 1
        """
    ).fetchone()
    if row is None:
        raise ValueError("durable admission metadata row is missing")
    return DurableRecursiveStarkAdmissionCursor(
        revision=int(row["revision"]),
        state_root=_hex_hash(bytes(row["state_root"])),
        chain_id=row["chain_id"],
        root_count=int(row["root_count"]),
        slot_count=int(row["slot_count"]),
        child_claim_count=int(row["child_claim_count"]),
        receipt_count=int(row["receipt_count"]),
        message_count=int(row["message_count"]),
    )


def _read_admission_row(
    connection: sqlite3.Connection,
    root_journal_hash: bytes,
) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM zrpf_admissions WHERE root_journal_hash = ?",
        (root_journal_hash,),
    ).fetchone()


def _receipt_from_row(row: sqlite3.Row) -> DurableRecursiveStarkAdmissionReceipt:
    from src.core.recursive_stark_admission import RecursiveStarkAdmissionSlot

    return DurableRecursiveStarkAdmissionReceipt(
        outcome_key=_hex_hash(bytes(row["outcome_key"])),
        slot=RecursiveStarkAdmissionSlot(
            chain_id=str(row["chain_id"]),
            epoch_id=int.from_bytes(bytes(row["epoch_id_be"]), "big"),
            proof_profile=str(row["proof_profile"]),
        ),
        root_journal_hash=_hex_hash(bytes(row["root_journal_hash"])),
        committed_revision=int(row["revision"]),
        previous_state_root=_hex_hash(bytes(row["previous_state_root"])),
        result_state_root=_hex_hash(bytes(row["result_state_root"])),
        result_root_count=int(row["result_root_count"]),
        result_slot_count=int(row["result_slot_count"]),
        result_child_claim_count=int(row["result_child_claim_count"]),
        result_receipt_count=int(row["result_receipt_count"]),
        result_message_count=int(row["result_message_count"]),
        authority_manifest_sha256=bytes(row["authority_manifest_sha256"]).hex(),
        verifier_executable_sha256=bytes(row["verifier_executable_sha256"]).hex(),
        verification_request_sha256=bytes(row["verification_request_sha256"]).hex(),
        release_binding_config_digest=("0x" + bytes(row["release_binding_config_digest"]).hex()),
        replay_manifest_sha256="sha256:" + bytes(row["replay_manifest_sha256"]).hex(),
    )


def _validate_stored_outcome_key(row: sqlite3.Row) -> None:
    recomputed = _domain_hash(
        _OUTCOME_DOMAIN,
        (
            bytes(row["facts_digest"]),
            bytes(row["authority_manifest_sha256"]),
            bytes(row["verifier_executable_sha256"]),
            bytes(row["verification_request_sha256"]),
            bytes(row["release_binding_config_digest"]),
            bytes(row["replay_manifest_sha256"]),
        ),
    )
    if recomputed != bytes(row["outcome_key"]):
        raise ValueError("stored durable admission outcome key is inconsistent")
