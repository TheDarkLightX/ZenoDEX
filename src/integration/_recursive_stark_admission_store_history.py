"""Full canonical restart validation for the ZRPF replay-admission history."""

from __future__ import annotations

import sqlite3
from collections.abc import Iterator

from src.core.recursive_stark_admission import (
    RecursiveStarkRootFacts,
)
from src.integration._recursive_stark_admission_store_engine import (
    _next_cursor,
    _read_cursor,
    _validate_stored_outcome_key,
)
from src.integration._recursive_stark_admission_store_hashes import _facts_digest
from src.integration._recursive_stark_admission_store_schema import GENESIS_STATE_ROOT
from src.integration.recursive_stark_admission_store_types import (
    DurableRecursiveStarkAdmissionCursor,
    _hex_hash,
)


def _validate_complete_history(connection: sqlite3.Connection) -> None:
    """Recompute every committed link and require exact metadata equality."""

    if not connection.in_transaction:
        raise ValueError("complete history validation requires an existing transaction")

    expected_cursor = DurableRecursiveStarkAdmissionCursor(
        revision=0,
        state_root=_hex_hash(GENESIS_STATE_ROOT),
        chain_id=None,
        root_count=0,
        slot_count=0,
        child_claim_count=0,
        receipt_count=0,
        message_count=0,
    )
    child_sequences = _iter_identifier_sequences(connection, "zrpf_child_claims")
    receipt_sequences = _iter_identifier_sequences(connection, "zrpf_accepted_receipts")
    message_sequences = _iter_identifier_sequences(
        connection,
        "zrpf_cross_shard_messages",
    )
    rows = connection.execute("SELECT * FROM zrpf_admissions ORDER BY revision")
    for expected_revision, row in enumerate(rows, start=1):
        if int(row["revision"]) != expected_revision:
            raise ValueError("durable admission revisions must be dense")
        facts = _facts_from_row(
            row,
            _sequence_for_revision(child_sequences, expected_revision),
            _sequence_for_revision(receipt_sequences, expected_revision),
            _sequence_for_revision(message_sequences, expected_revision),
        )
        if expected_cursor.chain_id not in (None, facts.chain_id):
            raise ValueError("durable admission history changes chain scope")
        row_facts_digest = bytes(row["facts_digest"])
        if _facts_digest(facts) != row_facts_digest:
            raise ValueError("durable admission stored facts digest mismatch")
        _validate_stored_outcome_key(row)
        expected_next = _next_cursor(
            expected_cursor,
            facts,
            bytes(row["outcome_key"]),
            row_facts_digest,
        )
        observed_next = _cursor_from_admission_row(row)
        if observed_next != expected_next:
            raise ValueError("durable admission state-root history mismatch")
        if _hex_hash(bytes(row["previous_state_root"])) != expected_cursor.state_root:
            raise ValueError("durable admission previous state-root link mismatch")
        expected_cursor = expected_next

    _require_exhausted(child_sequences, "zrpf_child_claims")
    _require_exhausted(receipt_sequences, "zrpf_accepted_receipts")
    _require_exhausted(message_sequences, "zrpf_cross_shard_messages")

    if _read_cursor(connection) != expected_cursor:
        raise ValueError("durable admission metadata head does not match history")


def _facts_from_row(
    row: sqlite3.Row,
    children: tuple[str, ...],
    receipts: tuple[str, ...],
    messages: tuple[str, ...],
) -> RecursiveStarkRootFacts:
    root = bytes(row["root_journal_hash"])
    return RecursiveStarkRootFacts(
        chain_id=str(row["chain_id"]),
        epoch_id=int.from_bytes(bytes(row["epoch_id_be"]), "big"),
        proof_profile=str(row["proof_profile"]),
        root_journal_hash=_hex_hash(root),
        verifier_set_root=_hex_hash(bytes(row["verifier_set_root"])),
        public_policy_hash=_hex_hash(bytes(row["public_policy_hash"])),
        child_verification_claim_hashes=children,
        child_verification_claims_root=_hex_hash(bytes(row["child_claims_root"])),
        accepted_receipt_ids=receipts,
        accepted_receipts_root=_hex_hash(bytes(row["accepted_receipts_root"])),
        cross_shard_message_ids=messages,
        cross_shard_message_ids_root=_hex_hash(bytes(row["message_ids_root"])),
    )


def _iter_identifier_sequences(
    connection: sqlite3.Connection,
    table: str,
) -> Iterator[tuple[int, tuple[str, ...]]]:
    if table not in {
        "zrpf_child_claims",
        "zrpf_accepted_receipts",
        "zrpf_cross_shard_messages",
    }:
        raise ValueError("unsupported durable history identifier table")
    rows = connection.execute(
        f"SELECT a.revision, i.ordinal, i.identifier "
        "FROM zrpf_admissions AS a "
        f"LEFT JOIN {table} AS i ON i.root_journal_hash = a.root_journal_hash "
        "ORDER BY a.revision, i.ordinal"
    )
    current_revision: int | None = None
    values: list[str] = []
    for row in rows:
        revision = int(row["revision"])
        if current_revision is not None and revision != current_revision:
            yield current_revision, tuple(values)
            values = []
        current_revision = revision
        ordinal = row["ordinal"]
        identifier = row["identifier"]
        if ordinal is None and identifier is None:
            continue
        if ordinal is None or identifier is None:
            raise ValueError(f"durable admission {table} has a partial null row")
        if int(ordinal) != len(values):
            raise ValueError(f"durable admission {table} ordinals must be dense")
        values.append(_hex_hash(bytes(identifier)))
    if current_revision is not None:
        yield current_revision, tuple(values)


def _sequence_for_revision(
    sequences: Iterator[tuple[int, tuple[str, ...]]],
    expected_revision: int,
) -> tuple[str, ...]:
    try:
        revision, values = next(sequences)
    except StopIteration as exc:
        raise ValueError("durable admission identifier history ended early") from exc
    if revision != expected_revision:
        raise ValueError("durable admission identifier history revision mismatch")
    return values


def _require_exhausted(
    sequences: Iterator[tuple[int, tuple[str, ...]]],
    table: str,
) -> None:
    try:
        next(sequences)
    except StopIteration:
        return
    raise ValueError(f"durable admission {table} history has trailing rows")


def _cursor_from_admission_row(
    row: sqlite3.Row,
) -> DurableRecursiveStarkAdmissionCursor:
    return DurableRecursiveStarkAdmissionCursor(
        revision=int(row["revision"]),
        state_root=_hex_hash(bytes(row["result_state_root"])),
        chain_id=str(row["chain_id"]),
        root_count=int(row["result_root_count"]),
        slot_count=int(row["result_slot_count"]),
        child_claim_count=int(row["result_child_claim_count"]),
        receipt_count=int(row["result_receipt_count"]),
        message_count=int(row["result_message_count"]),
    )
