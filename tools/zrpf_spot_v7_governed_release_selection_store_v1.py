"""Atomic authority-false Spot V7 release selection and revocation history.

The store consumes exact governed selector bytes and reparses exact candidate
bytes.  It owns lineage, CAS, replay, and terminal-revocation invariants.  It
does not authenticate selector publishers, activate runtime code, or mint any
release, settlement, runtime, or production capability.
"""

from __future__ import annotations

import hashlib
import json
import os
import sqlite3
import stat
from contextlib import closing
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Final, NoReturn, cast, final

from tools.zrpf_spot_v7_governed_release_selector_input_v1 import (
    ZERO_DIGEST_V1,
    GovernedReleaseSelectorInputV1,
    SelectorOperationV1,
    SpotV7RevocationRecordV1,
    SpotV7SelectorInputRejectV1,
    parse_exact_governed_release_selector_input_v1,
    parse_exact_spot_v7_revocation_record_v1,
)
from tools.zrpf_spot_v7_release_candidate_manifest_v1 import (
    SpotV7ReleaseCandidateManifestV1,
    SpotV7ReleaseCandidateRejectV1,
    canonical_document_bytes_v1,
    check_exact_spot_v7_release_candidate_manifest_v1,
)

STORE_SCHEMA_VERSION_V1: Final = 1
STORE_APPLICATION_ID_V1: Final = 0x5A535637
DEFAULT_BUSY_TIMEOUT_MS_V1: Final = 5_000
MAX_BUSY_TIMEOUT_MS_V1: Final = 60_000
MAX_SELECTION_EVENTS_V1: Final = 4_096

_GENESIS_STATE_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.selection.genesis.v1"
_EVENT_STATE_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.selection.event.v1"
_SCOPE_ID_DOMAIN_V1: Final = b"zenodex.zrpf.spot_v7.selection.scope.v1"

GENESIS_SELECTION_STATE_ROOT_V1: Final = hashlib.sha256(
    _GENESIS_STATE_DOMAIN_V1 + STORE_SCHEMA_VERSION_V1.to_bytes(4, "big")
).digest()


class ReleaseSelectionDispositionV1(str, Enum):
    COMMITTED = "committed"
    IDEMPOTENT = "idempotent_exact_replay"
    REJECTED = "rejected"


class SpotV7ReleaseSelectionStoreErrorV1(RuntimeError):
    """Storage or integrity failure, distinct from a governed reject."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


class _SelectionRejectV1(ValueError):
    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@final
@dataclass(frozen=True, slots=True)
class SpotV7ReleaseSelectionCursorV1:
    database_revision: int
    state_root: bytes
    last_evaluation_epoch: int | None
    current_candidate_id: bytes | None
    current_candidate_sha256: bytes | None
    current_release_revision: int | None
    current_select_input_id: bytes | None
    current_scope_id: bytes | None
    current_revoked: bool
    current_revocation_record_id: bytes | None

    @property
    def candidate_current(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


@final
@dataclass(frozen=True, slots=True)
class SpotV7ReleaseSelectionResultV1:
    disposition: ReleaseSelectionDispositionV1
    code: str
    operation: SelectorOperationV1
    input_id: bytes | None
    cursor: SpotV7ReleaseSelectionCursorV1

    @property
    def candidate_selected(self) -> bool:
        return False

    @property
    def revocation_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


@dataclass(frozen=True, slots=True)
class _CandidateFactsV1:
    canonical_bytes: bytes
    candidate_id: bytes
    candidate_sha256: bytes
    release_revision: int
    parent_candidate_id: bytes | None
    activation_epoch: int
    expiration_epoch: int | None
    revocation_policy_root: bytes
    rollback_policy_root: bytes
    scope_id: bytes


_SCHEMA_STATEMENTS_V1: Final = (
    """
    CREATE TABLE spot_v7_release_selection_meta (
        singleton INTEGER NOT NULL PRIMARY KEY CHECK (singleton = 1),
        schema_version INTEGER NOT NULL CHECK (schema_version = 1),
        database_revision_be BLOB NOT NULL CHECK (typeof(database_revision_be) = 'blob' AND length(database_revision_be) = 8),
        state_root BLOB NOT NULL CHECK (typeof(state_root) = 'blob' AND length(state_root) = 32),
        event_count INTEGER NOT NULL CHECK (event_count BETWEEN 0 AND 4096),
        last_evaluation_epoch_be BLOB CHECK (last_evaluation_epoch_be IS NULL OR (typeof(last_evaluation_epoch_be) = 'blob' AND length(last_evaluation_epoch_be) = 8)),
        current_candidate_id BLOB CHECK (current_candidate_id IS NULL OR (typeof(current_candidate_id) = 'blob' AND length(current_candidate_id) = 32)),
        current_candidate_sha256 BLOB CHECK (current_candidate_sha256 IS NULL OR (typeof(current_candidate_sha256) = 'blob' AND length(current_candidate_sha256) = 32)),
        current_release_revision_be BLOB CHECK (current_release_revision_be IS NULL OR (typeof(current_release_revision_be) = 'blob' AND length(current_release_revision_be) = 8)),
        current_select_input_id BLOB CHECK (current_select_input_id IS NULL OR (typeof(current_select_input_id) = 'blob' AND length(current_select_input_id) = 32)),
        current_scope_id BLOB CHECK (current_scope_id IS NULL OR (typeof(current_scope_id) = 'blob' AND length(current_scope_id) = 32)),
        current_revoked INTEGER NOT NULL CHECK (current_revoked IN (0, 1)),
        current_revocation_record_id BLOB CHECK (current_revocation_record_id IS NULL OR (typeof(current_revocation_record_id) = 'blob' AND length(current_revocation_record_id) = 32)),
        CHECK (
            (event_count = 0 AND last_evaluation_epoch_be IS NULL AND current_candidate_id IS NULL AND current_candidate_sha256 IS NULL AND current_release_revision_be IS NULL AND current_select_input_id IS NULL AND current_scope_id IS NULL AND current_revoked = 0 AND current_revocation_record_id IS NULL)
            OR
            (event_count > 0 AND last_evaluation_epoch_be IS NOT NULL AND current_candidate_id IS NOT NULL AND current_candidate_sha256 IS NOT NULL AND current_release_revision_be IS NOT NULL AND current_select_input_id IS NOT NULL AND current_scope_id IS NOT NULL AND ((current_revoked = 0 AND current_revocation_record_id IS NULL) OR (current_revoked = 1 AND current_revocation_record_id IS NOT NULL)))
        )
    ) STRICT, WITHOUT ROWID
    """,
    """
    CREATE TABLE spot_v7_release_selection_events (
        event_revision_be BLOB NOT NULL PRIMARY KEY CHECK (typeof(event_revision_be) = 'blob' AND length(event_revision_be) = 8),
        operation INTEGER NOT NULL CHECK (operation IN (1, 2)),
        input_id BLOB NOT NULL UNIQUE CHECK (typeof(input_id) = 'blob' AND length(input_id) = 32),
        input_bytes BLOB NOT NULL CHECK (typeof(input_bytes) = 'blob' AND length(input_bytes) = 320),
        candidate_id BLOB NOT NULL CHECK (typeof(candidate_id) = 'blob' AND length(candidate_id) = 32),
        candidate_sha256 BLOB NOT NULL CHECK (typeof(candidate_sha256) = 'blob' AND length(candidate_sha256) = 32),
        candidate_bytes BLOB NOT NULL CHECK (typeof(candidate_bytes) = 'blob' AND length(candidate_bytes) BETWEEN 1 AND 262144),
        release_revision_be BLOB NOT NULL CHECK (typeof(release_revision_be) = 'blob' AND length(release_revision_be) = 8),
        evaluation_epoch_be BLOB NOT NULL CHECK (typeof(evaluation_epoch_be) = 'blob' AND length(evaluation_epoch_be) = 8),
        expected_database_revision_be BLOB NOT NULL CHECK (typeof(expected_database_revision_be) = 'blob' AND length(expected_database_revision_be) = 8),
        expected_current_candidate_id BLOB CHECK (expected_current_candidate_id IS NULL OR (typeof(expected_current_candidate_id) = 'blob' AND length(expected_current_candidate_id) = 32)),
        expected_current_select_input_id BLOB CHECK (expected_current_select_input_id IS NULL OR (typeof(expected_current_select_input_id) = 'blob' AND length(expected_current_select_input_id) = 32)),
        rollback_policy_root BLOB NOT NULL CHECK (typeof(rollback_policy_root) = 'blob' AND length(rollback_policy_root) = 32),
        revocation_registry_root BLOB NOT NULL CHECK (typeof(revocation_registry_root) = 'blob' AND length(revocation_registry_root) = 32),
        revocation_record_id BLOB CHECK (revocation_record_id IS NULL OR (typeof(revocation_record_id) = 'blob' AND length(revocation_record_id) = 32)),
        revocation_record_bytes BLOB CHECK (revocation_record_bytes IS NULL OR (typeof(revocation_record_bytes) = 'blob' AND length(revocation_record_bytes) = 216)),
        scope_id BLOB NOT NULL CHECK (typeof(scope_id) = 'blob' AND length(scope_id) = 32),
        previous_state_root BLOB NOT NULL CHECK (typeof(previous_state_root) = 'blob' AND length(previous_state_root) = 32),
        result_state_root BLOB NOT NULL UNIQUE CHECK (typeof(result_state_root) = 'blob' AND length(result_state_root) = 32),
        release_authority INTEGER NOT NULL CHECK (release_authority = 0),
        settlement_authority INTEGER NOT NULL CHECK (settlement_authority = 0),
        runtime_authority INTEGER NOT NULL CHECK (runtime_authority = 0),
        production_authority INTEGER NOT NULL CHECK (production_authority = 0),
        CHECK ((operation = 1 AND revocation_record_id IS NULL AND revocation_record_bytes IS NULL) OR (operation = 2 AND revocation_record_id IS NOT NULL AND revocation_record_bytes IS NOT NULL)),
        UNIQUE (candidate_id, operation)
    ) STRICT, WITHOUT ROWID
    """,
)

_EXPECTED_SCHEMA_SQL_V1: Final = {
    "spot_v7_release_selection_meta": _SCHEMA_STATEMENTS_V1[0],
    "spot_v7_release_selection_events": _SCHEMA_STATEMENTS_V1[1],
}


@final
class SQLiteSpotV7GovernedReleaseSelectionStoreV1:
    """Fsync-backed lineage store with no authority-minting surface."""

    __slots__ = ("_busy_timeout_ms", "_path")

    def __init__(
        self,
        path: Path,
        *,
        busy_timeout_ms: int = DEFAULT_BUSY_TIMEOUT_MS_V1,
    ) -> None:
        _validate_store_path(path, busy_timeout_ms)
        self._path = path
        self._busy_timeout_ms = busy_timeout_ms
        created = _create_private_database_file(path)
        try:
            with closing(self._connect()) as connection:
                connection.execute("BEGIN EXCLUSIVE")
                try:
                    _initialize_or_validate(connection)
                    connection.commit()
                except (sqlite3.Error, ValueError):
                    if connection.in_transaction:
                        connection.rollback()
                    raise
            if created:
                _fsync_directory(path.parent)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise SpotV7ReleaseSelectionStoreErrorV1("STORE_OPEN_FAILED", str(exc)) from exc

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SQLiteSpotV7GovernedReleaseSelectionStoreV1 cannot be subclassed")

    @property
    def path(self) -> Path:
        return self._path

    def read_cursor(self) -> SpotV7ReleaseSelectionCursorV1:
        try:
            with closing(self._connect()) as connection:
                _validate_schema(connection)
                return _validate_complete_history(connection)
        except (OSError, sqlite3.Error, ValueError) as exc:
            raise SpotV7ReleaseSelectionStoreErrorV1("STORE_READ_FAILED", str(exc)) from exc

    def select(
        self,
        *,
        candidate: object,
        selector_input_bytes: bytes,
        expected_selector_input_id: bytes,
    ) -> SpotV7ReleaseSelectionResultV1:
        """Attempt one forward candidate selection; every rejection is a no-op."""

        return self._apply(
            candidate=candidate,
            selector_input_bytes=selector_input_bytes,
            expected_selector_input_id=expected_selector_input_id,
            expected_operation=SelectorOperationV1.SELECT,
            revocation_record_bytes=None,
            expected_revocation_record_id=None,
        )

    def revoke(
        self,
        *,
        candidate: object,
        selector_input_bytes: bytes,
        expected_selector_input_id: bytes,
        revocation_record_bytes: bytes,
        expected_revocation_record_id: bytes,
    ) -> SpotV7ReleaseSelectionResultV1:
        """Append one terminal revocation of the exact current candidate."""

        return self._apply(
            candidate=candidate,
            selector_input_bytes=selector_input_bytes,
            expected_selector_input_id=expected_selector_input_id,
            expected_operation=SelectorOperationV1.REVOKE,
            revocation_record_bytes=revocation_record_bytes,
            expected_revocation_record_id=expected_revocation_record_id,
        )

    def _apply(
        self,
        *,
        candidate: object,
        selector_input_bytes: bytes,
        expected_selector_input_id: bytes,
        expected_operation: SelectorOperationV1,
        revocation_record_bytes: bytes | None,
        expected_revocation_record_id: bytes | None,
    ) -> SpotV7ReleaseSelectionResultV1:
        operation = expected_operation
        try:
            selector = parse_exact_governed_release_selector_input_v1(
                selector_input_bytes,
                expected_input_id=expected_selector_input_id,
            )
            if selector.operation is not expected_operation:
                raise _SelectionRejectV1("SELECTOR_OPERATION_MISMATCH")
            facts = _reparse_candidate(candidate, selector)
            revocation = _prepare_revocation(
                selector,
                facts,
                revocation_record_bytes,
                expected_revocation_record_id,
            )
        except (SpotV7SelectorInputRejectV1, SpotV7ReleaseCandidateRejectV1) as exc:
            return self._rejected(operation, f"CANONICAL_INPUT_REJECTED:{exc.code}")
        except _SelectionRejectV1 as exc:
            return self._rejected(operation, exc.code)

        connection: sqlite3.Connection | None = None
        try:
            connection = self._connect()
            connection.execute("BEGIN IMMEDIATE")
            _validate_schema(connection)
            cursor = _validate_complete_history(connection)
            existing = _read_event_by_input_id(connection, selector.input_id)
            if existing is not None:
                result = _resolve_exact_replay(
                    existing,
                    selector=selector,
                    facts=facts,
                    revocation=revocation,
                    cursor=cursor,
                )
                connection.rollback()
                return result
            try:
                next_cursor = _apply_transition(cursor, selector, facts, revocation)
            except _SelectionRejectV1 as exc:
                connection.rollback()
                return _result(
                    ReleaseSelectionDispositionV1.REJECTED,
                    exc.code,
                    selector.operation,
                    selector.input_id,
                    cursor,
                )
            _insert_event(connection, cursor, next_cursor, selector, facts, revocation)
            _cas_meta(connection, cursor, next_cursor)
            connection.commit()
            _fsync_directory(self._path.parent)
            return _result(
                ReleaseSelectionDispositionV1.COMMITTED,
                f"{selector.operation.name}_COMMITTED",
                selector.operation,
                selector.input_id,
                next_cursor,
            )
        except SpotV7ReleaseSelectionStoreErrorV1:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise
        except (OSError, sqlite3.Error, ValueError) as exc:
            if connection is not None and connection.in_transaction:
                connection.rollback()
            raise SpotV7ReleaseSelectionStoreErrorV1("STORE_COMMIT_FAILED", str(exc)) from exc
        finally:
            if connection is not None:
                connection.close()

    def _rejected(
        self,
        operation: SelectorOperationV1,
        code: str,
    ) -> SpotV7ReleaseSelectionResultV1:
        return _result(
            ReleaseSelectionDispositionV1.REJECTED,
            code,
            operation,
            None,
            self.read_cursor(),
        )

    def _connect(self) -> sqlite3.Connection:
        _validate_database_file(self._path)
        return _connect_database(self._path, self._busy_timeout_ms)


def _reparse_candidate(
    candidate: object,
    selector: GovernedReleaseSelectorInputV1,
) -> _CandidateFactsV1:
    """Reparse bytes and compare every nominally exposed derived field."""

    if type(candidate) is not SpotV7ReleaseCandidateManifestV1:
        raise _SelectionRejectV1("CANDIDATE_NOMINAL_TYPE_REJECTED")
    candidate_value = cast(SpotV7ReleaseCandidateManifestV1, candidate)
    try:
        raw = candidate_value.canonical_bytes
        nominal_id = candidate_value.candidate_id
        nominal_inventory_root = candidate_value.evidence_inventory_root
        nominal_revision = candidate_value.release_revision
        nominal_parent = candidate_value.parent_candidate_id
    except (AttributeError, TypeError) as exc:
        raise _SelectionRejectV1("CANDIDATE_NOMINAL_FIELDS_REJECTED") from exc
    checked = check_exact_spot_v7_release_candidate_manifest_v1(
        raw,
        expected_candidate_id=selector.target_candidate_id,
    )
    if (
        nominal_id != checked.candidate_id
        or nominal_inventory_root != checked.evidence_inventory_root
        or nominal_revision != checked.release_revision
        or nominal_parent != checked.parent_candidate_id
        or raw != checked.canonical_bytes
    ):
        raise _SelectionRejectV1("CANDIDATE_NOMINAL_BINDING_MISMATCH")
    candidate_sha256 = hashlib.sha256(raw).digest()
    if candidate_sha256 != selector.target_candidate_sha256:
        raise _SelectionRejectV1("CANDIDATE_CANONICAL_SHA256_MISMATCH")
    document = cast(dict[str, Any], json.loads(raw))
    lineage = cast(dict[str, Any], document["lineage"])
    scope = cast(dict[str, Any], document["scope"])
    release_scope = {
        "application_id": scope["application_id"],
        "chain_id": scope["chain_id"],
        "domain_id": scope["domain_id"],
        "release_profile": scope["release_profile"],
    }
    facts = _CandidateFactsV1(
        canonical_bytes=raw,
        candidate_id=checked.candidate_id,
        candidate_sha256=candidate_sha256,
        release_revision=checked.release_revision,
        parent_candidate_id=checked.parent_candidate_id,
        activation_epoch=cast(int, lineage["proposed_activation_epoch"]),
        expiration_epoch=cast(int | None, lineage["proposed_expiration_epoch"]),
        revocation_policy_root=bytes.fromhex(cast(str, lineage["revocation_policy_root"])),
        rollback_policy_root=bytes.fromhex(cast(str, lineage["rollback_policy_root"])),
        scope_id=_domain_hash(
            _SCOPE_ID_DOMAIN_V1,
            canonical_document_bytes_v1(release_scope),
        ),
    )
    if selector.target_release_revision != facts.release_revision:
        raise _SelectionRejectV1("CANDIDATE_RELEASE_REVISION_MISMATCH")
    if selector.rollback_policy_root != facts.rollback_policy_root:
        raise _SelectionRejectV1("ROLLBACK_POLICY_ROOT_MISMATCH")
    return facts


def _prepare_revocation(
    selector: GovernedReleaseSelectorInputV1,
    facts: _CandidateFactsV1,
    raw: bytes | None,
    expected_record_id: bytes | None,
) -> SpotV7RevocationRecordV1 | None:
    if selector.operation is SelectorOperationV1.SELECT:
        if raw is not None or expected_record_id is not None:
            raise _SelectionRejectV1("SELECT_REVOCATION_RECORD_FORBIDDEN")
        return None
    if raw is None or expected_record_id is None:
        raise _SelectionRejectV1("REVOKE_REVOCATION_RECORD_REQUIRED")
    record = parse_exact_spot_v7_revocation_record_v1(
        raw,
        expected_record_id=expected_record_id,
    )
    if selector.revocation_record_id != record.record_id:
        raise _SelectionRejectV1("REVOCATION_RECORD_INPUT_BINDING_MISMATCH")
    if record.candidate_id != facts.candidate_id:
        raise _SelectionRejectV1("REVOCATION_CANDIDATE_MISMATCH")
    if record.revocation_policy_root != facts.revocation_policy_root:
        raise _SelectionRejectV1("REVOCATION_POLICY_ROOT_MISMATCH")
    if record.revocation_registry_root != selector.revocation_registry_root:
        raise _SelectionRejectV1("REVOCATION_REGISTRY_ROOT_MISMATCH")
    if record.effective_epoch > selector.evaluation_epoch:
        raise _SelectionRejectV1("FUTURE_REVOCATION_REJECTED")
    return record


def _apply_transition(
    cursor: SpotV7ReleaseSelectionCursorV1,
    selector: GovernedReleaseSelectorInputV1,
    facts: _CandidateFactsV1,
    revocation: SpotV7RevocationRecordV1 | None,
) -> SpotV7ReleaseSelectionCursorV1:
    if cursor.current_revoked:
        code = (
            "REVOCATION_CONFLICT"
            if selector.operation is SelectorOperationV1.REVOKE
            else "CURRENT_HEAD_REVOKED"
        )
        raise _SelectionRejectV1(code)
    if (
        cursor.last_evaluation_epoch is not None
        and selector.evaluation_epoch < cursor.last_evaluation_epoch
    ):
        raise _SelectionRejectV1("EVALUATION_EPOCH_ROLLBACK_REJECTED")
    if selector.operation is SelectorOperationV1.SELECT:
        _validate_select_relation(cursor, selector, facts)
    else:
        _validate_revoke_relation(cursor, selector, facts, revocation)
    _validate_exact_cas(cursor, selector)
    next_revision = cursor.database_revision + 1
    if next_revision > MAX_SELECTION_EVENTS_V1:
        raise _SelectionRejectV1("EVENT_LIMIT_REACHED")
    record_id = None if revocation is None else revocation.record_id
    next_root = _event_state_root(
        cursor.state_root,
        next_revision,
        selector.input_id,
        facts.candidate_id,
        facts.candidate_sha256,
        record_id,
    )
    if selector.operation is SelectorOperationV1.SELECT:
        return SpotV7ReleaseSelectionCursorV1(
            database_revision=next_revision,
            state_root=next_root,
            last_evaluation_epoch=selector.evaluation_epoch,
            current_candidate_id=facts.candidate_id,
            current_candidate_sha256=facts.candidate_sha256,
            current_release_revision=facts.release_revision,
            current_select_input_id=selector.input_id,
            current_scope_id=facts.scope_id,
            current_revoked=False,
            current_revocation_record_id=None,
        )
    return SpotV7ReleaseSelectionCursorV1(
        database_revision=next_revision,
        state_root=next_root,
        last_evaluation_epoch=selector.evaluation_epoch,
        current_candidate_id=cursor.current_candidate_id,
        current_candidate_sha256=cursor.current_candidate_sha256,
        current_release_revision=cursor.current_release_revision,
        current_select_input_id=cursor.current_select_input_id,
        current_scope_id=cursor.current_scope_id,
        current_revoked=True,
        current_revocation_record_id=record_id,
    )


def _validate_select_relation(
    cursor: SpotV7ReleaseSelectionCursorV1,
    selector: GovernedReleaseSelectorInputV1,
    facts: _CandidateFactsV1,
) -> None:
    if selector.evaluation_epoch < facts.activation_epoch:
        raise _SelectionRejectV1("CANDIDATE_NOT_ACTIVE")
    if facts.expiration_epoch is not None and selector.evaluation_epoch >= facts.expiration_epoch:
        raise _SelectionRejectV1("CANDIDATE_EXPIRED")
    current_revision = cursor.current_release_revision
    if current_revision is None:
        if facts.release_revision != 1:
            raise _SelectionRejectV1("RELEASE_REVISION_GAP")
        if facts.parent_candidate_id is not None:
            raise _SelectionRejectV1("GENESIS_PARENT_REJECTED")
        return
    if facts.scope_id != cursor.current_scope_id:
        raise _SelectionRejectV1("RELEASE_SCOPE_FORK_REJECTED")
    if facts.release_revision < current_revision:
        raise _SelectionRejectV1("RELEASE_ROLLBACK_REJECTED")
    if facts.release_revision == current_revision:
        code = (
            "RELEASE_REPLAY_CONFLICT"
            if facts.candidate_id == cursor.current_candidate_id
            else "RELEASE_FORK_REJECTED"
        )
        raise _SelectionRejectV1(code)
    if facts.release_revision != current_revision + 1:
        raise _SelectionRejectV1("RELEASE_REVISION_GAP")
    if facts.parent_candidate_id != cursor.current_candidate_id:
        raise _SelectionRejectV1("RELEASE_FORK_REJECTED")


def _validate_revoke_relation(
    cursor: SpotV7ReleaseSelectionCursorV1,
    selector: GovernedReleaseSelectorInputV1,
    facts: _CandidateFactsV1,
    revocation: SpotV7RevocationRecordV1 | None,
) -> None:
    if cursor.current_candidate_id is None or cursor.current_release_revision is None:
        raise _SelectionRejectV1("REVOCATION_WITHOUT_CURRENT_HEAD")
    if facts.candidate_id != cursor.current_candidate_id:
        raise _SelectionRejectV1("REVOCATION_NONCURRENT_CANDIDATE")
    if facts.candidate_sha256 != cursor.current_candidate_sha256:
        raise _SelectionRejectV1("REVOCATION_CANDIDATE_BYTES_MISMATCH")
    if facts.release_revision != cursor.current_release_revision:
        raise _SelectionRejectV1("REVOCATION_RELEASE_REVISION_MISMATCH")
    if facts.scope_id != cursor.current_scope_id:
        raise _SelectionRejectV1("REVOCATION_SCOPE_MISMATCH")
    if revocation is None or selector.revocation_record_id != revocation.record_id:
        raise _SelectionRejectV1("REVOCATION_RECORD_REQUIRED")


def _validate_exact_cas(
    cursor: SpotV7ReleaseSelectionCursorV1,
    selector: GovernedReleaseSelectorInputV1,
) -> None:
    if selector.expected_database_revision != cursor.database_revision:
        raise _SelectionRejectV1("DATABASE_REVISION_CAS_MISMATCH")
    if selector.expected_current_candidate_id != cursor.current_candidate_id:
        raise _SelectionRejectV1("CURRENT_CANDIDATE_CAS_MISMATCH")
    if selector.expected_current_select_input_id != cursor.current_select_input_id:
        raise _SelectionRejectV1("CURRENT_SELECTION_CAS_MISMATCH")


def _resolve_exact_replay(
    row: sqlite3.Row,
    *,
    selector: GovernedReleaseSelectorInputV1,
    facts: _CandidateFactsV1,
    revocation: SpotV7RevocationRecordV1 | None,
    cursor: SpotV7ReleaseSelectionCursorV1,
) -> SpotV7ReleaseSelectionResultV1:
    record_bytes = None if revocation is None else revocation.canonical_bytes
    expected_values = (
        int(selector.operation),
        selector.canonical_bytes,
        facts.candidate_id,
        facts.candidate_sha256,
        facts.canonical_bytes,
        None if revocation is None else revocation.record_id,
        record_bytes,
    )
    observed_values = (
        int(row["operation"]),
        bytes(row["input_bytes"]),
        bytes(row["candidate_id"]),
        bytes(row["candidate_sha256"]),
        bytes(row["candidate_bytes"]),
        _optional_blob(row["revocation_record_id"]),
        _optional_blob(row["revocation_record_bytes"]),
    )
    if observed_values != expected_values:
        raise ValueError("stored selector input identity collision or corruption")
    return _result(
        ReleaseSelectionDispositionV1.IDEMPOTENT,
        "EXACT_REPLAY",
        selector.operation,
        selector.input_id,
        cursor,
    )


def _insert_event(
    connection: sqlite3.Connection,
    previous: SpotV7ReleaseSelectionCursorV1,
    result: SpotV7ReleaseSelectionCursorV1,
    selector: GovernedReleaseSelectorInputV1,
    facts: _CandidateFactsV1,
    revocation: SpotV7RevocationRecordV1 | None,
) -> None:
    connection.execute(
        """
        INSERT INTO spot_v7_release_selection_events (
            event_revision_be, operation, input_id, input_bytes, candidate_id,
            candidate_sha256, candidate_bytes, release_revision_be,
            evaluation_epoch_be, expected_database_revision_be,
            expected_current_candidate_id, expected_current_select_input_id,
            rollback_policy_root, revocation_registry_root,
            revocation_record_id, revocation_record_bytes, scope_id,
            previous_state_root, result_state_root, release_authority,
            settlement_authority, runtime_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0)
        """,
        (
            _u64be(result.database_revision),
            int(selector.operation),
            selector.input_id,
            selector.canonical_bytes,
            facts.candidate_id,
            facts.candidate_sha256,
            facts.canonical_bytes,
            _u64be(facts.release_revision),
            _u64be(selector.evaluation_epoch),
            _u64be(selector.expected_database_revision),
            selector.expected_current_candidate_id,
            selector.expected_current_select_input_id,
            selector.rollback_policy_root,
            selector.revocation_registry_root,
            None if revocation is None else revocation.record_id,
            None if revocation is None else revocation.canonical_bytes,
            facts.scope_id,
            previous.state_root,
            result.state_root,
        ),
    )


def _cas_meta(
    connection: sqlite3.Connection,
    previous: SpotV7ReleaseSelectionCursorV1,
    result: SpotV7ReleaseSelectionCursorV1,
) -> None:
    cursor = connection.execute(
        """
        UPDATE spot_v7_release_selection_meta
        SET database_revision_be = ?, state_root = ?, event_count = ?,
            last_evaluation_epoch_be = ?,
            current_candidate_id = ?, current_candidate_sha256 = ?,
            current_release_revision_be = ?, current_select_input_id = ?,
            current_scope_id = ?, current_revoked = ?,
            current_revocation_record_id = ?
        WHERE singleton = 1 AND database_revision_be = ? AND state_root = ?
        """,
        (
            _u64be(result.database_revision),
            result.state_root,
            result.database_revision,
            _optional_u64be(result.last_evaluation_epoch),
            result.current_candidate_id,
            result.current_candidate_sha256,
            _optional_u64be(result.current_release_revision),
            result.current_select_input_id,
            result.current_scope_id,
            int(result.current_revoked),
            result.current_revocation_record_id,
            _u64be(previous.database_revision),
            previous.state_root,
        ),
    )
    if cursor.rowcount != 1:
        raise ValueError("release selection metadata CAS failed")


def _validate_complete_history(
    connection: sqlite3.Connection,
) -> SpotV7ReleaseSelectionCursorV1:
    _validate_database_integrity(connection)
    meta = _read_meta(connection)
    cursor = _genesis_cursor()
    rows = connection.execute(
        "SELECT * FROM spot_v7_release_selection_events ORDER BY event_revision_be"
    ).fetchall()
    if len(rows) > MAX_SELECTION_EVENTS_V1:
        raise ValueError("release selection event count exceeds maximum")
    for expected_revision, row in enumerate(rows, start=1):
        cursor = _replay_history_row(row, cursor, expected_revision)
    if int(meta["event_count"]) != len(rows):
        raise ValueError("release selection metadata event count mismatch")
    if _cursor_storage_values(cursor) != _meta_storage_values(meta):
        raise ValueError("release selection metadata disagrees with replayed history")
    return cursor


def _replay_history_row(
    row: sqlite3.Row,
    cursor: SpotV7ReleaseSelectionCursorV1,
    expected_revision: int,
) -> SpotV7ReleaseSelectionCursorV1:
    if bytes(row["event_revision_be"]) != _u64be(expected_revision):
        raise ValueError("release selection event revisions are not contiguous")
    input_bytes = bytes(row["input_bytes"])
    input_id = bytes(row["input_id"])
    selector = parse_exact_governed_release_selector_input_v1(
        input_bytes,
        expected_input_id=input_id,
    )
    candidate_id = bytes(row["candidate_id"])
    candidate_bytes = bytes(row["candidate_bytes"])
    candidate_sha256 = bytes(row["candidate_sha256"])
    nominal = check_exact_spot_v7_release_candidate_manifest_v1(
        candidate_bytes,
        expected_candidate_id=candidate_id,
    )
    facts = _reparse_candidate(nominal, selector)
    if facts.candidate_sha256 != candidate_sha256:
        raise ValueError("stored candidate SHA-256 mismatch")
    record_id = _optional_blob(row["revocation_record_id"])
    record_bytes = _optional_blob(row["revocation_record_bytes"])
    revocation = _prepare_revocation(selector, facts, record_bytes, record_id)
    expected_row = (
        int(selector.operation),
        _u64be(facts.release_revision),
        _u64be(selector.evaluation_epoch),
        _u64be(selector.expected_database_revision),
        selector.expected_current_candidate_id,
        selector.expected_current_select_input_id,
        selector.rollback_policy_root,
        selector.revocation_registry_root,
        facts.scope_id,
        cursor.state_root,
        0,
        0,
        0,
        0,
    )
    observed_row = (
        int(row["operation"]),
        bytes(row["release_revision_be"]),
        bytes(row["evaluation_epoch_be"]),
        bytes(row["expected_database_revision_be"]),
        _optional_blob(row["expected_current_candidate_id"]),
        _optional_blob(row["expected_current_select_input_id"]),
        bytes(row["rollback_policy_root"]),
        bytes(row["revocation_registry_root"]),
        bytes(row["scope_id"]),
        bytes(row["previous_state_root"]),
        int(row["release_authority"]),
        int(row["settlement_authority"]),
        int(row["runtime_authority"]),
        int(row["production_authority"]),
    )
    if observed_row != expected_row:
        raise ValueError("stored release selection event binding mismatch")
    result = _apply_transition(cursor, selector, facts, revocation)
    if result.database_revision != expected_revision:
        raise ValueError("replayed release selection revision mismatch")
    if bytes(row["result_state_root"]) != result.state_root:
        raise ValueError("stored release selection result root mismatch")
    return result


def _initialize_or_validate(connection: sqlite3.Connection) -> None:
    if not connection.in_transaction:
        raise ValueError("release selection initialization requires a transaction")
    existing = connection.execute(
        "SELECT name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%'"
    ).fetchall()
    if not existing:
        if int(connection.execute("PRAGMA application_id").fetchone()[0]) != 0:
            raise ValueError("empty release selection database has an application_id")
        if int(connection.execute("PRAGMA user_version").fetchone()[0]) != 0:
            raise ValueError("empty release selection database has a user_version")
        connection.execute(f"PRAGMA application_id = {STORE_APPLICATION_ID_V1}")
        connection.execute(f"PRAGMA user_version = {STORE_SCHEMA_VERSION_V1}")
        for statement in _SCHEMA_STATEMENTS_V1:
            connection.execute(statement)
        connection.execute(
            """
            INSERT INTO spot_v7_release_selection_meta (
                singleton, schema_version, database_revision_be, state_root,
                event_count, last_evaluation_epoch_be, current_candidate_id,
                current_candidate_sha256,
                current_release_revision_be, current_select_input_id,
                current_scope_id, current_revoked,
                current_revocation_record_id
            ) VALUES (1, 1, ?, ?, 0, NULL, NULL, NULL, NULL, NULL, NULL, 0, NULL)
            """,
            (_u64be(0), GENESIS_SELECTION_STATE_ROOT_V1),
        )
    _validate_schema(connection)
    _validate_complete_history(connection)


def _validate_schema(connection: sqlite3.Connection) -> None:
    if int(connection.execute("PRAGMA application_id").fetchone()[0]) != STORE_APPLICATION_ID_V1:
        raise ValueError("release selection application_id mismatch")
    if int(connection.execute("PRAGMA user_version").fetchone()[0]) != STORE_SCHEMA_VERSION_V1:
        raise ValueError("release selection user_version mismatch")
    rows = connection.execute(
        """
        SELECT type, name, sql FROM sqlite_master
        WHERE name NOT LIKE 'sqlite_%'
        ORDER BY type, name
        """
    ).fetchall()
    observed = {(str(row["type"]), str(row["name"])) for row in rows}
    expected = {("table", name) for name in _EXPECTED_SCHEMA_SQL_V1}
    if observed != expected:
        raise ValueError("release selection schema object set mismatch")
    for row in rows:
        name = str(row["name"])
        if _normalize_sql(str(row["sql"])) != _normalize_sql(_EXPECTED_SCHEMA_SQL_V1[name]):
            raise ValueError(f"release selection schema SQL mismatch for {name}")


def _validate_database_integrity(connection: sqlite3.Connection) -> None:
    quick = connection.execute("PRAGMA quick_check").fetchall()
    if len(quick) != 1 or quick[0][0] != "ok":
        raise ValueError("release selection quick_check failed")
    if connection.execute("PRAGMA foreign_key_check").fetchone() is not None:
        raise ValueError("release selection foreign_key_check failed")


def _read_meta(connection: sqlite3.Connection) -> sqlite3.Row:
    row = connection.execute(
        "SELECT * FROM spot_v7_release_selection_meta WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise ValueError("release selection metadata row missing")
    return row


def _read_event_by_input_id(
    connection: sqlite3.Connection,
    input_id: bytes,
) -> sqlite3.Row | None:
    return connection.execute(
        "SELECT * FROM spot_v7_release_selection_events WHERE input_id = ?",
        (input_id,),
    ).fetchone()


def _genesis_cursor() -> SpotV7ReleaseSelectionCursorV1:
    return SpotV7ReleaseSelectionCursorV1(
        database_revision=0,
        state_root=GENESIS_SELECTION_STATE_ROOT_V1,
        last_evaluation_epoch=None,
        current_candidate_id=None,
        current_candidate_sha256=None,
        current_release_revision=None,
        current_select_input_id=None,
        current_scope_id=None,
        current_revoked=False,
        current_revocation_record_id=None,
    )


def _cursor_storage_values(cursor: SpotV7ReleaseSelectionCursorV1) -> tuple[object, ...]:
    return (
        _u64be(cursor.database_revision),
        cursor.state_root,
        cursor.database_revision,
        _optional_u64be(cursor.last_evaluation_epoch),
        cursor.current_candidate_id,
        cursor.current_candidate_sha256,
        _optional_u64be(cursor.current_release_revision),
        cursor.current_select_input_id,
        cursor.current_scope_id,
        int(cursor.current_revoked),
        cursor.current_revocation_record_id,
    )


def _meta_storage_values(row: sqlite3.Row) -> tuple[object, ...]:
    return (
        bytes(row["database_revision_be"]),
        bytes(row["state_root"]),
        int(row["event_count"]),
        _optional_blob(row["last_evaluation_epoch_be"]),
        _optional_blob(row["current_candidate_id"]),
        _optional_blob(row["current_candidate_sha256"]),
        _optional_blob(row["current_release_revision_be"]),
        _optional_blob(row["current_select_input_id"]),
        _optional_blob(row["current_scope_id"]),
        int(row["current_revoked"]),
        _optional_blob(row["current_revocation_record_id"]),
    )


def _event_state_root(
    previous: bytes,
    revision: int,
    input_id: bytes,
    candidate_id: bytes,
    candidate_sha256: bytes,
    revocation_record_id: bytes | None,
) -> bytes:
    payload = (
        previous
        + _u64be(revision)
        + input_id
        + candidate_id
        + candidate_sha256
        + (ZERO_DIGEST_V1 if revocation_record_id is None else revocation_record_id)
    )
    return _domain_hash(_EVENT_STATE_DOMAIN_V1, payload)


def _result(
    disposition: ReleaseSelectionDispositionV1,
    code: str,
    operation: SelectorOperationV1,
    input_id: bytes | None,
    cursor: SpotV7ReleaseSelectionCursorV1,
) -> SpotV7ReleaseSelectionResultV1:
    return SpotV7ReleaseSelectionResultV1(
        disposition=disposition,
        code=code,
        operation=operation,
        input_id=input_id,
        cursor=cursor,
    )


def _connect_database(path: Path, busy_timeout_ms: int) -> sqlite3.Connection:
    timeout_seconds = max(1, (busy_timeout_ms + 999) // 1_000)
    connection = sqlite3.connect(path, timeout=timeout_seconds, isolation_level=None)
    try:
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys = ON")
        mode = str(connection.execute("PRAGMA journal_mode = DELETE").fetchone()[0]).lower()
        if mode != "delete":
            raise ValueError("release selection journal_mode must be DELETE")
        connection.execute("PRAGMA synchronous = EXTRA")
        connection.execute(f"PRAGMA busy_timeout = {busy_timeout_ms}")
        connection.execute("PRAGMA trusted_schema = OFF")
        connection.execute("PRAGMA temp_store = MEMORY")
        if int(connection.execute("PRAGMA foreign_keys").fetchone()[0]) != 1:
            raise ValueError("release selection foreign_keys must be enabled")
        if int(connection.execute("PRAGMA synchronous").fetchone()[0]) != 3:
            raise ValueError("release selection synchronous must be EXTRA")
        if int(connection.execute("PRAGMA trusted_schema").fetchone()[0]) != 0:
            raise ValueError("release selection trusted_schema must be disabled")
        if int(connection.execute("PRAGMA busy_timeout").fetchone()[0]) != busy_timeout_ms:
            raise ValueError("release selection busy_timeout mismatch")
    except (sqlite3.Error, ValueError):
        connection.close()
        raise
    return connection


def _validate_store_path(path: Path, busy_timeout_ms: int) -> None:
    if not isinstance(path, Path):
        raise TypeError("release selection path must be pathlib.Path")
    if not path.is_absolute():
        raise ValueError("release selection path must be absolute")
    if path.resolve(strict=False) != path:
        raise ValueError("release selection path must be canonical and symlink-free")
    if type(busy_timeout_ms) is not int or not 1 <= busy_timeout_ms <= MAX_BUSY_TIMEOUT_MS_V1:
        raise ValueError("release selection busy_timeout_ms is out of range")
    parent = path.parent
    parent_stat = parent.stat(follow_symlinks=False)
    if not stat.S_ISDIR(parent_stat.st_mode):
        raise ValueError("release selection parent is not a directory")
    if parent_stat.st_uid != os.getuid() or stat.S_IMODE(parent_stat.st_mode) & 0o077:
        raise ValueError("release selection parent must be private and owned by this uid")


def _create_private_database_file(path: Path) -> bool:
    flags = os.O_RDWR | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError:
        _validate_database_file(path)
        return False
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    _validate_database_file(path)
    return True


def _validate_database_file(path: Path) -> None:
    file_stat = path.stat(follow_symlinks=False)
    if not stat.S_ISREG(file_stat.st_mode):
        raise ValueError("release selection database is not a regular file")
    if file_stat.st_uid != os.getuid() or stat.S_IMODE(file_stat.st_mode) != 0o600:
        raise ValueError("release selection database must be private and owned by this uid")


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(
        path,
        os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _u64be(value: int) -> bytes:
    if type(value) is not int or not 0 <= value <= 0xFFFF_FFFF_FFFF_FFFF:
        raise ValueError("release selection u64 is out of range")
    return value.to_bytes(8, "big")


def _optional_u64be(value: int | None) -> bytes | None:
    return None if value is None else _u64be(value)


def _optional_blob(value: object) -> bytes | None:
    if value is None:
        return None
    if type(value) is not bytes:
        raise ValueError("release selection stored value is not a blob")
    return value


def _domain_hash(domain: bytes, payload: bytes) -> bytes:
    return hashlib.sha256(
        len(domain).to_bytes(2, "big") + domain + len(payload).to_bytes(8, "big") + payload
    ).digest()


def _normalize_sql(value: str) -> str:
    return " ".join(value.strip().removesuffix(";").split())
