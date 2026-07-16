"""Unified, transaction-bound Spot V7 release history mechanics.

This module owns the release tables that a later V7 economic store will use in
the same ``BEGIN IMMEDIATE`` transaction as settlement.  It replays every
retained SELECT or REVOKE quorum artifact before exposing a private current-head
projection.  Canonical watermark observations remain authority-neutral until a
separate protocol adapter authenticates an externally monotonic anchor.
"""

from __future__ import annotations

import hashlib
import sqlite3
from dataclasses import dataclass
from typing import Final, NoReturn, SupportsIndex, final

from src.integration import zrpf_spot_v7_authenticated_release_revocation_v1 as revoke_auth
from src.integration import zrpf_spot_v7_authenticated_release_selection_v1 as select_auth
from src.integration._zrpf_spot_v7_release_state_schema_v7 import (
    SPOT_V7_RELEASE_STATE_SCHEMA_VERSION_V7,
    SPOT_V7_RETIRED_SOURCE_USER_VERSION_V7,
    _install_spot_v7_release_schema_v7,
    _validate_spot_v7_release_schema_v7,
)
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_highest_observed_release_event_watermark_v1 as watermark_v1
from tools import zrpf_spot_v7_release_state_checkpoint_v1 as checkpoint_v1

MAX_U64_V7: Final = (1 << 64) - 1
_CUTOVER_ID_DOMAIN_V7: Final = b"zenodex.zrpf.spot_v7.release_cutover.v7\x00"


class SpotV7ReleaseStateEngineRejectV7(ValueError):
    """Stable fail-closed rejection from the unified release engine."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


def _reject(code: str, detail: str) -> SpotV7ReleaseStateEngineRejectV7:
    return SpotV7ReleaseStateEngineRejectV7(code, detail)


@dataclass(frozen=True, slots=True)
class _ReplayedReleaseHistoryV7:
    cursors: tuple[store_v3.SpotV7AuthenticatedReleaseStateCursorV3, ...]
    rows: tuple[sqlite3.Row, ...]
    checkpoint_bytes: bytes

    @property
    def cursor(self) -> store_v3.SpotV7AuthenticatedReleaseStateCursorV3:
        return self.cursors[-1]


class _CutoverResultSealV7:
    __slots__ = ()


_CUTOVER_RESULT_SEAL_V7: Final = _CutoverResultSealV7()


@final
class _AuthorityNeutralSpotV7ReleaseCutoverV7:
    """Opaque proof that one local V3 history was atomically moved and retired."""

    __slots__ = (
        "_cutover_id",
        "_database_revision",
        "_external_anchor_commitment",
        "_external_anchor_position",
        "_release_state_root",
        "_source_store_identity_sha256",
    )
    _cutover_id: bytes
    _database_revision: int
    _external_anchor_commitment: bytes
    _external_anchor_position: int
    _release_state_root: bytes
    _source_store_identity_sha256: bytes

    def __new__(cls) -> _AuthorityNeutralSpotV7ReleaseCutoverV7:
        raise TypeError("release cutover result requires the module-private seal")

    @classmethod
    def _from_locked_cutover(
        cls,
        *,
        cutover_id: bytes,
        source_store_identity_sha256: bytes,
        database_revision: int,
        release_state_root: bytes,
        external_anchor_position: int,
        external_anchor_commitment: bytes,
        seal: _CutoverResultSealV7,
    ) -> _AuthorityNeutralSpotV7ReleaseCutoverV7:
        if seal is not _CUTOVER_RESULT_SEAL_V7:
            raise TypeError("release cutover result requires the module-private seal")
        value = object.__new__(cls)
        object.__setattr__(value, "_cutover_id", _require_digest(cutover_id, "cutover_id"))
        object.__setattr__(
            value,
            "_source_store_identity_sha256",
            _require_digest(source_store_identity_sha256, "source_store_identity_sha256"),
        )
        object.__setattr__(
            value,
            "_database_revision",
            _require_u64(database_revision, "database_revision"),
        )
        object.__setattr__(
            value,
            "_release_state_root",
            _require_digest(release_state_root, "release_state_root"),
        )
        object.__setattr__(
            value,
            "_external_anchor_position",
            _require_u64(external_anchor_position, "external_anchor_position"),
        )
        object.__setattr__(
            value,
            "_external_anchor_commitment",
            _require_digest(external_anchor_commitment, "external_anchor_commitment"),
        )
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("release cutover result cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("release cutover result is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("release cutover result is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("release cutover result cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("release cutover result cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("release cutover result cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("release cutover result cannot be serialized")

    @property
    def cutover_id(self) -> bytes:
        return self._cutover_id

    @property
    def database_revision(self) -> int:
        return self._database_revision

    @property
    def release_state_root(self) -> bytes:
        return self._release_state_root

    @property
    def old_store_retired(self) -> bool:
        return True

    @property
    def new_release_writer_active(self) -> bool:
        return True

    @property
    def external_monotonic_anchor_authenticated(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


class _CurrentReleaseSealV7:
    __slots__ = ()


_CURRENT_RELEASE_SEAL_V7: Final = _CurrentReleaseSealV7()


@final
class _TransactionBoundSpotV7CurrentReleaseV7:
    """Private current release tied to one still-open SQLite transaction."""

    __slots__ = (
        "_connection",
        "_current_candidate_bytes",
        "_current_candidate_id",
        "_current_candidate_sha256",
        "_current_release_revision",
        "_current_select_input_id",
        "_database_revision",
        "_external_anchor_commitment",
        "_external_anchor_position",
        "_release_state_root",
        "_store_identity_sha256",
    )
    _connection: sqlite3.Connection
    _current_candidate_bytes: bytes
    _current_candidate_id: bytes
    _current_candidate_sha256: bytes
    _current_release_revision: int
    _current_select_input_id: bytes
    _database_revision: int
    _external_anchor_commitment: bytes
    _external_anchor_position: int
    _release_state_root: bytes
    _store_identity_sha256: bytes

    def __new__(cls) -> _TransactionBoundSpotV7CurrentReleaseV7:
        raise TypeError("transaction-bound release requires verified locked construction")

    @classmethod
    def _from_locked_history(
        cls,
        *,
        connection: sqlite3.Connection,
        identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
        cursor: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
        candidate_bytes: bytes,
        external_anchor_position: int,
        external_anchor_commitment: bytes,
        seal: _CurrentReleaseSealV7,
    ) -> _TransactionBoundSpotV7CurrentReleaseV7:
        if seal is not _CURRENT_RELEASE_SEAL_V7:
            raise TypeError("transaction-bound release requires the module-private seal")
        if type(connection) is not sqlite3.Connection or not connection.in_transaction:
            raise ValueError("transaction-bound release requires an open transaction")
        candidate_id = _require_digest(cursor.current_candidate_id, "current_candidate_id")
        candidate_sha = _require_digest(
            cursor.current_candidate_sha256,
            "current_candidate_sha256",
        )
        release_revision = _require_positive_u64(
            cursor.current_release_revision,
            "current_release_revision",
        )
        select_input_id = _require_digest(
            cursor.current_select_input_id,
            "current_select_input_id",
        )
        if cursor.current_revoked or cursor.current_revocation_record_id is not None:
            raise ValueError("transaction-bound release must be nonrevoked")
        if type(candidate_bytes) is not bytes or not candidate_bytes:
            raise TypeError("current candidate bytes must be nonempty exact bytes")
        if hashlib.sha256(candidate_bytes).digest() != candidate_sha:
            raise ValueError("current candidate bytes differ from the replayed SHA-256")
        value = object.__new__(cls)
        object.__setattr__(value, "_connection", connection)
        object.__setattr__(value, "_store_identity_sha256", identity.identity_sha256)
        object.__setattr__(value, "_database_revision", cursor.database_revision)
        object.__setattr__(value, "_release_state_root", cursor.state_root)
        object.__setattr__(value, "_current_candidate_id", candidate_id)
        object.__setattr__(value, "_current_candidate_sha256", candidate_sha)
        object.__setattr__(value, "_current_release_revision", release_revision)
        object.__setattr__(value, "_current_select_input_id", select_input_id)
        object.__setattr__(value, "_current_candidate_bytes", candidate_bytes)
        object.__setattr__(value, "_external_anchor_position", external_anchor_position)
        object.__setattr__(value, "_external_anchor_commitment", external_anchor_commitment)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("transaction-bound release cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("transaction-bound release is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("transaction-bound release is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("transaction-bound release cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("transaction-bound release cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("transaction-bound release cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("transaction-bound release cannot be serialized")

    @property
    def database_revision(self) -> int:
        return self._database_revision

    @property
    def release_state_root(self) -> bytes:
        return self._release_state_root

    @property
    def current_candidate_id(self) -> bytes:
        return self._current_candidate_id

    @property
    def current_candidate_sha256(self) -> bytes:
        return self._current_candidate_sha256

    @property
    def current_release_revision(self) -> int:
        return self._current_release_revision

    @property
    def current_select_input_id(self) -> bytes:
        return self._current_select_input_id

    @property
    def current_candidate_bytes(self) -> bytes:
        return self._current_candidate_bytes

    @property
    def release_and_settlement_share_write_transaction(self) -> bool:
        return self._connection.in_transaction

    @property
    def external_monotonic_anchor_authenticated(self) -> bool:
        return False

    @property
    def currentness_at_settlement_verified(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _cutover_attached_v3_history_locked_v7(
    connection: sqlite3.Connection,
    *,
    source_alias: str,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    exact_watermark_bytes: bytes,
) -> _AuthorityNeutralSpotV7ReleaseCutoverV7:
    """Replay, import, and retire one attached V3 store in the current transaction."""

    _require_locked_connection(connection)
    if source_alias != "source_v3":
        raise ValueError("release cutover accepts only the fixed source_v3 alias")
    if type(identity) is not store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3:
        raise TypeError("release cutover requires the exact Store V3 identity")
    if type(exact_watermark_bytes) is not bytes:
        raise TypeError("release cutover watermark must be exact bytes")
    _install_spot_v7_release_schema_v7(connection)
    history = _replay_attached_v3_history_locked(connection, identity=identity)
    cursor = history.cursor
    if cursor.database_revision == 0:
        raise _reject("CUTOVER_EMPTY_RELEASE", "release cutover requires a selected release")
    if cursor.current_revoked:
        raise _reject("CUTOVER_REVOKED_RELEASE", "release cutover requires a nonrevoked head")
    watermark, assessment = _assess_head_watermark(
        history.checkpoint_bytes,
        exact_watermark_bytes,
    )
    cutover_id = _cutover_id(
        identity=identity,
        checkpoint_bytes=history.checkpoint_bytes,
        watermark_bytes=exact_watermark_bytes,
    )
    _insert_cutover(
        connection,
        identity=identity,
        history=history,
        watermark=watermark,
        assessment=assessment,
        cutover_id=cutover_id,
    )
    connection.execute(
        f"PRAGMA {source_alias}.user_version = {SPOT_V7_RETIRED_SOURCE_USER_VERSION_V7}"
    )
    retired = int(connection.execute(f"PRAGMA {source_alias}.user_version").fetchone()[0])
    if retired != SPOT_V7_RETIRED_SOURCE_USER_VERSION_V7:
        raise _reject("SOURCE_RETIREMENT_FAILED", "source Store V3 did not enter retirement")
    _validate_complete_release_history_locked_v7(connection, identity=identity)
    return _AuthorityNeutralSpotV7ReleaseCutoverV7._from_locked_cutover(
        cutover_id=cutover_id,
        source_store_identity_sha256=identity.identity_sha256,
        database_revision=cursor.database_revision,
        release_state_root=cursor.state_root,
        external_anchor_position=watermark.external_position,
        external_anchor_commitment=bytes.fromhex(watermark.external_backend_commitment),
        seal=_CUTOVER_RESULT_SEAL_V7,
    )


def _apply_authenticated_release_event_locked_v7(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    capability: (
        select_auth._AuthenticatedSpotV7ReleaseSelectionV1
        | revoke_auth._AuthenticatedSpotV7ReleaseRevocationV1
    ),
) -> store_v3.SpotV7AuthenticatedReleaseStateCursorV3:
    """Append one authenticated event without committing the caller's transaction."""

    _require_locked_connection(connection)
    cursor = _validate_complete_release_history_locked_v7(connection, identity=identity)
    try:
        artifacts = store_v3._prepare_capability(capability)
        store_v3._require_store_identity_matches_artifacts(identity, artifacts)
        next_cursor = store_v3._apply_transition(cursor, artifacts)
    except TypeError:
        raise
    except ValueError as exc:
        code = getattr(exc, "code", "AUTHENTICATED_RELEASE_EVENT_REJECTED")
        raise _reject(str(code), str(exc)) from exc
    existing = connection.execute(
        "SELECT 1 FROM spot_v7_release_events_v7 WHERE selector_input_id = ?",
        (artifacts.selector_input_id,),
    ).fetchone()
    if existing is not None:
        raise _reject("RELEASE_EVENT_REPLAY", "selector input was already committed")
    _insert_event_row(
        connection,
        previous=cursor,
        result=next_cursor,
        artifacts=artifacts,
        identity=identity,
        origin="NATIVE_V7",
        cutover_id=None,
    )
    updated = connection.execute(
        """
        UPDATE spot_v7_release_state_v7
        SET database_revision_be = ?, release_state_root = ?, event_count = ?,
            last_evaluation_epoch_be = ?, current_candidate_id = ?,
            current_candidate_sha256 = ?, current_release_revision_be = ?,
            current_select_input_id = ?, current_revocation_record_id = ?
        WHERE singleton = 1 AND database_revision_be = ? AND release_state_root = ?
        """,
        (
            _u64be(next_cursor.database_revision),
            next_cursor.state_root,
            next_cursor.database_revision,
            _optional_u64be(next_cursor.last_evaluation_epoch),
            next_cursor.current_candidate_id,
            next_cursor.current_candidate_sha256,
            _optional_u64be(next_cursor.current_release_revision),
            next_cursor.current_select_input_id,
            next_cursor.current_revocation_record_id,
            _u64be(cursor.database_revision),
            cursor.state_root,
        ),
    )
    if updated.rowcount != 1:
        raise _reject("RELEASE_STATE_CAS_FAILED", "locked release head changed")
    return next_cursor


def _record_authority_neutral_watermark_locked_v7(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    exact_watermark_bytes: bytes,
) -> None:
    """Append one structurally monotonic observation without authenticating it."""

    _require_locked_connection(connection)
    cursor = _validate_complete_release_history_locked_v7(connection, identity=identity)
    checkpoint_bytes = _head_checkpoint_bytes(identity, _cursor_history_v7(connection, identity))
    watermark, assessment = _assess_head_watermark(checkpoint_bytes, exact_watermark_bytes)
    state = _read_state(connection)
    previous_position = _u64_from_be(state["external_anchor_position_be"])
    previous_commitment = bytes(state["external_anchor_commitment"])
    if watermark.external_backend_id != str(state["external_backend_id"]):
        raise _reject("EXTERNAL_BACKEND_CHANGED", "watermark backend must remain fixed")
    if watermark.external_position <= previous_position:
        raise _reject("EXTERNAL_POSITION_NOT_FORWARD", "watermark position must increase")
    if bytes.fromhex(watermark.external_parent_commitment) != previous_commitment:
        raise _reject("EXTERNAL_PARENT_MISMATCH", "watermark parent does not match current anchor")
    _insert_observation(
        connection,
        cursor=cursor,
        checkpoint_bytes=checkpoint_bytes,
        watermark=watermark,
        assessment=assessment,
    )
    connection.execute(
        """
        UPDATE spot_v7_release_state_v7
        SET external_backend_id = ?, external_anchor_position_be = ?,
            external_anchor_commitment = ?, external_anchor_parent_commitment = ?,
            external_anchor_watermark_hash = ?
        WHERE singleton = 1
        """,
        (
            watermark.external_backend_id,
            _u64be(watermark.external_position),
            bytes.fromhex(watermark.external_backend_commitment),
            bytes.fromhex(watermark.external_parent_commitment),
            bytes.fromhex(watermark.watermark_hash),
        ),
    )


def _current_release_for_atomic_join_locked_v7(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> _TransactionBoundSpotV7CurrentReleaseV7:
    """Project the exact nonrevoked head while the caller holds the write lock."""

    _require_locked_connection(connection)
    cursor = _validate_complete_release_history_locked_v7(connection, identity=identity)
    if cursor.database_revision == 0 or cursor.current_revoked:
        raise _reject("CURRENT_RELEASE_UNAVAILABLE", "current release is empty or revoked")
    state = _read_state(connection)
    latest_observation = connection.execute(
        "SELECT * FROM spot_v7_release_observations_v7 ORDER BY external_anchor_position_be DESC LIMIT 1"
    ).fetchone()
    if latest_observation is None:
        raise _reject("RELEASE_OBSERVATION_MISSING", "release watermark history is empty")
    if (
        _u64_from_be(latest_observation["observed_database_revision_be"])
        != cursor.database_revision
        or bytes(latest_observation["observed_release_state_root"]) != cursor.state_root
    ):
        raise _reject("RELEASE_OBSERVATION_STALE", "latest watermark does not bind current head")
    select_id = _require_digest(cursor.current_select_input_id, "current_select_input_id")
    row = connection.execute(
        "SELECT candidate_bytes FROM spot_v7_release_events_v7 WHERE selector_input_id = ? AND event_kind = 'SELECT'",
        (select_id,),
    ).fetchone()
    if row is None:
        raise _reject("CURRENT_SELECTION_MISSING", "current SELECT event is absent")
    return _TransactionBoundSpotV7CurrentReleaseV7._from_locked_history(
        connection=connection,
        identity=identity,
        cursor=cursor,
        candidate_bytes=bytes(row["candidate_bytes"]),
        external_anchor_position=_u64_from_be(state["external_anchor_position_be"]),
        external_anchor_commitment=bytes(state["external_anchor_commitment"]),
        seal=_CURRENT_RELEASE_SEAL_V7,
    )


def _require_current_release_still_locked_v7(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    release: _TransactionBoundSpotV7CurrentReleaseV7,
) -> _TransactionBoundSpotV7CurrentReleaseV7:
    """Recheck a private projection immediately before the economic write."""

    if type(release) is not _TransactionBoundSpotV7CurrentReleaseV7:
        raise TypeError("atomic join requires the exact transaction-bound release type")
    if connection is not release._connection or not connection.in_transaction:
        raise _reject("RELEASE_TRANSACTION_ENDED", "release projection escaped its transaction")
    current = _current_release_for_atomic_join_locked_v7(connection, identity=identity)
    observed = (
        release.database_revision,
        release.release_state_root,
        release.current_candidate_id,
        release.current_candidate_sha256,
        release.current_release_revision,
        release.current_select_input_id,
        release.current_candidate_bytes,
        release._external_anchor_position,
        release._external_anchor_commitment,
    )
    expected = (
        current.database_revision,
        current.release_state_root,
        current.current_candidate_id,
        current.current_candidate_sha256,
        current.current_release_revision,
        current.current_select_input_id,
        current.current_candidate_bytes,
        current._external_anchor_position,
        current._external_anchor_commitment,
    )
    if observed != expected:
        raise _reject("RELEASE_PROJECTION_STALE", "release projection changed in transaction")
    return release


def _validate_complete_release_history_locked_v7(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> store_v3.SpotV7AuthenticatedReleaseStateCursorV3:
    """Replay every event and observation under the caller's transaction."""

    _require_locked_connection(connection)
    _validate_spot_v7_release_schema_v7(connection)
    _acquire_release_write_lock(connection)
    state = _read_state(connection)
    _validate_state_identity_and_nonclaims(state, identity)
    cutover = connection.execute(
        "SELECT * FROM spot_v7_release_cutover_v7 WHERE singleton = 1"
    ).fetchone()
    if cutover is None:
        raise _reject("CUTOVER_ROW_MISSING", "V7 release cutover row is absent")
    cutover_id = bytes(cutover["cutover_id"])
    imported_revision = _u64_from_be(cutover["imported_final_revision_be"])
    if imported_revision != _u64_from_be(state["imported_final_revision_be"]):
        raise _reject("CUTOVER_REVISION_DRIFT", "cutover and state imported revisions differ")
    cursor = store_v3._genesis_cursor(identity)
    cursors = [cursor]
    rows = connection.execute(
        "SELECT * FROM spot_v7_release_events_v7 ORDER BY event_revision_be"
    ).fetchall()
    if len(rows) > store_v3.MAX_AUTHENTICATED_RELEASE_EVENTS_V3:
        raise _reject("EVENT_LIMIT", "V7 release event limit exceeded")
    for revision, row in enumerate(rows, start=1):
        if bytes(row["event_revision_be"]) != _u64be(revision):
            raise _reject("EVENT_SEQUENCE", "V7 release revisions are not contiguous")
        expected_origin = "IMPORTED_V3" if revision <= imported_revision else "NATIVE_V7"
        if str(row["event_origin"]) != expected_origin:
            raise _reject("EVENT_ORIGIN", "V7 release event origin is inconsistent")
        expected_cutover = cutover_id if expected_origin == "IMPORTED_V3" else None
        if _optional_blob(row["imported_cutover_id"]) != expected_cutover:
            raise _reject("EVENT_CUTOVER_BINDING", "V7 event cutover binding changed")
        artifacts = _revalidate_event_row(row)
        store_v3._require_store_identity_matches_artifacts(identity, artifacts)
        if store_v3._event_storage_values(row) != store_v3._artifact_storage_values(
            artifacts,
            identity,
        ):
            raise _reject("EVENT_PROJECTION", "V7 release event differs from authentication")
        if bytes(row["previous_state_root"]) != cursor.state_root:
            raise _reject("EVENT_PREVIOUS_ROOT", "V7 release event previous root differs")
        try:
            cursor = store_v3._apply_transition(cursor, artifacts)
        except ValueError as exc:
            raise _reject("EVENT_REPLAY", str(exc)) from exc
        if cursor.database_revision != revision:
            raise _reject("EVENT_REVISION", "V7 replay revision differs")
        if bytes(row["result_state_root"]) != cursor.state_root:
            raise _reject("EVENT_RESULT_ROOT", "V7 release event result root differs")
        _require_event_nonclaims(row)
        cursors.append(cursor)
    if int(state["event_count"]) != len(rows):
        raise _reject("EVENT_COUNT", "V7 release event count differs")
    if _state_cursor_values(state) != _cursor_values(cursor):
        raise _reject("STATE_CURSOR", "V7 release state differs from replayed history")
    _validate_cutover_row(cutover, identity, cursors, rows)
    _validate_observations(connection, identity, tuple(cursors), state)
    return cursor


def _replay_attached_v3_history_locked(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> _ReplayedReleaseHistoryV7:
    if int(connection.execute("PRAGMA source_v3.application_id").fetchone()[0]) != (
        store_v3.STORE_APPLICATION_ID_V3
    ):
        raise _reject("SOURCE_APPLICATION_ID", "attached source is not Store V3")
    if int(connection.execute("PRAGMA source_v3.user_version").fetchone()[0]) != (
        store_v3.STORE_SCHEMA_VERSION_V3
    ):
        raise _reject("SOURCE_SCHEMA_VERSION", "attached source Store V3 is not live")
    schema_rows = connection.execute(
        "SELECT name, sql FROM source_v3.sqlite_master WHERE name NOT LIKE 'sqlite_%' ORDER BY name"
    ).fetchall()
    observed = {str(row["name"]): str(row["sql"]) for row in schema_rows}
    if frozenset(observed) != frozenset(store_v3._EXPECTED_SCHEMA_SQL_V3):
        raise _reject("SOURCE_SCHEMA_OBJECTS", "source Store V3 schema object set differs")
    for name, expected in store_v3._EXPECTED_SCHEMA_SQL_V3.items():
        if store_v3._normalize_sql(observed[name]) != store_v3._normalize_sql(expected):
            raise _reject("SOURCE_SCHEMA_SQL", f"source Store V3 schema differs for {name}")
    check = connection.execute("PRAGMA source_v3.quick_check").fetchall()
    if len(check) != 1 or str(check[0][0]) != "ok":
        raise _reject("SOURCE_QUICK_CHECK", "source Store V3 quick_check failed")
    if connection.execute("PRAGMA source_v3.foreign_key_check").fetchone() is not None:
        raise _reject("SOURCE_FOREIGN_KEY_CHECK", "source Store V3 foreign keys failed")
    meta = connection.execute(
        "SELECT * FROM source_v3.spot_v7_authenticated_release_state_meta_v3 WHERE singleton = 1"
    ).fetchone()
    if meta is None:
        raise _reject("SOURCE_META_MISSING", "source Store V3 metadata is absent")
    try:
        store_v3._validate_meta_identity(meta, identity)
    except ValueError as exc:
        raise _reject("SOURCE_IDENTITY", str(exc)) from exc
    rows = tuple(
        connection.execute(
            "SELECT * FROM source_v3.spot_v7_authenticated_release_state_events_v3 ORDER BY event_revision_be"
        ).fetchall()
    )
    cursor = store_v3._genesis_cursor(identity)
    cursors = [cursor]
    for revision, row in enumerate(rows, start=1):
        if bytes(row["event_revision_be"]) != _u64be(revision):
            raise _reject("SOURCE_EVENT_SEQUENCE", "source event revisions are not contiguous")
        artifacts = _revalidate_event_row(row)
        store_v3._require_store_identity_matches_artifacts(identity, artifacts)
        if store_v3._event_storage_values(row) != store_v3._artifact_storage_values(
            artifacts,
            identity,
        ):
            raise _reject("SOURCE_EVENT_PROJECTION", "source event differs from authentication")
        if bytes(row["previous_state_root"]) != cursor.state_root:
            raise _reject("SOURCE_PREVIOUS_ROOT", "source event previous root differs")
        try:
            cursor = store_v3._apply_transition(cursor, artifacts)
        except ValueError as exc:
            raise _reject("SOURCE_EVENT_REPLAY", str(exc)) from exc
        if cursor.database_revision != revision or bytes(row["result_state_root"]) != (
            cursor.state_root
        ):
            raise _reject("SOURCE_EVENT_RESULT", "source event result differs")
        _require_source_event_nonclaims(row)
        cursors.append(cursor)
    if int(meta["event_count"]) != len(rows):
        raise _reject("SOURCE_EVENT_COUNT", "source event count differs")
    if store_v3._meta_cursor_values(meta) != store_v3._cursor_storage_values(cursor):
        raise _reject("SOURCE_CURSOR", "source metadata differs from replayed history")
    return _ReplayedReleaseHistoryV7(
        cursors=tuple(cursors),
        rows=rows,
        checkpoint_bytes=_head_checkpoint_bytes(identity, tuple(cursors)),
    )


def _insert_cutover(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    history: _ReplayedReleaseHistoryV7,
    watermark: watermark_v1.SpotV7HighestObservedReleaseEventWatermarkV1,
    assessment: watermark_v1._AuthorityNeutralReleaseCurrentnessAssessmentV1,
    cutover_id: bytes,
) -> None:
    cursor = history.cursor
    checkpoint = checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(
        history.checkpoint_bytes
    )
    connection.execute(
        """
        INSERT INTO spot_v7_release_cutover_v7 (
            singleton, cutover_id, source_schema_version,
            retired_source_user_version, source_store_identity_sha256,
            imported_final_revision_be, imported_release_state_root,
            imported_checkpoint_hash, exact_imported_checkpoint_bytes,
            exact_watermark_bytes, watermark_sha256, watermark_hash,
            currentness_assessment_sha256, external_backend_id,
            external_anchor_position_be, external_anchor_commitment,
            external_anchor_parent_commitment, old_store_retired,
            new_release_writer_active, external_monotonic_anchor_authenticated,
            currentness_at_settlement_verified, release_authority,
            settlement_authority, production_authority
        ) VALUES (1, ?, 3, 307, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 1, 0, 0, 0, 0, 0)
        """,
        (
            cutover_id,
            identity.identity_sha256,
            _u64be(cursor.database_revision),
            cursor.state_root,
            bytes.fromhex(checkpoint.release_checkpoint_hash),
            history.checkpoint_bytes,
            watermark.canonical_bytes,
            hashlib.sha256(watermark.canonical_bytes).digest(),
            bytes.fromhex(watermark.watermark_hash),
            assessment.assessment_sha256,
            watermark.external_backend_id,
            _u64be(watermark.external_position),
            bytes.fromhex(watermark.external_backend_commitment),
            bytes.fromhex(watermark.external_parent_commitment),
        ),
    )
    _insert_observation(
        connection,
        cursor=cursor,
        checkpoint_bytes=history.checkpoint_bytes,
        watermark=watermark,
        assessment=assessment,
    )
    for row, replayed_cursor in zip(history.rows, history.cursors[1:], strict=True):
        artifacts = _revalidate_event_row(row)
        previous = history.cursors[replayed_cursor.database_revision - 1]
        _insert_event_row(
            connection,
            previous=previous,
            result=replayed_cursor,
            artifacts=artifacts,
            identity=identity,
            origin="IMPORTED_V3",
            cutover_id=cutover_id,
        )
    connection.execute(
        """
        INSERT INTO spot_v7_release_state_v7 (
            singleton, schema_version, store_identity_bytes,
            store_identity_sha256, database_revision_be, release_state_root,
            event_count, last_evaluation_epoch_be, current_candidate_id,
            current_candidate_sha256, current_release_revision_be,
            current_select_input_id, current_revocation_record_id,
            imported_final_revision_be, cutover_id, external_backend_id,
            external_anchor_position_be, external_anchor_commitment,
            external_anchor_parent_commitment, external_anchor_watermark_hash,
            cutover_complete, old_store_retired, release_event_writer_active,
            release_governed_trust_roots_authenticated,
            external_monotonic_anchor_authenticated,
            currentness_at_settlement_verified, proof_receipt_authority,
            runtime_authority, release_authority, settlement_authority,
            production_authority
        ) VALUES (1, 7, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0)
        """,
        (
            identity.canonical_bytes,
            identity.identity_sha256,
            _u64be(cursor.database_revision),
            cursor.state_root,
            cursor.database_revision,
            _optional_u64be(cursor.last_evaluation_epoch),
            cursor.current_candidate_id,
            cursor.current_candidate_sha256,
            _optional_u64be(cursor.current_release_revision),
            cursor.current_select_input_id,
            cursor.current_revocation_record_id,
            _u64be(cursor.database_revision),
            cutover_id,
            watermark.external_backend_id,
            _u64be(watermark.external_position),
            bytes.fromhex(watermark.external_backend_commitment),
            bytes.fromhex(watermark.external_parent_commitment),
            bytes.fromhex(watermark.watermark_hash),
        ),
    )


def _insert_event_row(
    connection: sqlite3.Connection,
    *,
    previous: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
    result: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
    artifacts: store_v3._AuthenticatedEventArtifactsV3,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    origin: str,
    cutover_id: bytes | None,
) -> None:
    values = store_v3._artifact_storage_values(artifacts, identity)
    connection.execute(
        """
        INSERT INTO spot_v7_release_events_v7 (
            event_revision_be, event_origin, imported_cutover_id, event_kind,
            selector_input_id, selector_input_bytes, candidate_id,
            candidate_sha256, candidate_bytes, release_revision_be,
            evaluation_epoch_be, envelope_bytes, revocation_record_bytes,
            revocation_record_id, signer_registry_bytes,
            signature_envelopes_bytes, quorum_report_bytes,
            external_trust_pins_bytes, derived_static_trust_pin_identity,
            authentication_evidence_bytes, authentication_evidence_sha256,
            select_candidate_id, select_release_revision_be,
            revoke_candidate_id, revoke_release_revision_be,
            previous_state_root, result_state_root,
            durable_authenticated_release_state_recorded,
            release_governed_trust_roots_authenticated,
            external_monotonic_anchor_authenticated, proof_receipt_authority,
            runtime_authority, release_authority, settlement_authority,
            production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 0, 0, 0, 0, 0, 0, 0)
        """,
        (
            _u64be(result.database_revision),
            origin,
            cutover_id,
            *values,
            previous.state_root,
            result.state_root,
        ),
    )


def _insert_observation(
    connection: sqlite3.Connection,
    *,
    cursor: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
    checkpoint_bytes: bytes,
    watermark: watermark_v1.SpotV7HighestObservedReleaseEventWatermarkV1,
    assessment: watermark_v1._AuthorityNeutralReleaseCurrentnessAssessmentV1,
) -> None:
    parsed = checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(checkpoint_bytes)
    connection.execute(
        """
        INSERT INTO spot_v7_release_observations_v7 (
            external_anchor_position_be, external_backend_id,
            external_anchor_commitment, external_anchor_parent_commitment,
            watermark_hash, watermark_sha256, exact_watermark_bytes,
            local_checkpoint_hash, local_checkpoint_sha256,
            exact_local_checkpoint_bytes, assessment_sha256,
            exact_assessment_bytes, observed_database_revision_be,
            observed_release_state_root, observation_relation, blocker_code,
            external_finality_authenticated,
            external_monotonicity_authenticated,
            rollback_safe_currentness_established, release_authority,
            settlement_authority, production_authority
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0, 0, 0)
        """,
        (
            _u64be(watermark.external_position),
            watermark.external_backend_id,
            bytes.fromhex(watermark.external_backend_commitment),
            bytes.fromhex(watermark.external_parent_commitment),
            bytes.fromhex(watermark.watermark_hash),
            hashlib.sha256(watermark.canonical_bytes).digest(),
            watermark.canonical_bytes,
            bytes.fromhex(parsed.release_checkpoint_hash),
            hashlib.sha256(checkpoint_bytes).digest(),
            checkpoint_bytes,
            assessment.assessment_sha256,
            assessment.canonical_assessment_bytes,
            _u64be(cursor.database_revision),
            cursor.state_root,
            assessment.relation.value,
            assessment.blocker_code,
        ),
    )


def _validate_observations(
    connection: sqlite3.Connection,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    cursors: tuple[store_v3.SpotV7AuthenticatedReleaseStateCursorV3, ...],
    state: sqlite3.Row,
) -> None:
    rows = connection.execute(
        "SELECT * FROM spot_v7_release_observations_v7 ORDER BY external_anchor_position_be"
    ).fetchall()
    if not rows:
        raise _reject("OBSERVATION_HISTORY_EMPTY", "V7 release observations are absent")
    checkpoints = _checkpoint_history(identity, cursors)
    previous_position: int | None = None
    previous_commitment: bytes | None = None
    for row in rows:
        position = _u64_from_be(row["external_anchor_position_be"])
        if previous_position is not None:
            if position <= previous_position:
                raise _reject("OBSERVATION_POSITION", "observation position did not advance")
            if bytes(row["external_anchor_parent_commitment"]) != previous_commitment:
                raise _reject("OBSERVATION_PARENT", "observation parent commitment differs")
        revision = _u64_from_be(row["observed_database_revision_be"])
        if revision >= len(cursors):
            raise _reject("OBSERVATION_REVISION", "observation revision is outside history")
        exact_checkpoint = bytes(row["exact_local_checkpoint_bytes"])
        if exact_checkpoint != checkpoints[revision]:
            raise _reject("OBSERVATION_CHECKPOINT", "observation checkpoint differs from replay")
        exact_watermark = bytes(row["exact_watermark_bytes"])
        watermark, assessment = _assess_head_watermark(exact_checkpoint, exact_watermark)
        observed = (
            str(row["external_backend_id"]),
            position,
            bytes(row["external_anchor_commitment"]),
            bytes(row["external_anchor_parent_commitment"]),
            bytes(row["watermark_hash"]),
            bytes(row["watermark_sha256"]),
            bytes(row["local_checkpoint_hash"]),
            bytes(row["local_checkpoint_sha256"]),
            bytes(row["assessment_sha256"]),
            bytes(row["exact_assessment_bytes"]),
            bytes(row["observed_release_state_root"]),
            str(row["observation_relation"]),
            str(row["blocker_code"]),
        )
        expected = (
            watermark.external_backend_id,
            watermark.external_position,
            bytes.fromhex(watermark.external_backend_commitment),
            bytes.fromhex(watermark.external_parent_commitment),
            bytes.fromhex(watermark.watermark_hash),
            hashlib.sha256(exact_watermark).digest(),
            bytes.fromhex(
                checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(
                    exact_checkpoint
                ).release_checkpoint_hash
            ),
            hashlib.sha256(exact_checkpoint).digest(),
            assessment.assessment_sha256,
            assessment.canonical_assessment_bytes,
            cursors[revision].state_root,
            assessment.relation.value,
            assessment.blocker_code,
        )
        if observed != expected:
            raise _reject("OBSERVATION_PROJECTION", "stored observation differs from bytes")
        _require_zero_flags(
            row,
            (
                "external_finality_authenticated",
                "external_monotonicity_authenticated",
                "rollback_safe_currentness_established",
                "release_authority",
                "settlement_authority",
                "production_authority",
            ),
            "observation",
        )
        previous_position = position
        previous_commitment = bytes(row["external_anchor_commitment"])
    latest = rows[-1]
    if (
        str(state["external_backend_id"]) != str(latest["external_backend_id"])
        or bytes(state["external_anchor_position_be"])
        != bytes(latest["external_anchor_position_be"])
        or bytes(state["external_anchor_commitment"]) != bytes(latest["external_anchor_commitment"])
        or bytes(state["external_anchor_parent_commitment"])
        != bytes(latest["external_anchor_parent_commitment"])
        or bytes(state["external_anchor_watermark_hash"]) != bytes(latest["watermark_hash"])
    ):
        raise _reject("OBSERVATION_HEAD", "release state does not bind latest observation")


def _validate_cutover_row(
    row: sqlite3.Row,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    cursors: list[store_v3.SpotV7AuthenticatedReleaseStateCursorV3],
    events: list[sqlite3.Row],
) -> None:
    imported_revision = _u64_from_be(row["imported_final_revision_be"])
    if imported_revision >= len(cursors):
        raise _reject("CUTOVER_IMPORTED_REVISION", "cutover revision is outside history")
    imported = cursors[imported_revision]
    checkpoint_bytes = bytes(row["exact_imported_checkpoint_bytes"])
    if checkpoint_bytes != _checkpoint_history(identity, tuple(cursors))[imported_revision]:
        raise _reject("CUTOVER_CHECKPOINT", "cutover checkpoint differs from imported history")
    parsed = checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(checkpoint_bytes)
    exact_watermark = bytes(row["exact_watermark_bytes"])
    watermark, assessment = _assess_head_watermark(checkpoint_bytes, exact_watermark)
    observed = (
        bytes(row["cutover_id"]),
        bytes(row["source_store_identity_sha256"]),
        bytes(row["imported_release_state_root"]),
        bytes(row["imported_checkpoint_hash"]),
        bytes(row["watermark_sha256"]),
        bytes(row["watermark_hash"]),
        bytes(row["currentness_assessment_sha256"]),
        str(row["external_backend_id"]),
        _u64_from_be(row["external_anchor_position_be"]),
        bytes(row["external_anchor_commitment"]),
        bytes(row["external_anchor_parent_commitment"]),
        int(row["source_schema_version"]),
        int(row["retired_source_user_version"]),
    )
    expected = (
        _cutover_id(
            identity=identity,
            checkpoint_bytes=checkpoint_bytes,
            watermark_bytes=exact_watermark,
        ),
        identity.identity_sha256,
        imported.state_root,
        bytes.fromhex(parsed.release_checkpoint_hash),
        hashlib.sha256(exact_watermark).digest(),
        bytes.fromhex(watermark.watermark_hash),
        assessment.assessment_sha256,
        watermark.external_backend_id,
        watermark.external_position,
        bytes.fromhex(watermark.external_backend_commitment),
        bytes.fromhex(watermark.external_parent_commitment),
        store_v3.STORE_SCHEMA_VERSION_V3,
        SPOT_V7_RETIRED_SOURCE_USER_VERSION_V7,
    )
    if observed != expected or imported_revision > len(events):
        raise _reject("CUTOVER_PROJECTION", "cutover row differs from imported history")
    _require_zero_flags(
        row,
        (
            "external_monotonic_anchor_authenticated",
            "currentness_at_settlement_verified",
            "release_authority",
            "settlement_authority",
            "production_authority",
        ),
        "cutover",
    )
    if int(row["old_store_retired"]) != 1 or int(row["new_release_writer_active"]) != 1:
        raise _reject("CUTOVER_LIFECYCLE", "cutover lifecycle flags differ")


def _validate_state_identity_and_nonclaims(
    row: sqlite3.Row,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> None:
    if (
        int(row["schema_version"]) != SPOT_V7_RELEASE_STATE_SCHEMA_VERSION_V7
        or bytes(row["store_identity_bytes"]) != identity.canonical_bytes
        or bytes(row["store_identity_sha256"]) != identity.identity_sha256
    ):
        raise _reject("STATE_IDENTITY", "V7 release identity differs")
    if (
        int(row["cutover_complete"]) != 1
        or int(row["old_store_retired"]) != 1
        or int(row["release_event_writer_active"]) != 1
    ):
        raise _reject("STATE_LIFECYCLE", "V7 release lifecycle flags differ")
    _require_zero_flags(
        row,
        (
            "release_governed_trust_roots_authenticated",
            "external_monotonic_anchor_authenticated",
            "currentness_at_settlement_verified",
            "proof_receipt_authority",
            "runtime_authority",
            "release_authority",
            "settlement_authority",
            "production_authority",
        ),
        "release state",
    )


def _require_event_nonclaims(row: sqlite3.Row) -> None:
    if int(row["durable_authenticated_release_state_recorded"]) != 1:
        raise _reject("EVENT_DURABILITY_FLAG", "release event durability flag differs")
    _require_zero_flags(
        row,
        (
            "release_governed_trust_roots_authenticated",
            "external_monotonic_anchor_authenticated",
            "proof_receipt_authority",
            "runtime_authority",
            "release_authority",
            "settlement_authority",
            "production_authority",
        ),
        "release event",
    )


def _require_source_event_nonclaims(row: sqlite3.Row) -> None:
    expected = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    observed = tuple(
        int(row[name])
        for name in (
            "durable_authenticated_release_state_recorded",
            "release_governed_trust_roots_authenticated",
            "external_monotonic_state_anchor_verified",
            "hostile_same_interpreter_resistance_established",
            "same_uid_path_substitution_resistance_established",
            "revocation_authority",
            "release_authority",
            "runtime_authority",
            "settlement_authority",
            "production_authority",
        )
    )
    if observed != expected:
        raise _reject("SOURCE_AUTHORITY_FLAGS", "source Store V3 flags differ")


def _revalidate_event_row(row: sqlite3.Row) -> store_v3._AuthenticatedEventArtifactsV3:
    kind = str(row["event_kind"])
    evidence = bytes(row["authentication_evidence_bytes"])
    try:
        if kind == store_v3.ReleaseStateEventKindV3.SELECT.value:
            return store_v3._revalidate_selection_evidence(evidence)
        if kind == store_v3.ReleaseStateEventKindV3.REVOKE.value:
            return store_v3._revalidate_revocation_evidence(evidence)
    except (TypeError, ValueError) as exc:
        raise _reject("EVENT_AUTHENTICATION", str(exc)) from exc
    raise _reject("EVENT_KIND", "release event kind is unsupported")


def _assess_head_watermark(
    checkpoint_bytes: bytes,
    exact_watermark_bytes: bytes,
) -> tuple[
    watermark_v1.SpotV7HighestObservedReleaseEventWatermarkV1,
    watermark_v1._AuthorityNeutralReleaseCurrentnessAssessmentV1,
]:
    try:
        watermark = watermark_v1.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(
            exact_watermark_bytes
        )
        assessment = watermark_v1.assess_exact_spot_v7_release_currentness_against_watermark_v1(
            exact_local_checkpoint_bytes=checkpoint_bytes,
            exact_finalized_checkpoint_bytes=checkpoint_bytes,
            exact_highest_observed_checkpoint_bytes=checkpoint_bytes,
            exact_watermark_bytes=exact_watermark_bytes,
        )
    except (TypeError, ValueError) as exc:
        raise _reject("WATERMARK_REJECTED", str(exc)) from exc
    if (
        assessment.relation
        is not watermark_v1.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_FINALIZED_SELECTION
    ):
        raise _reject(
            "WATERMARK_NOT_CURRENT_SELECTION",
            f"watermark relation is {assessment.relation.value}",
        )
    return watermark, assessment


def _cursor_history_v7(
    connection: sqlite3.Connection,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> tuple[store_v3.SpotV7AuthenticatedReleaseStateCursorV3, ...]:
    cursor = store_v3._genesis_cursor(identity)
    output = [cursor]
    rows = connection.execute(
        "SELECT * FROM spot_v7_release_events_v7 ORDER BY event_revision_be"
    ).fetchall()
    for row in rows:
        artifacts = _revalidate_event_row(row)
        cursor = store_v3._apply_transition(cursor, artifacts)
        output.append(cursor)
    return tuple(output)


def _checkpoint_history(
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    cursors: tuple[store_v3.SpotV7AuthenticatedReleaseStateCursorV3, ...],
) -> tuple[bytes, ...]:
    parent_hash = checkpoint_v1.ZERO_DIGEST_HEX_V1
    output: list[bytes] = []
    for cursor in cursors:
        raw = checkpoint_v1.build_spot_v7_release_state_checkpoint_v1(
            application_id=identity.application_id,
            chain_id=identity.chain_id,
            domain_id=identity.domain_id,
            release_profile=identity.release_profile,
            store_identity_hash=identity.identity_sha256.hex(),
            database_revision=cursor.database_revision,
            last_evaluation_epoch=cursor.last_evaluation_epoch or 0,
            release_state_root=cursor.state_root.hex(),
            current_candidate_id=_optional_hex(cursor.current_candidate_id),
            current_candidate_sha256=_optional_hex(cursor.current_candidate_sha256),
            current_release_revision=cursor.current_release_revision,
            current_select_input_id=_optional_hex(cursor.current_select_input_id),
            current_revocation_record_id=_optional_hex(cursor.current_revocation_record_id),
            parent_release_checkpoint_hash=parent_hash,
            release_checkpoint_sequence=cursor.database_revision,
        )
        parsed = checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(raw)
        if output:
            checkpoint_v1.validate_spot_v7_release_state_checkpoint_successor_v1(
                checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(output[-1]),
                parsed,
            )
        output.append(raw)
        parent_hash = parsed.release_checkpoint_hash
    return tuple(output)


def _head_checkpoint_bytes(
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    cursors: tuple[store_v3.SpotV7AuthenticatedReleaseStateCursorV3, ...],
) -> bytes:
    return _checkpoint_history(identity, cursors)[-1]


def _cutover_id(
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    checkpoint_bytes: bytes,
    watermark_bytes: bytes,
) -> bytes:
    return hashlib.sha256(
        _CUTOVER_ID_DOMAIN_V7
        + identity.identity_sha256
        + hashlib.sha256(checkpoint_bytes).digest()
        + hashlib.sha256(watermark_bytes).digest()
    ).digest()


def _read_state(connection: sqlite3.Connection) -> sqlite3.Row:
    row = connection.execute(
        "SELECT * FROM spot_v7_release_state_v7 WHERE singleton = 1"
    ).fetchone()
    if row is None:
        raise _reject("STATE_ROW_MISSING", "V7 release state row is absent")
    return row


def _state_cursor_values(row: sqlite3.Row) -> tuple[object, ...]:
    return (
        _u64_from_be(row["database_revision_be"]),
        bytes(row["release_state_root"]),
        _optional_u64_from_be(row["last_evaluation_epoch_be"]),
        _optional_blob(row["current_candidate_id"]),
        _optional_blob(row["current_candidate_sha256"]),
        _optional_u64_from_be(row["current_release_revision_be"]),
        _optional_blob(row["current_select_input_id"]),
        row["current_revocation_record_id"] is not None,
        _optional_blob(row["current_revocation_record_id"]),
    )


def _cursor_values(
    cursor: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
) -> tuple[object, ...]:
    return (
        cursor.database_revision,
        cursor.state_root,
        cursor.last_evaluation_epoch,
        cursor.current_candidate_id,
        cursor.current_candidate_sha256,
        cursor.current_release_revision,
        cursor.current_select_input_id,
        cursor.current_revoked,
        cursor.current_revocation_record_id,
    )


def _require_locked_connection(connection: sqlite3.Connection) -> None:
    if type(connection) is not sqlite3.Connection:
        raise TypeError("release engine requires an exact SQLite connection")
    if not connection.in_transaction:
        raise _reject("WRITE_TRANSACTION_REQUIRED", "release engine requires a transaction")
    if connection.row_factory is not sqlite3.Row:
        raise _reject("ROW_FACTORY_REQUIRED", "release engine requires sqlite3.Row")


def _acquire_release_write_lock(connection: sqlite3.Connection) -> None:
    """Upgrade even a deferred transaction before deriving currentness."""

    updated = connection.execute(
        "UPDATE spot_v7_release_state_v7 SET singleton = singleton WHERE singleton = 1"
    )
    if updated.rowcount != 1:
        raise _reject("RELEASE_WRITE_LOCK", "release state singleton is absent")


def _require_zero_flags(row: sqlite3.Row, fields: tuple[str, ...], scope: str) -> None:
    if any(int(row[field]) != 0 for field in fields):
        raise _reject("AUTHORITY_FLAG_DRIFT", f"{scope} authority flags changed")


def _require_digest(value: object, name: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise ValueError(f"{name} must be a nonzero 32-byte digest")
    return value


def _require_u64(value: object, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64_V7:
        raise ValueError(f"{name} must be a u64")
    return value


def _require_positive_u64(value: object, name: str) -> int:
    result = _require_u64(value, name)
    if result == 0:
        raise ValueError(f"{name} must be positive")
    return result


def _u64be(value: int) -> bytes:
    return _require_u64(value, "u64 value").to_bytes(8, "big")


def _u64_from_be(value: object) -> int:
    if type(value) is bytes:
        raw = value
    elif type(value) is memoryview:
        raw = value.tobytes()
    else:
        raise ValueError("u64 storage value must be bytes")
    if len(raw) != 8:
        raise ValueError("u64 storage value must contain eight bytes")
    return int.from_bytes(raw, "big")


def _optional_u64be(value: int | None) -> bytes | None:
    return None if value is None else _u64be(value)


def _optional_u64_from_be(value: object) -> int | None:
    return None if value is None else _u64_from_be(value)


def _optional_blob(value: object) -> bytes | None:
    if value is None:
        return None
    if type(value) is bytes:
        return value
    if type(value) is memoryview:
        return value.tobytes()
    raise ValueError("optional storage blob must be bytes")


def _optional_hex(value: bytes | None) -> str | None:
    return None if value is None else value.hex()


__all__ = ()
