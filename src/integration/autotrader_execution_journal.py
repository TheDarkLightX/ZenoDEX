"""Crash-conservative execution journal for AutoTrader value submission.

The journal reserves an execution ID durably before the first network send.
Any recorded state blocks replay. ``PENDING`` means the external outcome needs
operator reconciliation. ``SENT`` means the Tau RPC returned explicit success;
it does not claim mining or finality. This module deliberately provides no
automatic release transition.
"""

from __future__ import annotations

import fcntl
import json
import os
import re
from collections.abc import Mapping
from dataclasses import dataclass
from enum import Enum
from typing import TextIO

EXECUTION_JOURNAL_SCHEMA_V1 = "zenodex/autotrader-execution-journal/v1"
EXECUTION_JOURNAL_SCHEMA_V2 = "zenodex/autotrader-execution-journal/v2"
EXECUTION_JOURNAL_SCHEMA_V3 = "zenodex/autotrader-execution-journal/v3"
_ROOT_RE = re.compile(r"0x[0-9a-f]{64}")
_SURFACES = frozenset(
    {
        "autotrader_live_execute_once",
        "autotrader_live_supervisor_execute",
    }
)


class ExecutionJournalStateV2(str, Enum):
    PENDING = "PENDING"
    SENT = "SENT"


@dataclass(frozen=True, slots=True)
class ExecutionJournalEntryV2:
    state: ExecutionJournalStateV2
    surface: str
    submission_root: str | None


def _require_submission_root(value: object) -> str:
    if type(value) is not str or _ROOT_RE.fullmatch(value) is None:
        raise ValueError("execution journal submission_root must be a canonical root")
    return value


def _require_execution_id(value: object) -> str:
    if type(value) is not str or not value.strip():
        raise ValueError("execution journal row missing execution_id")
    if value != value.strip():
        raise ValueError("execution journal execution_id must be canonical")
    if len(value) > 128:
        raise ValueError("execution journal execution_id too long")
    if any(character.isspace() for character in value):
        raise ValueError("execution journal execution_id must not contain whitespace")
    return value


def _require_surface(value: object) -> str:
    if type(value) is not str or not value:
        raise ValueError("execution journal row missing surface")
    if value not in _SURFACES:
        raise ValueError("execution journal row has unsupported surface")
    return value


def _object_without_duplicate_fields(pairs: list[tuple[str, object]]) -> dict[str, object]:
    obj: dict[str, object] = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError("execution journal row has duplicate JSON field")
        obj[key] = value
    return obj


def _decode_journal_row(text: str, *, line_number: int) -> dict[str, object]:
    try:
        row = json.loads(text, object_pairs_hook=_object_without_duplicate_fields)
    except json.JSONDecodeError as exc:
        raise ValueError(f"execution journal row {line_number} is not valid JSON") from exc
    if type(row) is not dict:
        raise ValueError("execution journal row must be an object")
    return row


def _entry_from_row(
    row: dict[str, object],
) -> tuple[str, str, ExecutionJournalEntryV2]:
    schema = row.get("schema")
    execution_id = _require_execution_id(row.get("execution_id"))
    surface = _require_surface(row.get("surface"))
    if schema == EXECUTION_JOURNAL_SCHEMA_V1:
        return schema, execution_id, ExecutionJournalEntryV2(
            state=ExecutionJournalStateV2.SENT,
            surface=surface,
            submission_root=None,
        )
    if schema == EXECUTION_JOURNAL_SCHEMA_V2:
        expected_fields = {"schema", "execution_id", "surface", "state"}
        submission_root = None
    elif schema == EXECUTION_JOURNAL_SCHEMA_V3:
        expected_fields = {"schema", "execution_id", "surface", "state", "submission_root"}
        submission_root = _require_submission_root(row.get("submission_root"))
    else:
        raise ValueError("execution journal row has unsupported schema")
    if set(row) != expected_fields:
        raise ValueError("execution journal row has unexpected fields")
    try:
        state = ExecutionJournalStateV2(row.get("state"))
    except (TypeError, ValueError) as exc:
        raise ValueError("execution journal row has invalid state") from exc
    return schema, execution_id, ExecutionJournalEntryV2(
        state=state,
        surface=surface,
        submission_root=submission_root,
    )


def _parse_execution_journal(handle: TextIO) -> dict[str, ExecutionJournalEntryV2]:
    handle.seek(0)
    entries: dict[str, ExecutionJournalEntryV2] = {}
    for line_number, line in enumerate(handle, start=1):
        text = line.strip()
        if not text:
            continue
        schema, execution_id, entry = _entry_from_row(
            _decode_journal_row(text, line_number=line_number)
        )
        previous = entries.get(execution_id)
        if previous is None:
            if (
                schema != EXECUTION_JOURNAL_SCHEMA_V1
                and entry.state is not ExecutionJournalStateV2.PENDING
            ):
                raise ValueError("execution journal execution must start PENDING")
        else:
            if previous.surface != entry.surface:
                raise ValueError("execution journal surface changed within execution")
            if previous.submission_root != entry.submission_root:
                raise ValueError("execution journal submission root changed within execution")
            if (
                previous.state is not ExecutionJournalStateV2.PENDING
                or entry.state is not ExecutionJournalStateV2.SENT
            ):
                raise ValueError("execution journal has invalid state transition")
        entries[execution_id] = entry
    return entries


def execution_journal_ids(path: str) -> set[str]:
    if not path or not os.path.exists(path):
        return set()
    try:
        with open(path, "r", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_SH)
            try:
                return set(_parse_execution_journal(handle))
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    except OSError as exc:
        raise ValueError(f"execution_journal_read_failed:{type(exc).__name__}") from exc


def _fsync_parent_directory(path: str) -> None:
    parent = os.path.dirname(path) or "."
    directory_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)


def _append_execution_journal_row(handle: TextIO, row: Mapping[str, str]) -> None:
    handle.seek(0, os.SEEK_END)
    handle.write(json.dumps(dict(row), sort_keys=True, separators=(",", ":")) + "\n")
    handle.flush()
    os.fsync(handle.fileno())


def reserve_execution_id(
    *,
    path: str,
    execution_keys: set[str],
    execution_id: str,
    surface: str,
    submission_root: str,
) -> None:
    if not path:
        raise ValueError("execution_journal_path_required")
    execution_id = _require_execution_id(execution_id)
    surface = _require_surface(surface)
    submission_root = _require_submission_root(submission_root)
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    file_existed = os.path.exists(path)
    row = {
        "schema": EXECUTION_JOURNAL_SCHEMA_V3,
        "execution_id": execution_id,
        "surface": surface,
        "state": ExecutionJournalStateV2.PENDING.value,
        "submission_root": submission_root,
    }
    try:
        with open(path, "a+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                if execution_id in _parse_execution_journal(handle):
                    raise ValueError("execution_replay")
                _append_execution_journal_row(handle, row)
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        if not file_existed:
            _fsync_parent_directory(path)
    except OSError as exc:
        raise ValueError(f"execution_journal_write_failed:{type(exc).__name__}") from exc
    execution_keys.add(execution_id)


def mark_execution_sent(
    *,
    path: str,
    execution_id: str,
    surface: str,
    submission_root: str,
) -> None:
    if not path:
        raise ValueError("execution_journal_path_required")
    execution_id = _require_execution_id(execution_id)
    surface = _require_surface(surface)
    submission_root = _require_submission_root(submission_root)
    row = {
        "schema": EXECUTION_JOURNAL_SCHEMA_V3,
        "execution_id": execution_id,
        "surface": surface,
        "state": ExecutionJournalStateV2.SENT.value,
        "submission_root": submission_root,
    }
    try:
        with open(path, "r+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                entry = _parse_execution_journal(handle).get(execution_id)
                if entry is None:
                    raise ValueError("execution_journal_pending_reservation_missing")
                if entry.surface != surface:
                    raise ValueError("execution_journal_surface_mismatch")
                if entry.submission_root is None:
                    if entry.state is ExecutionJournalStateV2.SENT:
                        return
                    raise ValueError("execution_journal_submission_root_unavailable")
                if entry.submission_root != submission_root:
                    raise ValueError("execution_journal_submission_root_mismatch")
                if entry.state is ExecutionJournalStateV2.SENT:
                    return
                if entry.state is not ExecutionJournalStateV2.PENDING:
                    raise ValueError("execution_journal_pending_reservation_missing")
                _append_execution_journal_row(handle, row)
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    except OSError as exc:
        raise ValueError(f"execution_journal_write_failed:{type(exc).__name__}") from exc
