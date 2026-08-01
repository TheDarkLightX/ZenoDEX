"""Focused H06 fail-closed SQLite durability-profile tests."""

from __future__ import annotations

import json
import sqlite3
from pathlib import Path
from typing import cast

import pytest

from experiments.fcis_m6_h02_sqlite_publication import create_connection
from experiments.fcis_m6_h06_durability_config import (
    H06_REQUIRED_BUSY_TIMEOUT_MS,
    H06_REQUIRED_FOREIGN_KEYS,
    H06_REQUIRED_JOURNAL_MODE,
    H06_REQUIRED_LOCKING_MODE,
    H06_REQUIRED_SYNCHRONOUS,
    H06AcceptV1,
    H06CodeV1,
    H06Error,
    H06RejectV1,
    H06SQLiteObservationV1,
    check_sqlite_durability,
    configure_sqlite_durability,
)

_PROFILE_PATH = (
    Path(__file__).resolve().parents[2]
    / "docs/research/m6_tasks/TASK_H06_DURABILITY_PROFILE_V1.json"
)


def _file_connection(path: Path) -> sqlite3.Connection:
    return cast(sqlite3.Connection, create_connection(path))


def _assert_rejected(result: object, code: H06CodeV1) -> None:
    if type(result) is not H06RejectV1:
        raise AssertionError(f"expected H06 rejection, got {result!r}")
    assert cast(H06RejectV1, result).code is code


def test_profile_manifest_matches_closed_checker_constants() -> None:
    payload = cast(dict[str, object], json.loads(_PROFILE_PATH.read_text(encoding="utf-8")))

    assert payload["journal_mode"] == H06_REQUIRED_JOURNAL_MODE
    assert payload["synchronous"] == H06_REQUIRED_SYNCHRONOUS
    assert payload["foreign_keys"] == H06_REQUIRED_FOREIGN_KEYS
    assert payload["minimum_busy_timeout_ms"] == H06_REQUIRED_BUSY_TIMEOUT_MS
    assert payload["locking_mode"] == H06_REQUIRED_LOCKING_MODE


def test_closed_profile_configures_and_then_accepts(tmp_path: Path) -> None:
    connection = _file_connection(tmp_path / "h06.sqlite")

    configured = configure_sqlite_durability(connection)
    checked = check_sqlite_durability(connection)

    assert type(configured) is H06AcceptV1
    assert type(checked) is H06AcceptV1
    assert configured.observation == checked.observation
    assert checked.observation.journal_mode == "wal"
    assert checked.observation.synchronous == 2
    assert checked.observation.foreign_keys == 1
    assert checked.observation.busy_timeout_ms >= 5000
    assert checked.observation.locking_mode == "normal"
    connection.close()


def test_memory_database_is_rejected() -> None:
    connection = create_connection()

    result = check_sqlite_durability(connection)

    _assert_rejected(result, H06CodeV1.NOT_FILE_BACKED)
    connection.close()


def test_open_transaction_is_rejected_before_configuration() -> None:
    connection = sqlite3.connect(":memory:", isolation_level=None)
    connection.execute("BEGIN")

    result = configure_sqlite_durability(connection)

    _assert_rejected(result, H06CodeV1.TRANSACTION_OPEN)
    assert connection.in_transaction
    connection.rollback()
    connection.close()


@pytest.mark.parametrize(  # type: ignore[untyped-decorator]
    ("pragma", "expected"),
    (
        ("PRAGMA journal_mode = DELETE", H06CodeV1.JOURNAL_MODE_MISMATCH),
        ("PRAGMA synchronous = OFF", H06CodeV1.SYNCHRONOUS_MISMATCH),
        ("PRAGMA foreign_keys = OFF", H06CodeV1.FOREIGN_KEYS_DISABLED),
        ("PRAGMA busy_timeout = 0", H06CodeV1.BUSY_TIMEOUT_TOO_LOW),
        ("PRAGMA locking_mode = EXCLUSIVE", H06CodeV1.LOCKING_MODE_MISMATCH),
    ),
)
def test_each_weakening_is_rejected(
    tmp_path: Path,
    pragma: str,
    expected: H06CodeV1,
) -> None:
    path = tmp_path / "h06-weak.sqlite"
    configured = _file_connection(path)
    assert type(configure_sqlite_durability(configured)) is H06AcceptV1
    configured.close()

    weakened = sqlite3.connect(str(path), isolation_level=None)
    weakened.execute("PRAGMA foreign_keys = ON")
    weakened.execute(pragma)
    result = check_sqlite_durability(weakened)

    _assert_rejected(result, expected)
    weakened.close()


def test_observation_rejects_boolean_integer_alias() -> None:
    with pytest.raises(H06Error, match="foreign_keys"):
        H06SQLiteObservationV1(
            database_path="/tmp/h06.sqlite",
            journal_mode="wal",
            synchronous=2,
            foreign_keys=True,
            busy_timeout_ms=5000,
            locking_mode="normal",
        )


def test_invalid_connection_is_rejected() -> None:
    result = check_sqlite_durability(object())

    _assert_rejected(result, H06CodeV1.INVALID_CONNECTION)
