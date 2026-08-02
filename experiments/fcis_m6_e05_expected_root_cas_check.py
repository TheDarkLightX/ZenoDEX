"""Independent deterministic checks for the E05 CAS packet."""

from __future__ import annotations

import json
import sqlite3
from pathlib import Path
from typing import Any, cast

from experiments.fcis_m6_e04_retry_classifier import (
    POST_STATE_ROOT_V1,
    build_attempt,
    build_reopen_receipt,
    build_state,
)
from experiments.fcis_m6_e05_expected_root_cas import (
    create_database,
    publish,
    read_state,
)
from src.core.fcis_m6_e05_expected_root_cas import (
    E05CodeV1,
    E05PublicationRequestV1,
    E05RejectV1,
)
from src.state.canonical import canonical_json_bytes

_ROOT = Path(__file__).resolve().parents[1]
_VECTOR_PATH = _ROOT / "docs/research/m6_tasks/TASK_E05_EXPECTED_ROOT_CAS_V1.json"
_SCHEMA = "zenodex/fcis/m6/e05/expected-root-cas/v1"


def _request() -> E05PublicationRequestV1:
    attempt = build_attempt()
    pre_state = build_state()
    post_state = build_state(
        attempts=((attempt, POST_STATE_ROOT_V1),),
        current_state_root=POST_STATE_ROOT_V1,
    )
    return E05PublicationRequestV1(
        attempt=attempt,
        pre_state=pre_state,
        post_state=post_state,
        reopen_receipt=build_reopen_receipt(pre_state),
    )


def _state_wire(state: object) -> dict[str, object]:
    exact = read_state(cast(sqlite3.Connection, state))
    return {
        "current_state_root": exact.current_state_root,
        "snapshot_root": exact.snapshot_root,
        "authority_epoch_index": exact.authority_epoch_index,
        "authority_state_root": exact.authority_state_root,
        "deployment_config_root": exact.deployment_config_root,
        "verifier_profile_root": exact.verifier_profile_root,
        "next_publication_sequence": exact.next_publication_sequence,
        "publication_set_root": exact.publication_set_root,
        "publications": [row.to_wire() for row in exact.publications],
    }


def build_payload() -> dict[str, object]:
    request = _request()
    connection = create_database(request.pre_state)
    result = publish(connection, request)
    if not hasattr(result, "to_wire"):
        raise AssertionError(f"valid E05 request rejected: {result!r}")
    return {
        "schema": _SCHEMA,
        "attempt_root": request.attempt.attempt_root,
        "pre_snapshot_root": request.pre_state.snapshot_root,
        "post_snapshot_root": request.post_state.snapshot_root,
        "pre_reopen_receipt_root": request.reopen_receipt.receipt_root,
        "result": cast(Any, result).to_wire(),
        "post_state": _state_wire(connection),
    }


def _expect_reject(value: object, code: E05CodeV1) -> None:
    if type(value) is not E05RejectV1:
        raise AssertionError(f"expected E05 rejection, got {value!r}")
    if value.code is not code:
        raise AssertionError(f"expected {code.value}, got {value!r}")


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    request = _request()
    connection = create_database(request.pre_state)
    trace: list[str] = []
    connection.set_trace_callback(trace.append)
    committed = publish(connection, request)
    if not hasattr(committed, "to_wire"):
        raise AssertionError(f"valid E05 request rejected: {committed!r}")
    normalized = [statement.strip().upper() for statement in trace]
    if not normalized or normalized[0] != "BEGIN IMMEDIATE":
        raise AssertionError("E05 performed a read before BEGIN IMMEDIATE")
    update_index = next(
        index
        for index, statement in enumerate(normalized)
        if statement.startswith("UPDATE E05_HEAD")
    )
    insert_index = next(
        index
        for index, statement in enumerate(normalized)
        if statement.startswith("INSERT INTO E05_PUBLICATIONS")
    )
    if update_index >= insert_index:
        raise AssertionError("E05 publication insert bypassed the head CAS")

    before_retry = read_state(connection)
    _expect_reject(publish(connection, request), E05CodeV1.STALE_SNAPSHOT_CAS)
    if read_state(connection) != before_retry:
        raise AssertionError("stale E05 retry changed durable state")

    authority_connection = create_database(request.pre_state)
    authority_connection.execute(
        "UPDATE e05_head SET authority_epoch_index = authority_epoch_index + 1"
    )
    before_authority = read_state(authority_connection)
    _expect_reject(publish(authority_connection, request), E05CodeV1.STALE_AUTHORITY_CAS)
    if read_state(authority_connection) != before_authority:
        raise AssertionError("authority CAS rejection changed durable state")

    rollback_connection = create_database(request.pre_state)
    rollback_connection.execute(
        """
        CREATE TRIGGER force_e05_check_abort
        AFTER INSERT ON e05_nullifiers
        BEGIN
            SELECT RAISE(ABORT, 'forced E05 check abort');
        END
        """
    )
    before_rollback = read_state(rollback_connection)
    _expect_reject(publish(rollback_connection, request), E05CodeV1.SQL_ROLLBACK)
    if read_state(rollback_connection) != before_rollback:
        raise AssertionError("E05 rollback did not restore the predecessor")

    payload = build_payload()
    if check_vector:
        expected = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(payload) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: E05 expected-root CAS vector is stale")
    return payload


def main() -> None:
    print("E05_EXPECTED_ROOT_CAS_CHECKS_PASS")
    payload = run_checks()
    print(cast(dict[str, object], payload["result"])["attempt_root"])


if __name__ == "__main__":
    main()
