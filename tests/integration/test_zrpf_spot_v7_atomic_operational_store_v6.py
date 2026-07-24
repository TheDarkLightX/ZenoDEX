"""CBC tests for exact finality-invocation persistence in Spot V7 V6."""

from __future__ import annotations

import hashlib
import json
import sqlite3
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from threading import Barrier
from typing import cast
from unittest.mock import patch

import pytest

import tests.integration.test_zrpf_spot_v7_atomic_operational_store_v4 as v4_test
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v5 import (
    SpotV7OperationalStoreActivationUnavailableV5,
    _DormantSpotV7AuthorityPrerequisitesV5,
    _seal_test_only_dormant_spot_v7_authority_prerequisites_v5,
)
from src.integration.zrpf_spot_v7_atomic_operational_store_v6 import (
    SQLiteSpotV7AtomicOperationalStoreV6,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementCursorV1,
    SpotV7AtomicSettlementDispositionV1,
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7AtomicSettlementResultV1,
    SpotV7AtomicSettlementStoreErrorV1,
)
from src.state.canonical import canonical_json_bytes

_INVOCATION_TABLE = "spot_v7_checkpoint_finality_invocation_v6"
_FALSE_FIELDS = (
    "release_governed_checker_identity_verified",
    "hostile_same_interpreter_resistance_established",
    "proof_receipt_authority",
    "runtime_authority",
    "release_authority",
    "settlement_authority",
    "production_authority",
)


def _private_directory(tmp_path: Path, name: str = "private-v6") -> Path:
    directory = tmp_path / name
    directory.mkdir(mode=0o700)
    return directory


def _sealed_prerequisites(
    fixture: v4_test._GenuineV4Fixture,
) -> _DormantSpotV7AuthorityPrerequisitesV5:
    return _seal_test_only_dormant_spot_v7_authority_prerequisites_v5(
        operational_capability_v3=fixture.capability,
        exact_proof_verifier_manifest_bytes=b'{"schema":"test.proof-verifier.v6"}',
        exact_runtime_manifest_bytes=b'{"schema":"test.runtime-manifest.v6"}',
        exact_release_manifest_bytes=b'{"schema":"test.release-manifest.v6"}',
        exact_release_evidence_bytes=b'{"schema":"test.release-evidence.v6"}',
        exact_authority_manifest_bytes=b'{"schema":"test.authority-manifest.v6"}',
        release_revision=1,
        release_activation_epoch=0,
        release_revocation_epoch=None,
        evaluation_epoch=fixture.capability._packet_for_atomic_store_v4().candidate.epoch_id,
    )


def _resolver(
    fixture: v4_test._GenuineV4Fixture,
    prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
):
    return lambda commitment: prerequisites if commitment == fixture.settlement_commitment else None


def _make_store(
    tmp_path: Path,
    fixture: v4_test._GenuineV4Fixture,
    prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
    *,
    name: str = "spot-v7-v6.sqlite3",
) -> SQLiteSpotV7AtomicOperationalStoreV6:
    path = _private_directory(tmp_path) / name
    return SQLiteSpotV7AtomicOperationalStoreV6(
        path,
        identity=fixture.identity,
        genesis_cells=fixture.genesis_cells,
        governed_operational_policy=fixture.policy,
        prerequisite_resolver=_resolver(fixture, prerequisites),
    )


def _commit_one(
    store: SQLiteSpotV7AtomicOperationalStoreV6,
    prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
):
    return store._commit_authority_prerequisites_v6(
        expected_cursor=store.read_cursor(),
        prerequisites=prerequisites,
    )


def _flip_first(raw: bytes) -> bytes:
    assert raw
    return bytes((raw[0] ^ 1,)) + raw[1:]


@pytest.fixture(scope="module")
def genuine_v4_fixture() -> v4_test._GenuineV4Fixture:
    return v4_test._build_genuine_v4_fixture()


def test_given_exact_v6_prerequisites_when_committed_then_invocation_bytes_and_digests_are_atomic(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    packet = prerequisites._packet_for_atomic_store_v5().operational
    artifacts = packet.checkpoint_finality_checker_invocation
    store = _make_store(tmp_path, fixture, prerequisites)

    result = _commit_one(store, prerequisites)

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert store.manifest_pinned_checkpoint_finality_cross_check_executed is True
    assert store.release_governed_checkpoint_finality_checker_identity_verified is False
    assert store.hostile_same_interpreter_resistance_established is False
    assert store.proof_receipt_authority is False
    assert store.runtime_authority is False
    assert store.release_authority is False
    assert store.settlement_authority is False
    assert store.production_authority is False
    with sqlite3.connect(store.path) as connection:
        assert connection.execute("PRAGMA user_version").fetchone() == (6,)
        row = connection.execute(f"SELECT * FROM {_INVOCATION_TABLE}").fetchone()
        assert row is not None
        columns = tuple(
            item[1] for item in connection.execute(f"PRAGMA table_info({_INVOCATION_TABLE})")
        )
        stored = dict(zip(columns, row, strict=True))
        assert stored["exact_authority_manifest"] == (artifacts.exact_authority_manifest_bytes)
        assert stored["exact_request"] == artifacts.exact_request_bytes
        assert stored["exact_response"] == artifacts.exact_response_bytes
        assert stored["authority_manifest_sha256"] == bytes.fromhex(
            artifacts.evidence.authority_manifest_sha256
        )
        assert stored["checker_executable_sha256"] == bytes.fromhex(
            artifacts.evidence.executable_sha256
        )
        assert stored["request_sha256"] == bytes.fromhex(artifacts.evidence.request_sha256)
        assert stored["response_sha256"] == bytes.fromhex(artifacts.evidence.response_sha256)
        assert stored["finality_certificate_root"] == bytes.fromhex(
            packet.finality.certificate_root[2:]
        )
        assert (
            stored["exact_finality_certificate_sha256"]
            == hashlib.sha256(packet.exact_finality_certificate_bytes).digest()
        )
        assert stored["manifest_pinned_cross_check_executed"] == 1
        assert tuple(stored[field] for field in _FALSE_FIELDS) == (0,) * len(_FALSE_FIELDS)


def test_given_exact_retry_and_reopen_when_checker_execution_is_forbidden_then_replay_is_idempotent(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    committed = _commit_one(store, prerequisites)

    replayed = store._commit_authority_prerequisites_v6(
        expected_cursor=committed.head_cursor,
        prerequisites=prerequisites,
    )
    assert replayed.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY

    with patch(
        "src.integration.zrpf_spot_v7_checkpoint_finality_checker_adapter."
        "execute_pinned_verifier_once",
        side_effect=AssertionError("database replay must not execute the checker"),
    ):
        reopened = SQLiteSpotV7AtomicOperationalStoreV6(
            store.path,
            identity=fixture.identity,
            genesis_cells=fixture.genesis_cells,
            governed_operational_policy=fixture.policy,
            prerequisite_resolver=_resolver(fixture, prerequisites),
        )
        assert reopened.read_cursor() == committed.head_cursor
        assert reopened.get_receipt(fixture.settlement_commitment) == committed.receipt


def test_given_untrusted_activation_input_then_v6_typed_blocker_fails_closed(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)

    assert store.release_authority is False
    assert store.settlement_authority is False
    assert store.production_authority is False
    with pytest.raises(SpotV7OperationalStoreActivationUnavailableV5):
        store._activate_with_fresh_governed_release_evidence_v6(
            {"release_authority": True, "production_authority": True}
        )


@pytest.mark.parametrize(
    "field",
    ("exact_authority_manifest", "exact_request", "exact_response"),
)
def test_given_one_persisted_invocation_byte_field_is_mutated_then_read_and_reopen_reject(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
    field: str,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites, name=f"bytes-{field}.sqlite3")
    _commit_one(store, prerequisites)
    with sqlite3.connect(store.path) as connection:
        raw = bytes(connection.execute(f"SELECT {field} FROM {_INVOCATION_TABLE}").fetchone()[0])
        connection.execute(f"UPDATE {_INVOCATION_TABLE} SET {field} = ?", (_flip_first(raw),))
        connection.commit()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as read_error:
        store.read_cursor()
    assert read_error.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_READ_FAILED"
    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as open_error:
        SQLiteSpotV7AtomicOperationalStoreV6(
            store.path,
            identity=fixture.identity,
            genesis_cells=fixture.genesis_cells,
            governed_operational_policy=fixture.policy,
            prerequisite_resolver=_resolver(fixture, prerequisites),
        )
    assert open_error.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_OPEN_FAILED"


@pytest.mark.parametrize(
    "field",
    (
        "authority_manifest_sha256",
        "checker_executable_sha256",
        "request_sha256",
        "response_sha256",
    ),
)
def test_given_one_persisted_invocation_digest_is_mutated_then_reopen_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
    field: str,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites, name=f"digest-{field}.sqlite3")
    _commit_one(store, prerequisites)
    with sqlite3.connect(store.path) as connection:
        raw = bytes(connection.execute(f"SELECT {field} FROM {_INVOCATION_TABLE}").fetchone()[0])
        connection.execute(f"UPDATE {_INVOCATION_TABLE} SET {field} = ?", (_flip_first(raw),))
        connection.commit()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        SQLiteSpotV7AtomicOperationalStoreV6(
            store.path,
            identity=fixture.identity,
            genesis_cells=fixture.genesis_cells,
            governed_operational_policy=fixture.policy,
            prerequisite_resolver=_resolver(fixture, prerequisites),
        )
    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_OPEN_FAILED"


def test_given_coherently_rehashed_alternate_manifest_then_exact_packet_binding_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    _commit_one(store, prerequisites)
    with sqlite3.connect(store.path) as connection:
        raw = bytes(
            connection.execute(
                f"SELECT exact_authority_manifest FROM {_INVOCATION_TABLE}"
            ).fetchone()[0]
        )
        document = json.loads(raw)
        document["executable_sha256"] = "11" * 32
        changed = canonical_json_bytes(document)
        connection.execute(
            f"UPDATE {_INVOCATION_TABLE} SET exact_authority_manifest = ?, "
            "authority_manifest_sha256 = ?, checker_executable_sha256 = ?",
            (changed, hashlib.sha256(changed).digest(), bytes.fromhex("11" * 32)),
        )
        connection.commit()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        store.read_cursor()
    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_READ_FAILED"


@pytest.mark.parametrize("field", _FALSE_FIELDS)
def test_given_sql_authority_field_promotion_then_strict_schema_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
    field: str,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites, name=f"flag-{field}.sqlite3")
    _commit_one(store, prerequisites)

    with sqlite3.connect(store.path) as connection:
        with pytest.raises(sqlite3.IntegrityError):
            connection.execute(f"UPDATE {_INVOCATION_TABLE} SET {field} = 1")
        connection.rollback()
        assert connection.execute(f"SELECT {field} FROM {_INVOCATION_TABLE}").fetchone() == (0,)


def test_given_finality_certificate_binding_is_mutated_then_reopen_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    _commit_one(store, prerequisites)
    with sqlite3.connect(store.path) as connection:
        root = bytes(
            connection.execute(
                f"SELECT finality_certificate_root FROM {_INVOCATION_TABLE}"
            ).fetchone()[0]
        )
        connection.execute(
            f"UPDATE {_INVOCATION_TABLE} SET finality_certificate_root = ?",
            (_flip_first(root),),
        )
        connection.commit()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        SQLiteSpotV7AtomicOperationalStoreV6(
            store.path,
            identity=fixture.identity,
            genesis_cells=fixture.genesis_cells,
            governed_operational_policy=fixture.policy,
            prerequisite_resolver=_resolver(fixture, prerequisites),
        )
    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_OPEN_FAILED"


def test_given_unknown_schema_extension_then_open_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    with sqlite3.connect(store.path) as connection:
        connection.execute("CREATE TABLE attacker_extension(value BLOB) STRICT")
        connection.commit()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        SQLiteSpotV7AtomicOperationalStoreV6(
            store.path,
            identity=fixture.identity,
            genesis_cells=fixture.genesis_cells,
            governed_operational_policy=fixture.policy,
            prerequisite_resolver=_resolver(fixture, prerequisites),
        )
    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_OPEN_FAILED"


def test_given_two_concurrent_exact_commits_then_one_commits_and_one_is_idempotent(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    first = _make_store(tmp_path, fixture, prerequisites)
    second = SQLiteSpotV7AtomicOperationalStoreV6(
        first.path,
        identity=fixture.identity,
        genesis_cells=fixture.genesis_cells,
        governed_operational_policy=fixture.policy,
        prerequisite_resolver=_resolver(fixture, prerequisites),
    )
    stale = first.read_cursor()
    barrier = Barrier(2)

    def attempt(
        store: SQLiteSpotV7AtomicOperationalStoreV6,
    ) -> object:
        barrier.wait()
        try:
            return store._commit_authority_prerequisites_v6(
                expected_cursor=stale,
                prerequisites=prerequisites,
            )
        except SpotV7AtomicSettlementStoreErrorV1 as exc:
            return exc

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = tuple(executor.map(attempt, (first, second)))

    committed = tuple(
        result for result in results if not isinstance(result, SpotV7AtomicSettlementStoreErrorV1)
    )
    retried = tuple(
        result for result in results if isinstance(result, SpotV7AtomicSettlementStoreErrorV1)
    )
    assert len(committed) == 1
    committed_result = cast(SpotV7AtomicSettlementResultV1, committed[0])
    assert committed_result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert len(retried) == 1
    assert retried[0].code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_RETRY_REQUIRED"
    exact_retry = first._commit_authority_prerequisites_v6(
        expected_cursor=stale,
        prerequisites=prerequisites,
    )
    assert exact_retry.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY
    with sqlite3.connect(first.path) as connection:
        assert connection.execute(f"SELECT count(*) FROM {_INVOCATION_TABLE}").fetchone() == (1,)


def test_given_persistence_failure_after_prior_rows_then_transaction_rolls_back_all_state(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    before = store.read_cursor()

    with patch(
        "src.integration.zrpf_spot_v7_atomic_operational_store_v6._persist_finality_invocation_v6",
        side_effect=ValueError("forced V6 persistence failure"),
    ):
        with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
            store._commit_authority_prerequisites_v6(
                expected_cursor=before,
                prerequisites=prerequisites,
            )
    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V6_COMMIT_FAILED"
    assert store.read_cursor() == before
    with sqlite3.connect(store.path) as connection:
        for table in (
            "spot_v7_settlements",
            "spot_v7_operational_finality_v4",
            "spot_v7_authority_provenance_v5",
            _INVOCATION_TABLE,
        ):
            assert connection.execute(f"SELECT count(*) FROM {table}").fetchone() == (0,)


def test_given_unknown_stale_cursor_then_reject_is_noop(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    genesis = store.read_cursor()
    stale = SpotV7AtomicSettlementCursorV1(
        revision=1,
        state_root=genesis.state_root,
        settlement_count=1,
        cell_count=genesis.cell_count,
        last_epoch_id=0,
    )

    result = store._commit_authority_prerequisites_v6(
        expected_cursor=stale,
        prerequisites=prerequisites,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.REJECTED
    assert result.reject_reason is SpotV7AtomicSettlementRejectReasonV1.CURSOR_MISMATCH
    assert store.read_cursor() == genesis
    with sqlite3.connect(store.path) as connection:
        assert connection.execute(f"SELECT count(*) FROM {_INVOCATION_TABLE}").fetchone() == (0,)
