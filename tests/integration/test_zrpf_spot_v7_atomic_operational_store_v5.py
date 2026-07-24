"""CBC tests for the dormant authority-capable Spot V7 V5 store."""

from __future__ import annotations

import sqlite3
from pathlib import Path

import pytest

import tests.integration.test_zrpf_spot_v7_atomic_operational_store_v4 as v4_test
from src.integration._zrpf_spot_v7_atomic_settlement_engine_v5 import (
    SpotV7OperationalStoreActivationBlockerCodeV5,
    SpotV7OperationalStoreActivationUnavailableV5,
    _DormantSpotV7AuthorityPrerequisitesV5,
    _seal_test_only_dormant_spot_v7_authority_prerequisites_v5,
)
from src.integration.zrpf_spot_v7_atomic_operational_store_v5 import (
    SQLiteSpotV7AtomicOperationalStoreV5,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementCursorV1,
    SpotV7AtomicSettlementDispositionV1,
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7AtomicSettlementStoreErrorV1,
)


def _private_directory(tmp_path: Path, name: str = "private-v5") -> Path:
    directory = tmp_path / name
    directory.mkdir(mode=0o700)
    return directory


def _sealed_prerequisites(
    fixture: v4_test._GenuineV4Fixture,
) -> _DormantSpotV7AuthorityPrerequisitesV5:
    return _seal_test_only_dormant_spot_v7_authority_prerequisites_v5(
        operational_capability_v3=fixture.capability,
        exact_proof_verifier_manifest_bytes=b'{"schema":"test.proof-verifier.v5"}',
        exact_runtime_manifest_bytes=b'{"schema":"test.runtime-manifest.v5"}',
        exact_release_manifest_bytes=b'{"schema":"test.release-manifest.v5"}',
        exact_release_evidence_bytes=b'{"schema":"test.release-evidence.v5"}',
        exact_authority_manifest_bytes=b'{"schema":"test.authority-manifest.v5"}',
        release_revision=1,
        release_activation_epoch=0,
        release_revocation_epoch=None,
        evaluation_epoch=fixture.capability._packet_for_atomic_store_v4().candidate.epoch_id,
    )


def _make_store(
    tmp_path: Path,
    fixture: v4_test._GenuineV4Fixture,
    prerequisites: _DormantSpotV7AuthorityPrerequisitesV5,
    *,
    name: str = "spot-v7-v5.sqlite3",
) -> SQLiteSpotV7AtomicOperationalStoreV5:
    path = _private_directory(tmp_path) / name
    return SQLiteSpotV7AtomicOperationalStoreV5(
        path,
        identity=fixture.identity,
        genesis_cells=fixture.genesis_cells,
        governed_operational_policy=fixture.policy,
        prerequisite_resolver=lambda commitment: (
            prerequisites if commitment == fixture.settlement_commitment else None
        ),
    )


@pytest.fixture(scope="module")
def genuine_v4_fixture() -> v4_test._GenuineV4Fixture:
    """Reuse one immutable genuine prerequisite graph across isolated databases."""

    return v4_test._build_genuine_v4_fixture()


def test_given_exact_sealed_v5_prerequisites_when_committed_then_economics_and_all_provenance_are_atomic(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)

    result = store._commit_authority_prerequisites_v5(
        expected_cursor=store.read_cursor(),
        prerequisites=prerequisites,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert result.settlement_authority is False
    assert store.release_authority is False
    assert store.settlement_authority is False
    assert store.production_authority is False
    assert store.activation_blocker.codes == (
        SpotV7OperationalStoreActivationBlockerCodeV5.GOVERNED_RELEASE_SELECTION_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_REVOCATION_POLICY_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_ROLLBACK_PROTECTION_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.FRESH_GOVERNED_RELEASE_EVIDENCE_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.FRESH_GOVERNED_RUNTIME_EVIDENCE_REQUIRED,
    )
    with sqlite3.connect(store.path) as connection:
        assert connection.execute("PRAGMA user_version").fetchone() == (5,)
        assert connection.execute("SELECT count(*) FROM spot_v7_settlements").fetchone() == (1,)
        assert connection.execute(
            "SELECT count(*) FROM spot_v7_authority_provenance_v5"
        ).fetchone() == (1,)
        flags = connection.execute(
            "SELECT current_release_evidence_verified, proof_receipt_authority, "
            "runtime_authority, release_authority, settlement_authority, "
            "production_authority FROM spot_v7_authority_provenance_v5"
        ).fetchone()
        assert flags == (0, 0, 0, 0, 0, 0)
        lifecycle_flags = connection.execute(
            "SELECT governed_release_selection_verified, "
            "release_revocation_policy_verified, "
            "release_rollback_protection_verified, "
            "fresh_governed_release_evidence_verified, "
            "fresh_governed_runtime_evidence_verified, release_authority, "
            "settlement_authority, production_authority "
            "FROM spot_v7_activation_blocker_v5 WHERE singleton = 1"
        ).fetchone()
        assert lifecycle_flags == (0, 0, 0, 0, 0, 0, 0, 0)

    reopened = SQLiteSpotV7AtomicOperationalStoreV5(
        store.path,
        identity=fixture.identity,
        genesis_cells=fixture.genesis_cells,
        governed_operational_policy=fixture.policy,
        prerequisite_resolver=lambda commitment: (
            prerequisites if commitment == fixture.settlement_commitment else None
        ),
    )
    assert reopened.read_cursor() == result.head_cursor
    assert reopened.read_cells() == store.read_cells()


@pytest.mark.parametrize(
    "untrusted",
    (
        True,
        False,
        {"verified": True},
        {"release_authority": True, "settlement_authority": True},
        object(),
    ),
)
def test_given_raw_data_or_booleans_when_commit_is_attempted_then_seam_rejects_without_state_change(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
    untrusted: object,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    before_cursor = store.read_cursor()
    before_cells = store.read_cells()

    with pytest.raises(TypeError, match="exact sealed Spot V7 V5 prerequisites"):
        store._commit_authority_prerequisites_v5(
            expected_cursor=before_cursor,
            prerequisites=untrusted,
        )

    assert store.read_cursor() == before_cursor
    assert store.read_cells() == before_cells


def test_given_v4_authority_false_capability_when_v5_commit_is_attempted_then_it_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    before = store.read_cursor()

    with pytest.raises(TypeError, match="exact sealed Spot V7 V5 prerequisites"):
        store._commit_authority_prerequisites_v5(
            expected_cursor=before,
            prerequisites=fixture.capability,
        )

    assert store.read_cursor() == before


def test_given_forged_v5_instance_when_private_seal_is_absent_then_commit_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    forged = object.__new__(_DormantSpotV7AuthorityPrerequisitesV5)

    with pytest.raises(TypeError, match="private V5 prerequisite seal"):
        store._commit_authority_prerequisites_v5(
            expected_cursor=store.read_cursor(),
            prerequisites=forged,
        )


def test_given_two_v5_stores_with_one_exact_stale_retry_then_second_is_idempotent_without_partial_write(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    first = _make_store(tmp_path, fixture, prerequisites)
    second = SQLiteSpotV7AtomicOperationalStoreV5(
        first.path,
        identity=fixture.identity,
        genesis_cells=fixture.genesis_cells,
        governed_operational_policy=fixture.policy,
        prerequisite_resolver=lambda _commitment: prerequisites,
    )
    stale = first.read_cursor()

    accepted = first._commit_authority_prerequisites_v5(
        expected_cursor=stale,
        prerequisites=prerequisites,
    )
    rejected = second._commit_authority_prerequisites_v5(
        expected_cursor=stale,
        prerequisites=prerequisites,
    )

    assert accepted.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert rejected.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY
    assert second.read_cursor() == accepted.head_cursor
    with sqlite3.connect(first.path) as connection:
        assert connection.execute(
            "SELECT count(*) FROM spot_v7_authority_provenance_v5"
        ).fetchone() == (1,)


def test_given_fresh_release_activation_is_requested_then_typed_blocker_fails_closed(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    assert (
        SpotV7OperationalStoreActivationBlockerCodeV5.FRESH_GOVERNED_RELEASE_EVIDENCE_REQUIRED
        in (store.activation_blocker.codes)
    )
    assert store.activation_blocker.codes[:3] == (
        SpotV7OperationalStoreActivationBlockerCodeV5.GOVERNED_RELEASE_SELECTION_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_REVOCATION_POLICY_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_ROLLBACK_PROTECTION_REQUIRED,
    )

    with pytest.raises(SpotV7OperationalStoreActivationUnavailableV5):
        store._activate_with_fresh_governed_release_evidence_v5(object())


def test_given_persisted_authority_provenance_is_mutated_then_reopen_rejects(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    store._commit_authority_prerequisites_v5(
        expected_cursor=store.read_cursor(),
        prerequisites=prerequisites,
    )
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_authority_provenance_v5 SET exact_release_evidence = ?",
            (b'{"schema":"tampered"}',),
        )
        connection.commit()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        SQLiteSpotV7AtomicOperationalStoreV5(
            store.path,
            identity=fixture.identity,
            genesis_cells=fixture.genesis_cells,
            governed_operational_policy=fixture.policy,
            prerequisite_resolver=lambda _commitment: prerequisites,
        )

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V5_OPEN_FAILED"


def test_given_authority_flag_escalation_sql_when_applied_then_schema_rejects_and_state_remains_false(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    store._commit_authority_prerequisites_v5(
        expected_cursor=store.read_cursor(),
        prerequisites=prerequisites,
    )

    with sqlite3.connect(store.path) as connection:
        with pytest.raises(sqlite3.IntegrityError):
            connection.execute(
                "UPDATE spot_v7_authority_provenance_v5 SET settlement_authority = 1"
            )
        connection.rollback()
        assert connection.execute(
            "SELECT settlement_authority FROM spot_v7_authority_provenance_v5"
        ).fetchone() == (0,)
        with pytest.raises(sqlite3.IntegrityError):
            connection.execute(
                "UPDATE spot_v7_activation_blocker_v5 SET governed_release_selection_verified = 1"
            )
        connection.rollback()
        assert connection.execute(
            "SELECT governed_release_selection_verified "
            "FROM spot_v7_activation_blocker_v5 WHERE singleton = 1"
        ).fetchone() == (0,)


def test_given_one_release_evidence_digest_when_schema_is_created_then_digest_is_reusable(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)

    with sqlite3.connect(store.path) as connection:
        schema = connection.execute(
            "SELECT sql FROM sqlite_master "
            "WHERE type = 'table' AND name = 'spot_v7_authority_provenance_v5'"
        ).fetchone()

    assert schema is not None
    normalized = " ".join(str(schema[0]).split())
    assert "release_evidence_sha256 BLOB NOT NULL UNIQUE" not in normalized
    assert "release_evidence_sha256 BLOB NOT NULL CHECK" in normalized


def test_given_unknown_stale_cursor_when_commit_is_attempted_then_cursor_mismatch_rejects_without_writes(
    tmp_path: Path,
    genuine_v4_fixture: v4_test._GenuineV4Fixture,
) -> None:
    fixture = genuine_v4_fixture
    prerequisites = _sealed_prerequisites(fixture)
    store = _make_store(tmp_path, fixture, prerequisites)
    genesis = store.read_cursor()
    unknown_stale = SpotV7AtomicSettlementCursorV1(
        revision=1,
        state_root=genesis.state_root,
        settlement_count=1,
        cell_count=genesis.cell_count,
        last_epoch_id=0,
    )

    rejected = store._commit_authority_prerequisites_v5(
        expected_cursor=unknown_stale,
        prerequisites=prerequisites,
    )
    assert rejected.disposition is SpotV7AtomicSettlementDispositionV1.REJECTED
    assert rejected.reject_reason is SpotV7AtomicSettlementRejectReasonV1.CURSOR_MISMATCH
    assert store.read_cursor() == genesis
    with sqlite3.connect(store.path) as connection:
        assert connection.execute("SELECT count(*) FROM spot_v7_settlements").fetchone() == (0,)
        assert connection.execute(
            "SELECT count(*) FROM spot_v7_authority_provenance_v5"
        ).fetchone() == (0,)
