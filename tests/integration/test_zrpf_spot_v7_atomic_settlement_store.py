"""BDD and adversarial evidence for the non-authoritative Spot V7 atomic store."""

from __future__ import annotations

import copy
import pickle
import sqlite3
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from threading import Barrier
from unittest.mock import patch

import pytest

import src.integration.zrpf_spot_v7_atomic_settlement_store as store_module
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _seal_test_only_spot_v7_settlement_v1,
    _SpotV7SettlementCandidateInputV1,
    _TestOnlySealedSpotV7SettlementV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_store import (
    SQLiteSpotV7AtomicSettlementStoreV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1,
    SpotV7AssetEffectV1,
    SpotV7AtomicSettlementDispositionV1,
    SpotV7AtomicSettlementRejectReasonV1,
    SpotV7AtomicSettlementStoreIdentityV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    spot_v7_cell_transitions_root_v1,
)


def _hash(seed: int) -> str:
    return f"0x{seed:064x}"


def _subject(byte: int, length: int) -> str:
    return "0x" + (bytes([byte]) * length).hex()


_SENDER = _subject(0x11, 48)
_POOL = _subject(0x22, 32)
_INPUT_ASSET = _hash(0x33)
_OUTPUT_ASSET = _hash(0x44)
_RECIPIENT = _subject(0x55, 48)


def _opening(
    kind: SpotV7CellKindV1,
    subject_id: str,
    asset_id: str,
    atoms: int,
) -> SpotV7CellOpeningV1:
    return SpotV7CellOpeningV1(
        kind=kind,
        subject_id=subject_id,
        asset_id=asset_id,
        atoms=atoms,
    )


def _transitions(
    values: tuple[int, int, int, int],
    *,
    input_atoms: int,
    output_atoms: int,
) -> tuple[SpotV7CellTransitionV1, ...]:
    sender_input, pool_input, pool_output, recipient_output = values
    rows = (
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.DEBIT,
            pre=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _SENDER,
                _INPUT_ASSET,
                sender_input,
            ),
            post=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _SENDER,
                _INPUT_ASSET,
                sender_input - input_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.CREDIT,
            pre=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _INPUT_ASSET,
                pool_input,
            ),
            post=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _INPUT_ASSET,
                pool_input + input_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.DEBIT,
            pre=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _OUTPUT_ASSET,
                pool_output,
            ),
            post=_opening(
                SpotV7CellKindV1.POOL_RESERVE,
                _POOL,
                _OUTPUT_ASSET,
                pool_output - output_atoms,
            ),
        ),
        SpotV7CellTransitionV1(
            role=SpotV7CellRoleV1.CREDIT,
            pre=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _RECIPIENT,
                _OUTPUT_ASSET,
                recipient_output,
            ),
            post=_opening(
                SpotV7CellKindV1.ACCOUNT_BALANCE,
                _RECIPIENT,
                _OUTPUT_ASSET,
                recipient_output + output_atoms,
            ),
        ),
    )
    return tuple(sorted(rows, key=lambda row: row.cell_key))


def _identity() -> SpotV7AtomicSettlementStoreIdentityV1:
    return SpotV7AtomicSettlementStoreIdentityV1(
        application_id=_hash(1),
        chain_or_domain_id=_hash(2),
        verified_program_id=_hash(3),
        verified_profile_id=_hash(4),
        verified_program_manifest_root=_hash(5),
        genesis_state_root=_hash(6),
    )


def _initial_cells() -> tuple[SpotV7CellOpeningV1, ...]:
    return tuple(
        sorted(
            (
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_000),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 25),
            ),
            key=lambda row: row.cell_key,
        )
    )


def _candidate(
    seed: int = 100,
    *,
    pre_state_root: str | None = None,
    post_state_root: str | None = None,
    values: tuple[int, int, int, int] = (1_000, 5_000, 8_000, 25),
    input_atoms: int = 100,
    output_atoms: int = 60,
    action_id: str | None = None,
    authorization_nullifier: str | None = None,
    grant_spend_nullifier: str | None = None,
) -> _TestOnlySealedSpotV7SettlementV1:
    identity = _identity()
    action = action_id or _hash(seed + 1)
    transitions = _transitions(values, input_atoms=input_atoms, output_atoms=output_atoms)
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, _INPUT_ASSET, input_atoms),
                SpotV7AssetEffectV1(action, _OUTPUT_ASSET, output_atoms),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    proposal = _SpotV7SettlementCandidateInputV1(
        application_id=identity.application_id,
        chain_or_domain_id=identity.chain_or_domain_id,
        epoch_id=seed,
        verified_program_id=identity.verified_program_id,
        verified_profile_id=identity.verified_profile_id,
        verified_program_manifest_root=identity.verified_program_manifest_root,
        source_child_claim_binding=_hash(seed + 2),
        source_child_journal_sha256=_hash(seed + 3),
        data_availability_certificate_root=_hash(seed + 4),
        data_root=_hash(seed + 5),
        settlement_effect_plan_commitment=_hash(seed + 6),
        pre_state_root=pre_state_root or identity.genesis_state_root,
        post_state_root=post_state_root or _hash(seed + 7),
        economic_action_id=action,
        authorization_nullifier=authorization_nullifier or _hash(seed + 8),
        authorization_grant_spend_nullifier=grant_spend_nullifier or _hash(seed + 9),
        consumed_object_ids=(_hash(seed + 10), _hash(seed + 11)),
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
        asset_effects=effects,
        exact_v7_receipt_bytes=f"receipt-{seed}".encode(),
        exact_v7_journal_bytes=f"journal-{seed}".encode(),
        exact_plan_b_bytes=f"plan-b-{seed}".encode(),
        exact_firecracker_execution_record_bytes=f"execution-{seed}".encode(),
        exact_firecracker_output_bytes=f"output-{seed}".encode(),
    )
    return _seal_test_only_spot_v7_settlement_v1(proposal)


def _store(tmp_path: Path) -> SQLiteSpotV7AtomicSettlementStoreV1:
    directory = tmp_path / "private"
    directory.mkdir(mode=0o700)
    return SQLiteSpotV7AtomicSettlementStoreV1(
        directory / "spot-v7.sqlite3",
        identity=_identity(),
        genesis_cells=_initial_cells(),
    )


def _reopen(store: SQLiteSpotV7AtomicSettlementStoreV1) -> SQLiteSpotV7AtomicSettlementStoreV1:
    return SQLiteSpotV7AtomicSettlementStoreV1(
        store.path,
        identity=_identity(),
        genesis_cells=_initial_cells(),
    )


def _database_rows(path: Path) -> tuple[tuple[str, tuple[tuple[object, ...], ...]], ...]:
    with sqlite3.connect(path) as connection:
        tables = [
            str(row[0])
            for row in connection.execute(
                "SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%' "
                "ORDER BY name"
            )
        ]
        result = []
        for table in tables:
            columns = [str(row[1]) for row in connection.execute(f"PRAGMA table_info({table})")]
            order = ", ".join(columns)
            rows = tuple(connection.execute(f"SELECT * FROM {table} ORDER BY {order}").fetchall())
            result.append((table, rows))
        return tuple(result)


def test_given_raw_verifier_output_when_committing_then_no_authority_entrypoint_exists(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)

    assert not hasattr(store, "commit")
    assert not hasattr(store, "commit_verifier_output")
    assert not hasattr(store, "commit_firecracker_execution")
    assert store.governed_firecracker_binder_available is False
    with pytest.raises(TypeError, match="test-only sealed Spot V7 candidate"):
        store._commit_test_only_sealed_candidate(
            expected_cursor=store.read_cursor(),
            candidate=b"raw SpotSettlementV7VerifierOutputV1 bytes",  # type: ignore[arg-type]
        )
    assert store.read_cursor().revision == 0


def test_python_cell_hashing_matches_the_reviewed_rust_v7_fixed_vector() -> None:
    """Detect drift against one reviewed Rust effect-binding vector."""

    sender = _subject(0xAA, 48)
    pool = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686"
    input_asset = _subject(0x11, 32)
    output_asset = _subject(0x22, 32)
    rows = (
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, input_asset, 5_000),
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, input_asset, 4_000),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, input_asset, 1_000_000),
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, input_asset, 1_001_000),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.DEBIT,
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, output_asset, 2_000_000),
            _opening(SpotV7CellKindV1.POOL_RESERVE, pool, output_asset, 1_998_008),
        ),
        SpotV7CellTransitionV1(
            SpotV7CellRoleV1.CREDIT,
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, output_asset, 100),
            _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, sender, output_asset, 2_092),
        ),
    )
    ordered = tuple(sorted(rows, key=lambda row: row.cell_key))

    assert spot_v7_cell_transitions_root_v1(ordered) == (
        "0xe7750210d2ebbcad884ec908e5f371405a53c423d5adbf3bc340c74dc709787b"
    )


def test_test_only_capability_cannot_be_copied_pickled_or_claim_authority() -> None:
    candidate = _candidate()

    assert candidate.settlement_authority is False
    assert candidate.production_authority is False
    assert candidate.firecracker_execution_verified is False
    assert candidate.authority_blocked_reason == (
        SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
    )
    for operation in (copy.copy, copy.deepcopy, pickle.dumps):
        with pytest.raises(TypeError):
            operation(candidate)
    with pytest.raises(TypeError, match="cannot be mutated"):
        candidate._input = candidate._input


@pytest.mark.parametrize("direction", ["all_deposits", "all_withdrawals"])
def test_restricted_spot_candidate_requires_opposite_global_leg_directions(
    direction: str,
) -> None:
    base = _candidate(output_atoms=10)
    action = base.economic_action_id
    if direction == "all_deposits":
        rows = (
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_000),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 900),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_100),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 25),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 15),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_010),
            ),
        )
    else:
        rows = (
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 5_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _INPUT_ASSET, 4_900),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_000),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _SENDER, _INPUT_ASSET, 1_100),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.DEBIT,
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 8_000),
                _opening(SpotV7CellKindV1.POOL_RESERVE, _POOL, _OUTPUT_ASSET, 7_990),
            ),
            SpotV7CellTransitionV1(
                SpotV7CellRoleV1.CREDIT,
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 25),
                _opening(SpotV7CellKindV1.ACCOUNT_BALANCE, _RECIPIENT, _OUTPUT_ASSET, 35),
            ),
        )
    transitions = tuple(sorted(rows, key=lambda row: row.cell_key))
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, _INPUT_ASSET, 100),
                SpotV7AssetEffectV1(action, _OUTPUT_ASSET, 10),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    proposal = replace(
        base._input,
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
        asset_effects=effects,
    )

    with pytest.raises(
        ValueError,
        match="restricted Spot V7 requires one input leg and one output leg",
    ):
        _seal_test_only_spot_v7_settlement_v1(proposal)


@pytest.mark.parametrize("method_name", ["read_cursor", "read_cells", "get_receipt"])
def test_read_entrypoints_hold_one_sqlite_snapshot_through_history_validation(
    tmp_path: Path,
    method_name: str,
) -> None:
    store = _store(tmp_path)
    observed: list[bool] = []
    real_validate = store_module._validate_complete_spot_v7_history

    def assert_transaction(connection: sqlite3.Connection) -> None:
        observed.append(connection.in_transaction)
        real_validate(connection)

    with patch.object(
        store_module,
        "_validate_complete_spot_v7_history",
        side_effect=assert_transaction,
    ):
        if method_name == "read_cursor":
            store.read_cursor()
        elif method_name == "read_cells":
            store.read_cells()
        else:
            store.get_receipt(_hash(900))

    assert observed == [True]


def test_given_test_sealed_v7_candidate_when_committed_then_state_and_ids_move_atomically(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert result.committed is True
    assert result.settlement_authority is False
    assert result.production_authority is False
    assert result.head_cursor.revision == 1
    assert result.head_cursor.state_root == candidate.post_state_root
    assert result.receipt is not None
    assert result.receipt.firecracker_execution_verified is False
    assert result.receipt.settlement_authority is False
    assert result.receipt.production_authority is False
    assert result.receipt.receipt_sha256 == candidate.receipt_sha256
    assert result.receipt.firecracker_execution_record_sha256 == (
        candidate.firecracker_execution_record_sha256
    )
    assert result.receipt.economic_action_id == candidate.economic_action_id
    assert result.receipt.authorization_nullifier == candidate.authorization_nullifier
    assert result.receipt.authorization_grant_spend_nullifier == (
        candidate.authorization_grant_spend_nullifier
    )
    cells = {cell.cell_key: cell for cell in store.read_cells()}
    assert cells == {row.post.cell_key: row.post for row in candidate.cell_transitions}


@pytest.mark.parametrize("mode", ["cursor", "pre_state", "cell_pre_state"])
def test_given_stale_or_mismatched_state_when_committing_then_reject_is_no_op(
    tmp_path: Path,
    mode: str,
) -> None:
    store = _store(tmp_path)
    expected = store.read_cursor()
    candidate = _candidate()
    if mode == "cursor":
        expected = replace(expected, state_root=_hash(999))
        expected_reason = SpotV7AtomicSettlementRejectReasonV1.CURSOR_MISMATCH
    elif mode == "pre_state":
        candidate = _candidate(pre_state_root=_hash(998))
        expected_reason = SpotV7AtomicSettlementRejectReasonV1.PRE_STATE_ROOT_MISMATCH
    else:
        candidate = _candidate(values=(999, 5_000, 8_000, 25))
        expected_reason = SpotV7AtomicSettlementRejectReasonV1.CELL_PRE_STATE_MISMATCH
    before = _database_rows(store.path)

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=expected,
        candidate=candidate,
    )

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.REJECTED
    assert result.reject_reason is expected_reason
    assert _database_rows(store.path) == before


def test_given_lost_response_when_exact_candidate_retries_then_result_is_idempotent(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    candidate = _candidate()
    committed = store._commit_test_only_sealed_candidate(
        expected_cursor=initial,
        candidate=candidate,
    )

    retried = store._commit_test_only_sealed_candidate(
        expected_cursor=initial,
        candidate=candidate,
    )

    assert committed.committed is True
    assert retried.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY
    assert retried.receipt == committed.receipt
    assert retried.head_cursor == committed.head_cursor


def test_given_two_concurrent_exact_retries_then_exactly_one_transaction_commits(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    cursor = store.read_cursor()
    candidate = _candidate()
    barrier = Barrier(2)

    def submit():
        barrier.wait()
        return store._commit_test_only_sealed_candidate(
            expected_cursor=cursor,
            candidate=candidate,
        )

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = tuple(executor.map(lambda _index: submit(), range(2)))

    assert sum(result.committed for result in results) == 1
    assert sum(result.idempotent_replay for result in results) == 1
    assert store.read_cursor().revision == 1


def test_given_two_concurrent_conflicts_then_exactly_one_transaction_commits(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    cursor = store.read_cursor()
    first = _candidate(seed=100)
    second = _candidate(seed=200, action_id=first.economic_action_id)
    barrier = Barrier(2)

    def submit(candidate):
        barrier.wait()
        return store._commit_test_only_sealed_candidate(
            expected_cursor=cursor,
            candidate=candidate,
        )

    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = (executor.submit(submit, first), executor.submit(submit, second))
        results = tuple(future.result() for future in futures)

    assert sum(result.committed for result in results) == 1
    assert sum(result.disposition is SpotV7AtomicSettlementDispositionV1.REJECTED for result in results) == 1
    assert store.read_cursor().revision == 1


@pytest.mark.parametrize("reused_field", ["action", "authorization", "grant_spend"])
def test_given_reused_economic_identity_when_next_state_commits_then_duplicate_rejects_no_op(
    tmp_path: Path,
    reused_field: str,
) -> None:
    store = _store(tmp_path)
    first = _candidate()
    first_result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=first,
    )
    assert first_result.committed is True
    values = (900, 5_100, 7_940, 85)
    overrides = {
        "action_id": first.economic_action_id if reused_field == "action" else None,
        "authorization_nullifier": (
            first.authorization_nullifier if reused_field == "authorization" else None
        ),
        "grant_spend_nullifier": (
            first.authorization_grant_spend_nullifier if reused_field == "grant_spend" else None
        ),
    }
    second = _candidate(
        seed=200,
        pre_state_root=first.post_state_root,
        values=values,
        input_atoms=50,
        output_atoms=30,
        **overrides,
    )
    before = _database_rows(store.path)

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=second,
    )

    expected = {
        "action": SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_ECONOMIC_ACTION,
        "authorization": SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_NULLIFIER,
        "grant_spend": SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND,
    }[reused_field]
    assert result.reject_reason is expected
    assert _database_rows(store.path) == before


@pytest.mark.parametrize(
    ("field", "reason"),
    [
        ("exact_v7_receipt_bytes", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_RECEIPT),
        ("exact_v7_journal_bytes", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_JOURNAL),
        (
            "exact_firecracker_execution_record_bytes",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FIRECRACKER_EXECUTION,
        ),
        (
            "exact_firecracker_output_bytes",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_FIRECRACKER_OUTPUT,
        ),
        (
            "settlement_effect_plan_commitment",
            SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN,
        ),
        ("exact_plan_b_bytes", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN),
        ("source_child_claim_binding", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SOURCE_CHILD),
        ("source_child_journal_sha256", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SOURCE_CHILD),
        ("post_state_root", SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_POST_STATE_ROOT),
    ],
)
def test_given_reused_proof_or_execution_identity_then_typed_duplicate_rejects_no_op(
    tmp_path: Path,
    field: str,
    reason: SpotV7AtomicSettlementRejectReasonV1,
) -> None:
    store = _store(tmp_path)
    first = _candidate()
    committed = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=first,
    )
    assert committed.committed is True
    second = _candidate(
        seed=200,
        pre_state_root=first.post_state_root,
        values=(900, 5_100, 7_940, 85),
        input_atoms=50,
        output_atoms=30,
    )
    replacement = getattr(first._input, field)
    proposal = replace(second._input, **{field: replacement})
    candidate = _seal_test_only_spot_v7_settlement_v1(proposal)
    before = _database_rows(store.path)

    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )

    assert result.reject_reason is reason
    assert _database_rows(store.path) == before


def test_given_failure_after_cell_updates_when_transaction_aborts_then_all_rows_roll_back(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    before = _database_rows(store.path)
    candidate = _candidate()
    cursor = store.read_cursor()

    with patch(
        "src.integration._zrpf_spot_v7_atomic_settlement_engine._persist_asset_effects",
        side_effect=sqlite3.IntegrityError("injected post-cell failure"),
    ):
        with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED"):
            store._commit_test_only_sealed_candidate(
                expected_cursor=cursor,
                candidate=candidate,
            )

    assert _database_rows(store.path) == before


def test_given_failure_after_metadata_cas_when_transaction_aborts_then_all_rows_roll_back(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    before = _database_rows(store.path)
    candidate = _candidate()
    cursor = store.read_cursor()
    real_validate = store_module._validate_complete_spot_v7_history
    calls = 0

    def fail_second_validation(connection: sqlite3.Connection) -> None:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise ValueError("injected post-CAS failure")
        real_validate(connection)

    with patch.object(
        store_module,
        "_validate_complete_spot_v7_history",
        side_effect=fail_second_validation,
    ):
        with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_COMMIT_FAILED"):
            store._commit_test_only_sealed_candidate(
                expected_cursor=cursor,
                candidate=candidate,
            )

    assert _database_rows(store.path) == before


def test_given_committed_history_when_store_reopens_then_exact_state_reconstructs(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()
    committed = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )
    assert committed.receipt is not None

    reopened = _reopen(store)

    assert reopened.read_cursor() == committed.head_cursor
    assert reopened.get_receipt(candidate.settlement_commitment) == committed.receipt
    assert reopened.read_cells() == tuple(row.post for row in candidate.cell_transitions)


def test_given_tampered_persisted_cell_when_store_reopens_then_history_replay_rejects(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()
    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )
    assert result.committed is True
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_cells SET atoms_be = zeroblob(16) WHERE cell_key = ?",
            (bytes.fromhex(candidate.cell_transitions[0].cell_key[2:]),),
        )
        connection.commit()

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        _reopen(store)


@pytest.mark.parametrize("tamper", ["updated_revision", "journal", "authority"])
def test_given_tampered_persisted_metadata_when_store_reopens_then_rejects(
    tmp_path: Path,
    tamper: str,
) -> None:
    store = _store(tmp_path)
    candidate = _candidate()
    result = store._commit_test_only_sealed_candidate(
        expected_cursor=store.read_cursor(),
        candidate=candidate,
    )
    assert result.committed is True
    with sqlite3.connect(store.path) as connection:
        if tamper == "updated_revision":
            connection.execute("UPDATE spot_v7_cells SET updated_revision = 0")
        elif tamper == "journal":
            connection.execute(
                "UPDATE spot_v7_settlements SET exact_v7_journal = ?",
                (b"tampered-journal",),
            )
        else:
            with pytest.raises(sqlite3.IntegrityError):
                connection.execute(
                    "UPDATE spot_v7_settlements SET settlement_authority = 1"
                )
            return
        connection.commit()

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        _reopen(store)


def test_given_reopened_store_when_identity_or_genesis_cells_drift_then_open_fails_closed(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)

    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=replace(_identity(), verified_program_id=_hash(700)),
            genesis_cells=_initial_cells(),
        )
    changed = list(_initial_cells())
    changed[0] = replace(changed[0], atoms=changed[0].atoms + 1)
    with pytest.raises(RuntimeError, match="SPOT_V7_ATOMIC_SETTLEMENT_OPEN_FAILED"):
        SQLiteSpotV7AtomicSettlementStoreV1(
            store.path,
            identity=_identity(),
            genesis_cells=tuple(changed),
        )
