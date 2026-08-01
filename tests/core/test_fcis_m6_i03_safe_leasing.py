"""I03 safe leasing and expired-lease recovery tests."""

from __future__ import annotations

import sqlite3
from pathlib import Path
from typing import Final

import pytest

from experiments.fcis_m6_h02_sqlite_publication import (
    ANFPublicationRowV1,
    H02Error,
    H02LeaseCodeV1,
    H02LeaseRejectV1,
    H02OutboxLeaseRequestV1,
    H02OutboxLeaseV1,
    H02OutboxStatusV1,
    acquire_outbox_lease,
    create_connection,
    initialize_database,
    read_outbox_delivery_rows,
    read_state,
    reclaim_expired_outbox_leases,
)
from src.core.fcis_durable_retraction import (
    U32_MAX,
    AuthorizedHistoryV1,
    DurableSnapshotV1,
    OutboxEffectV1,
    PublicationAtomV1,
    derive_effect_id,
    encode_history,
    initial_authority_state,
    tagged_digest,
)

_DB_NAME: Final[str] = "i03-leasing.sqlite"


def _snapshot_with_effect() -> tuple[
    DurableSnapshotV1,
    OutboxEffectV1,
    ANFPublicationRowV1,
]:
    authority = initial_authority_state(
        tagged_digest("i03/legacy-writer"),
        tagged_digest("i03/target-writer"),
    )
    genesis_root = tagged_digest("i03/genesis")
    commit_id = tagged_digest("i03/commit")
    payload_root = tagged_digest("i03/payload")
    effect = OutboxEffectV1(
        effect_id=derive_effect_id(
            commit_id=commit_id,
            ordinal=0,
            destination="i03-destination",
            payload_root=payload_root,
            writer_profile_root=authority.active_profile_root,
        ),
        ordinal=0,
        destination="i03-destination",
        payload_root=payload_root,
        adapter_profile_root=tagged_digest("i03/adapter"),
    )
    atom = PublicationAtomV1(
        sequence=1,
        commit_id=commit_id,
        command_root=tagged_digest("i03/command"),
        expected_pre_root=genesis_root,
        post_state_root=tagged_digest("i03/post-state"),
        writer_profile_root=authority.active_profile_root,
        authority_epoch_index=authority.epoch_index,
        authority_state_root=authority.root,
        nullifier_root=tagged_digest("i03/nullifier"),
        response_root=tagged_digest("i03/response"),
        receipt_root=tagged_digest("i03/receipt"),
        decision_root=tagged_digest("i03/decision"),
        bundle_root=tagged_digest("i03/bundle"),
        replay_root=tagged_digest("i03/replay"),
        outbox=(effect,),
    )
    history = AuthorizedHistoryV1(
        genesis_state_root=genesis_root,
        authority_epochs=(authority,),
        atoms=(atom,),
        acks=(),
    )
    snapshot = encode_history(history)
    anf_row = ANFPublicationRowV1(
        commit_id=commit_id,
        atom_root=atom.atom_root,
        anf_root=tagged_digest("i03/anf"),
    )
    return snapshot, effect, anf_row


def _open_workers(
    tmp_path: Path,
) -> tuple[
    sqlite3.Connection,
    sqlite3.Connection,
    DurableSnapshotV1,
    OutboxEffectV1,
]:
    snapshot, effect, anf_row = _snapshot_with_effect()
    database_path = tmp_path / _DB_NAME
    worker_a = create_connection(database_path)
    initialize_database(worker_a, snapshot, (anf_row,))
    worker_b = create_connection(database_path)
    return worker_a, worker_b, snapshot, effect


def _close_workers(
    worker_a: sqlite3.Connection,
    worker_b: sqlite3.Connection,
) -> None:
    worker_a.close()
    worker_b.close()


def test_active_lease_rejects_second_worker_without_state_change(
    tmp_path: Path,
) -> None:
    worker_a, worker_b, snapshot, effect = _open_workers(tmp_path)
    try:
        first = acquire_outbox_lease(
            worker_a,
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-a",
                now=10,
                lease_duration=5,
            ),
        )
        assert isinstance(first, H02OutboxLeaseV1)
        assert first.effect == effect
        assert first.lease_expiry == 15
        assert first.attempt_count == 1

        before = read_state(worker_b)
        second = acquire_outbox_lease(
            worker_b,
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-b",
                now=14,
                lease_duration=5,
            ),
        )
        assert isinstance(second, H02LeaseRejectV1)
        assert second.code is H02LeaseCodeV1.NOT_AVAILABLE
        assert read_state(worker_b) == before
        assert read_state(worker_b).snapshot == snapshot
    finally:
        _close_workers(worker_a, worker_b)


def test_expired_lease_reaper_returns_pending_then_same_effect_is_released(
    tmp_path: Path,
) -> None:
    worker_a, worker_b, _, effect = _open_workers(tmp_path)
    try:
        first = acquire_outbox_lease(
            worker_a,
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-a",
                now=10,
                lease_duration=5,
            ),
        )
        assert isinstance(first, H02OutboxLeaseV1)

        assert reclaim_expired_outbox_leases(worker_a, 14) == 0
        assert reclaim_expired_outbox_leases(worker_a, 15) == 1
        pending = read_outbox_delivery_rows(worker_a, read_state(worker_a).snapshot)
        assert pending[0].status is H02OutboxStatusV1.PENDING
        assert pending[0].lease_owner is None
        assert pending[0].lease_expiry is None
        assert pending[0].attempt_count == 1

        second = acquire_outbox_lease(
            worker_b,
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-b",
                now=15,
                lease_duration=5,
            ),
        )
        assert isinstance(second, H02OutboxLeaseV1)
        assert second.effect.effect_id == first.effect.effect_id
        assert second.effect.payload_root == first.effect.payload_root
        assert second.attempt_count == 2
    finally:
        _close_workers(worker_a, worker_b)


def test_acquisition_reclaims_expired_lease_atomically_with_stable_identity(
    tmp_path: Path,
) -> None:
    worker_a, worker_b, _, effect = _open_workers(tmp_path)
    try:
        first = acquire_outbox_lease(
            worker_a,
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-a",
                now=10,
                lease_duration=5,
            ),
        )
        assert isinstance(first, H02OutboxLeaseV1)
        second = acquire_outbox_lease(
            worker_b,
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-b",
                now=15,
                lease_duration=5,
            ),
        )
        assert isinstance(second, H02OutboxLeaseV1)
        assert second.effect == first.effect
        assert second.worker_id == "worker-b"
        assert second.lease_expiry == 20
        assert second.attempt_count == 2
    finally:
        _close_workers(worker_a, worker_b)


def test_invalid_or_uncommitted_lease_requests_fail_closed(tmp_path: Path) -> None:
    worker_a, worker_b, _, effect = _open_workers(tmp_path)
    try:
        with pytest.raises(H02Error):
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-a",
                now=10,
                lease_duration=0,
            )
        with pytest.raises(H02Error):
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-a",
                now=U32_MAX,
                lease_duration=1,
            )

        before = read_state(worker_b)
        missing = acquire_outbox_lease(
            worker_b,
            H02OutboxLeaseRequestV1(
                effect_id=tagged_digest("i03/missing-effect"),
                worker_id="worker-b",
                now=10,
                lease_duration=5,
            ),
        )
        assert isinstance(missing, H02LeaseRejectV1)
        assert missing.code is H02LeaseCodeV1.NOT_AVAILABLE
        assert read_state(worker_b) == before

        worker_a.execute(
            "UPDATE publication_outbox SET attempt_count = ? WHERE effect_id = ?",
            (U32_MAX, effect.effect_id),
        )
        exhausted = acquire_outbox_lease(
            worker_b,
            H02OutboxLeaseRequestV1(
                effect_id=effect.effect_id,
                worker_id="worker-b",
                now=10,
                lease_duration=5,
            ),
        )
        assert isinstance(exhausted, H02LeaseRejectV1)
        assert exhausted.code is H02LeaseCodeV1.NOT_AVAILABLE
        assert read_state(worker_b).snapshot == before.snapshot
    finally:
        _close_workers(worker_a, worker_b)
