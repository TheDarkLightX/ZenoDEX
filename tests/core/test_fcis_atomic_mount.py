from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.dex import DexState
from src.core.fcis_atomic_mount_codec import (
    build_accept_decision_v1,
    build_commit_bundle_v1,
    build_committed_failure_decision_v1,
    build_reject_decision_v1,
    commit_bundle_root_v1,
    committed_state_root_v1,
    encode_decision_v1,
    receipt_root_v1,
)
from src.core.fcis_atomic_mount_values import (
    FCISAcceptV1,
    FCISCommittedDexStateV1,
    FCISCommittedFailureV1,
    FCISOutboxEffectV1,
    FCISRejectV1,
    FCISReplayUpdateV1,
)
from src.integration.fcis_atomic_commit_reference import (
    FCISReferenceAtomicStoreV1,
    FCISReferenceCommitStatusV1,
    FCISReferenceCrashPointV1,
    commit_bundle_reference_v1,
)
from src.state import BalanceTable, LPTable
from src.state.canonical import sha256_hex
from src.state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_nonce_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)
from src.state.nonces import NonceTable
from src.state.state_snapshots import (
    snapshot_fee_accumulator,
    snapshot_oracle,
    snapshot_perps,
    snapshot_vault,
)

_OWNER = "0x" + "11" * 48
_ASSET = "0x" + "01" * 32


def _digest(label: bytes) -> str:
    return sha256_hex(label)


def _state(balance: int, nonce: int = 0) -> FCISCommittedDexStateV1:
    balances = BalanceTable()
    if balance:
        balances.set(_OWNER, _ASSET, balance)
    nonces = NonceTable()
    if nonce:
        nonces.set_last(_OWNER, nonce)
    legacy = DexState(
        balances=balances,
        pools={},
        lp_balances=LPTable(),
        nonces=nonces,
    )
    return FCISCommittedDexStateV1(
        snapshot_version=4,
        balances=admit_legacy_balance_for_differential_v1(legacy.balances),
        pools=admit_legacy_pool_map_for_differential_v1(legacy.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(legacy.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(legacy.nonces),
        vault=snapshot_vault(legacy.vault),
        oracle=snapshot_oracle(legacy.oracle),
        fee_accumulator=snapshot_fee_accumulator(legacy.fee_accumulator),
        perps=snapshot_perps(legacy.perps),
    )


def _accept(pre: FCISCommittedDexStateV1, post: FCISCommittedDexStateV1):
    expected_pre_root = committed_state_root_v1(pre)
    context_hash = _digest(b"context")
    command_root = _digest(b"command")
    decision = build_accept_decision_v1(
        expected_pre_root=expected_pre_root,
        execution_context_hash=context_hash,
        command_or_batch_root=command_root,
        next_state=post,
        canonical_patch_bytes=b"canonical-patch-v1",
        value_plan_bytes=b"value-plan-v1",
        replay_updates=(FCISReplayUpdateV1(_OWNER, 0, 1),),
        outbox_effects=(FCISOutboxEffectV1("dex.receipt", b"event-payload-v1"),),
        receipt_detail_bytes=b"receipt-detail-v1",
    )
    bundle = build_commit_bundle_v1(
        expected_pre_root=expected_pre_root,
        execution_context_hash=context_hash,
        command_or_batch_root=command_root,
        decision=decision,
    )
    return decision, bundle


def test_reject_has_no_successor_plan_replay_or_outbox() -> None:
    reject = build_reject_decision_v1(
        code="nonce_rejected",
        public_reason="nonce rejected",
        detail_bytes=b"nonce:expected=0:observed=2",
    )

    assert type(reject) is FCISRejectV1
    assert not hasattr(reject, "next_state")
    assert not hasattr(reject, "commit_plan")
    assert not hasattr(reject, "replay_updates")
    assert not hasattr(reject, "outbox_plan")
    assert reject.rejection_receipt.candidate_root is None
    with pytest.raises(ValueError, match="ordinary rejection"):
        build_commit_bundle_v1(
            expected_pre_root=_digest(b"pre"),
            execution_context_hash=_digest(b"context"),
            command_or_batch_root=_digest(b"command"),
            decision=reject,
        )


def test_accept_is_deterministic_and_outbox_ids_are_receipt_derived() -> None:
    pre = _state(10)
    post = _state(9, 1)
    first, first_bundle = _accept(pre, post)
    second, second_bundle = _accept(pre, post)

    assert type(first) is FCISAcceptV1
    assert first == second
    assert encode_decision_v1(first) == encode_decision_v1(second)
    assert commit_bundle_root_v1(first_bundle) == commit_bundle_root_v1(second_bundle)
    record = first.commit_plan.outbox_plan.records[0]
    assert record.receipt_root == receipt_root_v1(first.receipt)
    assert record.idempotency_key == second.commit_plan.outbox_plan.records[0].idempotency_key


def test_committed_failure_is_distinct_and_unknown_variant_fails_closed() -> None:
    state = _state(10)
    decision = build_committed_failure_decision_v1(
        reason="protocol_named_failure",
        expected_pre_root=committed_state_root_v1(state),
        execution_context_hash=_digest(b"context"),
        command_or_batch_root=_digest(b"command"),
        next_state=state,
        canonical_patch_bytes=b"failure-patch",
        value_plan_bytes=b"failure-plan",
        replay_updates=(),
        outbox_effects=(),
        receipt_code="protocol_named_failure",
        public_reason="protocol named failure",
    )

    assert type(decision) is FCISCommittedFailureV1
    assert encode_decision_v1(decision) != encode_decision_v1(
        build_reject_decision_v1(code="rejected", public_reason="rejected")
    )
    with pytest.raises(TypeError, match="unknown FCIS decision variant"):
        encode_decision_v1(object())  # type: ignore[arg-type]


def test_bundle_rejects_cross_candidate_receipt_and_payload_mutation() -> None:
    pre = _state(10)
    post = _state(9, 1)
    _first_decision, first = _accept(pre, post)
    other_decision = build_accept_decision_v1(
        expected_pre_root=committed_state_root_v1(pre),
        execution_context_hash=_digest(b"context"),
        command_or_batch_root=_digest(b"different-command"),
        next_state=post,
        canonical_patch_bytes=b"canonical-patch-v1",
        value_plan_bytes=b"value-plan-v1",
        replay_updates=(FCISReplayUpdateV1(_OWNER, 0, 1),),
        outbox_effects=(),
    )

    with pytest.raises(ValueError, match="candidate|receipt"):
        replace(
            first,
            receipt=other_decision.receipt,
            receipt_root=receipt_root_v1(other_decision.receipt),
        )
    with pytest.raises(ValueError, match="does not bind"):
        replace(first.canonical_patch, canonical_bytes=b"mutated")


def test_reference_commit_has_one_publication_point_and_idempotent_retry() -> None:
    pre = _state(10)
    post = _state(9, 1)
    decision, bundle = _accept(pre, post)
    initial = FCISReferenceAtomicStoreV1(pre)

    for crash_point in FCISReferenceCrashPointV1:
        failed = commit_bundle_reference_v1(
            store=initial,
            bundle=bundle,
            crash_point=crash_point,
        )
        assert failed.status is FCISReferenceCommitStatusV1.INJECTED_FAILURE
        assert failed.store is initial

    published = commit_bundle_reference_v1(store=initial, bundle=bundle)
    assert published.status is FCISReferenceCommitStatusV1.PUBLISHED
    assert published.store.state == post
    assert published.store.receipts == (decision.receipt,)
    assert published.store.replay_batches == (decision.commit_plan.replay_updates,)
    assert published.store.outbox_records == decision.commit_plan.outbox_plan.records
    assert published.store.accepted_bundle_roots == (commit_bundle_root_v1(bundle),)

    duplicate = commit_bundle_reference_v1(store=published.store, bundle=bundle)
    assert duplicate.status is FCISReferenceCommitStatusV1.DUPLICATE
    assert duplicate.store is published.store


def test_reference_commit_stale_or_invalid_bundle_publishes_nothing() -> None:
    pre = _state(10)
    post = _state(9, 1)
    _decision, bundle = _accept(pre, post)
    different = FCISReferenceAtomicStoreV1(_state(11))

    stale = commit_bundle_reference_v1(store=different, bundle=bundle)
    assert stale.status is FCISReferenceCommitStatusV1.STALE
    assert stale.store is different

    object.__setattr__(bundle, "receipt_root", _digest(b"mutated-receipt-root"))
    invalid = commit_bundle_reference_v1(store=FCISReferenceAtomicStoreV1(pre), bundle=bundle)
    assert invalid.status is FCISReferenceCommitStatusV1.INVALID
    assert invalid.store == FCISReferenceAtomicStoreV1(pre)
