from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.dex import DexState
from src.core.fcis_atomic_mount_codec import (
    build_accept_decision_v1,
    build_commit_bundle_v1,
    committed_state_root_v1,
    receipt_root_v1,
)
from src.core.fcis_atomic_mount_values import (
    FCISCommittedDexStateV1,
    FCISOutboxEffectV1,
    FCISReplayUpdateV1,
)
from src.integration.fcis_atomic_commit_reference import (
    FCISReferenceAtomicStoreV1,
    FCISReferenceCommitStatusV1,
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


def _state(balance: int) -> FCISCommittedDexStateV1:
    balances = BalanceTable()
    if balance:
        balances.set(_OWNER, _ASSET, balance)
    legacy = DexState(balances=balances, pools={}, lp_balances=LPTable())
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


def _bundle(
    pre: FCISCommittedDexStateV1,
    post: FCISCommittedDexStateV1,
    *,
    command_label: bytes,
    outbox_payload: bytes,
    value_plan: bytes = b"value-plan-v1",
    expected_last: int = 0,
    new_last: int = 1,
):
    expected_pre_root = committed_state_root_v1(pre)
    context_hash = _digest(b"context")
    command_root = _digest(command_label)
    decision = build_accept_decision_v1(
        expected_pre_root=expected_pre_root,
        execution_context_hash=context_hash,
        command_or_batch_root=command_root,
        next_state=post,
        canonical_patch_bytes=b"canonical-patch-v1",
        value_plan_bytes=value_plan,
        replay_updates=(FCISReplayUpdateV1(_OWNER, expected_last, new_last),),
        outbox_effects=(FCISOutboxEffectV1("dex.receipt", outbox_payload),),
        receipt_detail_bytes=b"receipt-detail-v1",
    )
    bundle = build_commit_bundle_v1(
        expected_pre_root=expected_pre_root,
        execution_context_hash=context_hash,
        command_or_batch_root=command_root,
        decision=decision,
    )
    return decision, bundle


def test_same_state_transition_with_different_effects_has_different_candidate() -> None:
    pre = _state(10)
    post = _state(9)
    first, first_bundle = _bundle(
        pre,
        post,
        command_label=b"same-command",
        outbox_payload=b"first-payload",
    )
    second, _second_bundle = _bundle(
        pre,
        post,
        command_label=b"same-command",
        outbox_payload=b"second-payload",
    )

    assert first.commit_plan.candidate_root != second.commit_plan.candidate_root
    assert first.receipt.candidate_root != second.receipt.candidate_root
    assert (
        first.commit_plan.outbox_plan.records[0].idempotency_key
        != second.commit_plan.outbox_plan.records[0].idempotency_key
    )
    with pytest.raises(ValueError, match="candidate|receipt"):
        replace(
            first_bundle,
            receipt=second.receipt,
            receipt_root=receipt_root_v1(second.receipt),
        )


def test_same_transition_with_different_plan_has_different_candidate() -> None:
    pre = _state(10)
    post = _state(9)
    first, _first_bundle = _bundle(
        pre,
        post,
        command_label=b"same-command",
        outbox_payload=b"payload",
        value_plan=b"first-value-plan",
    )
    second, _second_bundle = _bundle(
        pre,
        post,
        command_label=b"same-command",
        outbox_payload=b"payload",
        value_plan=b"second-value-plan",
    )

    assert first.commit_plan.candidate_root != second.commit_plan.candidate_root


def test_shell_revalidates_nested_payload_after_frozen_bypass() -> None:
    pre = _state(10)
    post = _state(9)
    _decision, bundle = _bundle(
        pre,
        post,
        command_label=b"command",
        outbox_payload=b"payload",
    )
    initial = FCISReferenceAtomicStoreV1(pre)

    object.__setattr__(bundle.commit_plan.value_plan, "canonical_bytes", b"hostile mutation")
    result = commit_bundle_reference_v1(store=initial, bundle=bundle)

    assert result.status is FCISReferenceCommitStatusV1.INVALID
    assert result.store is initial


def test_replay_history_is_retained_as_per_bundle_batches() -> None:
    first_state = _state(10)
    second_state = _state(9)
    third_state = _state(8)
    first_decision, first_bundle = _bundle(
        first_state,
        second_state,
        command_label=b"command-1",
        outbox_payload=b"payload-1",
        expected_last=0,
        new_last=1,
    )
    second_decision, second_bundle = _bundle(
        second_state,
        third_state,
        command_label=b"command-2",
        outbox_payload=b"payload-2",
        expected_last=1,
        new_last=2,
    )

    first_commit = commit_bundle_reference_v1(
        store=FCISReferenceAtomicStoreV1(first_state),
        bundle=first_bundle,
    )
    assert first_commit.status is FCISReferenceCommitStatusV1.PUBLISHED
    second_commit = commit_bundle_reference_v1(
        store=first_commit.store,
        bundle=second_bundle,
    )

    assert second_commit.status is FCISReferenceCommitStatusV1.PUBLISHED
    assert second_commit.store.replay_batches == (
        first_decision.commit_plan.replay_updates,
        second_decision.commit_plan.replay_updates,
    )
