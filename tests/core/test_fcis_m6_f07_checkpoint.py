"""Focused F07 checkpoint and full-tip compaction tests."""

from __future__ import annotations

from experiments.fcis_m6_f07_checkpoint_check import (
    build_genesis_acceptance,
    build_pending_source,
    build_source,
    mutate_checkpoint_without_revalidation,
    recompute_checkpoint_with,
)
from src.core.fcis_m6_f07_checkpoint import (
    F07CheckpointAcceptanceV1,
    F07CheckpointCodeV1,
    F07CheckpointRejectV1,
    F07ProofKindV1,
    build_f07_checkpoint_v1,
    validate_f07_checkpoint_v1,
)


def test_full_tip_checkpoint_binds_replay_and_complete_accumulators() -> None:
    source = build_source()
    genesis = build_genesis_acceptance(source)

    result = build_f07_checkpoint_v1(source, genesis=genesis)

    assert type(result) is F07CheckpointAcceptanceV1
    assert result.removed_history_count == 1
    assert result.removed_nullifier_count == 1
    assert result.removed_outbox_count == 1
    assert result.checkpoint.checkpoint_sequence == 1
    assert result.checkpoint.proof_kind is F07ProofKindV1.REPLAY
    assert result.checkpoint.pending_outbox == ()
    assert result.compacted_snapshot.checkpoint == result.checkpoint

    checked = validate_f07_checkpoint_v1(
        source,
        genesis=genesis,
        checkpoint=result.checkpoint,
    )
    assert type(checked) is F07CheckpointAcceptanceV1
    assert checked == result


def test_pending_outbox_identity_is_retained_by_compaction() -> None:
    source = build_pending_source()
    genesis = build_genesis_acceptance(source)

    result = build_f07_checkpoint_v1(source, genesis=genesis)

    assert type(result) is F07CheckpointAcceptanceV1
    assert len(result.checkpoint.pending_outbox) == 1
    pending = result.checkpoint.pending_outbox[0]
    assert pending.commit_id == source.history.atoms[0].commit_id
    assert pending.record.effect_id == source.history.atoms[0].outbox[0].effect_id

    omitted = recompute_checkpoint_with(result.checkpoint, pending_outbox=())
    rejected = validate_f07_checkpoint_v1(source, genesis=genesis, checkpoint=omitted)
    assert type(rejected) is F07CheckpointRejectV1
    assert rejected.code is F07CheckpointCodeV1.PENDING_OUTBOX_MISMATCH


def test_crossed_state_and_unsupported_snapshot_proof_reject() -> None:
    source = build_source()
    genesis = build_genesis_acceptance(source)
    result = build_f07_checkpoint_v1(source, genesis=genesis)
    assert type(result) is F07CheckpointAcceptanceV1

    crossed = recompute_checkpoint_with(
        result.checkpoint,
        checkpoint_state_root="0x" + "f" * 64,
    )
    crossed_result = validate_f07_checkpoint_v1(source, genesis=genesis, checkpoint=crossed)
    assert type(crossed_result) is F07CheckpointRejectV1
    assert crossed_result.code is F07CheckpointCodeV1.CHECKPOINT_MISMATCH

    snapshot_proof = recompute_checkpoint_with(
        result.checkpoint,
        proof_kind=F07ProofKindV1.APPROVED_SNAPSHOT,
    )
    snapshot_result = validate_f07_checkpoint_v1(
        source,
        genesis=genesis,
        checkpoint=snapshot_proof,
    )
    assert type(snapshot_result) is F07CheckpointRejectV1
    assert snapshot_result.code is F07CheckpointCodeV1.UNSUPPORTED_PROOF


def test_partial_or_untyped_inputs_fail_closed() -> None:
    source = build_source()
    genesis = build_genesis_acceptance(source)
    result = build_f07_checkpoint_v1(source, genesis=genesis)
    assert type(result) is F07CheckpointAcceptanceV1

    partial = mutate_checkpoint_without_revalidation(
        result.checkpoint,
        checkpoint_sequence=0,
    )
    partial_result = validate_f07_checkpoint_v1(source, genesis=genesis, checkpoint=partial)
    assert type(partial_result) is F07CheckpointRejectV1
    assert partial_result.code is F07CheckpointCodeV1.INVALID_CHECKPOINT

    assert type(build_f07_checkpoint_v1(object(), genesis=genesis)) is F07CheckpointRejectV1
    assert type(build_f07_checkpoint_v1(source, genesis=object())) is F07CheckpointRejectV1
    assert type(validate_f07_checkpoint_v1(source, genesis=genesis, checkpoint=object())) is (
        F07CheckpointRejectV1
    )
