"""J06 quiescence gate and state-preserving rejection tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_j06_quiescence_check import _attempt, _gate, run_checks
from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_j06_quiescence import (
    J06AdmissionResultV1,
    J06Error,
    J06QuiescenceGateV1,
    J06RejectCodeV1,
    J06WriterAttemptV1,
    quiescence_root_from_body_v1,
    reject_writer_v1,
    writer_attempt_root_v1,
)
from tools.build_fcis_m6_j06_quiescence import build_payload


def test_j06_checker_passes() -> None:
    run_checks()


def test_j06_every_covered_writer_rejects_without_state_change() -> None:
    gate = _gate(build_payload())
    for publisher_id in gate.covered_writer_ids:
        result = reject_writer_v1(gate, _attempt(gate, publisher_id))
        assert result.code is J06RejectCodeV1.QUIESCED_WRITER_REJECTED
        assert result.accepted is False
        assert result.state_unchanged is True
        assert result.pre_head_root == result.post_head_root == gate.current_head_root
        assert result.pre_authority_state_root == result.post_authority_state_root


def test_j06_stale_and_uncovered_witnesses_fail_closed() -> None:
    gate = _gate(build_payload())
    base = _attempt(gate, gate.covered_writer_ids[0])
    assert (
        reject_writer_v1(
            gate,
            replace(base, authority_epoch_index=gate.authority_epoch_index + 1),
        ).code
        is J06RejectCodeV1.AUTHORITY_EPOCH_MISMATCH
    )
    assert (
        reject_writer_v1(
            gate, replace(base, expected_head_root=dra.tagged_digest("test/head"))
        ).code
        is J06RejectCodeV1.HEAD_MISMATCH
    )
    uncovered = replace(base, publisher_id="not-in-k01")
    assert reject_writer_v1(gate, uncovered).code is J06RejectCodeV1.ENTRYPOINT_NOT_COVERED


def test_j06_gate_and_result_mutations_reject() -> None:
    gate = _gate(build_payload())
    with pytest.raises(J06Error):
        replace(gate, replay_head_root=dra.tagged_digest("test/divergence"))
    result = reject_writer_v1(gate, _attempt(gate, gate.covered_writer_ids[0]))
    with pytest.raises(J06Error):
        replace(result, accepted=True)
    with pytest.raises(J06Error):
        replace(result, post_head_root=dra.tagged_digest("test/post"))


def test_j06_public_gate_and_result_constructors_are_not_authority_minting_apis() -> None:
    gate = _gate(build_payload())
    with pytest.raises(J06Error, match="verifier-owned"):
        J06QuiescenceGateV1(
            manifest_root=gate.manifest_root,
            entrypoint_inventory_root=gate.entrypoint_inventory_root,
            phase=gate.phase,
            activation_sequence=gate.activation_sequence,
            authority_epoch_index=gate.authority_epoch_index,
            authority_state_root=gate.authority_state_root,
            legacy_profile_root=gate.legacy_profile_root,
            target_profile_root=gate.target_profile_root,
            current_head_root=gate.current_head_root,
            replay_head_root=gate.replay_head_root,
            current_snapshot_root=gate.current_snapshot_root,
            replay_snapshot_root=gate.replay_snapshot_root,
            replay_evidence_root=gate.replay_evidence_root,
            covered_writer_ids=gate.covered_writer_ids,
            evidence_markers=gate.evidence_markers,
            quiescence_root=gate.quiescence_root,
        )
    with pytest.raises(J06Error, match="verifier-owned"):
        attempt = _attempt(gate, gate.covered_writer_ids[0])
        J06AdmissionResultV1(
            gate_root=gate.quiescence_root,
            attempt_root=writer_attempt_root_v1(attempt),
            publisher_id=gate.covered_writer_ids[0],
            writer_profile_root=gate.target_profile_root,
            attempt_authority_epoch_index=attempt.authority_epoch_index,
            attempt_authority_state_root=attempt.authority_state_root,
            attempt_expected_head_root=attempt.expected_head_root,
            attempt_sequence=attempt.sequence,
            command_root=dra.tagged_digest("test/command"),
            commit_id=dra.tagged_digest("test/commit"),
            code=J06RejectCodeV1.QUIESCED_WRITER_REJECTED,
            accepted=False,
            state_unchanged=True,
            pre_head_root=gate.current_head_root,
            post_head_root=gate.current_head_root,
            pre_snapshot_root=gate.current_snapshot_root,
            post_snapshot_root=gate.current_snapshot_root,
            pre_authority_state_root=gate.authority_state_root,
            post_authority_state_root=gate.authority_state_root,
        )


def test_j06_root_codec_rejects_malformed_candidate_body() -> None:
    payload = build_payload()
    body = {
        key: value
        for key, value in payload.items()
        if key
        not in {"schema", "quiescence_root", "profile_id", "pinned_quiescence_root", "nonclaims"}
    }
    body["activation_sequence"] = True
    with pytest.raises(J06Error):
        quiescence_root_from_body_v1(body)


def test_j06_writer_attempt_is_typed_and_bounded() -> None:
    gate = _gate(build_payload())
    with pytest.raises(ValueError):
        J06WriterAttemptV1(
            publisher_id=gate.covered_writer_ids[0],
            writer_profile_root=dra.tagged_digest("test/profile"),
            authority_epoch_index=gate.authority_epoch_index,
            authority_state_root=gate.authority_state_root,
            expected_head_root=gate.current_head_root,
            commit_id=dra.tagged_digest("test/commit"),
            command_root=dra.tagged_digest("test/command"),
            sequence=0,
        )


def test_j06_rejection_identity_includes_the_complete_attempt() -> None:
    gate = _gate(build_payload())
    base = _attempt(gate, gate.covered_writer_ids[0])
    first = reject_writer_v1(gate, replace(base, sequence=gate.activation_sequence + 1))
    second = reject_writer_v1(gate, replace(base, sequence=gate.activation_sequence + 2))
    assert first.code is J06RejectCodeV1.SEQUENCE_MISMATCH
    assert second.code is J06RejectCodeV1.SEQUENCE_MISMATCH
    assert first.attempt_sequence != second.attempt_sequence
    assert first.attempt_root != second.attempt_root
    assert first.to_wire() != second.to_wire()
