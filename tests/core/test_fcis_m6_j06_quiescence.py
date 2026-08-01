"""J06 quiescence gate and state-preserving rejection tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_j06_quiescence_check import _attempt, _gate, run_checks
from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_j06_quiescence import (
    J06Error,
    J06RejectCodeV1,
    J06WriterAttemptV1,
    reject_writer_v1,
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
    with pytest.raises(J06Error, match="replay head"):
        replace(gate, replay_head_root=dra.tagged_digest("test/divergence"))
    result = reject_writer_v1(gate, _attempt(gate, gate.covered_writer_ids[0]))
    with pytest.raises(J06Error, match="accepted"):
        replace(result, accepted=True)
    with pytest.raises(J06Error, match="state"):
        replace(result, post_head_root=dra.tagged_digest("test/post"))


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
