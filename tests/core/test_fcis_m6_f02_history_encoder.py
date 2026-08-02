"""Focused F02 canonical history encoder tests."""

from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_f02_history_encoder_check import build_history
from src.core.fcis_m6_f02_history_encoder import (
    F02DurableLayoutV1,
    F02HistoryEncoderError,
    encode_history,
    encode_layout_v1,
)


def test_encoder_emits_all_parallel_row_families_from_one_history() -> None:
    layout = encode_history(build_history())

    assert layout.header.history_count == len(layout.history_rows) == 1
    assert layout.header.evidence_count == len(layout.evidence_rows) == 8
    assert layout.header.nullifier_count == len(layout.nullifier_rows) == 1
    assert layout.header.outbox_count == len(layout.outbox_rows) == 1
    assert layout.header.authority_count == len(layout.authority_rows) == 4
    assert layout.header.ack_count == len(layout.ack_rows) == 1
    assert layout.history_rows[0].atom.sequence == 1
    assert layout.evidence_rows[0].kind.value == "anf"
    assert layout.evidence_rows[-1].kind.value == "outbox"


def test_encoder_is_deterministic_and_layout_root_covers_complete_layout() -> None:
    first = encode_history(build_history())
    second = encode_history(build_history())

    assert first.layout_root == second.layout_root
    assert encode_layout_v1(first) == encode_layout_v1(second)


def test_encoder_rejects_crossed_source_context_and_ack() -> None:
    history = build_history()
    with pytest.raises(F02HistoryEncoderError, match="deployment context"):
        replace(history, deployment_config_root="0x" + "a" * 64)

    ack = history.acks[0]
    with pytest.raises(F02HistoryEncoderError, match="provenance"):
        replace(history, acks=(replace(ack, commit_id="0x" + "b" * 64),))


def test_layout_constructor_rejects_missing_or_reordered_rows() -> None:
    layout = encode_history(build_history())

    with pytest.raises(F02HistoryEncoderError, match="evidence"):
        replace(layout, evidence_rows=layout.evidence_rows[:-1])
    with pytest.raises(F02HistoryEncoderError, match="evidence"):
        replace(layout, evidence_rows=tuple(reversed(layout.evidence_rows)))


def test_encoder_input_and_layout_types_fail_closed() -> None:
    with pytest.raises(F02HistoryEncoderError, match="exact F02 history"):
        encode_history({})

    layout = encode_history(build_history())
    with pytest.raises(F02HistoryEncoderError, match="exact F02 layout"):
        encode_layout_v1(object())
    assert type(layout) is F02DurableLayoutV1
