"""Focused F04 whole-layout fixed-point tests."""

from __future__ import annotations

from experiments.fcis_m6_f04_fixed_point_check import build_layout, build_mutation_payloads
from src.core.fcis_m6_f02_history_encoder import encode_layout_v1
from src.core.fcis_m6_f04_fixed_point import (
    F04FixedPointCodeV1,
    F04FixedPointRejectV1,
    F04FixedPointSuccessV1,
    check_whole_layout_fixed_point,
)


def test_fixed_point_gate_returns_complete_source_owned_layout() -> None:
    layout = build_layout()
    result = check_whole_layout_fixed_point(encode_layout_v1(layout))

    assert type(result) is F04FixedPointSuccessV1
    assert result.layout == layout
    assert result.history.current_state_root == layout.header.current_state_root
    assert result.canonical_layout_bytes == encode_layout_v1(layout)


def test_fixed_point_gate_rejects_invalid_mutants_and_preserves_pending_ack() -> None:
    mutants = build_mutation_payloads()
    assert len(mutants) == 26

    for name, payload in mutants.items():
        result = check_whole_layout_fixed_point(payload)
        if name == "ack_rows:missing":
            assert type(result) is F04FixedPointSuccessV1
        else:
            assert type(result) is F04FixedPointRejectV1
            assert result.code is F04FixedPointCodeV1.REOPEN_REJECTED
            assert result.source_code is not None


def test_fixed_point_gate_rejects_untyped_payload_without_partial_value() -> None:
    result = check_whole_layout_fixed_point(object())

    assert type(result) is F04FixedPointRejectV1
    assert result.code is F04FixedPointCodeV1.WRONG_EXACT_TYPE
    assert result.source_code is None
