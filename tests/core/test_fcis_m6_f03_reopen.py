"""Focused F03 total reopen tests."""

from __future__ import annotations

import json

from experiments.fcis_m6_f03_reopen_check import build_layout
from src.core.fcis_m6_f02_history_encoder import encode_layout_v1
from src.core.fcis_m6_f03_reopen import (
    F03ReopenCodeV1,
    F03ReopenRejectV1,
    F03ReopenSuccessV1,
    reopen_layout,
    reopen_layout_bytes,
)
from src.state.canonical import canonical_json_bytes


def test_reopen_reconstructs_one_complete_history_and_fixed_point_bytes() -> None:
    layout = build_layout()
    encoded = encode_layout_v1(layout)

    result = reopen_layout_bytes(encoded)

    assert type(result) is F03ReopenSuccessV1
    assert result.history.current_state_root == layout.header.current_state_root
    assert result.layout_root == layout.layout_root
    assert result.canonical_layout_bytes == encoded


def test_reopen_rejects_missing_surplus_and_reordered_rows() -> None:
    layout = build_layout()
    wire = json.loads(encode_layout_v1(layout).decode("utf-8"))
    value = wire["value"]
    assert type(value) is dict

    evidence = value["evidence_rows"]
    assert type(evidence) is list
    evidence.pop()
    missing = reopen_layout_bytes(canonical_json_bytes(wire))
    assert type(missing) is F03ReopenRejectV1

    wire = json.loads(encode_layout_v1(layout).decode("utf-8"))
    value = wire["value"]
    assert type(value) is dict
    evidence = value["evidence_rows"]
    assert type(evidence) is list
    evidence.reverse()
    reordered = reopen_layout_bytes(canonical_json_bytes(wire))
    assert type(reordered) is F03ReopenRejectV1


def test_reopen_rejects_selected_root_mutation_and_noncanonical_bytes() -> None:
    layout = build_layout()
    wire = json.loads(encode_layout_v1(layout).decode("utf-8"))
    value = wire["value"]
    assert type(value) is dict
    value["layout_root"] = "0x" + "f" * 64
    selected_root = reopen_layout_bytes(canonical_json_bytes(wire))
    assert type(selected_root) is F03ReopenRejectV1

    noncanonical = reopen_layout_bytes(b" " + encode_layout_v1(layout))
    assert type(noncanonical) is F03ReopenRejectV1
    assert noncanonical.code is F03ReopenCodeV1.NONCANONICAL_BYTES


def test_reopen_rejects_wrong_type_and_incomplete_object() -> None:
    assert type(reopen_layout(object())) is F03ReopenRejectV1
    incomplete = object.__new__(type(build_layout()))
    result = reopen_layout(incomplete)
    assert type(result) is F03ReopenRejectV1


def test_reopen_rejects_invalid_wire_bytes() -> None:
    invalid_json = reopen_layout_bytes(b"{")
    invalid_utf8 = reopen_layout_bytes(b"\xff")
    invalid_text = reopen_layout_bytes(b"not-json")
    assert type(invalid_json) is F03ReopenRejectV1
    assert type(invalid_utf8) is F03ReopenRejectV1
    assert type(invalid_text) is F03ReopenRejectV1
    assert invalid_json.code is F03ReopenCodeV1.INVALID_JSON
    assert invalid_utf8.code is F03ReopenCodeV1.INVALID_UTF8
    assert invalid_text.code is F03ReopenCodeV1.INVALID_JSON
