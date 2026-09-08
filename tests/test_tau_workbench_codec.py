"""Closed task decoding preserves exact bytes and rejects ambiguous requests."""

import json

import pytest

from src.tau_workbench.codec import MAX_TASK_BYTES, decode_task, encode_task
from src.tau_workbench.examples import message_task


def test_task_roundtrip_preserves_every_program_and_subject() -> None:
    task = message_task()
    decoded = decode_task(json.dumps(encode_task(task)))
    assert decoded == task
    assert decoded.subject_id == task.subject_id


@pytest.mark.parametrize("field, value", [
    ("schema", "tau-workbench/task-v2"), ("bits", True), ("bits", 8.0),
    ("unexpected", "field"), ("inputs", [0, 0]), ("expected", [True] * 64),
])
def test_task_unknown_versions_fields_and_inexact_domain_values_reject(field, value) -> None:
    data = encode_task(message_task())
    data[field] = value
    with pytest.raises(ValueError):
        decode_task(json.dumps(data))


def test_nested_duplicate_source_is_rejected() -> None:
    text = json.dumps(encode_task(message_task()))
    ambiguous = text.replace('"source":', '"source": "def transform(x): return x", "source":', 1)
    with pytest.raises(ValueError, match="duplicate"):
        decode_task(ambiguous)


@pytest.mark.parametrize("text", [" " * (MAX_TASK_BYTES + 1), "[" * 1001, "\ud800"])
def test_oversize_deep_or_non_utf8_task_rejects(text) -> None:
    with pytest.raises(ValueError):
        decode_task(text)


def test_source_type_is_exact_at_decode_boundary() -> None:
    data = encode_task(message_task())
    data["stages"][0]["programs"][0]["source"] = ["def transform(x): return x"]
    with pytest.raises(ValueError, match="program_source_text"):
        decode_task(json.dumps(data))
