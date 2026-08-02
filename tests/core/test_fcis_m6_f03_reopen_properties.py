"""Property-style mutation tests for the F03 reopen boundary."""

from __future__ import annotations

import json
from typing import cast

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_f03_reopen_check import build_layout
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_f02_history_encoder import encode_layout_v1
from src.core.fcis_m6_f03_reopen import F03ReopenRejectV1, reopen_layout_bytes
from src.state.canonical import canonical_json_bytes

_COLLECTIONS = st.sampled_from(("authority_rows", "evidence_rows"))
_MUTATIONS = st.sampled_from(("delete", "duplicate", "reverse"))
_ROOT_LABELS = st.text(
    alphabet=st.characters(
        whitelist_categories=("Ll", "Lu", "Nd"),
        whitelist_characters="_-",
    ),
    min_size=1,
    max_size=32,
)


def _wire() -> dict[str, object]:
    return cast(dict[str, object], json.loads(encode_layout_v1(build_layout())))


def _value(wire: dict[str, object]) -> dict[str, object]:
    raw = wire["value"]
    if type(raw) is not dict:
        raise AssertionError("layout value is not an exact object")
    return cast(dict[str, object], raw)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(collection=_COLLECTIONS, mutation=_MUTATIONS)  # type: ignore[untyped-decorator]
def test_reopen_rejects_every_generated_parallel_collection_mutation(
    collection: str, mutation: str
) -> None:
    wire = _wire()
    rows = _value(wire)[collection]
    if type(rows) is not list or not rows:
        raise AssertionError("fixture collection is not a nonempty list")

    if mutation == "delete":
        rows.pop()
    elif mutation == "duplicate":
        rows.append(rows[-1])
    elif mutation == "reverse":
        if len(rows) < 2:
            # The chosen collections are both multi-row in the governed fixture.
            raise AssertionError("fixture collection cannot test reordering")
        rows.reverse()
    else:
        raise AssertionError("unknown generated mutation")

    result = reopen_layout_bytes(canonical_json_bytes(wire))
    assert type(result) is F03ReopenRejectV1


@settings(max_examples=32, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(label=_ROOT_LABELS)  # type: ignore[untyped-decorator]
def test_reopen_rejects_every_generated_foreign_selected_root(label: str) -> None:
    wire = _wire()
    foreign_root = tagged_digest(f"f03/property/{label}")
    current_value = _value(wire)
    if foreign_root == current_value["layout_root"]:
        raise AssertionError("generated foreign root collided with fixture root")
    current_value["layout_root"] = foreign_root

    result = reopen_layout_bytes(canonical_json_bytes(wire))
    assert type(result) is F03ReopenRejectV1
