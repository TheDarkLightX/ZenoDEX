from __future__ import annotations

import json
from pathlib import Path
from typing import Callable

import pytest

from src.core.fcis_b1b_authority_admission import (
    decode_fcis_b1b_authority_v2,
    validate_fcis_b1b_json_resource_bounds_v2,
)
from src.core.fcis_b1b_authority_values import (
    MAX_B1B_JSON_COLLECTION_ITEMS_V2,
    MAX_B1B_JSON_DEPTH_V2,
    MAX_B1B_JSON_NODES_V2,
    B1BAuthorityAdmissionCodeV2,
    B1BAuthorityAdmissionRejectV2,
)


def _resource_code(payload: bytes) -> B1BAuthorityAdmissionCodeV2 | None:
    reject = validate_fcis_b1b_json_resource_bounds_v2(payload)
    return None if reject is None else reject.code


def _nested_array(depth: int) -> bytes:
    return (b"[" * depth) + b"0" + (b"]" * depth)


def _nested_object(depth: int) -> bytes:
    return (b'{"k":' * depth) + b"0" + (b"}" * depth)


def _nested_mixed(depth: int) -> bytes:
    prefixes: list[bytes] = []
    suffixes: list[bytes] = []
    for index in range(depth):
        if index % 2:
            prefixes.append(b'{"k":')
            suffixes.append(b"}")
        else:
            prefixes.append(b"[")
            suffixes.append(b"]")
    return b"".join(prefixes) + b"0" + b"".join(reversed(suffixes))


def _exact_fixture_int(value: object) -> int:
    if type(value) is not int:
        raise AssertionError("fixture parameter must be an exact integer")
    return value


def _exact_fixture_ints(value: object) -> tuple[int, ...]:
    if type(value) is not list or any(type(item) is not int for item in value):
        raise AssertionError("fixture parameter must be an exact integer list")
    return tuple(value)


@pytest.mark.parametrize(
    "builder",
    (_nested_array, _nested_object, _nested_mixed),
)
def test_json_depth_limit_is_exact(builder: Callable[[int], bytes]) -> None:
    assert _resource_code(builder(MAX_B1B_JSON_DEPTH_V2)) is None
    assert _resource_code(builder(MAX_B1B_JSON_DEPTH_V2 + 1)) is (
        B1BAuthorityAdmissionCodeV2.JSON_DEPTH_LIMIT
    )


def test_json_collection_limit_is_exact_for_arrays_and_objects() -> None:
    exact_array = b"[" + b",".join(
        b"0" for _ in range(MAX_B1B_JSON_COLLECTION_ITEMS_V2)
    ) + b"]"
    oversized_array = exact_array[:-1] + b",0]"
    assert _resource_code(exact_array) is None
    assert _resource_code(oversized_array) is (
        B1BAuthorityAdmissionCodeV2.JSON_COLLECTION_LIMIT
    )

    exact_object = b"{" + b",".join(
        f'"k{index}":0'.encode("ascii")
        for index in range(MAX_B1B_JSON_COLLECTION_ITEMS_V2)
    ) + b"}"
    oversized_object = exact_object[:-1] + b',"overflow":0}'
    assert _resource_code(exact_object) is None
    assert _resource_code(oversized_object) is (
        B1BAuthorityAdmissionCodeV2.JSON_COLLECTION_LIMIT
    )


def test_json_node_limit_is_exact() -> None:
    assert MAX_B1B_JSON_NODES_V2 == 256

    def payload(sizes: tuple[int, ...]) -> bytes:
        return b"[" + b",".join(
            b"[" + b",".join(b"0" for _ in range(size)) + b"]"
            for size in sizes
        ) + b"]"

    assert _resource_code(payload((63, 63, 63, 62))) is None
    assert _resource_code(payload((63, 63, 63, 63))) is (
        B1BAuthorityAdmissionCodeV2.JSON_NODE_LIMIT
    )


def test_deep_untrusted_json_returns_a_closed_rejection() -> None:
    result = decode_fcis_b1b_authority_v2(_nested_array(1_000))
    assert type(result) is B1BAuthorityAdmissionRejectV2
    assert result.code is B1BAuthorityAdmissionCodeV2.JSON_DEPTH_LIMIT
    assert result.path == ()


def test_depth_precedes_duplicate_detection_beyond_the_limit() -> None:
    duplicate = b'{"a":0,"a":1}'
    result = decode_fcis_b1b_authority_v2(duplicate)
    assert type(result) is B1BAuthorityAdmissionRejectV2
    assert result.code is B1BAuthorityAdmissionCodeV2.DUPLICATE_FIELD

    deep_duplicate = (b'{"a":' * (MAX_B1B_JSON_DEPTH_V2 + 1)) + duplicate
    deep_duplicate += b"}" * (MAX_B1B_JSON_DEPTH_V2 + 1)
    result = decode_fcis_b1b_authority_v2(deep_duplicate)
    assert type(result) is B1BAuthorityAdmissionRejectV2
    assert result.code is B1BAuthorityAdmissionCodeV2.JSON_DEPTH_LIMIT


@pytest.mark.parametrize(
    "payload",
    (
        b"",
        b"[",
        b'{"unterminated":"value',
        (b"[" * 1_000) + b"0" + (b"]" * 1_000),
        b"\xff",
    ),
)
def test_decoder_never_raises_for_bounded_malformed_bytes(payload: bytes) -> None:
    result = decode_fcis_b1b_authority_v2(payload)
    assert type(result) is B1BAuthorityAdmissionRejectV2


def _shared_resource_payload(case: dict[str, object]) -> bytes:
    kind = case["kind"]
    parameter = case["parameter"]
    if kind == "nested_array":
        return _nested_array(_exact_fixture_int(parameter))
    if kind == "nested_object":
        return _nested_object(_exact_fixture_int(parameter))
    if kind == "nested_mixed":
        return _nested_mixed(_exact_fixture_int(parameter))
    if kind == "flat_array":
        size = _exact_fixture_int(parameter)
        return b"[" + b",".join(b"0" for _ in range(size)) + b"]"
    if kind == "node_fanout":
        sizes = _exact_fixture_ints(parameter)
        return b"[" + b",".join(
            b"[" + b",".join(b"0" for _ in range(size)) + b"]"
            for size in sizes
        ) + b"]"
    if kind == "byte_repeat":
        return b"0" * _exact_fixture_int(parameter)
    if kind == "invalid_utf8":
        return bytes((_exact_fixture_int(parameter),))
    raise AssertionError(f"unknown shared resource-vector kind: {kind}")


def test_shared_python_rust_json_resource_vectors_match_python() -> None:
    fixture = (
        Path(__file__).resolve().parents[1]
        / "fixtures"
        / "fcis_b1b_authority_v2_golden.json"
    )
    limits = json.loads(fixture.read_text(encoding="utf-8"))["json_resource_limits"]
    assert limits["maximum_depth"] == MAX_B1B_JSON_DEPTH_V2
    assert limits["maximum_nodes"] == MAX_B1B_JSON_NODES_V2
    assert limits["maximum_collection_items"] == MAX_B1B_JSON_COLLECTION_ITEMS_V2
    for case in limits["cases"]:
        code = _resource_code(_shared_resource_payload(case))
        actual = None if code is None else code.value
        assert actual == case["expected_code"], case["id"]
