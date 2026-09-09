"""Bounded JSON wire tests for the owned ZenoLacuna model."""

from __future__ import annotations

import json
from enum import Enum

import pytest

from src.zenolacuna.codec import (
    MAX_JSON_ARRAY_ITEMS,
    MAX_JSON_BYTES,
    MAX_JSON_DEPTH,
    MAX_JSON_STRING_LENGTH,
    decode_candidate,
    decode_decision,
    decode_scope,
    encode,
)
from src.zenolacuna.model import (
    Candidate,
    Decision,
    Evidence,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Policy,
    Profile,
    Question,
    Report,
    Scope,
    ScopeKind,
    Workflow,
)


def _scope() -> Scope:
    return Scope(
        name="scope",
        contexts=("context",),
        outcomes=(Outcome("accept", "accepted", OutcomeKind.ACCEPT),),
        assumptions=(0,),
        contract=((0,),),
        protected=(),
        hypotheses=(Hypothesis("hypothesis", ((0,),)),),
        questions=(Question("question", "What happened?", 1, ("yes",)),),
    )


def _candidate() -> Candidate:
    return Candidate(name="candidate", allowed=((0,),), assumptions=(0,))


def _decision() -> Decision:
    return Decision(
        command_id="command",
        scope_root="scope-root",
        parent="parent",
        question="question",
        answer="answer",
        witness_root="witness-root",
        profile=Profile.SIMULATED,
        actor="actor",
    )


def _payload(raw: bytes) -> dict[str, object]:
    value = json.loads(raw)
    assert type(value) is dict
    return value


def _raw(value: object) -> bytes:
    return json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _code(decoder: object, raw: object) -> str:
    with pytest.raises(LacunaError) as raised:
        decoder(raw)  # type: ignore[operator]
    return raised.value.code


@pytest.mark.parametrize(
    ("value", "decoder"),
    ((_scope(), decode_scope), (_candidate(), decode_candidate), (_decision(), decode_decision)),
)
def test_owned_values_roundtrip_through_canonical_bytes(value: object, decoder: object) -> None:
    raw = encode(value)
    assert raw.endswith(b"\n")
    assert decoder(raw) == value  # type: ignore[operator]


def test_encode_is_plain_compact_ascii_json_and_emits_scope_defaults() -> None:
    raw = encode(_scope())
    payload = _payload(raw)

    assert set(payload) == {
        "name",
        "contexts",
        "outcomes",
        "assumptions",
        "contract",
        "protected",
        "hypotheses",
        "questions",
        "sources",
        "profile",
        "kind",
        "history_bound",
        "omission_family",
        "max_work",
    }
    assert "schema" not in payload
    assert b'": ' not in raw
    assert b", " not in raw
    assert raw.decode("ascii").endswith("}\n")


def test_report_defaults_are_serialized_as_owned_fields() -> None:
    report = Report(
        scope_root="root",
        workflow=Workflow.COMPLETE_FOR_SCOPE,
        evidence=Evidence.EXHAUSTIVE_FINITE,
        code="OK",
        survivors=(0,),
        classes=((0,),),
        policy=Policy("SAFE", None, None, 1),
        witness=None,
    )
    payload = _payload(encode(report))
    assert payload["authority"] == "NONE"
    assert payload["scope_kind"] == ScopeKind.FINITE_RELATION.value
    assert payload["history_bound"] is None
    assert payload["claim"] == "FINITE_MODEL_ONLY"


def test_reordered_objects_are_accepted_and_normalized() -> None:
    payload = _payload(encode(_scope()))
    reordered = {key: payload[key] for key in reversed(tuple(payload))}
    assert encode(decode_scope(_raw(reordered))) == encode(_scope())


def test_duplicate_json_keys_are_rejected_at_the_root() -> None:
    raw = b'{"name":"scope","name":"other"}'
    assert _code(decode_scope, raw) == "JSON_DUPLICATE_KEY"


def test_duplicate_json_keys_are_rejected_inside_nested_records() -> None:
    raw = encode(_scope())
    nested = b'{"kind":"ACCEPT","name":"accept","observation":"accepted"}'
    duplicate = b'{"kind":"ACCEPT","name":"accept","name":"other","observation":"accepted"}'
    assert nested in raw
    assert _code(decode_scope, raw.replace(nested, duplicate, 1)) == "JSON_DUPLICATE_KEY"


@pytest.mark.parametrize("raw", (b"", b"{", b"\xff", b"true", b"[]"))
def test_malformed_or_wrong_root_json_has_stable_rejection(raw: bytes) -> None:
    expected = "JSON_TYPE" if raw in (b"true", b"[]") else "JSON_INVALID"
    assert _code(decode_scope, raw) == expected


def test_input_size_is_bounded_before_parse() -> None:
    assert _code(decode_scope, b" " * (MAX_JSON_BYTES + 1)) == "JSON_TOO_LARGE"


def test_nesting_is_bounded_before_parse() -> None:
    depth = MAX_JSON_DEPTH + 1
    raw = (b"[" * depth) + b"0" + (b"]" * depth)
    assert _code(decode_candidate, raw) == "JSON_DEPTH"


@pytest.mark.parametrize(
    "payload",
    (
        {"name": "candidate", "allowed": [[0.0]], "assumptions": [0]},
        {"name": "candidate", "allowed": [[0]], "assumptions": [True]},
        {"name": "candidate", "allowed": [[0]], "assumptions": [None]},
    ),
)
def test_floats_and_boolean_integer_aliases_are_rejected(payload: dict[str, object]) -> None:
    assert _code(decode_candidate, _raw(payload)) == "JSON_TYPE"


def test_unknown_or_missing_fields_are_rejected_even_for_defaulted_scope_fields() -> None:
    payload = _payload(encode(_scope()))
    missing = dict(payload)
    del missing["sources"]
    unknown = dict(payload)
    unknown["extra"] = 1

    assert _code(decode_scope, _raw(missing)) == "JSON_FIELDS"
    assert _code(decode_scope, _raw(unknown)) == "JSON_FIELDS"


def test_unknown_enum_variant_is_rejected_before_model_validation() -> None:
    payload = _payload(encode(_decision()))
    payload["profile"] = "UNTRUSTED_PROFILE"
    assert _code(decode_decision, _raw(payload)) == "JSON_VARIANT"


def test_nested_shape_errors_are_json_type_errors() -> None:
    payload = _payload(encode(_candidate()))
    payload["allowed"] = [0]
    assert _code(decode_candidate, _raw(payload)) == "JSON_TYPE"


def test_string_and_array_bounds_are_enforced() -> None:
    decision = _payload(encode(_decision()))
    decision["answer"] = "x" * (MAX_JSON_STRING_LENGTH + 1)
    assert _code(decode_decision, _raw(decision)) == "JSON_TYPE"

    candidate = {"name": "candidate", "allowed": [[0]], "assumptions": [0] * (MAX_JSON_ARRAY_ITEMS + 1)}
    assert _code(decode_candidate, _raw(candidate)) == "JSON_TYPE"


def test_valid_wire_shape_preserves_model_validation_codes() -> None:
    payload = _payload(encode(_scope()))
    payload["max_work"] = 0
    assert _code(decode_scope, _raw(payload)) == "INVALID_INTEGER"


def test_malicious_strings_remain_data() -> None:
    marker = '__import__("os").system("touch /tmp/zenolacuna-codec-pwned")'
    decision = _decision()
    payload = _payload(encode(decision))
    payload["answer"] = marker

    decoded = decode_decision(_raw(payload))
    assert decoded.answer == marker


def test_encode_rejects_unowned_values_and_unknown_enum_variants() -> None:
    class ForeignVariant(Enum):
        VALUE = "VALUE"

    assert _code(encode, object()) == "JSON_TYPE"
    assert _code(encode, ForeignVariant.VALUE) == "JSON_VARIANT"
