from __future__ import annotations

import pytest

from src.core.dex_intent_auth_shape_gate import (
    dex_intent_auth_shape_gate_error,
    evaluate_dex_intent_auth_shape_gate,
)


def test_dex_intent_auth_shape_gate_accepts_intent_object_mapping_fields() -> None:
    outcome = evaluate_dex_intent_auth_shape_gate(
        intent_object_mode=True,
        fields_object_ok=True,
        explicit_fields_present=False,
        explicit_fields_mapping_ok=False,
        salt_present=True,
    )

    assert outcome.use_object_fields is True
    assert outcome.use_explicit_mapping_fields is False
    assert outcome.use_transport_flattened_fields is False
    assert outcome.include_salt is True
    assert outcome.shape_ok is True
    assert dex_intent_auth_shape_gate_error(outcome) is None


def test_dex_intent_auth_shape_gate_rejects_intent_object_non_mapping_fields() -> None:
    outcome = evaluate_dex_intent_auth_shape_gate(
        intent_object_mode=True,
        fields_object_ok=False,
        explicit_fields_present=False,
        explicit_fields_mapping_ok=False,
        salt_present=False,
    )

    assert outcome.shape_ok is False
    assert dex_intent_auth_shape_gate_error(outcome) == "intent.fields must be a mapping"


def test_dex_intent_auth_shape_gate_accepts_transport_explicit_fields_mapping() -> None:
    outcome = evaluate_dex_intent_auth_shape_gate(
        intent_object_mode=False,
        fields_object_ok=True,
        explicit_fields_present=True,
        explicit_fields_mapping_ok=True,
        salt_present=False,
    )

    assert outcome.mapping_mode is True
    assert outcome.use_object_fields is False
    assert outcome.use_explicit_mapping_fields is True
    assert outcome.use_transport_flattened_fields is False
    assert outcome.shape_ok is True


def test_dex_intent_auth_shape_gate_rejects_transport_non_mapping_explicit_fields() -> None:
    outcome = evaluate_dex_intent_auth_shape_gate(
        intent_object_mode=False,
        fields_object_ok=True,
        explicit_fields_present=True,
        explicit_fields_mapping_ok=False,
        salt_present=True,
    )

    assert outcome.shape_ok is False
    assert dex_intent_auth_shape_gate_error(outcome) == "intent.fields must be a mapping when present"


def test_dex_intent_auth_shape_gate_rejects_non_flag_inputs() -> None:
    with pytest.raises(TypeError):
        evaluate_dex_intent_auth_shape_gate(
            intent_object_mode="yes",
            fields_object_ok=True,
            explicit_fields_present=False,
            explicit_fields_mapping_ok=False,
            salt_present=False,
        )
