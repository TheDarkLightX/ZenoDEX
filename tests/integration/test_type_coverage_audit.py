from __future__ import annotations

import ast

from tools.type_coverage_audit import (
    _check_thresholds,
    _function_annotation_state,
    audit_typing,
)


def _first_function(source: str) -> ast.FunctionDef:
    tree = ast.parse(source)
    function = tree.body[0]
    assert isinstance(function, ast.FunctionDef)
    return function


def test_function_annotation_state_classifies_full_partial_and_untyped() -> None:
    assert _function_annotation_state(_first_function("def f(x: int) -> int:\n    return x\n")) == "full"
    assert _function_annotation_state(_first_function("def f(x: int):\n    return x\n")) == "partial"
    assert _function_annotation_state(_first_function("def f(x):\n    return x\n")) == "none"


def test_current_tracked_python_typing_ratchet_holds() -> None:
    result = audit_typing()
    errors = _check_thresholds(
        result,
        min_src_full_typed_pct=98.9,
        min_core_state_full_typed_pct=97.5,
        min_mypy_configured_present=25,
    )

    assert errors == []
    assert result["scopes"]["src"]["fully_typed_percent"] >= 98.9
    assert result["scopes"]["core_state"]["fully_typed_percent"] >= 97.5
