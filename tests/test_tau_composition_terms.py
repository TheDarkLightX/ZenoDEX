"""Focused semantic and boundary tests for Tau composition Boolean terms."""

from __future__ import annotations

import os
from collections.abc import Callable
from itertools import product

import pytest

from src.tau_composition.runtime import TauRuntime
from src.tau_composition.terms import (
    MAX_NATIVE_TERM_BYTES,
    MAX_NATIVE_TERM_DEPTH,
    MAX_NATIVE_TERM_NODES,
    constant,
    join,
    meet,
    negate,
    parse_native_term,
    variable,
    xor,
)


@pytest.mark.parametrize(
    ("x_value", "y_value", "z_value", "expected"),
    [
        (False, False, False, False),
        (False, False, True, True),
        (False, True, False, True),
        (False, True, True, False),
        (True, False, False, True),
        (True, False, True, True),
        (True, True, False, True),
        (True, True, True, False),
    ],
)
def test_truth_table_matches_fixed_boolean_vectors(
    x_value: bool, y_value: bool, z_value: bool, expected: bool
) -> None:
    term = join(
        meet(variable("x"), negate(variable("y"))),
        xor(variable("y"), variable("z")),
    )

    assert term.evaluate({"x": x_value, "y": y_value, "z": z_value}) is expected


def test_constructors_fold_constants_without_boolean_rewriting() -> None:
    x = variable("x")

    assert meet(constant(True), x) == x
    assert meet(constant(False), x) == constant(False)
    assert join(constant(False), x) == x
    assert join(constant(True), x) == constant(True)
    assert negate(constant(False)) == constant(True)
    assert negate(negate(x)).kind == "negate"
    assert xor(constant(False), x).kind == "xor"


def test_evaluation_rejects_missing_or_non_bool_values() -> None:
    term = variable("x")

    with pytest.raises(ValueError, match="missing variable value"):
        term.evaluate({})
    with pytest.raises(ValueError, match="variable value must be bool"):
        term.evaluate({"x": 1})


def test_substitution_is_simultaneous_and_never_rewrites_replacements() -> None:
    source = join(variable("x"), variable("y"))
    substituted = source.substitute({"x": variable("y"), "y": constant(False)})

    assert substituted.evaluate({"y": True}) is True
    assert substituted.evaluate({"y": False}) is False


def test_native_parser_accepts_lgrs_rhs_juxtaposition_and_typed_coefficients() -> None:
    symbols = {"v0": "x", "v1": "y", "a": "a"}

    assert parse_native_term("v0 v1'", symbols) == meet(variable("x"), negate(variable("y")))
    assert parse_native_term("v0&v1'", symbols) == meet(variable("x"), negate(variable("y")))
    assert parse_native_term("{ a' }:sbf v0", symbols) == meet(negate(variable("a")), variable("x"))
    assert parse_native_term("{ 0 }:sbf", symbols) == constant(False)


def test_native_parser_preserves_conventional_join_and_xor_semantics() -> None:
    symbols = {"v0": "x", "v1": "y"}

    assert parse_native_term("v0|v1", symbols) == join(variable("x"), variable("y"))
    assert parse_native_term("v0^v1", symbols) == xor(variable("x"), variable("y"))


def test_native_parser_xor_precedes_join_regression() -> None:
    parsed = parse_native_term("v0 ^ v1 | v2", {"v0": "x", "v1": "y", "v2": "z"})

    assert parsed.evaluate({"x": True, "y": False, "z": True}) is True


_MIXED_NATIVE_PRECEDENCE: tuple[tuple[str, Callable[[bool, bool, bool], bool]], ...] = (
    ("v0 & v1 ^ v2", lambda x, y, z: (x and y) != z),
    ("v0 ^ v1 & v2", lambda x, y, z: x != (y and z)),
    ("v0 & v1 | v2", lambda x, y, z: (x and y) or z),
    ("v0 | v1 & v2", lambda x, y, z: x or (y and z)),
    ("v0 ^ v1 | v2", lambda x, y, z: (x != y) or z),
    ("v0 | v1 ^ v2", lambda x, y, z: x or (y != z)),
)


@pytest.mark.parametrize(("text", "expected"), _MIXED_NATIVE_PRECEDENCE)
def test_native_parser_matches_independent_mixed_precedence_truth_tables(
    text: str, expected: Callable[[bool, bool, bool], bool]
) -> None:
    parsed = parse_native_term(text, {"v0": "x", "v1": "y", "v2": "z"})

    for x_value, y_value, z_value in product((False, True), repeat=3):
        values = {"x": x_value, "y": y_value, "z": z_value}
        assert parsed.evaluate(values) is expected(x_value, y_value, z_value)


def test_native_parser_mixed_precedence_agrees_with_tau_when_configured() -> None:
    binary = os.environ.get("TAU_COMPOSITION_BIN")
    if binary is None:
        pytest.skip("set TAU_COMPOSITION_BIN to run native Tau precedence parity")
    runtime = TauRuntime(binary, timeout_seconds=8.0)
    symbols = {"x": "v0:sbf", "y": "v1:sbf", "z": "v2:sbf"}
    aliases = {"v0": "x", "v1": "y", "v2": "z"}

    for text, _expected in _MIXED_NATIVE_PRECEDENCE:
        native = text.replace("v0", "v0:sbf").replace("v1", "v1:sbf").replace("v2", "v2:sbf")
        parsed = parse_native_term(text, aliases)
        host = parsed.to_tau(symbols)
        query = f"all v0:sbf, v1:sbf, v2:sbf (({native}) = ({host}))"

        assert runtime.valid(query) is True


def test_tau_rendering_roundtrips_safe_typed_native_symbols() -> None:
    term = xor(join(variable("x"), negate(variable("y"))), variable("z"))
    rendered = term.to_tau({"x": "v0:sbf", "y": "{a}:sbf", "z": "v1"})
    recovered = parse_native_term(rendered, {"v0": "x", "a": "y", "v1": "z"})

    assert rendered == "((v0:sbf|({a}:sbf)')^v1)"
    for x_value, y_value, z_value in product((False, True), repeat=3):
        values = {"x": x_value, "y": y_value, "z": z_value}
        assert recovered.evaluate(values) is term.evaluate(values)


def test_canonical_data_and_hash_are_deterministic_for_the_same_tree() -> None:
    first = meet(variable("x"), negate(variable("y")))
    second = meet(variable("x"), negate(variable("y")))

    assert first.canonical_data() == second.canonical_data()
    assert first.canonical_json() == second.canonical_json()
    assert first.sha256() == second.sha256()
    assert len(first.sha256()) == 64
    assert first.sha256() != meet(variable("y"), negate(variable("x"))).sha256()


def test_names_constants_and_rendered_symbols_reject_injection_or_aliases() -> None:
    with pytest.raises(ValueError, match="invalid variable name"):
        variable("x); always z")
    with pytest.raises(ValueError, match="constant value must be bool"):
        constant(1)

    x = variable("x")
    with pytest.raises(ValueError, match="invalid Tau symbol map value"):
        x.to_tau({"x": "v0);always z"})
    with pytest.raises(ValueError, match="Tau symbol map aliases native symbols"):
        meet(variable("x"), variable("y")).to_tau({"x": "v0", "y": "v0:sbf"})


@pytest.mark.parametrize(
    ("text", "message"),
    [
        ("v9", "unknown symbol"),
        ("v0 := v1", "invalid syntax"),
        ("always v0", "invalid syntax"),
        ("v0[t]", "invalid syntax"),
        ("v0:bv[8]", "invalid syntax"),
        ("v0.", "invalid syntax"),
        ("v0&&v1", "invalid syntax"),
        ("v0|", "invalid syntax"),
    ],
)
def test_native_parser_fails_closed_on_unknown_or_unsupported_syntax(text: str, message: str) -> None:
    with pytest.raises(ValueError, match=message):
        parse_native_term(text, {"v0": "x", "v1": "y"})


def test_native_parser_rejects_ambiguous_adjacent_symbol_segmentation() -> None:
    with pytest.raises(ValueError, match="segmentation is ambiguous"):
        parse_native_term("ab", {"a": "x", "b": "y", "ab": "z"})


def test_native_parser_enforces_size_node_and_depth_bounds() -> None:
    with pytest.raises(ValueError, match="byte limit"):
        parse_native_term("v0" + (" " * MAX_NATIVE_TERM_BYTES), {"v0": "x"})

    too_deep = ("(" * (MAX_NATIVE_TERM_DEPTH + 1)) + "v0" + (")" * (MAX_NATIVE_TERM_DEPTH + 1))
    with pytest.raises(ValueError, match="depth limit"):
        parse_native_term(too_deep, {"v0": "x"})

    too_many_terms = " ".join("v0" for _ in range((MAX_NATIVE_TERM_NODES // 2) + 1))
    with pytest.raises(ValueError, match="node limit"):
        parse_native_term(too_many_terms, {"v0": "x"})


def test_small_expression_operators_match_python_boolean_semantics_exhaustively() -> None:
    x = variable("x")
    y = variable("y")
    terms = (x, y, negate(x), negate(y), constant(False), constant(True), meet(x, y), join(x, y))

    for left, right in product(terms, repeat=2):
        for x_value, y_value in product((False, True), repeat=2):
            values = {"x": x_value, "y": y_value}
            left_value = left.evaluate(values)
            right_value = right.evaluate(values)

            assert meet(left, right).evaluate(values) is (left_value and right_value)
            assert join(left, right).evaluate(values) is (left_value or right_value)
            assert xor(left, right).evaluate(values) is (left_value != right_value)


def test_small_terms_roundtrip_through_native_syntax_for_every_valuation() -> None:
    x = variable("x")
    y = variable("y")
    terms = (x, y, negate(x), meet(x, y), join(x, negate(y)), xor(x, y))

    for term in terms:
        recovered = parse_native_term(term.to_tau({"x": "v0", "y": "v1"}), {"v0": "x", "v1": "y"})
        for x_value, y_value in product((False, True), repeat=2):
            values = {"x": x_value, "y": y_value}
            assert recovered.evaluate(values) is term.evaluate(values)
