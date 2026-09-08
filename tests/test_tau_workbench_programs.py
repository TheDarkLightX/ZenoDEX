"""Bounded, independent semantic tests for the Tau workbench program profile."""

from __future__ import annotations

import hashlib
from collections.abc import Callable
from dataclasses import FrozenInstanceError

import pytest

from src.tau_workbench.programs import (
    BEHAVIOR_OUTPUT_RANGE,
    BEHAVIOR_OUTPUT_TYPE,
    BEHAVIOR_OUTPUTS_LENGTH,
    BEHAVIOR_OUTPUTS_TYPE,
    BITS_RANGE,
    BITS_TYPE,
    BOOLEAN_LITERAL,
    BOOLEAN_OPERAND,
    BOOLEAN_OUTPUT,
    COMPARISON_ARITY,
    CONDITION_TYPE,
    CONDITIONAL_BRANCH_TYPE,
    DIVISION_BY_ZERO,
    INTEGER_LITERAL_RANGE,
    MAX_AST_DEPTH,
    MAX_NAME_LENGTH,
    MAX_SOURCE_BYTES,
    PROGRAM_NAME_INVALID,
    PROGRAM_NAME_LIMIT,
    PROGRAM_NAME_TYPE,
    PROGRAM_SOURCE_LIMIT,
    PROGRAM_SOURCE_TYPE,
    RESULT_RANGE,
    SHIFT_AMOUNT,
    SOURCE_AST_DEPTH_LIMIT,
    SOURCE_AST_NODE_LIMIT,
    SOURCE_ENCODING,
    SOURCE_SHAPE,
    SOURCE_SYNTAX,
    UNKNOWN_NAME,
    UNSUPPORTED_EXPRESSION,
    UNSUPPORTED_OPERATOR,
    VALUE_RANGE,
    VALUE_TYPE,
    Behavior,
    Program,
    analyze,
    execute,
)


def _program(expression: str, name: str = "candidate") -> Program:
    source = f"def transform(x):\n    return {expression}\n".encode("utf-8")
    return Program(name, source)


def test_program_is_frozen_and_hashes_exact_source_bytes() -> None:
    source = b"def transform(x):\n    return x\n"
    program = Program("identity", source)

    assert program.sha256 == hashlib.sha256(source).hexdigest()
    with pytest.raises(FrozenInstanceError):
        program.name = "changed"  # type: ignore[misc]


def test_analyze_evaluates_the_complete_closed_domain_and_execute_matches_it() -> None:
    program = _program("(((x * 3 + 5) // 2) ^ (x >> 1)) & 255")

    behavior = analyze(program, 8)
    expected = tuple((((value * 3 + 5) // 2) ^ (value >> 1)) & 255 for value in range(256))

    assert behavior.program is program
    assert behavior.bits == 8
    assert behavior.outputs == expected
    assert tuple(execute(program, value, 8) for value in range(256)) == expected


@pytest.mark.parametrize(
    ("operator", "expected"),
    [
        ("==", lambda value: int(value == 7)),
        ("!=", lambda value: int(value != 7)),
        ("<", lambda value: int(value < 7)),
        ("<=", lambda value: int(value <= 7)),
        (">", lambda value: int(value > 7)),
        (">=", lambda value: int(value >= 7)),
    ],
)
def test_single_comparisons_are_only_used_as_conditional_conditions(
    operator: str, expected: Callable[[int], int]
) -> None:
    program = _program(f"1 if x {operator} 7 else 0")

    assert analyze(program, 4).outputs == tuple(
        expected(value) for value in range(16)
    )


def test_unary_bitwise_and_all_allowed_binary_operators_have_integer_semantics() -> None:
    program = _program("((~(-(+x)) & 255) | ((x ^ 3) % 7))")

    expected = tuple(((~(-(+value)) & 255) | ((value ^ 3) % 7)) for value in range(256))
    assert analyze(program, 8).outputs == expected


def test_behavior_validates_shape_without_treating_outputs_as_credentials() -> None:
    program = _program("x", name="observed")
    observation = Behavior(program, 2, (0, 0, 0, 0))

    assert observation.outputs == (0, 0, 0, 0)
    assert observation != analyze(program, 2)


def test_behavior_rejects_wrong_shape_types_and_domain_values() -> None:
    program = _program("x")

    with pytest.raises(ValueError, match=BEHAVIOR_OUTPUTS_TYPE):
        Behavior(program, 2, [0, 0, 0, 0])  # type: ignore[arg-type]
    with pytest.raises(ValueError, match=BEHAVIOR_OUTPUTS_LENGTH):
        Behavior(program, 2, (0, 0, 0))
    with pytest.raises(ValueError, match=BEHAVIOR_OUTPUT_TYPE):
        Behavior(program, 2, (0, 0, True, 0))
    with pytest.raises(ValueError, match=BEHAVIOR_OUTPUT_RANGE):
        Behavior(program, 2, (0, 0, 0, 4))


@pytest.mark.parametrize(
    ("bad_source", "error_code"),
    [
        ("def transform(x):\n    return True\n", BOOLEAN_LITERAL),
        ("def transform(x):\n    return x == 1\n", BOOLEAN_OUTPUT),
        ("def transform(x):\n    return (x == 1) + 1\n", BOOLEAN_OPERAND),
        ("def transform(x):\n    return 1 if x else 0\n", CONDITION_TYPE),
        (
            "def transform(x):\n    return 1 if x == 1 else (x == 2)\n",
            CONDITIONAL_BRANCH_TYPE,
        ),
        ("def transform(x):\n    return y\n", UNKNOWN_NAME),
        ("def transform(x):\n    return x < 1 < 2\n", COMPARISON_ARITY),
    ],
)
def test_boolean_and_expression_type_boundaries_fail_closed(
    bad_source: str, error_code: str
) -> None:
    with pytest.raises(ValueError, match=error_code):
        analyze(Program("bad", bad_source.encode("utf-8")), 8)


@pytest.mark.parametrize(
    "bad_source",
    [
        "@decorator\ndef transform(x):\n    return x\n",
        "def transform(x: int):\n    return x\n",
        "def transform(x=1):\n    return x\n",
        "def transform(*args):\n    return args[0]\n",
        "async def transform(x):\n    return x\n",
        "def transform(x):\n    \"docstring\"\n    return x\n",
        "import os\ndef transform(x):\n    return x\n",
        "def helper(x):\n    return x\ndef transform(x):\n    return x\n",
        "def transform(x):\n    x = 1\n    return x\n",
        "def transform(x):\n    while x:\n        return x\n    return 0\n",
        "def transform(x):\n    return forbidden(x)\n",
        "def transform(x):\n    return x.value\n",
        "def transform(x):\n    return x[0]\n",
        "def transform(x):\n    return x and 1\n",
        "def transform(x):\n    return 0 if x == 0 else forbidden(x)\n",
    ],
)
def test_unsupported_source_and_dead_branches_are_rejected_before_execution(
    bad_source: str,
) -> None:
    with pytest.raises(ValueError) as error:
        analyze(Program("bad", bad_source.encode("utf-8")), 8)
    assert str(error.value) in {
        SOURCE_SHAPE,
        UNSUPPORTED_EXPRESSION,
        UNSUPPORTED_OPERATOR,
    }


def _balanced_addition(leaf_count: int) -> str:
    if leaf_count == 1:
        return "x"
    left_count = leaf_count // 2
    return f"({_balanced_addition(left_count)} + {_balanced_addition(leaf_count - left_count)})"


def test_ast_node_budget_counts_ordinary_ast_overhead_before_recursive_parsing() -> None:
    expression = _balanced_addition(128)
    program = _program(expression)

    assert len(program.source) <= MAX_SOURCE_BYTES
    with pytest.raises(ValueError, match=SOURCE_AST_NODE_LIMIT):
        analyze(program, 8)


def test_ast_depth_budget_includes_function_and_expression_overhead() -> None:
    expression = "-" * 30 + "x"
    program = _program(expression)

    assert MAX_AST_DEPTH < 40
    with pytest.raises(ValueError, match=SOURCE_AST_DEPTH_LIMIT):
        analyze(program, 8)


def test_source_and_literal_bounds_are_stable() -> None:
    with pytest.raises(ValueError, match=PROGRAM_SOURCE_LIMIT):
        Program("large", b"x" * (MAX_SOURCE_BYTES + 1))
    with pytest.raises(ValueError, match=PROGRAM_SOURCE_TYPE):
        Program("wrong", bytearray(b"source"))  # type: ignore[arg-type]
    with pytest.raises(ValueError, match=SOURCE_ENCODING):
        analyze(Program("encoding", b"\xff"), 8)
    with pytest.raises(ValueError, match=SOURCE_ENCODING):
        analyze(
            Program(
                "latin_cookie",
                b"# coding: latin-1\ndef transform(x):\n    return x\n",
            ),
            8,
        )
    with pytest.raises(ValueError, match=SOURCE_SYNTAX):
        analyze(Program("syntax", b"def transform(x):"), 8)
    with pytest.raises(ValueError, match=INTEGER_LITERAL_RANGE):
        analyze(_program("65536"), 8)
    with pytest.raises(ValueError, match=SHIFT_AMOUNT):
        analyze(_program("x << 9"), 8)
    with pytest.raises(ValueError, match=DIVISION_BY_ZERO):
        analyze(_program("x // 0"), 8)


@pytest.mark.parametrize(
    ("bad_name", "error_code"),
    [
        (True, PROGRAM_NAME_TYPE),
        ("a" * (MAX_NAME_LENGTH + 1), PROGRAM_NAME_LIMIT),
        ("with-dash", PROGRAM_NAME_INVALID),
        ("é", PROGRAM_NAME_INVALID),
        ("class", PROGRAM_NAME_INVALID),
    ],
)
def test_program_names_are_exact_bounded_ascii_identifiers(
    bad_name: object, error_code: str
) -> None:
    with pytest.raises(ValueError, match=error_code):
        Program(bad_name, b"def transform(x):\n    return x\n")  # type: ignore[arg-type]


def test_bits_and_direct_inputs_reject_bool_lookalikes_and_out_of_domain_values() -> None:
    program = _program("x")

    with pytest.raises(ValueError, match=BITS_TYPE):
        analyze(program, True)
    with pytest.raises(ValueError, match=BITS_RANGE):
        analyze(program, 0)
    with pytest.raises(ValueError, match=VALUE_TYPE):
        execute(program, True, 8)
    with pytest.raises(ValueError, match=VALUE_RANGE):
        execute(program, 256, 8)
    with pytest.raises(ValueError, match=RESULT_RANGE):
        analyze(_program("x + 1"), 1)


def test_complete_domain_distinguishes_candidates_that_match_initial_examples() -> None:
    masked = _program("x & 127", name="masked")
    identity = _program("x", name="identity")

    assert all(execute(masked, value, 8) == execute(identity, value, 8) for value in range(64))
    masked_behavior = analyze(masked, 8)
    identity_behavior = analyze(identity, 8)
    assert masked_behavior.outputs[:64] == identity_behavior.outputs[:64]
    assert masked_behavior.outputs[128] == 0
    assert identity_behavior.outputs[128] == 128
    assert masked_behavior.outputs != identity_behavior.outputs


def test_program_and_behavior_observations_have_no_mutable_state() -> None:
    program = _program("x", name="stable")
    behavior = analyze(program, 4)
    original_source = program.source

    assert program.source == original_source
    assert behavior.outputs == tuple(range(16))
    with pytest.raises(TypeError):
        behavior.outputs[0] = 1  # type: ignore[index]
