"""A small, source-bound interpreter for finite Tau workbench components.

The workbench admits one ordinary Python function with the shape
``def transform(x): return <expression>``.  Source bytes are treated as
untrusted artifact data.  They are parsed into an immutable expression tree
and interpreted directly; this module never evaluates, compiles, or executes
candidate source.

``Behavior`` contains observations from a complete finite-domain evaluation.
It validates only the observation shape, so callers must derive fresh behavior
with :func:`analyze` whenever a raw :class:`Program` is the input.
"""

from __future__ import annotations

import ast
import io
import keyword
import tokenize
from dataclasses import dataclass
from hashlib import sha256
from typing import Final, Literal, NoReturn

MAX_NAME_LENGTH: Final[int] = 64
MAX_SOURCE_BYTES: Final[int] = 8_192
MAX_AST_NODES: Final[int] = 256
MAX_AST_DEPTH: Final[int] = 32
MAX_LITERAL_VALUE: Final[int] = 65_535
MIN_BITS: Final[int] = 1
MAX_BITS: Final[int] = 8
MAX_SHIFT: Final[int] = 8

PROGRAM_TYPE: Final[str] = "program_type"
PROGRAM_NAME_TYPE: Final[str] = "program_name_type"
PROGRAM_NAME_LIMIT: Final[str] = "program_name_limit"
PROGRAM_NAME_INVALID: Final[str] = "program_name_invalid"
PROGRAM_SOURCE_TYPE: Final[str] = "program_source_type"
PROGRAM_SOURCE_LIMIT: Final[str] = "program_source_limit"
BITS_TYPE: Final[str] = "bits_type"
BITS_RANGE: Final[str] = "bits_range"
VALUE_TYPE: Final[str] = "value_type"
VALUE_RANGE: Final[str] = "value_range"
BEHAVIOR_PROGRAM_TYPE: Final[str] = "behavior_program_type"
BEHAVIOR_OUTPUTS_TYPE: Final[str] = "behavior_outputs_type"
BEHAVIOR_OUTPUTS_LENGTH: Final[str] = "behavior_outputs_length"
BEHAVIOR_OUTPUT_TYPE: Final[str] = "behavior_output_type"
BEHAVIOR_OUTPUT_RANGE: Final[str] = "behavior_output_range"
SOURCE_ENCODING: Final[str] = "source_encoding"
SOURCE_SYNTAX: Final[str] = "source_syntax"
SOURCE_AST_NODE_LIMIT: Final[str] = "source_ast_node_limit"
SOURCE_AST_DEPTH_LIMIT: Final[str] = "source_ast_depth_limit"
SOURCE_SHAPE: Final[str] = "source_shape"
SOURCE_UNSUPPORTED: Final[str] = "source_unsupported"
UNSUPPORTED_EXPRESSION: Final[str] = "unsupported_expression"
UNSUPPORTED_OPERATOR: Final[str] = "unsupported_operator"
UNKNOWN_NAME: Final[str] = "unknown_name"
NAME_CONTEXT: Final[str] = "name_context"
CONSTANT_TYPE: Final[str] = "constant_type"
BOOLEAN_LITERAL: Final[str] = "boolean_literal"
INTEGER_LITERAL_RANGE: Final[str] = "integer_literal_range"
BOOLEAN_OPERAND: Final[str] = "boolean_operand"
SHIFT_AMOUNT: Final[str] = "shift_amount"
COMPARISON_ARITY: Final[str] = "comparison_arity"
COMPARISON_OPERATOR: Final[str] = "comparison_operator"
CONDITION_TYPE: Final[str] = "condition_type"
CONDITIONAL_BRANCH_TYPE: Final[str] = "conditional_branch_type"
DIVISION_BY_ZERO: Final[str] = "division_by_zero"
BOOLEAN_OUTPUT: Final[str] = "boolean_output"
RESULT_TYPE: Final[str] = "result_type"
RESULT_RANGE: Final[str] = "result_range"

_Kind = Literal["int", "bool"]


def _reject(code: str) -> NoReturn:
    """Raise the stable public error representation used by this profile."""

    raise ValueError(code)


def _validate_name(value: object) -> None:
    if type(value) is not str:
        _reject(PROGRAM_NAME_TYPE)
    if len(value) > MAX_NAME_LENGTH:
        _reject(PROGRAM_NAME_LIMIT)
    if not value.isascii() or not value.isidentifier() or keyword.iskeyword(value):
        _reject(PROGRAM_NAME_INVALID)


def _validate_source_bytes(value: object) -> None:
    if type(value) is not bytes:
        _reject(PROGRAM_SOURCE_TYPE)
    if len(value) > MAX_SOURCE_BYTES:
        _reject(PROGRAM_SOURCE_LIMIT)


def _validate_bits(bits: object) -> int:
    if type(bits) is not int:
        _reject(BITS_TYPE)
    if bits < MIN_BITS or bits > MAX_BITS:
        _reject(BITS_RANGE)
    return bits


@dataclass(frozen=True, slots=True)
class Program:
    """An immutable named source artifact.

    The constructor validates the artifact envelope and size.  Source grammar
    is checked when a program is analyzed or directly executed, which keeps
    the exact bytes available for source identity even when they are rejected.
    """

    name: str
    source: bytes

    def __post_init__(self) -> None:
        _validate_name(self.name)
        _validate_source_bytes(self.source)

    @property
    def sha256(self) -> str:
        """Return the lowercase SHA-256 digest of the exact source bytes."""

        return sha256(self.source).hexdigest()


@dataclass(frozen=True, slots=True)
class Behavior:
    """A shape-checked complete observation table for one program and domain."""

    program: Program
    bits: int
    outputs: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.program) is not Program:
            _reject(BEHAVIOR_PROGRAM_TYPE)
        _validate_bits(self.bits)
        if type(self.outputs) is not tuple:
            _reject(BEHAVIOR_OUTPUTS_TYPE)
        expected_length = 1 << self.bits
        if len(self.outputs) != expected_length:
            _reject(BEHAVIOR_OUTPUTS_LENGTH)
        limit = expected_length
        for output in self.outputs:
            if type(output) is not int:
                _reject(BEHAVIOR_OUTPUT_TYPE)
            if output < 0 or output >= limit:
                _reject(BEHAVIOR_OUTPUT_RANGE)


@dataclass(frozen=True, slots=True)
class _Expression:
    """The only representation interpreted after source admission."""

    operation: str
    kind: _Kind
    value: int | str | None = None
    operands: tuple["_Expression", ...] = ()


def _validate_program_object(program: object) -> Program:
    if type(program) is not Program:
        _reject(PROGRAM_TYPE)
    _validate_name(program.name)
    _validate_source_bytes(program.source)
    return program


def _check_ast_budget(tree: ast.AST) -> None:
    """Bound every ordinary AST node before any recursive expression walk."""

    pending: list[tuple[ast.AST, int]] = [(tree, 1)]
    node_count = 0
    while pending:
        node, depth = pending.pop()
        node_count += 1
        if node_count > MAX_AST_NODES:
            _reject(SOURCE_AST_NODE_LIMIT)
        if depth > MAX_AST_DEPTH:
            _reject(SOURCE_AST_DEPTH_LIMIT)
        pending.extend((child, depth + 1) for child in ast.iter_child_nodes(node))


def _parse_program(program: Program) -> _Expression:
    program = _validate_program_object(program)
    try:
        encoding, _ = tokenize.detect_encoding(io.BytesIO(program.source).readline)
    except (SyntaxError, UnicodeDecodeError):
        _reject(SOURCE_ENCODING)
    if encoding != "utf-8":
        _reject(SOURCE_ENCODING)
    try:
        source_text = program.source.decode("utf-8")
    except UnicodeDecodeError:
        _reject(SOURCE_ENCODING)
    try:
        tree = ast.parse(source_text, mode="exec", type_comments=True)
    except (SyntaxError, ValueError):
        _reject(SOURCE_SYNTAX)
    except (MemoryError, RecursionError):
        _reject(SOURCE_AST_DEPTH_LIMIT)

    _check_ast_budget(tree)
    if type(tree) is not ast.Module or tree.type_ignores or len(tree.body) != 1:
        _reject(SOURCE_SHAPE)
    function = tree.body[0]
    if type(function) is not ast.FunctionDef:
        _reject(SOURCE_SHAPE)
    if (
        function.name != "transform"
        or function.decorator_list
        or function.returns is not None
        or function.type_comment is not None
        or getattr(function, "type_params", [])
    ):
        _reject(SOURCE_SHAPE)
    _validate_arguments(function.args)
    if len(function.body) != 1 or type(function.body[0]) is not ast.Return:
        _reject(SOURCE_SHAPE)
    return_node = function.body[0]
    if return_node.value is None:
        _reject(SOURCE_SHAPE)
    return _parse_expression(return_node.value)


def _validate_arguments(arguments: ast.arguments) -> None:
    if (
        type(arguments) is not ast.arguments
        or arguments.posonlyargs
        or len(arguments.args) != 1
        or arguments.vararg is not None
        or arguments.kwonlyargs
        or arguments.kw_defaults
        or arguments.kwarg is not None
        or arguments.defaults
    ):
        _reject(SOURCE_SHAPE)
    argument = arguments.args[0]
    if (
        type(argument) is not ast.arg
        or argument.arg != "x"
        or argument.annotation is not None
        or argument.type_comment is not None
    ):
        _reject(SOURCE_SHAPE)


def _parse_expression(node: ast.AST) -> _Expression:
    if type(node) is ast.Constant:
        return _parse_constant(node)
    if type(node) is ast.Name:
        return _parse_name(node)
    if type(node) is ast.UnaryOp:
        return _parse_unary(node)
    if type(node) is ast.BinOp:
        return _parse_binary(node)
    if type(node) is ast.Compare:
        return _parse_comparison(node)
    if type(node) is ast.IfExp:
        return _parse_conditional(node)
    _reject(UNSUPPORTED_EXPRESSION)


def _parse_constant(node: ast.Constant) -> _Expression:
    value = node.value
    if type(value) is bool:
        _reject(BOOLEAN_LITERAL)
    if type(value) is not int:
        _reject(CONSTANT_TYPE)
    if value < 0 or value > MAX_LITERAL_VALUE:
        _reject(INTEGER_LITERAL_RANGE)
    return _Expression("literal", "int", value=value)


def _parse_name(node: ast.Name) -> _Expression:
    if node.id != "x":
        _reject(UNKNOWN_NAME)
    if type(node.ctx) is not ast.Load:
        _reject(NAME_CONTEXT)
    return _Expression("input", "int")


def _parse_unary(node: ast.UnaryOp) -> _Expression:
    operand = _parse_expression(node.operand)
    operator = _unary_operator(node.op)
    if operator is None:
        _reject(UNSUPPORTED_OPERATOR)
    if operand.kind != "int":
        _reject(BOOLEAN_OPERAND)
    return _Expression("unary:" + operator, "int", operands=(operand,))


def _unary_operator(operator: ast.unaryop) -> str | None:
    if type(operator) is ast.UAdd:
        return "+"
    if type(operator) is ast.USub:
        return "-"
    if type(operator) is ast.Invert:
        return "~"
    return None


def _parse_binary(node: ast.BinOp) -> _Expression:
    left = _parse_expression(node.left)
    right = _parse_expression(node.right)
    operator = _binary_operator(node.op)
    if operator is None:
        _reject(UNSUPPORTED_OPERATOR)
    if operator in {"<<", ">>"}:
        _validate_shift_amount(node.right)
    if operator in {"//", "%"} and right.operation == "literal" and right.value == 0:
        _reject(DIVISION_BY_ZERO)
    if left.kind != "int" or right.kind != "int":
        _reject(BOOLEAN_OPERAND)
    return _Expression("binary:" + operator, "int", operands=(left, right))


def _binary_operator(operator: ast.operator) -> str | None:
    if type(operator) is ast.Add:
        return "+"
    if type(operator) is ast.Sub:
        return "-"
    if type(operator) is ast.Mult:
        return "*"
    if type(operator) is ast.FloorDiv:
        return "//"
    if type(operator) is ast.Mod:
        return "%"
    if type(operator) is ast.BitAnd:
        return "&"
    if type(operator) is ast.BitOr:
        return "|"
    if type(operator) is ast.BitXor:
        return "^"
    if type(operator) is ast.LShift:
        return "<<"
    if type(operator) is ast.RShift:
        return ">>"
    return None


def _validate_shift_amount(node: ast.AST) -> None:
    if type(node) is not ast.Constant or type(node.value) is not int:
        _reject(SHIFT_AMOUNT)
    if node.value < 0 or node.value > MAX_SHIFT:
        _reject(SHIFT_AMOUNT)


def _parse_comparison(node: ast.Compare) -> _Expression:
    left = _parse_expression(node.left)
    comparators = tuple(_parse_expression(item) for item in node.comparators)
    if len(node.ops) != 1 or len(comparators) != 1:
        _reject(COMPARISON_ARITY)
    if left.kind != "int" or comparators[0].kind != "int":
        _reject(BOOLEAN_OPERAND)
    operator = _comparison_operator(node.ops[0])
    if operator is None:
        _reject(COMPARISON_OPERATOR)
    return _Expression("compare:" + operator, "bool", operands=(left, comparators[0]))


def _comparison_operator(operator: ast.cmpop) -> str | None:
    if type(operator) is ast.Eq:
        return "=="
    if type(operator) is ast.NotEq:
        return "!="
    if type(operator) is ast.Lt:
        return "<"
    if type(operator) is ast.LtE:
        return "<="
    if type(operator) is ast.Gt:
        return ">"
    if type(operator) is ast.GtE:
        return ">="
    return None


def _parse_conditional(node: ast.IfExp) -> _Expression:
    when_true = _parse_expression(node.body)
    condition = _parse_expression(node.test)
    when_false = _parse_expression(node.orelse)
    if condition.kind != "bool":
        _reject(CONDITION_TYPE)
    if when_true.kind != when_false.kind:
        _reject(CONDITIONAL_BRANCH_TYPE)
    return _Expression(
        "conditional",
        when_true.kind,
        operands=(condition, when_true, when_false),
    )


def _evaluate(expression: _Expression, input_value: int) -> int | bool:
    operation = expression.operation
    if operation == "input":
        return input_value
    if operation == "literal":
        if type(expression.value) is not int:
            raise RuntimeError("invalid literal expression")
        return expression.value
    if operation.startswith("unary:"):
        return _evaluate_unary(operation[6:], expression.operands[0], input_value)
    if operation.startswith("binary:"):
        return _evaluate_binary(operation[7:], expression.operands, input_value)
    if operation.startswith("compare:"):
        return _evaluate_comparison(operation[8:], expression.operands, input_value)
    if operation == "conditional":
        return _evaluate_conditional(expression.operands, input_value)
    raise RuntimeError("invalid parsed expression")


def _evaluate_unary(operator: str, operand: _Expression, input_value: int) -> int:
    value = _evaluate(operand, input_value)
    if type(value) is not int:
        raise RuntimeError("boolean used as unary operand")
    if operator == "+":
        return +value
    if operator == "-":
        return -value
    if operator == "~":
        return ~value
    raise RuntimeError("invalid unary expression")


def _evaluate_binary(
    operator: str, operands: tuple[_Expression, ...], input_value: int
) -> int:
    left = _evaluate(operands[0], input_value)
    right = _evaluate(operands[1], input_value)
    if type(left) is not int or type(right) is not int:
        raise RuntimeError("boolean used as binary operand")
    try:
        if operator == "+":
            return left + right
        if operator == "-":
            return left - right
        if operator == "*":
            return left * right
        if operator == "//":
            return left // right
        if operator == "%":
            return left % right
        if operator == "&":
            return left & right
        if operator == "|":
            return left | right
        if operator == "^":
            return left ^ right
        if operator == "<<":
            return left << right
        if operator == ">>":
            return left >> right
    except ZeroDivisionError:
        _reject(DIVISION_BY_ZERO)
    raise RuntimeError("invalid binary expression")


def _evaluate_comparison(
    operator: str, operands: tuple[_Expression, ...], input_value: int
) -> bool:
    left = _evaluate(operands[0], input_value)
    right = _evaluate(operands[1], input_value)
    if type(left) is not int or type(right) is not int:
        raise RuntimeError("boolean used as comparison operand")
    if operator == "==":
        return left == right
    if operator == "!=":
        return left != right
    if operator == "<":
        return left < right
    if operator == "<=":
        return left <= right
    if operator == ">":
        return left > right
    if operator == ">=":
        return left >= right
    raise RuntimeError("invalid comparison expression")


def _evaluate_conditional(
    operands: tuple[_Expression, ...], input_value: int
) -> int | bool:
    condition = _evaluate(operands[0], input_value)
    if type(condition) is not bool:
        raise RuntimeError("conditional condition is not boolean")
    branch = operands[1] if condition else operands[2]
    return _evaluate(branch, input_value)


def _validate_result(result: int | bool, bits: int) -> int:
    if type(result) is bool:
        _reject(BOOLEAN_OUTPUT)
    if type(result) is not int:
        _reject(RESULT_TYPE)
    if result < 0 or result >= (1 << bits):
        _reject(RESULT_RANGE)
    return result


def execute(program: Program, value: int, bits: int) -> int:
    """Parse and directly evaluate one exact in-domain input.

    ``value`` and the returned result are exact integers in ``[0, 2**bits)``.
    Every source and AST bound is checked before interpretation.
    """

    bits = _validate_bits(bits)
    if type(value) is not int:
        _reject(VALUE_TYPE)
    if value < 0 or value >= (1 << bits):
        _reject(VALUE_RANGE)
    expression = _parse_program(program)
    return _validate_result(_evaluate(expression, value), bits)


def analyze(program: Program, bits: int) -> Behavior:
    """Evaluate a raw program on every integer in its closed finite domain."""

    bits = _validate_bits(bits)
    expression = _parse_program(program)
    outputs = tuple(
        _validate_result(_evaluate(expression, value), bits)
        for value in range(1 << bits)
    )
    return Behavior(program, bits, outputs)


__all__ = [
    "Behavior",
    "MAX_AST_DEPTH",
    "MAX_AST_NODES",
    "MAX_BITS",
    "MAX_LITERAL_VALUE",
    "MAX_NAME_LENGTH",
    "MAX_SHIFT",
    "MAX_SOURCE_BYTES",
    "MIN_BITS",
    "Program",
    "analyze",
    "execute",
]
