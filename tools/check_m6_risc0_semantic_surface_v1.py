#!/usr/bin/env python3
"""Fail closed on an unsupported claim of full-M6 Rust/RISC0 equivalence.

This source-level gate checks two necessary preconditions for the launch-plan
claim that a RISC0 guest runs the same M6 transition semantics as the Python
reference: the Rust state declaration must bind every non-derived Python
execution-state and state-root field, the command declaration must bind every
Python command field, and the visible state-root codec must be canonical-JSON
rather than postcard.
It deliberately cannot establish execution equivalence, receipt validity, or
RISC0 image provenance.  Consequently it remains non-activating even if both
static preconditions hold; an independently checked direct/RISC0 trace suite
and real receipt verifier are still required.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMA_V1 = "zenodex/m6-risc0-semantic-surface/v1"
_RUST_FIELD_RE = re.compile(
    r"^\s*(?:pub(?:\s*\([^)]*\))?\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:",
    re.MULTILINE,
)
_RUST_CANONICAL_CODEC_FUNCTION = "canonical_json_bytes_v1"
_RUST_POSTCARD_CODEC_FUNCTION = "hash_postcard_v1"
_DERIVED_STATE_FIELDS = frozenset(
    {
        "history_root_cache",
        "nullifier_root_cache",
        "outbox_root_cache",
    }
)

NONCLAIMS: tuple[str, ...] = (
    "this is a static source-surface inspection, not a Rust or Python transition proof",
    "matching field names or codec markers do not establish byte-level canonical encoding parity",
    "no RISC0 receipt, image binding, recursive proof, validator finality, data availability, or publication authority is verified",
    "a source inspection cannot provide independent direct/RISC0 execution parity evidence",
    "M6 remains research-only and unmounted regardless of this report",
)
REQUIRED_NEXT_EVIDENCE: tuple[str, ...] = (
    "a versioned full-state Python-to-Rust projection with exact canonical byte vectors",
    "per-command direct Python/Rust outcome, state, delta, history, nullifier, and outbox differential traces",
    "real pinned-image RISC0 receipts whose journals bind those full transition outputs",
    "a verifier-owned activation gate that rejects missing, stale, foreign-image, foreign-profile, and crossed-journal receipts before publication",
)


@dataclass(frozen=True, slots=True)
class _SurfaceInspectionV1:
    python_fields: tuple[str, ...]
    python_execution_fields: tuple[str, ...]
    python_command_fields: tuple[str, ...]
    rust_fields: tuple[str, ...]
    rust_command_fields: tuple[str, ...]
    python_canonical_codec_visible: bool
    rust_canonical_codec_visible: bool
    rust_postcard_state_codec_visible: bool
    rust_transition_function_visible: bool
    errors: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class _SurfaceComparisonV1:
    missing_state_root_fields: tuple[str, ...]
    missing_execution_state_fields: tuple[str, ...]
    missing_command_fields: tuple[str, ...]
    extra_rust_state_fields: tuple[str, ...]
    extra_rust_command_fields: tuple[str, ...]
    canonical_state_codec_match: bool


def _read_source_or_error(path: Path, *, label: str) -> tuple[str, str | None]:
    try:
        return path.read_text(encoding="utf-8"), None
    except (OSError, UnicodeError):
        return "", f"cannot read {label}"


def _class_named(tree: ast.Module, *, name: str) -> ast.ClassDef:
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == name:
            return node
    raise ValueError(f"Python {name} is missing")


def _method_named(class_node: ast.ClassDef, *, name: str) -> ast.FunctionDef | ast.AsyncFunctionDef:
    for member in class_node.body:
        if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)) and member.name == name:
            return member
    raise ValueError(f"Python {class_node.name}.{name} is missing")


def _function_named(tree: ast.Module, *, name: str) -> ast.FunctionDef | ast.AsyncFunctionDef:
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name:
            return node
    raise ValueError(f"Python {name} is missing")


class _DirectCallCollector(ast.NodeVisitor):
    """Collect calls from one already-selected unconditional expression."""

    def __init__(self) -> None:
        self.names: set[str] = set()

    def visit_Call(self, node: ast.Call) -> None:  # noqa: N802 - ast visitor API
        if isinstance(node.func, ast.Name):
            self.names.add(node.func.id)
        self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        return

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:  # noqa: N802
        return

    def visit_Lambda(self, node: ast.Lambda) -> None:  # noqa: N802
        return

    def visit_IfExp(self, node: ast.IfExp) -> None:  # noqa: N802
        return

    def visit_BoolOp(self, node: ast.BoolOp) -> None:  # noqa: N802
        return

    def visit_ListComp(self, node: ast.ListComp) -> None:  # noqa: N802
        return

    def visit_SetComp(self, node: ast.SetComp) -> None:  # noqa: N802
        return

    def visit_DictComp(self, node: ast.DictComp) -> None:  # noqa: N802
        return

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:  # noqa: N802
        return


def _direct_call_names(method: ast.FunctionDef | ast.AsyncFunctionDef) -> frozenset[str]:
    """Return calls from direct simple statements, excluding control-flow bodies."""

    collector = _DirectCallCollector()
    for statement in method.body:
        if isinstance(
            statement,
            (
                ast.If,
                ast.For,
                ast.AsyncFor,
                ast.While,
                ast.Try,
                ast.With,
                ast.AsyncWith,
                ast.Match,
                ast.Raise,
                ast.Break,
                ast.Continue,
            ),
        ):
            # Calls after control flow are not provably on the unconditional
            # path inspected by this intentionally small static gate.
            break
        expression: ast.expr | None = None
        if isinstance(statement, (ast.Expr, ast.Return, ast.Assign, ast.AugAssign)):
            expression = statement.value
        elif isinstance(statement, ast.AnnAssign):
            expression = statement.value
        if expression is not None:
            collector.visit(expression)
        if isinstance(statement, ast.Return):
            break
    return frozenset(collector.names)


def _python_canonical_codec_connected(
    tree: ast.Module,
    *,
    state_class: ast.ClassDef,
) -> bool:
    """Require a visible canonical-codec call on the state-root call path."""

    try:
        state_root = _method_named(state_class, name="state_root")
    except ValueError:
        return False
    state_root_calls = _direct_call_names(state_root)
    if _codec_value_reaches_return(state_root):
        return True
    if "hash_v1" not in state_root_calls:
        return False
    try:
        hash_function = _function_named(tree, name="hash_v1")
    except ValueError:
        return False
    return _codec_value_reaches_return(hash_function)


def _contains_named_call(node: ast.AST, name: str) -> bool:
    return any(
        isinstance(candidate, ast.Call)
        and isinstance(candidate.func, ast.Name)
        and candidate.func.id == name
        for candidate in ast.walk(node)
    )


def _expression_reads_name(node: ast.AST, name: str) -> bool:
    return any(
        isinstance(candidate, ast.Name)
        and isinstance(candidate.ctx, ast.Load)
        and candidate.id == name
        for candidate in ast.walk(node)
    )


def _codec_value_reaches_return(method: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    """Conservatively trace canonical bytes into one unconditional return."""

    codec_values: set[str] = set()
    codec_accumulators: set[str] = set()
    for statement in method.body:
        if isinstance(
            statement,
            (
                ast.If,
                ast.For,
                ast.AsyncFor,
                ast.While,
                ast.Try,
                ast.With,
                ast.AsyncWith,
                ast.Match,
                ast.Raise,
                ast.Break,
                ast.Continue,
            ),
        ):
            break
        if isinstance(statement, (ast.Assign, ast.AnnAssign)):
            value = statement.value
            if value is not None and _contains_named_call(value, "canonical_bytes_v1"):
                targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
                codec_values.update(
                    target.id for target in targets if isinstance(target, ast.Name)
                )
        elif isinstance(statement, ast.Expr):
            expression = statement.value
            if (
                isinstance(expression, ast.Call)
                and isinstance(expression.func, ast.Attribute)
                and isinstance(expression.func.value, ast.Name)
                and _contains_named_call(expression, "canonical_bytes_v1")
            ):
                codec_accumulators.add(expression.func.value.id)
        elif isinstance(statement, ast.Return):
            value = statement.value
            if value is None:
                return False
            return (
                _contains_named_call(value, "canonical_bytes_v1")
                or any(_expression_reads_name(value, name) for name in codec_values)
                or any(_expression_reads_name(value, name) for name in codec_accumulators)
            )
    return False


def _returned_dictionary(method: ast.FunctionDef | ast.AsyncFunctionDef) -> ast.Dict:
    direct_returns = [
        statement.value
        for statement in method.body
        if isinstance(statement, ast.Return) and isinstance(statement.value, ast.Dict)
    ]
    if len(direct_returns) != 1:
        raise ValueError(
            f"Python {method.name} must directly return exactly one dictionary"
        )
    return direct_returns[0]


def _direct_self_fields(root_dictionary: ast.Dict) -> tuple[str, ...]:
    fields: list[str] = []
    seen_keys: set[str] = set()
    for key, value in zip(root_dictionary.keys, root_dictionary.values, strict=True):
        if not isinstance(key, ast.Constant) or not isinstance(key.value, str):
            raise ValueError("Python M6 state root keys must be static strings")
        key_name = key.value
        if key_name in seen_keys:
            raise ValueError("Python M6 state root contains duplicate fields")
        seen_keys.add(key_name)
        is_self_field = (
            isinstance(value, ast.Attribute)
            and isinstance(value.value, ast.Name)
            and value.value.id == "self"
        )
        if key_name == "schema":
            if is_self_field:
                raise ValueError("Python M6 state root schema cannot be state-authored")
            continue
        if not is_self_field or value.attr != key_name:
            raise ValueError(
                f"Python M6 state root field {key_name} must bind self.{key_name}"
            )
        fields.append(key_name)
    if not fields:
        raise ValueError("Python M6 state root has no direct state fields")
    return tuple(fields)


def _annotated_fields(
    class_node: ast.ClassDef,
    *,
    label: str,
) -> tuple[str, ...]:
    """Return source-order declared dataclass fields."""

    fields: list[str] = []
    for member in class_node.body:
        if not isinstance(member, ast.AnnAssign) or not isinstance(member.target, ast.Name):
            continue
        field_name = member.target.id
        fields.append(field_name)
    if not fields:
        raise ValueError(f"Python {label} has no annotated fields")
    if len(fields) != len(set(fields)):
        raise ValueError(f"Python {label} contains duplicate fields")
    return tuple(fields)


def _non_derived_state_fields(state_class: ast.ClassDef) -> tuple[str, ...]:
    """Remove deterministic archive-root caches from the execution surface."""

    declared_fields = _annotated_fields(
        state_class,
        label="M6ApplicationStateV1 execution state",
    )
    # These are deterministic caches of archives committed through separate
    # roots.  They carry no independent transition authority.
    return tuple(field_name for field_name in declared_fields if field_name not in _DERIVED_STATE_FIELDS)


def _python_state_surface(
    source: str,
) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...], bool]:
    """Return Python execution-state, state-root, and command fields in source order."""

    try:
        tree = ast.parse(source, filename="m6_safe_mount_types_v1.py")
    except SyntaxError as exc:
        raise ValueError(f"cannot parse Python M6 types: {exc.msg}") from exc
    state_class = _class_named(tree, name="M6ApplicationStateV1")
    command_class = _class_named(tree, name="GlobalCommandV1")
    state_root_method = _method_named(state_class, name="_state_root_canonical")
    return (
        _non_derived_state_fields(state_class),
        _direct_self_fields(_returned_dictionary(state_root_method)),
        _annotated_fields(command_class, label="GlobalCommandV1"),
        _python_canonical_codec_connected(tree, state_class=state_class),
    )


def _blank_non_newlines(value: str) -> str:
    return "".join("\n" if character == "\n" else " " for character in value)


def _rust_code_only(source: str) -> str:
    """Blank Rust comments and literals before source-surface inspection."""

    output: list[str] = []
    index = 0
    while index < len(source):
        if source.startswith("//", index):
            end = source.find("\n", index + 2)
            end = len(source) if end < 0 else end
            output.append(_blank_non_newlines(source[index:end]))
            index = end
            continue
        if source.startswith("/*", index):
            start = index
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith("/*", index):
                    depth += 1
                    index += 2
                elif source.startswith("*/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError("Rust source has an unterminated block comment")
            output.append(_blank_non_newlines(source[start:index]))
            continue

        raw_prefix_length = 0
        raw_hash_count = 0
        token_boundary = index == 0 or not (source[index - 1].isalnum() or source[index - 1] == "_")
        if token_boundary:
            for prefix in ("br", "cr", "r"):
                if not source.startswith(prefix, index):
                    continue
                cursor = index + len(prefix)
                while cursor < len(source) and source[cursor] == "#":
                    cursor += 1
                if cursor < len(source) and source[cursor] == '"':
                    raw_prefix_length = cursor - index + 1
                    raw_hash_count = cursor - index - len(prefix)
                    break
        if raw_prefix_length:
            start = index
            closing = '"' + ("#" * raw_hash_count)
            end = source.find(closing, index + raw_prefix_length)
            if end < 0:
                raise ValueError("Rust source has an unterminated raw string")
            index = end + len(closing)
            output.append(_blank_non_newlines(source[start:index]))
            continue

        if source[index] == '"':
            start = index
            index += 1
            escaped = False
            while index < len(source):
                character = source[index]
                index += 1
                if escaped:
                    escaped = False
                elif character == "\\":
                    escaped = True
                elif character == '"':
                    break
            else:
                raise ValueError("Rust source has an unterminated string")
            output.append(_blank_non_newlines(source[start:index]))
            continue

        is_simple_character = (
            source[index] == "'"
            and index + 2 < len(source)
            and source[index + 2] == "'"
        )
        is_escaped_character = (
            source[index] == "'"
            and index + 3 < len(source)
            and source[index + 1] == "\\"
            and source[index + 3] == "'"
        )
        if is_simple_character or is_escaped_character:
            literal_length = 4 if is_escaped_character else 3
            output.append(" " * literal_length)
            index += literal_length
            continue

        output.append(source[index])
        index += 1
    return "".join(output)


def _balanced_block(source: str, marker: str, *, label: str) -> str:
    match = re.search(
        rf"(?<![A-Za-z0-9_]){re.escape(marker)}(?![A-Za-z0-9_])",
        source,
    )
    if match is None:
        raise ValueError(f"{label} is missing")
    start = match.start()
    if source[:start].count("{") != source[:start].count("}"):
        raise ValueError(f"{label} is not a top-level Rust item")
    item_boundary = max(source.rfind("}", 0, start), source.rfind(";", 0, start))
    item_prefix = source[item_boundary + 1 : start]
    if re.search(r"#\s*\[[^\]]*\bcfg(?:_attr)?\b", item_prefix):
        raise ValueError(f"{label} is conditionally compiled")
    opening = source.find("{", start)
    if opening < 0:
        raise ValueError(f"{label} has no opening brace")
    depth = 0
    for index in range(opening, len(source)):
        character = source[index]
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return source[opening + 1 : index]
    raise ValueError(f"{label} has unbalanced braces")


def _rust_struct_fields(source: str, *, name: str) -> tuple[str, ...]:
    state_struct = _balanced_block(source, f"pub struct {name}", label=f"Rust {name} declaration")
    if re.search(r"#\s*\[[^\]]*\bcfg(?:_attr)?\b", state_struct):
        raise ValueError(f"Rust {name} fields are conditionally compiled")
    fields = tuple(_RUST_FIELD_RE.findall(state_struct))
    if not fields:
        raise ValueError(f"Rust {name} has no named fields")
    if len(fields) != len(set(fields)):
        raise ValueError(f"Rust {name} contains duplicate named fields")
    return fields


def _rust_call_visible(source: str, *, function_name: str) -> bool:
    top_level: list[str] = []
    brace_depth = 0
    for character in source:
        if character == "{":
            brace_depth += 1
            top_level.append(" ")
        elif character == "}":
            brace_depth = max(0, brace_depth - 1)
            top_level.append(" ")
        else:
            top_level.append(character if brace_depth == 0 else ("\n" if character == "\n" else " "))
    direct_source = "".join(top_level)
    exact_call = rf"(?<![A-Za-z0-9_]){re.escape(function_name)}\s*\("
    if re.search(rf"\breturn\s+[^;]*{exact_call}", direct_source):
        return True
    tail_expression = direct_source.rsplit(";", 1)[-1].strip()
    return bool(tail_expression and re.search(exact_call, tail_expression))


def _rust_public_function_visible(source: str, *, function_name: str) -> bool:
    match = re.search(
        rf"(?<![A-Za-z0-9_])pub\s+fn\s+{re.escape(function_name)}\s*\(",
        source,
    )
    if match is None:
        return False
    if source[: match.start()].count("{") != source[: match.start()].count("}"):
        return False
    item_boundary = max(source.rfind("}", 0, match.start()), source.rfind(";", 0, match.start()))
    item_prefix = source[item_boundary + 1 : match.start()]
    return re.search(r"#\s*\[[^\]]*\bcfg(?:_attr)?\b", item_prefix) is None


def _rust_state_surface(source: str) -> tuple[tuple[str, ...], tuple[str, ...], bool, bool, bool]:
    """Extract the closed Rust state declaration and visible root-codec markers."""

    code_only_source = _rust_code_only(source)
    fields = _rust_struct_fields(code_only_source, name="M6ApplicationStateV1")
    command_fields = _rust_struct_fields(code_only_source, name="GlobalCommandV1")
    implementation = _balanced_block(
        code_only_source,
        "impl M6ApplicationStateV1",
        label="Rust M6ApplicationStateV1 implementation",
    )
    state_root = _balanced_block(
        implementation,
        "pub fn state_root",
        label="Rust M6ApplicationStateV1.state_root",
    )
    if re.search(r"#\s*\[[^\]]*\bcfg(?:_attr)?\b", state_root):
        raise ValueError("Rust M6ApplicationStateV1.state_root is conditionally compiled")
    return (
        fields,
        command_fields,
        _rust_call_visible(state_root, function_name=_RUST_CANONICAL_CODEC_FUNCTION),
        _rust_call_visible(state_root, function_name=_RUST_POSTCARD_CODEC_FUNCTION),
        _rust_public_function_visible(
            code_only_source,
            function_name="run_m6_transition_v1",
        ),
    )


def _inspect_sources(
    python_source: str,
    rust_source: str,
    *,
    initial_errors: tuple[str, ...] = (),
) -> _SurfaceInspectionV1:
    errors = list(initial_errors)
    try:
        (
            python_execution_fields,
            python_fields,
            python_command_fields,
            python_canonical_codec_visible,
        ) = _python_state_surface(python_source)
    except ValueError as exc:
        python_fields = ()
        python_execution_fields = ()
        python_command_fields = ()
        python_canonical_codec_visible = False
        errors.append(str(exc))
    try:
        (
            rust_fields,
            rust_command_fields,
            rust_canonical_codec_visible,
            rust_postcard_state_codec_visible,
            rust_transition_function_visible,
        ) = _rust_state_surface(rust_source)
    except ValueError as exc:
        rust_fields = ()
        rust_command_fields = ()
        rust_canonical_codec_visible = False
        rust_postcard_state_codec_visible = False
        rust_transition_function_visible = False
        errors.append(str(exc))
    return _SurfaceInspectionV1(
        python_fields=python_fields,
        python_execution_fields=python_execution_fields,
        python_command_fields=python_command_fields,
        rust_fields=rust_fields,
        rust_command_fields=rust_command_fields,
        python_canonical_codec_visible=python_canonical_codec_visible,
        rust_canonical_codec_visible=rust_canonical_codec_visible,
        rust_postcard_state_codec_visible=rust_postcard_state_codec_visible,
        rust_transition_function_visible=rust_transition_function_visible,
        errors=tuple(errors),
    )


def _canonical_codec_match(inspection: _SurfaceInspectionV1) -> bool:
    return (
        inspection.python_canonical_codec_visible
        and inspection.rust_canonical_codec_visible
        and not inspection.rust_postcard_state_codec_visible
    )


def _compare_surfaces(inspection: _SurfaceInspectionV1) -> _SurfaceComparisonV1:
    required_root_fields = set(inspection.python_fields)
    required_execution_fields = set(inspection.python_execution_fields)
    declared_state_fields = set(inspection.rust_fields)
    required_command_fields = set(inspection.python_command_fields)
    declared_command_fields = set(inspection.rust_command_fields)
    return _SurfaceComparisonV1(
        missing_state_root_fields=tuple(sorted(required_root_fields - declared_state_fields)),
        missing_execution_state_fields=tuple(
            sorted(required_execution_fields - declared_state_fields)
        ),
        missing_command_fields=tuple(sorted(required_command_fields - declared_command_fields)),
        extra_rust_state_fields=tuple(
            sorted(declared_state_fields - (required_root_fields | required_execution_fields))
        ),
        extra_rust_command_fields=tuple(sorted(declared_command_fields - required_command_fields)),
        canonical_state_codec_match=_canonical_codec_match(inspection),
    )


def _semantic_blockers(
    inspection: _SurfaceInspectionV1,
    comparison: _SurfaceComparisonV1,
) -> list[str]:
    errors = list(inspection.errors)
    if comparison.missing_state_root_fields:
        errors.append(
            "Rust M6 state omits Python state-root fields: "
            + ", ".join(comparison.missing_state_root_fields)
        )
    if comparison.missing_execution_state_fields:
        errors.append(
            "Rust M6 state omits Python execution fields: "
            + ", ".join(comparison.missing_execution_state_fields)
        )
    if comparison.missing_command_fields:
        errors.append(
            "Rust M6 command omits Python fields: " + ", ".join(comparison.missing_command_fields)
        )
    if comparison.extra_rust_state_fields:
        errors.append(
            "Rust M6 state declares foreign fields: "
            + ", ".join(comparison.extra_rust_state_fields)
        )
    if comparison.extra_rust_command_fields:
        errors.append(
            "Rust M6 command declares foreign fields: "
            + ", ".join(comparison.extra_rust_command_fields)
        )
    if (
        inspection.python_execution_fields
        and not comparison.missing_execution_state_fields
        and not comparison.extra_rust_state_fields
        and inspection.rust_fields != inspection.python_execution_fields
    ):
        errors.append("Rust M6 state field order differs from Python execution state")
    if (
        inspection.python_command_fields
        and not comparison.missing_command_fields
        and not comparison.extra_rust_command_fields
        and inspection.rust_command_fields != inspection.python_command_fields
    ):
        errors.append("Rust M6 command field order differs from Python command")
    if not inspection.rust_transition_function_visible:
        errors.append("Rust run_m6_transition_v1 is missing")
    if not comparison.canonical_state_codec_match:
        errors.append(
            "Python/Rust canonical state-root codec parity is not statically visible "
            "or Rust state_root still uses postcard"
        )
    errors.append("independent direct/RISC0 execution parity evidence is absent")
    return errors


def _semantic_surface_status(
    inspection: _SurfaceInspectionV1,
    comparison: _SurfaceComparisonV1,
) -> str:
    if (
        inspection.errors
        or comparison.missing_state_root_fields
        or comparison.missing_execution_state_fields
        or comparison.missing_command_fields
        or comparison.extra_rust_state_fields
        or comparison.extra_rust_command_fields
        or inspection.rust_fields != inspection.python_execution_fields
        or inspection.rust_command_fields != inspection.python_command_fields
        or not comparison.canonical_state_codec_match
        or not inspection.rust_transition_function_visible
    ):
        return "BLOCKED_SEMANTIC_SURFACE"
    return "BLOCKED_EXECUTABLE_PARITY_EVIDENCE"


def _report_from_inspection(inspection: _SurfaceInspectionV1) -> dict[str, object]:
    comparison = _compare_surfaces(inspection)
    errors = _semantic_blockers(inspection, comparison)
    status = _semantic_surface_status(inspection, comparison)
    return {
        "activation_eligible": False,
        "canonical_state_codec_match": comparison.canonical_state_codec_match,
        "errors": errors,
        "extra_rust_state_fields": list(comparison.extra_rust_state_fields),
        "extra_rust_command_fields": list(comparison.extra_rust_command_fields),
        "independent_execution_parity_evidence": False,
        "missing_state_root_fields": list(comparison.missing_state_root_fields),
        "missing_execution_state_fields": list(comparison.missing_execution_state_fields),
        "missing_command_fields": list(comparison.missing_command_fields),
        "nonclaims": list(NONCLAIMS),
        "ok": False,
        "python_canonical_codec_visible": inspection.python_canonical_codec_visible,
        "python_execution_state_fields": list(inspection.python_execution_fields),
        "python_command_fields": list(inspection.python_command_fields),
        "python_to_rust_command_surface_match": bool(inspection.python_command_fields)
        and inspection.rust_command_fields == inspection.python_command_fields,
        "python_to_rust_execution_state_surface_match": bool(
            inspection.python_execution_fields
        )
        and inspection.rust_fields == inspection.python_execution_fields,
        "python_state_root_fields": list(inspection.python_fields),
        "python_to_rust_state_surface_match": bool(inspection.python_fields)
        and not comparison.missing_state_root_fields
        and inspection.rust_fields == inspection.python_execution_fields,
        "required_next_evidence": list(REQUIRED_NEXT_EVIDENCE),
        "rust_canonical_codec_visible": inspection.rust_canonical_codec_visible,
        "rust_postcard_state_codec_visible": inspection.rust_postcard_state_codec_visible,
        "rust_state_fields": list(inspection.rust_fields),
        "rust_command_fields": list(inspection.rust_command_fields),
        "rust_transition_function_visible": inspection.rust_transition_function_visible,
        "schema": SCHEMA_V1,
        "status": status,
    }


def inspect_m6_risc0_semantic_surface(
    python_types_path: Path,
    rust_core_path: Path,
) -> dict[str, object]:
    """Inspect explicit source paths without assigning any execution authority."""

    python_source, python_error = _read_source_or_error(
        python_types_path,
        label="Python M6 types",
    )
    rust_source, rust_error = _read_source_or_error(
        rust_core_path,
        label="Rust M6 core",
    )
    initial_errors = tuple(error for error in (python_error, rust_error) if error is not None)
    inspection = _inspect_sources(
        python_source,
        rust_source,
        initial_errors=initial_errors,
    )
    report = _report_from_inspection(inspection)
    report["python_source_sha256"] = (
        None if python_error is not None else hashlib.sha256(python_source.encode("utf-8")).hexdigest()
    )
    report["rust_source_sha256"] = (
        None if rust_error is not None else hashlib.sha256(rust_source.encode("utf-8")).hexdigest()
    )
    return report


def check_m6_risc0_semantic_surface(root: Path = REPO_ROOT) -> dict[str, object]:
    """Inspect the repository M6 Python and RISC0 sources with a closed report."""

    root = root.resolve()
    python_relative = Path("src/core/m6_safe_mount_types_v1.py")
    rust_relative = Path("zk/recursive_stark_v2_risc0/shared/src/m6_core_v1.rs")
    checker_relative = Path("tools/check_m6_risc0_semantic_surface_v1.py")
    report = inspect_m6_risc0_semantic_surface(
        root / python_relative,
        root / rust_relative,
    )
    report["git_head"] = _git_output(root, "rev-parse", "HEAD")
    scoped_status = _git_output(
        root,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--",
        python_relative.as_posix(),
        rust_relative.as_posix(),
        checker_relative.as_posix(),
    )
    source_tracked = {
        "python": _git_success(
            root,
            "ls-files",
            "--error-unmatch",
            python_relative.as_posix(),
        ),
        "rust": _git_success(
            root,
            "ls-files",
            "--error-unmatch",
            rust_relative.as_posix(),
        ),
        "checker": _git_success(
            root,
            "ls-files",
            "--error-unmatch",
            checker_relative.as_posix(),
        ),
    }
    report["source_paths"] = {
        "python": python_relative.as_posix(),
        "rust": rust_relative.as_posix(),
        "checker": checker_relative.as_posix(),
    }
    try:
        checker_bytes = (root / checker_relative).read_bytes()
    except OSError:
        report["checker_source_sha256"] = None
    else:
        report["checker_source_sha256"] = hashlib.sha256(checker_bytes).hexdigest()
    report["source_tracked"] = source_tracked
    report["scoped_worktree_clean"] = (
        scoped_status == "" and all(source_tracked.values())
    )
    return report


def _git_output(root: Path, *arguments: str) -> str | None:
    try:
        completed = subprocess.run(
            ("git", "-C", str(root), *arguments),
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if completed.returncode != 0:
        return None
    return completed.stdout.strip()


def _git_success(root: Path, *arguments: str) -> bool:
    try:
        completed = subprocess.run(
            ("git", "-C", str(root), *arguments),
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return completed.returncode == 0


def _markdown_report(report: Mapping[str, object]) -> str:
    def lines(name: str) -> list[str]:
        value = report.get(name, [])
        return [str(item) for item in value] if isinstance(value, list) else []

    errors = lines("errors")
    nonclaims = lines("nonclaims")
    evidence = lines("required_next_evidence")
    output = [
        "# M6 RISC0 Semantic Surface V1",
        "",
        f"- Status: `{report.get('status')}`",
        f"- Activation eligible: `{report.get('activation_eligible')}`",
        f"- Git HEAD: `{report.get('git_head')}`",
        f"- Scoped worktree clean: `{report.get('scoped_worktree_clean')}`",
        f"- Python source SHA-256: `{report.get('python_source_sha256')}`",
        f"- Rust source SHA-256: `{report.get('rust_source_sha256')}`",
        f"- Checker source SHA-256: `{report.get('checker_source_sha256')}`",
        "",
        "## Blockers",
        "",
        *(f"- {item}" for item in errors),
        "",
        "## Required next evidence",
        "",
        *(f"- {item}" for item in evidence),
        "",
        "## Nonclaims",
        "",
        *(f"- {item}" for item in nonclaims),
        "",
        "Generated by `python3 tools/check_m6_risc0_semantic_surface_v1.py`.",
        "",
    ]
    return "\n".join(output)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--markdown-out", type=Path)
    args = parser.parse_args(list(argv) if argv is not None else None)
    report = check_m6_risc0_semantic_surface(args.root)
    if args.json_out is not None:
        args.json_out.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.markdown_out is not None:
        args.markdown_out.write_text(_markdown_report(report), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
