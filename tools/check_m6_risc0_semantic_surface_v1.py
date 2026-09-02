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
import tomllib
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


def _read_source_or_error(
    path: Path,
    *,
    label: str,
) -> tuple[str, bytes | None, str | None]:
    try:
        raw = path.read_bytes()
        return raw.decode("utf-8"), raw, None
    except (OSError, UnicodeError):
        return "", None, f"cannot read {label}"


def _class_named(tree: ast.Module, *, name: str) -> ast.ClassDef:
    matches = [
        node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == name
    ]
    binding_count = sum(_statement_binds_name(node, name=name) for node in tree.body)
    if len(matches) == 1 and binding_count == 1:
        return matches[0]
    if binding_count:
        raise ValueError(f"Python {name} has duplicate bindings")
    raise ValueError(f"Python {name} is missing")


def _python_module_uses_dynamic_bindings(tree: ast.Module) -> bool:
    """Reject source shapes whose selected names cannot be resolved statically."""

    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and any(alias.name == "*" for alias in node.names):
            return True
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id in {
                "eval",
                "exec",
                "globals",
                "locals",
                "setattr",
            }:
                return True
    return False


def _python_definition_has_unsupported_decorators(
    node: ast.ClassDef | ast.FunctionDef | ast.AsyncFunctionDef,
    *,
    allowed_names: frozenset[str],
) -> bool:
    for decorator in node.decorator_list:
        name = decorator.func if isinstance(decorator, ast.Call) else decorator
        if not isinstance(name, ast.Name) or name.id not in allowed_names:
            return True
    return False


def _target_binds_name(target: ast.AST, *, name: str) -> bool:
    if isinstance(target, ast.Name):
        return target.id == name
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_target_binds_name(item, name=name) for item in target.elts)
    if isinstance(target, ast.Starred):
        return _target_binds_name(target.value, name=name)
    return False


class _ScopeBindingCollector(ast.NodeVisitor):
    """Collect bindings in one Python scope without entering child scopes."""

    def __init__(self) -> None:
        self.names: set[str] = set()

    def visit_Name(self, node: ast.Name) -> None:  # noqa: N802 - ast visitor API
        if isinstance(node.ctx, (ast.Store, ast.Del)):
            self.names.add(node.id)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:  # noqa: N802
        self.names.add(node.name)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:  # noqa: N802
        self.names.add(node.name)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:  # noqa: N802
        self.names.add(node.name)

    def visit_Lambda(self, node: ast.Lambda) -> None:  # noqa: N802
        return

    def visit_Import(self, node: ast.Import) -> None:  # noqa: N802
        self.names.update(alias.asname or alias.name.split(".", 1)[0] for alias in node.names)

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:  # noqa: N802
        self.names.update(alias.asname or alias.name for alias in node.names)

    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:  # noqa: N802
        if node.name is not None:
            self.names.add(node.name)
        if node.type is not None:
            self.visit(node.type)
        for statement in node.body:
            self.visit(statement)

    def visit_MatchAs(self, node: ast.MatchAs) -> None:  # noqa: N802
        if node.name is not None:
            self.names.add(node.name)
        if node.pattern is not None:
            self.visit(node.pattern)

    def visit_MatchStar(self, node: ast.MatchStar) -> None:  # noqa: N802
        if node.name is not None:
            self.names.add(node.name)

    def visit_MatchMapping(self, node: ast.MatchMapping) -> None:  # noqa: N802
        if node.rest is not None:
            self.names.add(node.rest)
        self.generic_visit(node)

    def _visit_comprehension_parts(
        self,
        generators: list[ast.comprehension],
        *values: ast.AST,
    ) -> None:
        for generator in generators:
            self.visit(generator.iter)
            for condition in generator.ifs:
                self.visit(condition)
        for value in values:
            self.visit(value)

    def visit_ListComp(self, node: ast.ListComp) -> None:  # noqa: N802
        self._visit_comprehension_parts(node.generators, node.elt)

    def visit_SetComp(self, node: ast.SetComp) -> None:  # noqa: N802
        self._visit_comprehension_parts(node.generators, node.elt)

    def visit_GeneratorExp(self, node: ast.GeneratorExp) -> None:  # noqa: N802
        self._visit_comprehension_parts(node.generators, node.elt)

    def visit_DictComp(self, node: ast.DictComp) -> None:  # noqa: N802
        self._visit_comprehension_parts(node.generators, node.key, node.value)


def _statement_binds_name(statement: ast.stmt, *, name: str) -> bool:
    collector = _ScopeBindingCollector()
    collector.visit(statement)
    return name in collector.names


def _method_named(class_node: ast.ClassDef, *, name: str) -> ast.FunctionDef | ast.AsyncFunctionDef:
    matches = [
        member
        for member in class_node.body
        if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef))
        and member.name == name
    ]
    binding_count = sum(
        _statement_binds_name(member, name=name) for member in class_node.body
    )
    if len(matches) == 1 and binding_count == 1:
        return matches[0]
    if binding_count:
        raise ValueError(f"Python {class_node.name}.{name} has duplicate bindings")
    raise ValueError(f"Python {class_node.name}.{name} is missing")


def _function_named(tree: ast.Module, *, name: str) -> ast.FunctionDef | ast.AsyncFunctionDef:
    matches = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name
    ]
    binding_count = sum(_statement_binds_name(node, name=name) for node in tree.body)
    if len(matches) == 1 and binding_count == 1:
        return matches[0]
    if binding_count:
        raise ValueError(f"Python {name} has duplicate bindings")
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
    if _python_definition_has_unsupported_decorators(
        state_root,
        allowed_names=frozenset({"property"}),
    ):
        return False
    state_root_calls = _direct_call_names(state_root)
    if _named_call_value_reaches_return(state_root, call_name="canonical_bytes_v1"):
        return True
    if (
        "hash_v1" not in state_root_calls
        or not _named_call_value_reaches_return(state_root, call_name="hash_v1")
    ):
        return False
    try:
        hash_function = _function_named(tree, name="hash_v1")
    except ValueError:
        return False
    if _python_definition_has_unsupported_decorators(
        hash_function,
        allowed_names=frozenset(),
    ):
        return False
    return _named_call_value_reaches_return(
        hash_function,
        call_name="canonical_bytes_v1",
    )


def _is_exact_named_call(node: ast.AST, *, call_name: str) -> bool:
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == call_name
    )


def _expression_has_provenance(
    node: ast.AST,
    *,
    call_name: str,
    value_names: set[str],
) -> bool:
    """Accept only expression shapes whose selected result carries provenance."""

    if _is_exact_named_call(node, call_name=call_name):
        return True
    if isinstance(node, ast.Name):
        return node.id in value_names
    return False


def _assigned_name_targets(statement: ast.Assign | ast.AnnAssign) -> tuple[str, ...]:
    targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
    return tuple(target.id for target in targets if isinstance(target, ast.Name))


_UNCONDITIONAL_PATH_TERMINATORS = (
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
)


def _named_call_value_reaches_return(
    method: ast.FunctionDef | ast.AsyncFunctionDef,
    *,
    call_name: str,
) -> bool:
    """Trace one direct call result through a restricted unconditional path."""

    argument_names = {
        argument.arg
        for argument in (
            *method.args.posonlyargs,
            *method.args.args,
            *method.args.kwonlyargs,
        )
    }
    if method.args.vararg is not None:
        argument_names.add(method.args.vararg.arg)
    if method.args.kwarg is not None:
        argument_names.add(method.args.kwarg.arg)
    if call_name in argument_names or any(
        _statement_binds_name(statement, name=call_name) for statement in method.body
    ):
        return False

    value_names: set[str] = set()
    for statement in method.body:
        if isinstance(statement, _UNCONDITIONAL_PATH_TERMINATORS):
            break
        if isinstance(statement, (ast.Assign, ast.AnnAssign)):
            value = statement.value
            assigned_names = _assigned_name_targets(statement)
            value_names.difference_update(assigned_names)
            if value is not None and _expression_has_provenance(
                value,
                call_name=call_name,
                value_names=value_names,
            ):
                value_names.update(assigned_names)
        elif isinstance(statement, ast.AugAssign):
            if isinstance(statement.target, ast.Name):
                value_names.discard(statement.target.id)
        elif isinstance(statement, ast.Expr):
            continue
        elif isinstance(statement, ast.Return):
            value = statement.value
            if value is None:
                return False
            return _expression_has_provenance(
                value,
                call_name=call_name,
                value_names=value_names,
            )
        else:
            break
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
    if _python_module_uses_dynamic_bindings(tree):
        raise ValueError("Python M6 types use unsupported dynamic bindings")
    state_class = _class_named(tree, name="M6ApplicationStateV1")
    command_class = _class_named(tree, name="GlobalCommandV1")
    if _python_definition_has_unsupported_decorators(
        state_class,
        allowed_names=frozenset({"dataclass"}),
    ) or _python_definition_has_unsupported_decorators(
        command_class,
        allowed_names=frozenset({"dataclass"}),
    ):
        raise ValueError("Python M6 types use unsupported class decorators")
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
    if not _rust_top_level_at(source, start):
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
    if re.search(r"#\s*\[[^\]]*\bserde\b", state_struct):
        raise ValueError(f"Rust {name} fields use unsupported serialization attributes")
    fields = tuple(_RUST_FIELD_RE.findall(state_struct))
    if not fields:
        raise ValueError(f"Rust {name} has no named fields")
    if len(fields) != len(set(fields)):
        raise ValueError(f"Rust {name} contains duplicate named fields")
    return fields


def _rust_expression_is_exact_call(expression: str, *, function_name: str) -> bool:
    stripped = expression.strip()
    prefix = re.match(rf"{re.escape(function_name)}\s*\(", stripped)
    if prefix is None:
        return False
    opening = stripped.find("(", prefix.start())
    depth = 0
    for index in range(opening, len(stripped)):
        if stripped[index] == "(":
            depth += 1
        elif stripped[index] == ")":
            depth -= 1
            if depth == 0:
                return not stripped[index + 1 :].strip()
    return False


def _rust_call_visible(
    source: str,
    *,
    function_name: str,
    signature: str = "",
    ambient_source: str = "",
) -> bool:
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
    escaped_name = re.escape(function_name)
    if ambient_source and re.search(
        rf"(?<![A-Za-z0-9_])(?:fn|const|static)\s+{escaped_name}\b|"
        rf"\buse\s+[^;]*\b{escaped_name}\b",
        ambient_source,
    ):
        return False
    if re.search(
        rf"(?:\blet\s+(?:mut\s+)?|\bfn\s+|\bconst\s+|\bstatic\s+)"
        rf"{escaped_name}\b|\buse\s+[^;]*\b{escaped_name}\b|"
        rf"\b(?:fn|const|static)\s+{escaped_name}\b",
        direct_source,
    ):
        return False
    parameter_list = re.search(r"\((.*)\)", signature, flags=re.DOTALL)
    if parameter_list is not None and re.search(
        rf"\b{escaped_name}\b",
        parameter_list.group(1),
    ):
        return False
    for returned in re.finditer(r"\breturn\s+([^;]+);", direct_source):
        if _rust_expression_is_exact_call(
            returned.group(1),
            function_name=function_name,
        ):
            return True
    tail_expression = direct_source.rsplit(";", 1)[-1].strip()
    return bool(
        tail_expression
        and _rust_expression_is_exact_call(
            tail_expression,
            function_name=function_name,
        )
    )


def _rust_public_function_visible(source: str, *, function_name: str) -> bool:
    match = re.search(
        rf"(?<![A-Za-z0-9_])pub\s+fn\s+{re.escape(function_name)}\s*\(",
        source,
    )
    if match is None:
        return False
    if not _rust_top_level_at(source, match.start()):
        return False
    item_boundary = max(source.rfind("}", 0, match.start()), source.rfind(";", 0, match.start()))
    item_prefix = source[item_boundary + 1 : match.start()]
    return re.search(r"#\s*\[[^\]]*\bcfg(?:_attr)?\b", item_prefix) is None


def _rust_top_level_at(source: str, index: int) -> bool:
    """Reject declarations nested in blocks or macro-token delimiters."""

    pairs = {"}": "{", ")": "(", "]": "["}
    openings = set(pairs.values())
    stack: list[str] = []
    for character in source[:index]:
        if character in openings:
            stack.append(character)
        elif character in pairs:
            if not stack or stack.pop() != pairs[character]:
                return False
    return not stack


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
    state_root_marker = implementation.find("pub fn state_root")
    state_root_body = implementation.find("{", state_root_marker)
    state_root_signature = implementation[state_root_marker:state_root_body]
    if re.search(r"#\s*\[[^\]]*\bcfg(?:_attr)?\b", state_root):
        raise ValueError("Rust M6ApplicationStateV1.state_root is conditionally compiled")
    return (
        fields,
        command_fields,
        _rust_call_visible(
            state_root,
            function_name=_RUST_CANONICAL_CODEC_FUNCTION,
            signature=state_root_signature,
            ambient_source=code_only_source[: code_only_source.find("impl M6ApplicationStateV1")],
        ),
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

    python_source, python_bytes, python_error = _read_source_or_error(
        python_types_path,
        label="Python M6 types",
    )
    rust_source, rust_bytes, rust_error = _read_source_or_error(
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
        None if python_bytes is None else hashlib.sha256(python_bytes).hexdigest()
    )
    report["rust_source_sha256"] = (
        None if rust_bytes is None else hashlib.sha256(rust_bytes).hexdigest()
    )
    return report


def check_m6_risc0_semantic_surface(root: Path = REPO_ROOT) -> dict[str, object]:
    """Inspect the repository M6 Python and RISC0 sources with a closed report."""

    root = root.resolve()
    python_relative = Path("src/core/m6_safe_mount_types_v1.py")
    python_transition_relative = Path("src/core/m6_safe_mount_transition_v1.py")
    rust_relative = Path("zk/recursive_stark_v2_risc0/shared/src/m6_core_v1.rs")
    rust_shared_lib_relative = Path("zk/recursive_stark_v2_risc0/shared/src/lib.rs")
    rust_shared_cargo_relative = Path("zk/recursive_stark_v2_risc0/shared/Cargo.toml")
    rust_guest_relative = Path("zk/recursive_stark_v2_risc0/methods/aggregate_v2/src/main.rs")
    rust_methods_cargo_relative = Path(
        "zk/recursive_stark_v2_risc0/methods/aggregate_v2/Cargo.toml"
    )
    checker_relative = Path("tools/check_m6_risc0_semantic_surface_v1.py")
    source_paths = {
        "python": python_relative,
        "python_transition": python_transition_relative,
        "rust": rust_relative,
        "rust_shared_lib": rust_shared_lib_relative,
        "rust_shared_cargo": rust_shared_cargo_relative,
        "rust_guest": rust_guest_relative,
        "rust_methods_cargo": rust_methods_cargo_relative,
        "checker": checker_relative,
    }
    report = inspect_m6_risc0_semantic_surface(
        root / python_relative,
        root / rust_relative,
    )
    report["risc0_guest_transition_reachable"] = _risc0_guest_calls_m6_transition(
        root / rust_guest_relative,
        root / rust_methods_cargo_relative,
    )
    if not report["risc0_guest_transition_reachable"]:
        errors = report.get("errors")
        if isinstance(errors, list):
            errors.append("selected RISC0 guest does not call the shared M6 transition")
        report["status"] = "BLOCKED_SEMANTIC_SURFACE"
    report["git_head"] = _git_output(root, "rev-parse", "HEAD")
    scoped_status = _git_output(
        root,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--",
        *(path.as_posix() for path in source_paths.values()),
    )
    source_tracked = {
        name: _git_success(
            root,
            "ls-files",
            "--error-unmatch",
            path.as_posix(),
        )
        for name, path in source_paths.items()
    }
    report["source_paths"] = {
        name: path.as_posix() for name, path in source_paths.items()
    }
    try:
        checker_bytes = (root / checker_relative).read_bytes()
    except OSError:
        report["checker_source_sha256"] = None
    else:
        report["checker_source_sha256"] = hashlib.sha256(checker_bytes).hexdigest()
    try:
        executing_checker_bytes = Path(__file__).resolve().read_bytes()
    except OSError:
        report["executing_checker_source_sha256"] = None
    else:
        report["executing_checker_source_sha256"] = hashlib.sha256(
            executing_checker_bytes
        ).hexdigest()
    report["checker_subject_matches_executing"] = (
        report["checker_source_sha256"] is not None
        and report["checker_source_sha256"]
        == report["executing_checker_source_sha256"]
    )
    if not report["checker_subject_matches_executing"]:
        errors = report.get("errors")
        if isinstance(errors, list):
            errors.append("subject checker source differs from executing checker")
        report["status"] = "BLOCKED_SEMANTIC_SURFACE"
    report["source_tracked"] = source_tracked
    report["scoped_worktree_clean"] = (
        scoped_status == "" and all(source_tracked.values())
    )
    return report


def _risc0_guest_calls_m6_transition(guest_path: Path, cargo_path: Path) -> bool:
    """Require an exact dependency and a direct call in selected ``main``."""

    guest_source, _guest_bytes, guest_error = _read_source_or_error(
        guest_path,
        label="RISC0 guest",
    )
    cargo_source, _cargo_bytes, cargo_error = _read_source_or_error(
        cargo_path,
        label="RISC0 methods Cargo manifest",
    )
    if guest_error is not None or cargo_error is not None:
        return False
    try:
        code = _rust_code_only(guest_source)
        cargo = tomllib.loads(cargo_source)
    except (ValueError, tomllib.TOMLDecodeError):
        return False
    dependencies = cargo.get("dependencies")
    if not isinstance(dependencies, dict):
        return False
    dependency = dependencies.get("tau-state-proof-risc0-shared-v2")
    if not isinstance(dependency, (str, dict)):
        return False
    try:
        main_body = _balanced_block(code, "pub fn main()", label="selected RISC0 guest main")
    except ValueError:
        return False
    if re.search(r"#\s*\[[^\]]*\bcfg(?:_attr)?\b", main_body):
        return False
    return _rust_direct_call_in_executable_main(
        main_body,
        function_name="run_m6_transition_v1",
    )


def _rust_direct_call_in_executable_main(source: str, *, function_name: str) -> bool:
    """Accept only a direct top-statement call in the selected entrypoint."""

    escaped = re.escape(function_name)
    if re.search(r"\b(?:macro_rules|fn|const|static)\s+" + escaped + r"\b", source):
        return False
    for match in re.finditer(r"(?<![A-Za-z0-9_])" + escaped + r"\s*\(", source):
        prefix = source[: match.start()]
        if _rust_delimiter_depths(prefix) != (0, 0, 0):
            continue
        statement = prefix.rsplit(";", 1)[-1]
        if re.search(r"(?:\bmove\s*)?\|[^|]*\|", statement):
            continue
        if re.search(r"\b(?:if|while|for|loop|match)\b", statement):
            continue
        return True
    return False


def _rust_delimiter_depths(source: str) -> tuple[int, int, int]:
    """Return nonnegative curly, parenthesis, and bracket depths."""

    depths = [0, 0, 0]
    indices = {"{": (0, 1), "}": (0, -1), "(": (1, 1), ")": (1, -1), "[": (2, 1), "]": (2, -1)}
    for character in source:
        update = indices.get(character)
        if update is None:
            continue
        index, delta = update
        depths[index] = max(0, depths[index] + delta)
    return depths[0], depths[1], depths[2]


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
        f"- Executing checker SHA-256: `{report.get('executing_checker_source_sha256')}`",
        f"- RISC0 guest transition reachable: `{report.get('risc0_guest_transition_reachable')}`",
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
