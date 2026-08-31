"""Observe durable-write operations in parsed Python source.

The scanner is pure: it consumes a module path and its parsed tree and returns
observations.  Each observation carries a source-derived fingerprint so an equal
occurrence count cannot hide a relocated operation.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass

from tools.m6_value_sinks.operations import (
    MODULE_OPERATIONS,
    RECEIVER_OPERATIONS,
    SQL_EXECUTE_ATTRIBUTES,
    ImportBindingsV2,
    classify_open_call,
    classify_os_open_call,
    classify_sql_statement,
    is_unary_call,
    literal_string_argument,
    operation_fingerprint,
    resolve_import_bindings,
)


@dataclass(frozen=True, slots=True, order=True)
class ValueSinkObservationV2:
    path: str
    symbol: str
    sink_kind: str
    fingerprint: str

    def identity(self) -> tuple[str, str, str]:
        return (self.path, self.symbol, self.sink_kind)


class _SinkVisitorV2(ast.NodeVisitor):
    """Record durable-write operations with their enclosing qualified symbol."""

    def __init__(self, *, path: str, bindings: ImportBindingsV2) -> None:
        self._path = path
        self._bindings = bindings
        self._scope: list[str] = []
        self.observations: list[ValueSinkObservationV2] = []

    def _symbol(self) -> str:
        return ".".join(self._scope) if self._scope else "<module>"

    def _add(self, kind: str, node: ast.AST) -> None:
        self.observations.append(
            ValueSinkObservationV2(
                path=self._path,
                symbol=self._symbol(),
                sink_kind=kind,
                fingerprint=operation_fingerprint(kind, node),
            )
        )

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._scope.append(node.name)
        self.generic_visit(node)
        self._scope.pop()

    def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
        self._scope.append(node.name)
        self.generic_visit(node)
        self._scope.pop()

    visit_FunctionDef = _visit_function
    visit_AsyncFunctionDef = _visit_function

    def _module_attribute_kind(self, node: ast.Call, function: ast.Attribute) -> str | None:
        base = function.value
        if not isinstance(base, ast.Name):
            return None
        module = self._bindings.module_aliases.get(base.id)
        if module is None:
            return None
        if module == "os" and function.attr == "open":
            return classify_os_open_call(node)
        return MODULE_OPERATIONS.get((module, function.attr))

    def _receiver_kind(self, node: ast.Call, function: ast.Attribute) -> str | None:
        if function.attr in RECEIVER_OPERATIONS:
            return RECEIVER_OPERATIONS[function.attr]
        if function.attr == "replace" and is_unary_call(node):
            return "PATH_REPLACE"
        if function.attr == "open":
            # ``Path.open(mode)`` takes the mode first; ``open(path, mode)`` second.
            return classify_open_call(node, mode_index=0)
        if function.attr in SQL_EXECUTE_ATTRIBUTES:
            return classify_sql_statement(literal_string_argument(node))
        return None

    def _is_tracked_module_attribute(self, function: ast.Attribute) -> bool:
        base = function.value
        return isinstance(base, ast.Name) and base.id in self._bindings.module_aliases

    def _visit_attribute_call(self, node: ast.Call, function: ast.Attribute) -> None:
        if self._is_tracked_module_attribute(function):
            # A tracked module function never falls through to the path-receiver
            # vocabulary. In particular, os.open uses integer flag semantics.
            kind = self._module_attribute_kind(node, function)
        else:
            kind = self._receiver_kind(node, function)
        if kind is not None:
            self._add(kind, node)

    def _visit_name_call(self, node: ast.Call, function: ast.Name) -> None:
        direct = self._bindings.direct_aliases.get(function.id)
        if direct is not None:
            kind = (
                classify_os_open_call(node)
                if direct == ("os", "open")
                else MODULE_OPERATIONS[direct]
            )
            if kind is not None:
                self._add(kind, node)
            return
        if function.id == "open":
            kind = classify_open_call(node, mode_index=1)
            if kind is not None:
                self._add(kind, node)

    def visit_Call(self, node: ast.Call) -> None:
        function = node.func
        if isinstance(function, ast.Attribute):
            self._visit_attribute_call(node, function)
        elif isinstance(function, ast.Name):
            self._visit_name_call(node, function)
        self.generic_visit(node)

    def _visit_state_target(self, target: ast.AST, node: ast.AST) -> None:
        if (
            isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id == "self"
            and target.attr == "_state"
        ):
            self._add("STATE_ATTRIBUTE_ASSIGN", node)

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            self._visit_state_target(target, node)
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        self._visit_state_target(node.target, node)
        self.generic_visit(node)


def scan_module(path: str, tree: ast.Module) -> tuple[ValueSinkObservationV2, ...]:
    """Observe every recognized durable-write operation in one parsed module."""

    visitor = _SinkVisitorV2(path=path, bindings=resolve_import_bindings(tree))
    visitor.visit(tree)
    return tuple(sorted(visitor.observations))
