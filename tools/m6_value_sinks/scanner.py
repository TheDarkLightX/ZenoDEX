"""Observe durable-write operations in parsed Python source.

The scanner is pure: it consumes a module path and its parsed tree and returns
observations.  Each observation carries a source-derived fingerprint bound to
its destination provenance, so an equal occurrence count cannot hide a relocated
operation and a shared helper cannot keep one judgement across callers that
write different artifacts.
"""

from __future__ import annotations

import ast
import hashlib
from dataclasses import dataclass, replace

from tools.m6_value_sinks.launchers import ScanResourceMeterV2
from tools.m6_value_sinks.operations import (
    MODULE_OPERAND_INDICES,
    MODULE_OPERAND_KEYWORDS,
    MODULE_OPERATIONS,
    RECEIVER_OPERATIONS,
    SPECIAL_MODULE_FUNCTIONS,
    SQL_EXECUTE_ATTRIBUTES,
    ImportBindingsV2,
    LiteralPathResolverV2,
    callable_target_is_writer,
    classify_descriptor_open,
    classify_named_temporary_file,
    classify_open_call,
    classify_sql_script,
    classify_sql_statement,
    classify_sqlite_connect,
    classify_temporary_directory,
    describe_destination,
    literal_string_argument,
    operation_fingerprint,
    resolve_callable_expression,
    resolve_import_bindings,
)


@dataclass(frozen=True, slots=True, order=True)
class ValueSinkObservationV2:
    path: str
    symbol: str
    sink_kind: str
    fingerprint: str
    destination: str = "NONE"
    caller_determined: bool = False
    destination_resolved: bool = False

    def identity(self) -> tuple[str, str, str]:
        return (self.path, self.symbol, self.sink_kind)


@dataclass(frozen=True, slots=True)
class _PendingV2:
    observation: ValueSinkObservationV2
    node: ast.AST
    function: str | None
    parameter: str | None


_TWO_ROLE_RECEIVER_OPERATIONS: dict[str, str] = {
    "hardlink_to": "NAMESPACE_LINK",
    "rename": "RENAME",
    "replace": "PATH_REPLACE",
    "symlink_to": "NAMESPACE_LINK",
}


def _argument_at(call: ast.Call, index: int, keyword: str | None = None) -> ast.expr | None:
    """Read one operand positionally, or by its keyword spelling."""

    if len(call.args) > index:
        return call.args[index]
    if keyword is not None:
        for supplied in call.keywords:
            if supplied.arg == keyword:
                return supplied.value
    return None


def _operands(
    call: ast.Call, target: tuple[str, str], indices: tuple[int, ...]
) -> tuple[ast.expr | None, ...]:
    keywords = MODULE_OPERAND_KEYWORDS.get(target, ())
    return tuple(
        _argument_at(call, index, keywords[position] if position < len(keywords) else None)
        for position, index in enumerate(indices)
    )


def _single_receiver_target(call: ast.Call, attribute: str) -> ast.expr | None:
    """Decode one valid target operand for a two-role pathlib-style method."""

    allowed_extras = {"target_is_directory"} if attribute == "symlink_to" else set()
    if any(keyword.arg is None for keyword in call.keywords):
        return None
    target_keywords = [keyword for keyword in call.keywords if keyword.arg == "target"]
    other_keywords = {
        keyword.arg for keyword in call.keywords if keyword.arg != "target"
    }
    if not other_keywords.issubset(allowed_extras):
        return None
    if len(call.args) == 1 and not isinstance(call.args[0], ast.Starred):
        return call.args[0] if not target_keywords else None
    if not call.args and len(target_keywords) == 1:
        return target_keywords[0].value
    return None


class _SinkVisitorV2(ast.NodeVisitor):
    """Record durable-write operations with their enclosing symbol and destination."""

    def __init__(
        self,
        *,
        path: str,
        bindings: ImportBindingsV2,
        path_resolver: LiteralPathResolverV2,
        resource_meter: ScanResourceMeterV2 | None,
    ) -> None:
        self._path = path
        self._bindings = bindings
        self._path_resolver = path_resolver
        self._resource_meter = resource_meter
        self._scope: list[str] = []
        self._parameters: list[frozenset[str]] = [frozenset()]
        self._functions: list[str] = []
        self.pending: list[_PendingV2] = []

    def _symbol(self) -> str:
        return ".".join(self._scope) if self._scope else "<module>"

    def _add(self, kind: str, node: ast.AST, operands: tuple[ast.expr | None, ...]) -> None:
        if self._resource_meter is not None:
            self._resource_meter.claim_observations(1)
        destination = describe_destination(
            operands,
            self._parameters[-1],
            self._path_resolver,
            node,
        )
        self.pending.append(
            _PendingV2(
                observation=ValueSinkObservationV2(
                    path=self._path,
                    symbol=self._symbol(),
                    sink_kind=kind,
                    fingerprint=operation_fingerprint(kind, node, destination.descriptor),
                    destination=destination.descriptor,
                    caller_determined=destination.caller_determined,
                    destination_resolved=destination.resolved,
                ),
                node=node,
                function=self._functions[-1] if self._functions else None,
                parameter=destination.parameter,
            )
        )

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._scope.append(node.name)
        self.generic_visit(node)
        self._scope.pop()

    def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
        self._scope.append(node.name)
        self._functions.append(node.name)
        arguments = node.args
        names = {
            argument.arg
            for group in (arguments.posonlyargs, arguments.args, arguments.kwonlyargs)
            for argument in group
        }
        for optional in (arguments.vararg, arguments.kwarg):
            if optional is not None:
                names.add(optional.arg)
        self._parameters.append(frozenset(names))
        self.generic_visit(node)
        self._parameters.pop()
        self._functions.pop()
        self._scope.pop()

    visit_FunctionDef = _visit_function
    visit_AsyncFunctionDef = _visit_function

    def _module_attribute_kind(
        self, node: ast.Call, function: ast.Attribute
    ) -> tuple[str | None, tuple[ast.expr | None, ...]]:
        base = function.value
        if not isinstance(base, ast.Name):
            return None, ()
        module = self._bindings.module_aliases.get(base.id)
        if module is None:
            return None, ()
        if (module, function.attr) in SPECIAL_MODULE_FUNCTIONS:
            return self._special_kind(node, (module, function.attr))
        target = (module, function.attr)
        kind = MODULE_OPERATIONS.get(target)
        return kind, _operands(node, target, MODULE_OPERAND_INDICES.get(target, (0,)))

    def _receiver_kind(
        self, node: ast.Call, function: ast.Attribute
    ) -> tuple[str | None, tuple[ast.expr | None, ...]]:
        target = _single_receiver_target(node, function.attr)
        if function.attr in _TWO_ROLE_RECEIVER_OPERATIONS:
            if target is not None:
                # ``a.replace(b)`` moves value from one path role to another, so
                # both operands are bound.
                return _TWO_ROLE_RECEIVER_OPERATIONS[function.attr], (function.value, target)
            if self._path_resolver.pathlib_receiver_literal_at(function.value, node) is not None:
                # A proved Path receiver with ``*args``/``**kwargs`` still names
                # a writer. Its target stays unresolved. A string receiver is
                # not proved Path and therefore avoids str.replace false hits.
                return _TWO_ROLE_RECEIVER_OPERATIONS[function.attr], (function.value, None)
        if function.attr in RECEIVER_OPERATIONS:
            return RECEIVER_OPERATIONS[function.attr], (function.value,)
        if function.attr == "open":
            return classify_open_call(node, mode_index=0), (function.value,)
        if function.attr == "executescript":
            # Every statement in a script runs, so the strongest one decides.
            return classify_sql_script(literal_string_argument(node)), (function.value,)
        if function.attr in SQL_EXECUTE_ATTRIBUTES:
            return classify_sql_statement(literal_string_argument(node)), (function.value,)
        return None, ()

    def _is_tracked_module_attribute(self, function: ast.Attribute) -> bool:
        base = function.value
        return isinstance(base, ast.Name) and base.id in self._bindings.module_aliases

    def _rebound_module_kind(self, function: ast.Attribute) -> str | None:
        base = function.value
        if not isinstance(base, ast.Name):
            return None
        modules = self._bindings.rebound_module_aliases.get(base.id)
        if not modules:
            return None
        known = any(
            (module, function.attr) in MODULE_OPERATIONS
            or (module, function.attr) in SPECIAL_MODULE_FUNCTIONS
            for module in modules
        )
        return "ALIAS_TARGET_UNKNOWN" if known else None

    def _visit_attribute_call(self, node: ast.Call, function: ast.Attribute) -> None:
        rebound = self._rebound_module_kind(function)
        if rebound is not None:
            # The name came from a tracked module and was reassigned, so the call
            # is recorded as unresolved instead of falling through to silence.
            self._add(rebound, node, (_argument_at(node, 0),))
            return
        if self._is_tracked_module_attribute(function):
            # ``os.open(path, flags)`` takes integer flags, not a mode string, so a
            # module function never falls through to the path-receiver vocabulary.
            kind, destination = self._module_attribute_kind(node, function)
        else:
            kind, destination = self._receiver_kind(node, function)
        if kind is not None:
            self._add(kind, node, destination)

    def _special_kind(
        self, node: ast.Call, target: tuple[str, str]
    ) -> tuple[str | None, tuple[ast.expr | None, ...]]:
        if target == ("os", "open"):
            return classify_descriptor_open(node, self._bindings), (_argument_at(node, 0),)
        if target == ("builtins", "open"):
            return classify_open_call(node, mode_index=1), (_argument_at(node, 0),)
        if target == ("tempfile", "NamedTemporaryFile"):
            directory = (
                None
                if any(isinstance(argument, ast.Starred) for argument in node.args)
                else _argument_at(node, 6, "dir")
            )
            return classify_named_temporary_file(node), (
                directory,
            )
        if target == ("tempfile", "TemporaryDirectory"):
            directory = (
                None
                if any(isinstance(argument, ast.Starred) for argument in node.args)
                else _argument_at(node, 2, "dir")
            )
            return classify_temporary_directory(node), (directory,)
        if target == ("sqlite3", "connect"):
            return classify_sqlite_connect(node), (
                _argument_at(node, 0, "database"),
            )
        kind = classify_open_call(node, mode_index=1)
        resolved = "DESCRIPTOR_OPEN_WRITE" if kind == "OPEN_WRITE" else kind
        return resolved, (_argument_at(node, 0),)

    def _visit_name_call(self, node: ast.Call, function: ast.Name) -> None:
        if function.id in self._bindings.ambiguous_writer_aliases:
            # The name reaches more than one tracked operation, so the call is
            # recorded as an unresolved write rather than dropped.
            self._add("ALIAS_TARGET_UNKNOWN", node, (_argument_at(node, 0),))
            return
        special = self._bindings.special_aliases.get(function.id)
        if special is not None:
            # A directly imported or rebound os.open keeps the same flag rules.
            kind, operands = self._special_kind(node, special)
            if kind is not None:
                self._add(kind, node, operands)
            return
        direct = self._bindings.direct_aliases.get(function.id)
        if direct is not None:
            self._add(MODULE_OPERATIONS[direct], node, _operands(node, direct, MODULE_OPERAND_INDICES.get(direct, (0,))))
            return
        receiver = self._bindings.receiver_aliases.get(function.id)
        if receiver is not None:
            kind = self._bound_receiver_kind(node, receiver[1])
            if kind is not None:
                self._add(kind, node, (None,))

    @staticmethod
    def _bound_receiver_kind(node: ast.Call, attribute: str) -> str | None:
        if attribute == "executescript":
            return classify_sql_script(literal_string_argument(node))
        if attribute in SQL_EXECUTE_ATTRIBUTES:
            return classify_sql_statement(literal_string_argument(node))
        return RECEIVER_OPERATIONS.get(attribute)

    def _visit_closed_expression_call(self, node: ast.Call, function: ast.expr) -> None:
        resolution = resolve_callable_expression(function, self._bindings)
        target = resolution.target
        if target is None or not callable_target_is_writer(target):
            return
        if target[0] == "<receiver>":
            kind = self._bound_receiver_kind(node, target[1])
            if kind is not None:
                self._add(kind, node, (None,))
            return
        if target in SPECIAL_MODULE_FUNCTIONS:
            kind, operands = self._special_kind(node, target)
            if kind is not None:
                self._add(kind, node, operands)
            return
        kind = MODULE_OPERATIONS.get(target)
        if kind is not None:
            self._add(
                kind,
                node,
                _operands(node, target, MODULE_OPERAND_INDICES.get(target, (0,))),
            )

    def visit_Call(self, node: ast.Call) -> None:
        function = node.func
        if isinstance(function, ast.Attribute):
            self._visit_attribute_call(node, function)
        elif isinstance(function, ast.Name):
            self._visit_name_call(node, function)
        elif isinstance(function, (ast.Subscript, ast.Call)):
            self._visit_closed_expression_call(node, function)
        self.generic_visit(node)

    def _visit_state_target(self, target: ast.AST, node: ast.AST) -> None:
        if (
            isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id == "self"
            and target.attr == "_state"
        ):
            self._add("STATE_ATTRIBUTE_ASSIGN", node, (ast.Constant(value="self._state"),))

    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            self._visit_state_target(target, node)
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        self._visit_state_target(node.target, node)
        self.generic_visit(node)


def _unique_module_function(tree: ast.Module, name: str) -> ast.FunctionDef | ast.AsyncFunctionDef | None:
    """Return a module-level function only when its name is unambiguous.

    A method, a nested function, or a redefinition may share a bare name, so an
    ambiguous name yields nothing and the destination stays unresolved.
    """

    matches = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name
    ]
    shadowed = sum(
        1
        for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name
    )
    return matches[0] if len(matches) == 1 and shadowed == 1 else None


def _local_caller_literals(tree: ast.Module, function: str, parameter: str) -> tuple[str, ...]:
    """Collect literals that local direct calls pass for one operand parameter.

    These enrich the fingerprint so a caller that swaps an evidence path for a
    balance path changes the identity.  They never prove the caller set: an
    attribute call, an alias, a dynamic call, or a caller in another module is
    outside this scan, so the destination stays unresolved regardless.
    """

    definition = _unique_module_function(tree, function)
    if definition is None:
        return ()
    names = [argument.arg for argument in (*definition.args.posonlyargs, *definition.args.args)]
    if parameter not in names:
        return ()
    position = names.index(parameter)
    literals: set[str] = set()
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name) or node.func.id != function:
            continue
        supplied: ast.expr | None = node.args[position] if len(node.args) > position else None
        if supplied is None:
            for keyword in node.keywords:
                if keyword.arg == parameter:
                    supplied = keyword.value
        if isinstance(supplied, ast.Constant) and isinstance(supplied.value, str):
            literals.add(supplied.value)
    return tuple(sorted(literals))


def _bind_callers(tree: ast.Module, pending: _PendingV2) -> ValueSinkObservationV2:
    observation = pending.observation
    if pending.parameter is None or pending.function is None:
        return observation
    literals = _local_caller_literals(tree, pending.function, pending.parameter)
    observed = f"LOCAL_CALLERS:{','.join(literals)}" if literals else "LOCAL_CALLERS:NONE"
    # A closed call graph is out of scope, so the destination remains
    # caller-determined even when every local call site is a literal.
    descriptor = f"{observation.destination}|{observed}|CALLER_SET:UNRESOLVED"
    return replace(
        observation,
        destination=descriptor,
        caller_determined=True,
        fingerprint=operation_fingerprint(observation.sink_kind, pending.node, descriptor),
    )


def _bind_module_source(
    observation: ValueSinkObservationV2, source_sha256: str
) -> ValueSinkObservationV2:
    payload = (
        b"zenodex-m6-operation-module-source-v2\0"
        + source_sha256.encode("ascii")
        + b"\0"
        + observation.fingerprint.encode("ascii")
    )
    return replace(observation, fingerprint=hashlib.sha256(payload).hexdigest())


def scan_module(
    path: str,
    tree: ast.Module,
    *,
    source_sha256: str | None = None,
    resource_meter: ScanResourceMeterV2 | None = None,
) -> tuple[ValueSinkObservationV2, ...]:
    """Observe every recognized durable-write operation in one parsed module."""

    bindings = resolve_import_bindings(tree)
    visitor = _SinkVisitorV2(
        path=path,
        bindings=bindings,
        path_resolver=LiteralPathResolverV2(tree),
        resource_meter=resource_meter,
    )
    visitor.visit(tree)
    source_binding = source_sha256 or hashlib.sha256(
        ast.dump(tree, annotate_fields=True, include_attributes=False).encode("utf-8")
    ).hexdigest()
    return tuple(
        sorted(
            _bind_module_source(_bind_callers(tree, item), source_binding)
            for item in visitor.pending
        )
    )
