"""Pure AST discovery for dynamic, lifecycle, and aliased sink surfaces."""

from __future__ import annotations

import ast
import re

from tools.m6_indirect_value_sinks.model import (
    DynamicDeclarationV1,
    IndirectAliasV1,
    LifecycleRecordV1,
    canonical_root,
    reject,
)
from tools.m6_value_sinks.operations import MODULE_OPERATIONS, RECEIVER_OPERATIONS

DYNAMIC_CALLS = frozenset(
    {"__import__", "exec_module", "import_module", "load_module", "spec_from_file_location"}
)
DYNAMIC_TARGET_SIGNATURES: dict[str, tuple[int, str, str]] = {
    "__import__": (0, "name", "MODULE_NAME"),
    "exec_module": (0, "module", "MODULE_OBJECT"),
    "import_module": (0, "name", "MODULE_NAME"),
    "load_module": (0, "fullname", "MODULE_NAME"),
    "spec_from_file_location": (1, "location", "FILE_LOCATION"),
}
LIFECYCLE_ORDER = ("RECOVERY", "MIGRATION", "CALLBACK", "WORKER", "ADMINISTRATIVE")
LIFECYCLE_STEMS: dict[str, tuple[str, ...]] = {
    "RECOVERY": ("recover", "reopen", "restore", "restart", "bootstrap", "reconcile", "replay"),
    "MIGRATION": ("migrat", "upgrade", "rollback", "quiesc", "cutover"),
    "CALLBACK": ("callback", "hook", "handler"),
    "WORKER": ("worker", "deliver", "outbox", "consumer", "relayer", "dequeue", "enqueue"),
    "ADMINISTRATIVE": (
        "admin",
        "govern",
        "operator",
        "emergency",
        "shutdown",
        "pause",
        "resume",
        "rotate",
        "revoke",
        "authorityswitch",
    ),
}


def _name_parts(value: str) -> tuple[str, ...]:
    split_camel = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", value)
    return tuple(part.lower() for part in re.split(r"[^A-Za-z0-9]+", split_camel) if part)


def lifecycle_categories(value: str) -> tuple[str, ...]:
    parts = _name_parts(value)
    found = {
        category
        for category, stems in LIFECYCLE_STEMS.items()
        if any(part.startswith(stem) for part in parts for stem in stems)
    }
    return tuple(category for category in LIFECYCLE_ORDER if category in found)


def _call_name(node: ast.Call) -> str | None:
    function = node.func
    if isinstance(function, ast.Name):
        return function.id
    return function.attr if isinstance(function, ast.Attribute) else None


def _target_argument(node: ast.Call, mechanism: str, *, path: str) -> tuple[ast.expr, str]:
    index, keyword_name, target_kind = DYNAMIC_TARGET_SIGNATURES[mechanism]
    if any(isinstance(arg, ast.Starred) for arg in node.args[: index + 1]):
        reject("DYNAMIC_SIGNATURE", path, f"{node.lineno}:{mechanism}:starred target")
    positional = node.args[index] if len(node.args) > index else None
    keywords = [keyword.value for keyword in node.keywords if keyword.arg == keyword_name]
    if any(keyword.arg is None for keyword in node.keywords):
        reject("DYNAMIC_SIGNATURE", path, f"{node.lineno}:{mechanism}:kwargs target")
    if len(keywords) > 1 or (positional is not None and keywords):
        reject("DYNAMIC_SIGNATURE", path, f"{node.lineno}:{mechanism}:ambiguous target")
    selected = positional if positional is not None else keywords[0] if keywords else None
    if selected is None:
        reject("DYNAMIC_SIGNATURE", path, f"{node.lineno}:{mechanism}:missing target")
    return selected, target_kind


def _closed_integration_exports(tree: ast.Module) -> tuple[str, ...]:
    for node in tree.body:
        if not isinstance(node, ast.AnnAssign) or not isinstance(node.target, ast.Name):
            continue
        if node.target.id != "_LAZY_EXPORTS_V1" or not isinstance(node.value, ast.Dict):
            continue
        modules: set[str] = set()
        for value in node.value.values:
            if not isinstance(value, ast.Tuple) or not value.elts:
                return ()
            module = value.elts[0]
            if not isinstance(module, ast.Constant) or not isinstance(module.value, str):
                return ()
            modules.add(module.value.replace(".", "/") + ".py")
        return tuple(sorted(modules))
    return ()


def scan_dynamic_declarations(
    path: str,
    tree: ast.Module,
    *,
    primary_reachable: bool,
    source_sha256: str,
) -> tuple[DynamicDeclarationV1, ...]:
    rows: list[DynamicDeclarationV1] = []
    closed_exports = _closed_integration_exports(tree) if path == "src/integration/__init__.py" else ()
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or (mechanism := _call_name(node)) not in DYNAMIC_CALLS:
            continue
        target_node, target_kind = _target_argument(node, mechanism, path=path)
        target_expression = ast.dump(
            target_node, annotate_fields=True, include_attributes=False
        )
        literal = (
            target_node.value
            if isinstance(target_node, ast.Constant) and isinstance(target_node.value, str)
            else None
        )
        status: str
        targets: tuple[str, ...]
        if mechanism != "exec_module" and literal is not None:
            status, targets = "LITERAL_TARGET", (literal,)
        elif mechanism == "import_module" and closed_exports:
            status, targets = "CLOSED_STATIC_REGISTRY", closed_exports
        else:
            status, targets = "UNRESOLVED_SYNTACTIC", ()
        fingerprint = canonical_root(
            "zenodex/o007c-dynamic-declaration/v1",
            {
                "ast": ast.dump(node, annotate_fields=True, include_attributes=False),
                "line": node.lineno,
                "mechanism": mechanism,
                "path": path,
                "status": status,
                "target_expression": target_expression,
                "target_kind": target_kind,
                "targets": list(targets),
            },
        )
        rows.append(
            DynamicDeclarationV1(
                path=path,
                line=node.lineno,
                mechanism=mechanism,
                fingerprint=fingerprint,
                primary_reachable=primary_reachable,
                source_sha256=source_sha256,
                target_expression=target_expression,
                target_kind=target_kind,
                target_status=status,
                targets=targets,
            )
        )
    return tuple(sorted(rows))


def _module_aliases(tree: ast.Module) -> dict[str, str]:
    return {
        alias.asname or alias.name: alias.name
        for node in ast.walk(tree)
        if isinstance(node, ast.Import)
        for alias in node.names
    }


def _path_aliases(tree: ast.Module) -> frozenset[str]:
    return frozenset(
        alias.asname or alias.name
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module == "pathlib"
        for alias in node.names
        if alias.name in {"Path", "PosixPath", "PurePath", "WindowsPath"}
    )


def _qualified_symbols(tree: ast.Module) -> dict[ast.AST, str]:
    result: dict[ast.AST, str] = {}

    class Visitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.scope: list[str] = []

        def visit_ClassDef(self, node: ast.ClassDef) -> None:
            self.scope.append(node.name)
            self.generic_visit(node)
            self.scope.pop()

        def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
            self.scope.append(node.name)
            self.generic_visit(node)
            self.scope.pop()

        visit_FunctionDef = _visit_function
        visit_AsyncFunctionDef = _visit_function

        def visit_Attribute(self, node: ast.Attribute) -> None:
            result[node] = ".".join(self.scope) if self.scope else "<module>"
            self.generic_visit(node)

    Visitor().visit(tree)
    return result


def scan_indirect_aliases(
    path: str,
    tree: ast.Module,
    *,
    primary_reachable: bool,
) -> tuple[IndirectAliasV1, ...]:
    parents = {child: parent for parent in ast.walk(tree) for child in ast.iter_child_nodes(parent)}
    modules = _module_aliases(tree)
    path_aliases = _path_aliases(tree)
    symbols = _qualified_symbols(tree)
    rows: list[IndirectAliasV1] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Attribute) or not isinstance(node.ctx, ast.Load):
            continue
        parent = parents.get(node)
        if isinstance(parent, ast.Call) and parent.func is node:
            continue
        sink_kind: str | None = None
        if isinstance(node.value, ast.Name):
            module = modules.get(node.value.id)
            if module is not None:
                sink_kind = MODULE_OPERATIONS.get((module, node.attr))
            if node.value.id in path_aliases:
                sink_kind = RECEIVER_OPERATIONS.get(node.attr)
        if sink_kind is None:
            continue
        fingerprint = canonical_root(
            "zenodex/o007c-indirect-alias/v1",
            {
                "ast": ast.dump(node, annotate_fields=True, include_attributes=False),
                "line": node.lineno,
                "path": path,
                "sink_kind": sink_kind,
                "symbol": symbols[node],
            },
        )
        rows.append(
            IndirectAliasV1(
                path=path,
                symbol=symbols[node],
                line=node.lineno,
                sink_kind=sink_kind,
                fingerprint=fingerprint,
                primary_reachable=primary_reachable,
            )
        )
    return tuple(sorted(rows))


def scan_lifecycle_records(
    path: str,
    tree: ast.Module,
    *,
    primary_reachable: bool,
) -> tuple[LifecycleRecordV1, ...]:
    rows: list[LifecycleRecordV1] = []

    class Visitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.scope: list[str] = []

        def visit_ClassDef(self, node: ast.ClassDef) -> None:
            self.scope.append(node.name)
            self.generic_visit(node)
            self.scope.pop()

        def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
            self.scope.append(node.name)
            symbol = ".".join(self.scope)
            categories = lifecycle_categories(node.name)
            if categories:
                rows.append(
                    LifecycleRecordV1(
                        path=path,
                        symbol=symbol,
                        line=node.lineno,
                        categories=categories,
                        fingerprint=canonical_root(
                            "zenodex/o007c-lifecycle/v1",
                            {
                                "ast": ast.dump(node.args, annotate_fields=True, include_attributes=False),
                                "categories": list(categories),
                                "line": node.lineno,
                                "path": path,
                                "symbol": symbol,
                            },
                        ),
                        primary_reachable=primary_reachable,
                    )
                )
            self.generic_visit(node)
            self.scope.pop()

        visit_FunctionDef = _visit_function
        visit_AsyncFunctionDef = _visit_function

    Visitor().visit(tree)
    return tuple(sorted(rows))
