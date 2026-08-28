"""Deterministic AST and fixed-vector analyzers for Tau source replay V1."""

from __future__ import annotations

import ast
import hashlib
import json
import re
from typing import Final, NoReturn

from tools.current_tau_compatibility_core_v1 import CurrentTauCompatibilityRejectV1

LEGACY_OPERATION_KEYS_V1: Final = (
    "_DEX_INTENTS_KEY",
    "_DEX_SETTLEMENT_KEY",
    "_DEX_FAUCET_KEY",
    "_PERP_OPS_KEY",
    "_TOKEN_OPS_KEY",
    "_PROOF_MINING_OPS_KEY",
    "_ZUSD_MONETARY_OPS_KEY",
)

_DYNAMIC_NAMESPACE_PRIMITIVES_V1: Final = frozenset(
    {
        "__builtins__",
        "__dict__",
        "__getattribute__",
        "__getattr__",
        "__setattr__",
        "compile",
        "delattr",
        "eval",
        "exec",
        "getattr",
        "globals",
        "locals",
        "setattr",
        "vars",
    }
)
_MUTATING_METHODS_V1: Final = frozenset(
    {
        "__delitem__",
        "__setitem__",
        "append",
        "clear",
        "extend",
        "insert",
        "pop",
        "popitem",
        "remove",
        "setdefault",
        "sort",
        "update",
    }
)


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CurrentTauCompatibilityRejectV1(code, path, detail)


def python_tree_v1(raw: bytes, path: str) -> ast.Module:
    try:
        return ast.parse(raw.decode("utf-8"), filename=path)
    except (SyntaxError, UnicodeDecodeError) as exc:
        _reject("PYTHON_SOURCE_PARSE", path, type(exc).__name__)


def _bound_name_v1(alias: ast.alias, *, import_from: bool) -> str:
    return alias.asname or (alias.name if import_from else alias.name.split(".", 1)[0])


def _name_binding_nodes_v1(root: ast.AST, name: str) -> tuple[ast.AST, ...]:
    """Return every syntactic binder of a protected name at every nesting level."""

    bindings: list[ast.AST] = []
    for node in ast.walk(root):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.name == name:
            bindings.append(node)
        elif isinstance(node, ast.Import):
            bindings.extend(
                alias
                for alias in node.names
                if _bound_name_v1(alias, import_from=False) == name
            )
        elif isinstance(node, ast.ImportFrom):
            bindings.extend(
                alias
                for alias in node.names
                if _bound_name_v1(alias, import_from=True) == name
            )
        elif isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id == name:
            bindings.append(node)
        elif isinstance(node, ast.arg) and node.arg == name:
            bindings.append(node)
        elif isinstance(node, (ast.Global, ast.Nonlocal)) and name in node.names:
            bindings.append(node)
    return tuple(bindings)


def _module_scope_statements_v1(root: ast.Module) -> tuple[ast.stmt, ...]:
    """Return statements that execute in the module namespace.

    A nested ``def main`` inside an unrelated callback is a lexical-local name,
    while ``if flag: def main`` competes for the module binding.  Keeping that
    distinction avoids treating ordinary upstream nested callbacks as a forged
    module entry point.
    """

    statements: list[ast.stmt] = []

    def visit(node: ast.AST, *, is_root: bool = False) -> None:
        if isinstance(node, ast.stmt):
            statements.append(node)
        if not is_root and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            return
        for child in ast.iter_child_nodes(node):
            visit(child)

    visit(root, is_root=True)
    return tuple(statements)


def _module_scope_name_bindings_v1(root: ast.Module, name: str) -> tuple[ast.AST, ...]:
    bindings: list[ast.AST] = []
    for node in _module_scope_statements_v1(root):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.name == name:
            bindings.append(node)
        elif isinstance(node, ast.Import):
            bindings.extend(
                alias
                for alias in node.names
                if _bound_name_v1(alias, import_from=False) == name
            )
        elif isinstance(node, ast.ImportFrom):
            bindings.extend(
                alias
                for alias in node.names
                if _bound_name_v1(alias, import_from=True) == name
            )
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete)):
            targets = (
                tuple(node.targets)
                if isinstance(node, (ast.Assign, ast.Delete))
                else (node.target,)
            )
            bindings.extend(
                target
                for target in targets
                if isinstance(target, ast.Name) and target.id == name
            )
    if any(isinstance(node, ast.Global) and name in node.names for node in ast.walk(root)):
        bindings.append(root)
    return tuple(bindings)


def _function_v1(tree: ast.Module, name: str, path: str) -> ast.FunctionDef:
    matches = [
        node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == name
    ]
    bindings = _module_scope_name_bindings_v1(tree, name)
    if (
        len(matches) != 1
        or matches[0].decorator_list
        or len(bindings) != 1
        or bindings[0] is not matches[0]
    ):
        _reject("FUNCTION_SHAPE", path, f"expected one unshadowed top-level function {name}")
    return matches[0]


def _has_exact_parameters_v1(
    function: ast.FunctionDef,
    names: tuple[str, ...],
) -> bool:
    arguments = function.args
    positional = (*arguments.posonlyargs, *arguments.args)
    return (
        tuple(argument.arg for argument in positional) == names
        and not arguments.kwonlyargs
        and arguments.vararg is None
        and arguments.kwarg is None
        and not arguments.defaults
        and not arguments.kw_defaults
    )


def _parent_map_v1(root: ast.AST) -> dict[ast.AST, ast.AST]:
    return {
        child: parent
        for parent in ast.walk(root)
        for child in ast.iter_child_nodes(parent)
    }


def _expression_root_name_v1(value: ast.AST | None) -> str | None:
    """Return the leftmost Name for an attribute/subscript access path."""

    current = value
    while isinstance(current, (ast.Attribute, ast.Subscript)):
        current = current.value
    return current.id if isinstance(current, ast.Name) else None


def _contains_expression_root_v1(value: ast.AST, name: str) -> bool:
    return any(_expression_root_name_v1(node) == name for node in ast.walk(value))


def _has_protected_member_mutation_v1(root: ast.AST, names: frozenset[str]) -> bool:
    """Reject rebinding/mutation through a protected module/object path."""

    for node in ast.walk(root):
        targets: tuple[ast.AST, ...] = ()
        if isinstance(node, ast.Assign):
            targets = tuple(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = (node.target,)
        elif isinstance(node, ast.Delete):
            targets = tuple(node.targets)
        if any(
            isinstance(target, (ast.Attribute, ast.Subscript))
            and _expression_root_name_v1(target) in names
            for target in targets
        ):
            return True
    return False


def _module_import_binding_is_closed_v1(tree: ast.Module, name: str) -> bool:
    imports = [
        (node, alias)
        for node in tree.body
        if isinstance(node, ast.Import)
        for alias in node.names
        if alias.name == name and alias.asname is None
    ]
    return (
        len(imports) == 1
        and len(_module_scope_name_bindings_v1(tree, name)) == 1
        and _module_scope_name_bindings_v1(tree, name)[0] is imports[0][1]
    )


def _from_import_binding_is_closed_v1(
    tree: ast.Module,
    *,
    module: str,
    level: int,
    name: str,
) -> bool:
    imports = [
        (node, alias)
        for node in tree.body
        if isinstance(node, ast.ImportFrom)
        and node.module == module
        and node.level == level
        and len(node.names) == 1
        for alias in node.names
        if alias.name == name and alias.asname is None
    ]
    bindings = _module_scope_name_bindings_v1(tree, name)
    return len(imports) == 1 and len(bindings) == 1 and bindings[0] is imports[0][1]


def _contains_dynamic_namespace_access_v1(root: ast.AST) -> bool:
    """Reject direct and aliased dynamic namespace capability acquisition.

    The parser is intentionally conservative.  A protected analyzer has no
    semantic reason to dynamically look up names, so unknown lookup routes are
    treated as possible authority escape paths.
    """

    for node in ast.walk(root):
        if isinstance(node, ast.Name) and node.id in _DYNAMIC_NAMESPACE_PRIMITIVES_V1:
            return True
        if isinstance(node, ast.Attribute) and node.attr in _DYNAMIC_NAMESPACE_PRIMITIVES_V1:
            return True
        if isinstance(node, (ast.Import, ast.ImportFrom)) and any(
            alias.name.split(".", 1)[-1] in _DYNAMIC_NAMESPACE_PRIMITIVES_V1
            for alias in node.names
        ):
            return True
    return False


def _contains_unbounded_namespace_access_v1(root: ast.AST) -> bool:
    """Identify namespace capabilities other than a statically resolved lookup."""

    non_lookup_primitives = _DYNAMIC_NAMESPACE_PRIMITIVES_V1 - frozenset(
        {"getattr", "__getattribute__"}
    )
    for node in ast.walk(root):
        if isinstance(node, ast.Name) and node.id in non_lookup_primitives:
            return True
        if isinstance(node, ast.Attribute) and node.attr in non_lookup_primitives:
            return True
        if isinstance(node, (ast.Import, ast.ImportFrom)) and any(
            alias.name.split(".", 1)[-1] in non_lookup_primitives for alias in node.names
        ):
            return True
    return False


def _constant_string_v1(value: ast.expr) -> str | None:
    if isinstance(value, ast.Constant) and type(value.value) is str:
        return value.value
    if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
        left = _constant_string_v1(value.left)
        right = _constant_string_v1(value.right)
        if left is not None and right is not None:
            return left + right
    return None


def _dynamic_lookup_aliases_v1(tree: ast.AST) -> frozenset[str]:
    """Find statically visible aliases of getattr-style lookup primitives."""

    aliases = {"getattr", "__getattribute__"}
    changed = True
    while changed:
        changed = False
        for node in ast.walk(tree):
            if not isinstance(node, ast.Assign) or len(node.targets) != 1:
                continue
            target = node.targets[0]
            if not isinstance(target, ast.Name):
                continue
            value = node.value
            source_name = (
                value.id
                if isinstance(value, ast.Name)
                else value.attr
                if isinstance(value, ast.Attribute)
                else None
            )
            if source_name in aliases and target.id not in aliases:
                aliases.add(target.id)
                changed = True
        for node in ast.walk(tree):
            if not isinstance(node, ast.ImportFrom):
                continue
            for alias in node.names:
                if alias.name in {"getattr", "__getattribute__"}:
                    bound = alias.asname or alias.name
                    if bound not in aliases:
                        aliases.add(bound)
                        changed = True
    return frozenset(aliases)


def _protected_binding_uses_dynamic_namespace_access_v1(
    tree: ast.Module,
    names: frozenset[str],
) -> bool:
    """Reject dynamic access that can resolve or replace protected bindings.

    A large source module may legitimately inspect a field on an unrelated
    domain object with ``getattr``.  That observation cannot replace a
    protected module constant.  Access through a namespace primitive, an
    imported primitive alias, a protected literal key, or an unknown lookup key
    remains ambiguous and therefore rejects.
    """

    direct_primitives = _DYNAMIC_NAMESPACE_PRIMITIVES_V1 - frozenset({"getattr"})
    for node in ast.walk(tree):
        if isinstance(node, ast.Name) and node.id in direct_primitives:
            return True
        if isinstance(node, ast.Attribute) and node.attr in direct_primitives:
            return True
        if isinstance(node, (ast.Import, ast.ImportFrom)) and any(
            alias.name.split(".", 1)[-1] in _DYNAMIC_NAMESPACE_PRIMITIVES_V1
            for alias in node.names
        ):
            return True
    lookup_aliases = _dynamic_lookup_aliases_v1(tree)
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        is_lookup = (
            isinstance(node.func, ast.Name) and node.func.id in lookup_aliases
        ) or (
            isinstance(node.func, ast.Attribute) and node.func.attr == "__getattribute__"
        )
        if not is_lookup:
            continue
        if len(node.args) < 2:
            return True
        lookup_key = _constant_string_v1(node.args[1])
        if lookup_key is None or lookup_key in names:
            return True
    return False


def source_references_identifier_v1(raw: bytes, path: str, identifier: str) -> bool:
    """Conservatively classify any executable identifier/string reference as present."""

    tree = python_tree_v1(raw, path)
    direct = any(
        (isinstance(node, ast.Name) and node.id == identifier)
        or (isinstance(node, ast.Attribute) and node.attr == identifier)
        or (
            isinstance(node, ast.Constant)
            and type(node.value) is str
            and node.value == identifier
        )
        for node in ast.walk(tree)
    )
    if direct:
        return True
    if _contains_unbounded_namespace_access_v1(tree):
        return True
    lookup_aliases = _dynamic_lookup_aliases_v1(tree)
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        dynamic_call = (
            isinstance(node.func, ast.Name) and node.func.id in lookup_aliases
        ) or (
            isinstance(node.func, ast.Attribute)
            and node.func.attr == "__getattribute__"
        )
        if not dynamic_call:
            continue
        if len(node.args) < 2:
            return True
        derived = _constant_string_v1(node.args[1])
        if derived is None or derived == identifier:
            return True
    return False


def literal_int_set_v1(raw: bytes, path: str, name: str) -> tuple[int, ...]:
    tree = python_tree_v1(raw, path)
    if _protected_binding_uses_dynamic_namespace_access_v1(tree, frozenset({name})):
        _reject("INT_SET_SHAPE", path, "dynamic namespace access is forbidden")
    matches: list[ast.Set] = []
    for node in tree.body:
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = [node.target]
        elif isinstance(node, ast.Delete):
            targets = node.targets
        else:
            targets = []
        if any(isinstance(target, ast.Name) and target.id == name for target in targets):
            if (
                isinstance(node, ast.Assign)
                and len(node.targets) == 1
                and isinstance(node.value, ast.Set)
            ):
                matches.append(node.value)
    references = [
        node for node in ast.walk(tree) if isinstance(node, ast.Name) and node.id == name
    ]
    if (
        len(matches) != 1
        or len(references) != 1
        or not isinstance(references[0].ctx, ast.Store)
    ):
        _reject("INT_SET_SHAPE", path, f"expected one sole literal write for {name}")
    values: list[int] = []
    for element in matches[0].elts:
        if not isinstance(element, ast.Constant) or type(element.value) is not int:
            _reject("INT_SET_VALUE", path, f"{name} must contain exact integer literals")
        values.append(element.value)
    if len(values) != len(set(values)):
        _reject("INT_SET_DUPLICATE", path, f"{name} contains duplicate integers")
    return tuple(sorted(values))


def literal_string_assignments_v1(
    raw: bytes,
    path: str,
    names: tuple[str, ...],
) -> tuple[int, ...]:
    tree = python_tree_v1(raw, path)
    if _protected_binding_uses_dynamic_namespace_access_v1(tree, frozenset(names)):
        _reject("STREAM_CONSTANT_SHAPE", path, "dynamic namespace access is forbidden")
    values: dict[str, int] = {}
    for node in tree.body:
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if not isinstance(target, ast.Name) or target.id not in names:
            continue
        if not isinstance(node.value, ast.Constant) or type(node.value.value) is not str:
            _reject("STREAM_CONSTANT_TYPE", path, f"{target.id} must be an exact string")
        if not node.value.value.isdigit():
            _reject("STREAM_CONSTANT_VALUE", path, f"{target.id} must be a decimal stream index")
        values[target.id] = int(node.value.value)
    if tuple(values) != names:
        _reject("STREAM_CONSTANT_SHAPE", path, "historical operation stream constants drift")
    for name in names:
        stores = sum(
            isinstance(node, ast.Name)
            and node.id == name
            and isinstance(node.ctx, (ast.Store, ast.Del))
            for node in ast.walk(tree)
        )
        if stores != 1:
            _reject("STREAM_CONSTANT_SHAPE", path, f"{name} must have one write")
    return tuple(values[name] for name in names)


def _dict_assignment_keys_v1(function: ast.FunctionDef, variable: str, path: str) -> set[str]:
    matches: list[ast.Dict] = []
    for node in function.body:
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            continue
        target = node.targets[0]
        if (
            isinstance(target, ast.Name)
            and target.id == variable
            and isinstance(node.value, ast.Dict)
        ):
            matches.append(node.value)
    if len(matches) != 1:
        _reject("SIGNING_DICT_SHAPE", path, f"expected one {variable} literal")
    keys: set[str] = set()
    for key, value in zip(matches[0].keys, matches[0].values, strict=True):
        if not isinstance(key, ast.Constant) or type(key.value) is not str:
            _reject("SIGNING_DICT_KEY", path, "signing keys must be exact strings")
        if key.value in keys:
            _reject("SIGNING_DICT_KEY", path, "signing keys must be unique")
        if not _payload_field_binding_v1(value, key.value):
            _reject("SIGNING_VALUE_BINDING", path, f"{key.value} is not bound to payload")
        keys.add(key.value)
    return keys


def _user_tx_branch_keys_v1(function: ast.FunctionDef, variable: str, path: str) -> set[str]:
    keys: set[str] = set()
    for node in function.body:
        if not isinstance(node, ast.If):
            continue
        test = node.test
        if not _is_user_tx_test_v1(test):
            continue
        for child in node.body:
            if not isinstance(child, ast.Assign) or len(child.targets) != 1:
                _reject("SIGNING_CONTROL_FLOW", path, "user transaction branch is not closed")
            target = child.targets[0]
            if not (
                isinstance(target, ast.Subscript)
                and isinstance(target.value, ast.Name)
                and target.value.id == variable
                and isinstance(target.slice, ast.Constant)
                and type(target.slice.value) is str
            ):
                _reject("SIGNING_CONTROL_FLOW", path, "user signing write shape drift")
            if not _payload_field_binding_v1(child.value, target.slice.value):
                _reject(
                    "SIGNING_VALUE_BINDING",
                    path,
                    f"{target.slice.value} is not bound to payload",
                )
            keys.add(target.slice.value)
    return keys


def _payload_field_binding_v1(value: ast.expr, field: str) -> bool:
    if field == "tx_type":
        return isinstance(value, ast.Name) and value.id == "tx_type"
    if (
        isinstance(value, ast.Subscript)
        and isinstance(value.value, ast.Name)
        and value.value.id == "payload"
        and isinstance(value.slice, ast.Constant)
        and type(value.slice.value) is str
    ):
        return value.slice.value == field
    return (
        isinstance(value, ast.Call)
        and isinstance(value.func, ast.Attribute)
        and isinstance(value.func.value, ast.Name)
        and value.func.value.id == "payload"
        and value.func.attr == "get"
        and len(value.args) in {1, 2}
        and isinstance(value.args[0], ast.Constant)
        and type(value.args[0].value) is str
        and value.args[0].value == field
        and not value.keywords
    )


def _is_user_tx_test_v1(test: ast.expr) -> bool:
    return (
        isinstance(test, ast.Compare)
        and isinstance(test.left, ast.Name)
        and test.left.id == "tx_type"
        and len(test.ops) == 1
        and isinstance(test.ops[0], ast.Eq)
        and len(test.comparators) == 1
        and isinstance(test.comparators[0], ast.Constant)
        and test.comparators[0].value == "user_tx"
    )


def user_tx_signing_fields_v1(raw: bytes, path: str, function_name: str) -> tuple[str, ...]:
    tree = python_tree_v1(raw, path)
    function = _function_v1(tree, function_name, path)
    if not _has_exact_parameters_v1(function, ("payload",)):
        _reject("SIGNING_FUNCTION_SHAPE", path, "signing function must take only payload")
    if _contains_dynamic_namespace_access_v1(function):
        _reject("SIGNING_MUTATION_SHAPE", path, "dynamic namespace access is forbidden")
    if any(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        and node.name == "signing_dict"
        for node in ast.walk(function)
    ):
        _reject("SIGNING_DICT_SHAPE", path, "nested signing_dict binding is forbidden")
    if _has_protected_member_mutation_v1(
        function,
        frozenset({"json", "canonical_json_bytes"}),
    ):
        _reject("SIGNING_MUTATION_SHAPE", path, "serializer member mutation is forbidden")
    if not _payload_uses_are_read_only_v1(function):
        _reject("SIGNING_VALUE_BINDING", path, "payload access is not read-only")
    top_level_returns = [
        index for index, node in enumerate(function.body) if isinstance(node, ast.Return)
    ]
    all_returns = [node for node in ast.walk(function) if isinstance(node, ast.Return)]
    if top_level_returns != [len(function.body) - 1] or len(all_returns) != 1:
        _reject("SIGNING_RETURN_SHAPE", path, "expected one final top-level return")
    if any(isinstance(node, (ast.Delete, ast.Raise)) for node in ast.walk(function)):
        _reject("SIGNING_MUTATION_SHAPE", path, "delete and raise are forbidden")
    signing_assignments = [
        index
        for index, node in enumerate(function.body)
        if isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "signing_dict"
    ]
    user_branches = [
        index
        for index, node in enumerate(function.body)
        if isinstance(node, ast.If) and _is_user_tx_test_v1(node.test)
    ]
    top_level_branches = [
        index for index, node in enumerate(function.body) if isinstance(node, ast.If)
    ]
    if (
        len(signing_assignments) != 1
        or len(user_branches) > 1
        or top_level_branches != user_branches
    ):
        _reject("SIGNING_CONTROL_FLOW", path, "signing assignment or user branch drift")
    branch_is_ordered = not user_branches or (
        signing_assignments[0] < user_branches[0] < top_level_returns[0]
    )
    if not signing_assignments[0] < top_level_returns[0] or not branch_is_ordered:
        _reject("SIGNING_CONTROL_FLOW", path, "signing statements are not reachable in order")
    final_return = function.body[-1]
    if not isinstance(final_return, ast.Return) or not _is_signing_return_v1(
        final_return.value
    ):
        _reject("SIGNING_RETURN_SHAPE", path, "final return must encode canonical signing JSON")
    if _uses_canonical_json_v1(final_return.value):
        if not _canonicalizer_binding_is_closed_v1(tree):
            _reject("SIGNING_RETURN_SHAPE", path, "canonical JSON binding is not closed")
    elif not _json_binding_is_closed_v1(tree):
        _reject("SIGNING_RETURN_SHAPE", path, "json binding is not closed")
    if not _signing_dict_uses_are_closed_v1(function, final_return):
        _reject("SIGNING_MUTATION_SHAPE", path, "signing projection use escaped closed grammar")
    if any(
        isinstance(node, ast.Assign)
        and any(
            isinstance(target, ast.Subscript)
            and isinstance(target.value, ast.Name)
            and target.value.id == "signing_dict"
            for target in node.targets
        )
        for node in function.body
    ):
        _reject("SIGNING_MUTATION_SHAPE", path, "top-level signing overwrite is forbidden")
    keys = _dict_assignment_keys_v1(function, "signing_dict", path)
    if "tx_type" in keys:
        tx_type_bindings = [
            node
            for node in function.body
            if isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and node.targets[0].id == "tx_type"
            and _assignment_matches_v1(node, 'payload.get("tx_type", "user_tx")')
        ]
        if len(tx_type_bindings) != 1 or _name_store_count_v1(function, "tx_type") != 1:
            _reject("SIGNING_VALUE_BINDING", path, "tx_type local binding drift")
    keys.update(_user_tx_branch_keys_v1(function, "signing_dict", path))
    return tuple(sorted(keys))


def _signing_dict_uses_are_closed_v1(
    function: ast.FunctionDef,
    final_return: ast.Return,
) -> bool:
    parents = _parent_map_v1(function)
    return_call = final_return.value
    if not isinstance(return_call, ast.Call):
        return False
    payload_call: ast.expr = return_call
    if isinstance(return_call.func, ast.Attribute) and return_call.func.attr == "encode":
        payload_call = return_call.func.value
    if not isinstance(payload_call, ast.Call):
        return False
    uses = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Name) and node.id == "signing_dict"
    ]
    stores = [node for node in uses if isinstance(node.ctx, ast.Store)]
    if len(stores) != 1:
        return False
    for node in uses:
        if isinstance(node.ctx, ast.Store):
            continue
        parent = parents.get(node)
        if (
            parent is payload_call
            and node in payload_call.args
            and payload_call.args == [node]
        ):
            continue
        if (
            isinstance(parent, ast.Subscript)
            and parent.value is node
            and isinstance(parent.ctx, ast.Store)
            and isinstance(parent.slice, ast.Constant)
            and type(parent.slice.value) is str
        ):
            continue
        return False
    return True


def _payload_uses_are_read_only_v1(function: ast.FunctionDef) -> bool:
    parents = _parent_map_v1(function)
    for node in ast.walk(function):
        targets: tuple[ast.AST, ...] = ()
        if isinstance(node, ast.Assign):
            targets = tuple(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = (node.target,)
        elif isinstance(node, ast.Delete):
            targets = tuple(node.targets)
        if any(_expression_root_name_v1(target) == "payload" for target in targets):
            return False
        if not isinstance(node, ast.Call):
            continue
        if (
            isinstance(node.func, ast.Attribute)
            and _expression_root_name_v1(node.func.value) == "payload"
            and node.func.attr != "get"
        ):
            return False
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr in _MUTATING_METHODS_V1
            and any(_contains_expression_root_v1(argument, "payload") for argument in node.args)
        ):
            return False
    for node in ast.walk(function):
        if not isinstance(node, ast.Name) or node.id != "payload":
            continue
        parent = parents.get(node)
        if (
            isinstance(parent, ast.Subscript)
            and parent.value is node
            and isinstance(parent.ctx, ast.Load)
        ):
            continue
        if (
            isinstance(parent, ast.Attribute)
            and parent.value is node
            and parent.attr == "get"
            and isinstance(parents.get(parent), ast.Call)
        ):
            continue
        if (
            isinstance(parent, ast.Compare)
            and any(comparator is node for comparator in parent.comparators)
            and any(isinstance(operator, ast.In) for operator in parent.ops)
        ):
            continue
        return False
    return True


def _is_signing_return_v1(value: ast.expr | None) -> bool:
    if not isinstance(value, ast.Call):
        return False
    if (
        isinstance(value.func, ast.Name)
        and value.func.id == "canonical_json_bytes"
        and len(value.args) == 1
        and isinstance(value.args[0], ast.Name)
        and value.args[0].id == "signing_dict"
        and not value.keywords
    ):
        return True
    return (
        isinstance(value.func, ast.Attribute)
        and value.func.attr == "encode"
        and isinstance(value.func.value, ast.Call)
        and isinstance(value.func.value.func, ast.Attribute)
        and isinstance(value.func.value.func.value, ast.Name)
        and value.func.value.func.value.id == "json"
        and value.func.value.func.attr == "dumps"
        and len(value.func.value.args) == 1
        and isinstance(value.func.value.args[0], ast.Name)
        and value.func.value.args[0].id == "signing_dict"
        and not value.args
        and not value.keywords
        and _json_dump_keywords_are_canonical_v1(value.func.value)
    )


def _uses_canonical_json_v1(value: ast.expr | None) -> bool:
    return (
        isinstance(value, ast.Call)
        and isinstance(value.func, ast.Name)
        and value.func.id == "canonical_json_bytes"
    )


def _json_dump_keywords_are_canonical_v1(call: ast.Call) -> bool:
    if len(call.keywords) != 2 or any(keyword.arg is None for keyword in call.keywords):
        return False
    keywords = {keyword.arg: keyword.value for keyword in call.keywords if keyword.arg is not None}
    sort_keys = keywords.get("sort_keys")
    separators = keywords.get("separators")
    return (
        len(keywords) == 2
        and isinstance(sort_keys, ast.Constant)
        and sort_keys.value is True
        and separators is not None
        and _is_compact_json_separators_v1(separators)
    )


def _canonicalizer_binding_is_closed_v1(tree: ast.Module) -> bool:
    return _from_import_binding_is_closed_v1(
        tree,
        module="state.canonical",
        level=2,
        name="canonical_json_bytes",
    ) and not _has_protected_member_mutation_v1(
        tree,
        frozenset({"canonical_json_bytes"}),
    )


def _json_binding_is_closed_v1(tree: ast.Module) -> bool:
    return _module_import_binding_is_closed_v1(tree, "json") and not _has_protected_member_mutation_v1(
        tree,
        frozenset({"json"}),
    )


def _class_v1(
    tree: ast.Module,
    name: str,
    path: str,
    *,
    allowed_decorators: frozenset[str] = frozenset(),
) -> ast.ClassDef:
    classes = [node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == name]
    bindings = _module_scope_name_bindings_v1(tree, name)
    if len(classes) != 1 or len(bindings) != 1 or bindings[0] is not classes[0]:
        _reject("CLASS_SHAPE", path, f"expected one unshadowed top-level class {name}")
    if any(
        not isinstance(decorator, ast.Name) or decorator.id not in allowed_decorators
        for decorator in classes[0].decorator_list
    ):
        _reject("CLASS_SHAPE", path, f"unexpected decorator on {name}")
    return classes[0]


def class_methods_v1(raw: bytes, path: str, class_name: str) -> set[str]:
    tree = python_tree_v1(raw, path)
    target = _class_v1(tree, class_name, path)
    return {node.name for node in target.body if isinstance(node, ast.FunctionDef)}


def require_success_envelope_v1(raw: bytes, path: str) -> None:
    tree = python_tree_v1(raw, path)
    function = _function_v1(tree, "success_response", path)
    if not _json_binding_is_closed_v1(tree):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "json binding is not closed")
    if not _has_exact_parameters_v1(function, ("command", "data")):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "success response parameters drift")
    if any(isinstance(node, ast.Raise) for node in ast.walk(function)):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "raise is forbidden")
    statements = [
        node
        for node in function.body
        if not (
            isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and type(node.value.value) is str
        )
    ]
    if len(statements) != 1 or not isinstance(statements[0], ast.Return):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "expected one reachable return")
    value = statements[0].value
    if not (
        isinstance(value, ast.Call)
        and isinstance(value.func, ast.Attribute)
        and isinstance(value.func.value, ast.Name)
        and value.func.value.id == "json"
        and value.func.attr == "dumps"
        and len(value.args) == 1
        and isinstance(value.args[0], ast.Dict)
    ):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "return must serialize one literal envelope")
    envelope = value.args[0]
    if len(envelope.keys) != 3 or len(envelope.values) != 3 or any(
        key is None for key in envelope.keys
    ):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "envelope must have exactly three fields")
    keys = tuple(
        key.value
        if isinstance(key, ast.Constant) and type(key.value) is str
        else None
        for key in envelope.keys
    )
    status_value, command_value, data_value = envelope.values
    keywords_are_exact = (
        len(value.keywords) == 1
        and value.keywords[0].arg == "separators"
        and _is_compact_json_separators_v1(value.keywords[0].value)
    )
    if keys != ("status", "command", "data") or not (
        isinstance(status_value, ast.Constant)
        and type(status_value.value) is str
        and status_value.value == "ok"
        and isinstance(command_value, ast.Name)
        and command_value.id == "command"
        and isinstance(data_value, ast.Call)
        and isinstance(data_value.func, ast.Name)
        and data_value.func.id == "dict"
        and len(data_value.args) == 1
        and isinstance(data_value.args[0], ast.Name)
        and data_value.args[0].id == "data"
        and not data_value.keywords
        and keywords_are_exact
    ):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "current JSON success envelope drift")


def _is_compact_json_separators_v1(value: ast.expr) -> bool:
    return (
        isinstance(value, ast.Tuple)
        and len(value.elts) == 2
        and all(isinstance(element, ast.Constant) for element in value.elts)
        and tuple(element.value for element in value.elts if isinstance(element, ast.Constant))
        == (",", ":")
    )


def force_test_requires_test_env_v1(raw: bytes, path: str) -> bool:
    tree = python_tree_v1(raw, path)
    function = _function_v1(tree, "is_force_test_enabled", path)
    if (
        not _has_exact_parameters_v1(function, ())
        or not _module_import_binding_is_closed_v1(tree, "os")
        or not _module_import_binding_is_closed_v1(tree, "config")
        or _has_protected_member_mutation_v1(tree, frozenset({"os", "config"}))
        or any(isinstance(node, ast.Raise) for node in ast.walk(function))
        or _name_store_count_v1(function, "requested") != 1
        or _name_store_count_v1(function, "runtime_env") != 1
    ):
        return False
    body = function.body
    requested = _named_assignment_index_v1(body, "requested")
    runtime_env = _named_assignment_index_v1(body, "runtime_env")
    requested_guards = [
        (index, node)
        for index, node in enumerate(body)
        if isinstance(node, ast.If)
        and isinstance(node.test, ast.UnaryOp)
        and isinstance(node.test.op, ast.Not)
        and isinstance(node.test.operand, ast.Name)
        and node.test.operand.id == "requested"
    ]
    test_guards = [
        (index, node)
        for index, node in enumerate(body)
        if isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and isinstance(node.test.left, ast.Name)
        and node.test.left.id == "runtime_env"
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.Eq)
        and len(node.test.comparators) == 1
        and isinstance(node.test.comparators[0], ast.Constant)
        and node.test.comparators[0].value == "test"
    ]
    returns = [node for node in ast.walk(function) if isinstance(node, ast.Return)]
    if (
        len(requested_guards) != 1
        or len(test_guards) != 1
        or requested < 0
        or runtime_env < 0
        or not _assignment_matches_v1(
            body[requested], 'os.environ.get("TAU_FORCE_TEST", "0") == "1"'
        )
        or not _assignment_matches_v1(
            body[runtime_env],
            'getattr(getattr(config, "settings", None), "env", None) '
            'or os.environ.get("TAU_ENV", "development")',
        )
        or (requested, requested_guards[0][0], runtime_env, test_guards[0][0])
        != (0, 1, 2, 3)
        or len(returns) != 3
        or not _body_is_single_bool_return_v1(requested_guards[0][1].body, False)
        or not _body_is_single_bool_return_v1(test_guards[0][1].body, True)
        or len(body) != 6
        or not _is_force_rejection_log_v1(body[4])
        or not isinstance(body[-1], ast.Return)
        or not isinstance(body[-1].value, ast.Constant)
        or body[-1].value.value is not False
    ):
        return False
    return True


def _is_force_rejection_log_v1(statement: ast.stmt) -> bool:
    return (
        isinstance(statement, ast.Expr)
        and isinstance(statement.value, ast.Call)
        and isinstance(statement.value.func, ast.Attribute)
        and isinstance(statement.value.func.value, ast.Name)
        and statement.value.func.value.id == "logger"
        and statement.value.func.attr == "error"
        and len(statement.value.args) == 2
        and isinstance(statement.value.args[0], ast.Constant)
        and type(statement.value.args[0].value) is str
        and isinstance(statement.value.args[1], ast.Name)
        and statement.value.args[1].id == "runtime_env"
        and not statement.value.keywords
    )


def _named_assignment_index_v1(body: list[ast.stmt], name: str) -> int:
    return next(
        (
            index
            for index, node in enumerate(body)
            if isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and node.targets[0].id == name
        ),
        -1,
    )


def _name_store_count_v1(root: ast.AST, name: str) -> int:
    return sum(
        isinstance(node, ast.Name)
        and node.id == name
        and isinstance(node.ctx, (ast.Store, ast.Del))
        for node in ast.walk(root)
    )


def _assignment_matches_v1(statement: ast.stmt, expected_expression: str) -> bool:
    if not isinstance(statement, ast.Assign):
        return False
    expected = ast.parse(expected_expression, mode="eval").body
    return ast.dump(statement.value, include_attributes=False) == ast.dump(
        expected, include_attributes=False
    )


def _body_is_single_bool_return_v1(body: list[ast.stmt], expected: bool) -> bool:
    return (
        len(body) == 1
        and isinstance(body[0], ast.Return)
        and isinstance(body[0].value, ast.Constant)
        and body[0].value.value is expected
    )


def historical_force_test_enters_mock_v1(raw: bytes, path: str) -> bool:
    tree = python_tree_v1(raw, path)
    function = _function_v1(
        tree,
        "start_and_manage_tau_process",
        path,
    )
    tau_test_assignments = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "tau_test_mode"
    ]
    false_assignments = [
        node
        for node in tau_test_assignments
        if isinstance(node.value, ast.Constant) and node.value.value is False
    ]
    if (
        not _has_exact_parameters_v1(function, ())
        or not _module_import_binding_is_closed_v1(tree, "os")
        or _contains_dynamic_namespace_access_v1(function)
        or _has_protected_member_mutation_v1(
            function,
            frozenset(
                {
                    "logger",
                    "os",
                    "server_should_stop",
                    "tau_process_ready",
                    "tau_ready",
                    "time",
                }
            ),
        )
        or len(tau_test_assignments) != _name_store_count_v1(function, "tau_test_mode")
        or len(false_assignments) != 1
        or any(
            not isinstance(node.value, ast.Constant)
            or type(node.value.value) is not bool
            for node in tau_test_assignments
        )
    ):
        return False
    initial_false = next(
        (
            index
            for index, node in enumerate(function.body)
            if node is false_assignments[0]
        ),
        -1,
    )
    if initial_false < 0:
        return False
    expected_force_branch = ast.parse(
        '''\
if os.environ.get("TAU_FORCE_TEST", "0") == "1":
    logger.warning("TAU_FORCE_TEST enabled. Running in TEST MODE without Docker.")
    tau_test_mode = True
    tau_process_ready.set()
    tau_ready.set()
    while not server_should_stop.is_set():
        time.sleep(0.05)
    logger.info("Server shutdown requested, Tau manager exiting.")
    return
'''
    ).body[0]
    matches = 0
    for index, node in enumerate(function.body):
        if not isinstance(node, ast.If):
            continue
        if ast.dump(node, include_attributes=False) == ast.dump(
            expected_force_branch, include_attributes=False
        ):
            if initial_false >= index or any(
                isinstance(prior, (ast.If, ast.For, ast.While, ast.Try, ast.With, ast.Match))
                for prior in function.body[:index]
            ):
                return False
            matches += 1
    return matches == 1


def _is_force_test_env_condition_v1(test: ast.expr) -> bool:
    return (
        isinstance(test, ast.Compare)
        and isinstance(test.left, ast.Call)
        and isinstance(test.left.func, ast.Attribute)
        and isinstance(test.left.func.value, ast.Attribute)
        and isinstance(test.left.func.value.value, ast.Name)
        and test.left.func.value.value.id == "os"
        and test.left.func.value.attr == "environ"
        and test.left.func.attr == "get"
        and len(test.left.args) == 2
        and isinstance(test.left.args[0], ast.Constant)
        and test.left.args[0].value == "TAU_FORCE_TEST"
        and isinstance(test.left.args[1], ast.Constant)
        and test.left.args[1].value == "0"
        and len(test.ops) == 1
        and isinstance(test.ops[0], ast.Eq)
        and len(test.comparators) == 1
        and isinstance(test.comparators[0], ast.Constant)
        and test.comparators[0].value == "1"
    )


def command_registry_keys_v1(raw: bytes, path: str) -> tuple[str, ...]:
    tree = python_tree_v1(raw, path)
    container = _class_v1(
        tree,
        "ServiceContainer",
        path,
        allowed_decorators=frozenset({"dataclass"}),
    )
    builds = [node for node in container.body if isinstance(node, ast.FunctionDef) and node.name == "build"]
    build_bindings = _name_binding_nodes_v1(container, "build")
    if (
        len(builds) != 1
        or len(build_bindings) != 1
        or build_bindings[0] is not builds[0]
        or len(builds[0].decorator_list) != 1
        or not isinstance(builds[0].decorator_list[0], ast.Name)
        or builds[0].decorator_list[0].id != "classmethod"
    ):
        _reject("COMMAND_REGISTRY_FUNCTION", path, "expected one build method")
    build = builds[0]
    positional = (*build.args.posonlyargs, *build.args.args)
    if (
        tuple(argument.arg for argument in positional) != ("cls",)
        or tuple(argument.arg for argument in build.args.kwonlyargs) != ("settings", "overrides")
        or build.args.vararg is not None
        or build.args.kwarg is not None
        or build.args.defaults
        or len(build.args.kw_defaults) != 2
        or any(
            default is None
            or not isinstance(default, ast.Constant)
            or default.value is not None
            for default in build.args.kw_defaults
        )
        or any(isinstance(node, ast.Raise) for node in ast.walk(build))
        or _contains_dynamic_namespace_access_v1(build)
        or _has_protected_member_mutation_v1(tree, frozenset({"ServiceContainer"}))
    ):
        _reject("COMMAND_REGISTRY_MUTATION", path, "raise is forbidden in registry construction")
    dictionaries: list[ast.Dict] = []
    override_maps: list[ast.Assign] = []
    for node in build.body:
        if (
            isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and node.targets[0].id == "override_map"
            and _assignment_matches_v1(node, "overrides or {}")
        ):
            override_maps.append(node)
        if not (
            isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and node.targets[0].id == "command_handlers"
            and isinstance(node.value, ast.BoolOp)
            and isinstance(node.value.op, ast.Or)
            and len(node.value.values) == 2
            and isinstance(node.value.values[0], ast.Call)
            and isinstance(node.value.values[0].func, ast.Attribute)
            and isinstance(node.value.values[0].func.value, ast.Name)
            and node.value.values[0].func.value.id == "override_map"
            and node.value.values[0].func.attr == "get"
            and len(node.value.values[0].args) == 1
            and isinstance(node.value.values[0].args[0], ast.Constant)
            and node.value.values[0].args[0].value == "command_handlers"
            and not node.value.values[0].keywords
            and isinstance(node.value.values[1], ast.Dict)
        ):
            continue
        dictionaries.append(node.value.values[1])
    if (
        len(dictionaries) != 1
        or len(override_maps) != 1
        or _name_store_count_v1(build, "override_map") != 1
        or _name_store_count_v1(build, "command_handlers") != 1
    ):
        _reject("COMMAND_REGISTRY_SHAPE", path, "expected one reachable literal registry")
    name_writes = sum(
        isinstance(node, ast.Name)
        and node.id == "command_handlers"
        and isinstance(node.ctx, (ast.Store, ast.Del))
        for node in ast.walk(build)
    )
    subscript_writes = sum(
        isinstance(node, ast.Subscript)
        and isinstance(node.ctx, (ast.Store, ast.Del))
        and isinstance(node.value, ast.Name)
        and node.value.id == "command_handlers"
        for node in ast.walk(build)
    )
    mutator_calls = sum(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "command_handlers"
        and node.func.attr in {"clear", "pop", "popitem", "setdefault", "update"}
        for node in ast.walk(build)
    )
    if (
        name_writes != 1
        or subscript_writes
        or mutator_calls
        or not _command_registry_uses_are_closed_v1(build)
    ):
        _reject("COMMAND_REGISTRY_MUTATION", path, "registry changes after construction")
    keys: list[str] = []
    for key in dictionaries[0].keys:
        if not isinstance(key, ast.Constant) or type(key.value) is not str:
            _reject("COMMAND_REGISTRY_KEY", path, "registry keys must be exact strings")
        keys.append(key.value)
    if len(keys) != len(set(keys)):
        _reject("COMMAND_REGISTRY_DUPLICATE", path, "duplicate command key")
    return tuple(keys)


def _command_registry_uses_are_closed_v1(function: ast.FunctionDef) -> bool:
    parents = _parent_map_v1(function)
    uses = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Name) and node.id == "command_handlers"
    ]
    stores = [node for node in uses if isinstance(node.ctx, ast.Store)]
    if len(stores) != 1:
        return False
    for node in uses:
        if isinstance(node.ctx, ast.Store):
            continue
        parent = parents.get(node)
        if (
            isinstance(parent, ast.keyword)
            and parent.arg == "command_handlers"
            and parent.value is node
            and isinstance(parents.get(parent), ast.Call)
            and isinstance(parents[parent].func, ast.Name)
            and parents[parent].func.id == "cls"
            and isinstance(parents.get(parents[parent]), ast.Return)
            and function.body[-1] is parents[parents[parent]]
        ):
            continue
        return False
    return True


def server_uses_default_command_registry_v1(raw: bytes, path: str) -> bool:
    tree = python_tree_v1(raw, path)
    try:
        function = _function_v1(tree, "main", path)
    except CurrentTauCompatibilityRejectV1:
        return False
    if not _from_import_binding_is_closed_v1(
        tree,
        module="app.container",
        level=0,
        name="ServiceContainer",
    ) or _has_protected_member_mutation_v1(tree, frozenset({"ServiceContainer"})):
        return False
    parents = _parent_map_v1(function)
    calls = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "ServiceContainer"
        and node.func.attr == "build"
    ]
    if len(calls) != 1 or calls[0].args or len(calls[0].keywords) != 1:
        return False
    call = calls[0]
    assignment = parents.get(call)
    if not (
        isinstance(assignment, ast.Assign)
        and len(assignment.targets) == 1
        and isinstance(assignment.targets[0], ast.Name)
        and assignment.targets[0].id == "container"
        and assignment in function.body
    ):
        return False
    keyword = calls[0].keywords[0]
    if keyword.arg != "overrides" or not isinstance(keyword.value, ast.Dict):
        return False
    keys = tuple(
        key.value if isinstance(key, ast.Constant) and type(key.value) is str else None
        for key in keyword.value.keys
    )
    if keys != ("logger", "ephemeral_identity"):
        return False
    build_index = function.body.index(assignment)
    if any(
        isinstance(node, (ast.Return, ast.Raise, ast.Break, ast.Continue))
        for node in function.body[:build_index]
    ):
        return False
    if _name_store_count_v1(function, "container") != 1:
        return False
    run_calls = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "_run_server"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
        and node.args[0].id == "container"
        and not node.keywords
    ]
    if len(run_calls) != 1:
        return False
    current: ast.AST = run_calls[0]
    top_level: ast.stmt | None = None
    while current in parents:
        current = parents[current]
        if current in function.body:
            top_level = current if isinstance(current, ast.stmt) else None
            break
    if top_level is None or function.body.index(top_level) <= build_index:
        return False
    return not any(
        (
            isinstance(node, ast.Attribute)
            and node.attr == "command_handlers"
            and isinstance(node.ctx, (ast.Store, ast.Del))
        )
        or (
            isinstance(node, ast.Subscript)
            and isinstance(node.ctx, (ast.Store, ast.Del))
            and isinstance(node.value, ast.Attribute)
            and node.value.attr == "command_handlers"
        )
        for node in ast.walk(tree)
    )


def historical_apply_app_tx_bridge_v1(raw: bytes, path: str) -> bool:
    function = _function_v1(python_tree_v1(raw, path), "_call_app_bridge", path)
    if _contains_dynamic_namespace_access_v1(function) or _has_protected_member_mutation_v1(
        function,
        frozenset({"bridge"}),
    ):
        return False
    statements = [
        node
        for node in function.body
        if not (
            isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and type(node.value.value) is str
        )
    ]
    if not statements or not isinstance(statements[0], ast.Try) or not statements[0].body:
        return False
    first = statements[0].body[0]
    return (
        isinstance(first, ast.Assign)
        and isinstance(first.value, ast.Call)
        and isinstance(first.value.func, ast.Attribute)
        and isinstance(first.value.func.value, ast.Name)
        and first.value.func.value.id == "bridge"
        and first.value.func.attr == "apply_app_tx"
    )


def single_profile_value_v1(raw: bytes, path: str, key: str) -> str:
    text = raw.decode("utf-8")
    pattern = re.compile(rf'^\s+{re.escape(key)}:\s*"([^"]+)"\s*$', re.MULTILINE)
    matches = pattern.findall(text)
    if len(matches) != 1:
        _reject("PROFILE_KEY_SHAPE", path, f"expected one quoted {key} value")
    return matches[0]


def compose_service_environment_value_v1(
    raw: bytes,
    path: str,
    service: str,
    key: str,
) -> str:
    """Read one double-quoted scalar from an exact Compose service environment path."""

    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        _reject("PROFILE_YAML_SHAPE", path, type(exc).__name__)
    if "\t" in text:
        _reject("PROFILE_YAML_SHAPE", path, "tabs are forbidden")
    stack: list[tuple[int, str]] = []
    occurrences: dict[tuple[str, ...], int] = {}
    matches: list[str] = []
    block_scalar_indent: int | None = None
    mapping_line = re.compile(r"^([A-Za-z0-9_.-]+):(?:\s*(.*))?$")
    block_scalar = re.compile(r"^[|>](?:[1-9][+-]?|[+-][1-9]?)?$")
    required_paths = (
        ("services",),
        ("services", service),
        ("services", service, "environment"),
        ("services", service, "environment", key),
    )
    for raw_line in text.splitlines():
        if not raw_line.strip() or raw_line.lstrip().startswith("#"):
            continue
        indent = len(raw_line) - len(raw_line.lstrip(" "))
        if block_scalar_indent is not None:
            if indent > block_scalar_indent:
                continue
            block_scalar_indent = None
        content = raw_line[indent:]
        parsed = mapping_line.fullmatch(content)
        if parsed is None:
            parents = tuple(value for _level, value in stack)
            if parents in required_paths[:-1]:
                _reject("PROFILE_YAML_SHAPE", path, "ambiguous effective-path syntax")
            continue
        while stack and stack[-1][0] >= indent:
            stack.pop()
        yaml_key, scalar = parsed.groups()
        parents = tuple(value for _level, value in stack)
        scalar = scalar or ""
        effective_path = (*parents, yaml_key)
        if effective_path in required_paths:
            occurrences[effective_path] = occurrences.get(effective_path, 0) + 1
            if occurrences[effective_path] != 1:
                _reject("PROFILE_YAML_SHAPE", path, "duplicate effective-path mapping")
        if yaml_key == "<<" or "<<:" in content:
            if any(
                effective_path[: len(required)] == required for required in required_paths[:-1]
            ):
                _reject("PROFILE_YAML_SHAPE", path, "merge key reaches effective path")
            continue
        if block_scalar.fullmatch(scalar):
            block_scalar_indent = indent
            continue
        is_required_parent = effective_path in required_paths[:-1]
        if is_required_parent and scalar:
            _reject("PROFILE_YAML_SHAPE", path, "effective-path parent must be one plain mapping")
        if parents == ("services", service, "environment") and yaml_key == key:
            if (
                len(scalar) < 2
                or not scalar.startswith('"')
                or not scalar.endswith('"')
                or '"' in scalar[1:-1]
                or "&" in scalar
                or "*" in scalar
                or "<<" in scalar
            ):
                _reject("PROFILE_YAML_VALUE", path, f"{key} must be a simple quoted scalar")
            matches.append(scalar[1:-1])
        if not scalar:
            stack.append((indent, yaml_key))
    if any(occurrences.get(required, 0) != 1 for required in required_paths) or len(matches) != 1:
        _reject("PROFILE_YAML_SHAPE", path, f"expected one services.{service}.environment.{key}")
    return matches[0]


def shell_forwards_force_test_v1(raw: bytes, path: str) -> bool:
    try:
        lines = [
            line.strip()
            for line in raw.decode("utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")
        ]
    except UnicodeDecodeError:
        return False
    condition = 'if [[ "${TAU_FORCE_TEST:-1}" == "1" ]]; then'
    matching = [index for index, line in enumerate(lines) if line == condition]
    if len(matching) != 1:
        return False
    index = matching[0]
    if lines[index : index + 3] != [condition, "ARGS+=(--force-test)", "fi"]:
        return False
    if sum("TAU_FORCE_TEST" in line for line in lines) != 1:
        return False
    if sum("--force-test" in line for line in lines) != 1:
        return False
    if any(
        line.startswith("ARGS=") or line.startswith("unset ARGS")
        for line in lines[index + 3 :]
    ):
        return False
    forbidden_control = re.compile(
        r"^(?:builtin|command)\s+(?:exec|exit)\b|^(?:return|break|continue)\b|"
        r"^(?:eval|(?:ba|z|da)?sh\s+-c)\b",
    )
    alias_or_function = re.compile(
        r"^(?:alias\s+[^=]+=(?:['\"])?(?:exec|exit)(?:['\"])?(?:\s|$)|"
        r"(?:function\s+)?(?:exec|exit)\s*(?:\(\)|\{)|"
        r"(?:(?:declare|export|local|readonly|typeset)\s+)?[A-Za-z_][A-Za-z0-9_]*="
        r"(?:['\"])?(?:exec|exit)(?:['\"])?(?:\s|$))",
    )
    trap = re.compile(r"^trap\b.*\b(?:DEBUG|EXIT)\b")
    if any(
        forbidden_control.search(line)
        or alias_or_function.search(line)
        or trap.search(line)
        for line in lines
    ):
        return False
    exec_lines = [
        position for position, line in enumerate(lines) if re.match(r"^exec(?:\s|$)", line)
    ]
    exit_lines = [position for position, line in enumerate(lines) if re.match(r"^exit(?:\s|$)", line)]
    missing_tau_condition = 'if [[ ! -f "$ROOT/external/tau-testnet/server.py" ]]; then'
    missing_index = next(
        (position for position, line in enumerate(lines) if line == missing_tau_condition),
        -1,
    )
    missing_end = next(
        (position for position in range(missing_index + 1, len(lines)) if lines[position] == "fi"),
        -1,
    )
    return (
        missing_index >= 0
        and missing_end > missing_index
        and exit_lines == [missing_index + 3]
        and lines[exit_lines[0]] == "exit 2"
        and exec_lines == [len(lines) - 1]
        and lines[-1] == 'exec python "${ARGS[@]}"'
    )


def python_env_default_v1(raw: bytes, path: str) -> str:
    tree = python_tree_v1(raw, path)
    function = _function_v1(tree, "_configure_tau_server_env", path)
    arguments = function.args
    positional = (*arguments.posonlyargs, *arguments.args)
    if not (
        tuple(argument.arg for argument in positional) == ("env",)
        and tuple(argument.arg for argument in arguments.kwonlyargs) == ("args", "root")
        and arguments.vararg is None
        and arguments.kwarg is None
        and not arguments.defaults
        and arguments.kw_defaults == [None, None]
    ):
        _reject("PROFILE_ENV_DEFAULT_DRIFT", path, "environment helper signature drift")
    expected = ast.parse(
        'env.setdefault("TAU_ENV", env.get("TAU_ENV", "development"))',
        mode="eval",
    ).body
    matches = [
        node
        for node in function.body
        if isinstance(node, ast.Expr)
        and ast.dump(node.value, include_attributes=False)
        == ast.dump(expected, include_attributes=False)
    ]
    match_index = next(
        (index for index, node in enumerate(function.body) if node in matches),
        -1,
    )
    tau_env_constants = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Constant)
        and type(node.value) is str
        and node.value == "TAU_ENV"
    ]
    env_mutators = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Call)
        and (
            isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == "env"
            and node.func.attr in {"clear", "pop", "popitem", "update"}
            or isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == "dict"
            and node.func.attr in {"clear", "pop", "popitem", "update"}
            and any(isinstance(argument, ast.Name) and argument.id == "env" for argument in node.args)
        )
    ]
    if (
        len(matches) != 1
        or len(tau_env_constants) != 2
        or env_mutators
        or _environment_writes_tau_env_v1(function, matches[0].value if matches else None)
        or _contains_dynamic_namespace_access_v1(function)
        or not _environment_uses_are_direct_v1(function)
        or match_index < 0
        or any(
            isinstance(node, (ast.Return, ast.Raise, ast.If, ast.For, ast.While, ast.Try, ast.With, ast.Match))
            for node in function.body[:match_index]
        )
    ):
        _reject("PROFILE_ENV_DEFAULT_DRIFT", path, "TAU_ENV helper default flow drift")
    return "development"


def _environment_uses_are_direct_v1(function: ast.FunctionDef) -> bool:
    parents = _parent_map_v1(function)
    for node in ast.walk(function):
        if not isinstance(node, ast.Name) or node.id != "env":
            continue
        parent = parents.get(node)
        if isinstance(parent, ast.Subscript) and parent.value is node:
            continue
        if (
            isinstance(parent, ast.Attribute)
            and parent.value is node
            and parent.attr in {"get", "setdefault"}
        ):
            continue
        return False
    return True


def _environment_writes_tau_env_v1(
    function: ast.FunctionDef,
    expected_default: ast.expr | None,
) -> bool:
    """Reject every direct, computed, or aliased write route to TAU_ENV."""

    expected_dump = (
        ast.dump(expected_default, include_attributes=False)
        if expected_default is not None
        else None
    )
    string_bindings: dict[str, str] = {}
    changed = True
    while changed:
        changed = False
        for candidate in ast.walk(function):
            if (
                not isinstance(candidate, ast.Assign)
                or len(candidate.targets) != 1
                or not isinstance(candidate.targets[0], ast.Name)
            ):
                continue
            value = _constant_string_v1(candidate.value)
            if value is None and isinstance(candidate.value, ast.Name):
                value = string_bindings.get(candidate.value.id)
            if value is not None and string_bindings.get(candidate.targets[0].id) != value:
                string_bindings[candidate.targets[0].id] = value
                changed = True

    def key_value(value: ast.expr) -> str | None:
        direct = _constant_string_v1(value)
        return direct if direct is not None else string_bindings.get(value.id) if isinstance(value, ast.Name) else None

    for node in ast.walk(function):
        targets: tuple[ast.AST, ...] = ()
        if isinstance(node, ast.Assign):
            targets = tuple(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = (node.target,)
        elif isinstance(node, ast.Delete):
            targets = tuple(node.targets)
        for target in targets:
            if (
                isinstance(target, ast.Subscript)
                and _expression_root_name_v1(target.value) == "env"
                and key_value(target.slice) in {None, "TAU_ENV"}
            ):
                return True
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute):
            continue
        if _expression_root_name_v1(node.func.value) != "env":
            continue
        if (
            node.func.attr == "setdefault"
            and ast.dump(node, include_attributes=False) == expected_dump
        ):
            continue
        if node.func.attr in _MUTATING_METHODS_V1:
            if not node.args:
                return True
            if key_value(node.args[0]) in {None, "TAU_ENV"}:
                return True
            if node.func.attr in {"clear", "update"}:
                return True
        if node.func.attr in {"__setitem__", "__delitem__"}:
            return True
    return False


def signing_vector_sha256_v1(fields: tuple[str, ...]) -> str:
    sample_payload = {
        "sender_pubkey": "11" * 48,
        "sequence_number": 7,
        "expiration_time": 1_700_000_000,
        "fee_limit": "10",
        "tx_type": "user_tx",
        "operations": {"5": "{}"},
    }
    payload = {key: sample_payload[key] for key in fields}
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def success_envelope_v1() -> str:
    return json.dumps(
        {"status": "ok", "command": "sendtx", "data": {"tx_hash": "aa" * 32}},
        separators=(",", ":"),
    )


def success_envelope_sha256_v1() -> str:
    return hashlib.sha256(success_envelope_v1().encode()).hexdigest()


def legacy_prefix_parser_accepts_v1(raw: bytes, response: object, path: str) -> bool:
    function = _function_v1(
        python_tree_v1(raw, path), "tau_rpc_response_is_success", path
    )
    statements = [
        node
        for node in function.body
        if not (
            isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and type(node.value.value) is str
        )
    ]
    source_shape = ast.unparse(ast.Module(body=statements, type_ignores=[]))
    required_fragments = (
        "if not isinstance(response, str):\n    return False",
        "text = response.strip().upper()",
        'text == \'SUCCESS\' or text.startswith(\'SUCCESS:\') or text.startswith(\'SUCCESS \')',
    )
    if len(statements) != 3 or any(part not in source_shape for part in required_fragments):
        _reject("LEGACY_RPC_PARSER_SHAPE", path, "legacy success parser drift")
    if type(response) is not str:
        return False
    text = response.strip().upper()
    return text == "SUCCESS" or text.startswith("SUCCESS:") or text.startswith("SUCCESS ")
