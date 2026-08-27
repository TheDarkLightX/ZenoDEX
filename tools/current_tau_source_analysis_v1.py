"""Deterministic AST and fixed-vector analyzers for Tau source replay V1."""

from __future__ import annotations

import ast
import hashlib
import json
import re
from typing import Final, NoReturn

from src.core.current_tau_compatibility_v1 import CurrentTauCompatibilityRejectV1

LEGACY_OPERATION_KEYS_V1: Final = (
    "_DEX_INTENTS_KEY",
    "_DEX_SETTLEMENT_KEY",
    "_DEX_FAUCET_KEY",
    "_PERP_OPS_KEY",
    "_TOKEN_OPS_KEY",
    "_PROOF_MINING_OPS_KEY",
    "_ZUSD_MONETARY_OPS_KEY",
)
_SAMPLE_PAYLOAD_V1: Final = {
    "sender_pubkey": "11" * 48,
    "sequence_number": 7,
    "expiration_time": 1_700_000_000,
    "fee_limit": "10",
    "tx_type": "user_tx",
    "operations": {"5": "{}"},
}


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CurrentTauCompatibilityRejectV1(code, path, detail)


def python_tree_v1(raw: bytes, path: str) -> ast.Module:
    try:
        return ast.parse(raw.decode("utf-8"), filename=path)
    except (SyntaxError, UnicodeDecodeError) as exc:
        _reject("PYTHON_SOURCE_PARSE", path, type(exc).__name__)


def _function_v1(tree: ast.Module, name: str, path: str) -> ast.FunctionDef:
    matches = [
        node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == name
    ]
    if len(matches) != 1:
        _reject("FUNCTION_SHAPE", path, f"expected one function {name}")
    return matches[0]


def literal_int_set_v1(raw: bytes, path: str, name: str) -> tuple[int, ...]:
    tree = python_tree_v1(raw, path)
    matches: list[ast.Set] = []
    writes = 0
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
            writes += 1
            if (
                isinstance(node, ast.Assign)
                and len(node.targets) == 1
                and isinstance(node.value, ast.Set)
            ):
                matches.append(node.value)
        if (
            isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and isinstance(node.value.func.value, ast.Name)
            and node.value.func.value.id == name
            and node.value.func.attr in {"add", "clear", "discard", "pop", "remove", "update"}
        ):
            writes += 1
    if len(matches) != 1 or writes != 1:
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
    for key in matches[0].keys:
        if not isinstance(key, ast.Constant) or type(key.value) is not str:
            _reject("SIGNING_DICT_KEY", path, "signing keys must be exact strings")
        keys.add(key.value)
    return keys


def _user_tx_branch_keys_v1(function: ast.FunctionDef, variable: str) -> set[str]:
    keys: set[str] = set()
    for node in function.body:
        if not isinstance(node, ast.If):
            continue
        test = node.test
        if not _is_user_tx_test_v1(test):
            continue
        for child in node.body:
            target = (
                child.targets[0]
                if isinstance(child, ast.Assign) and len(child.targets) == 1
                else None
            )
            if (
                isinstance(target, ast.Subscript)
                and isinstance(target.value, ast.Name)
                and target.value.id == variable
                and isinstance(target.slice, ast.Constant)
                and type(target.slice.value) is str
            ):
                keys.add(target.slice.value)
    return keys


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
    function = _function_v1(python_tree_v1(raw, path), function_name, path)
    top_level_returns = [
        index for index, node in enumerate(function.body) if isinstance(node, ast.Return)
    ]
    if top_level_returns != [len(function.body) - 1]:
        _reject("SIGNING_RETURN_SHAPE", path, "expected one final top-level return")
    if any(isinstance(node, ast.Delete) for node in ast.walk(function)):
        _reject("SIGNING_MUTATION_SHAPE", path, "delete is forbidden in signing projection")
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
    if len(signing_assignments) != 1 or len(user_branches) > 1:
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
    keys = _dict_assignment_keys_v1(function, "signing_dict", path)
    keys.update(_user_tx_branch_keys_v1(function, "signing_dict"))
    return tuple(sorted(keys))


def _is_signing_return_v1(value: ast.expr | None) -> bool:
    if not isinstance(value, ast.Call):
        return False
    if (
        isinstance(value.func, ast.Name)
        and value.func.id == "canonical_json_bytes"
        and len(value.args) == 1
        and isinstance(value.args[0], ast.Name)
        and value.args[0].id == "signing_dict"
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
    )


def class_methods_v1(raw: bytes, path: str, class_name: str) -> set[str]:
    tree = python_tree_v1(raw, path)
    classes = [
        node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == class_name
    ]
    if len(classes) != 1:
        _reject("CLASS_SHAPE", path, f"expected one class {class_name}")
    return {node.name for node in classes[0].body if isinstance(node, ast.FunctionDef)}


def require_success_envelope_v1(raw: bytes, path: str) -> None:
    function = _function_v1(python_tree_v1(raw, path), "success_response", path)
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
    keys = tuple(
        key.value
        for key in envelope.keys
        if isinstance(key, ast.Constant) and type(key.value) is str
    )
    status_value = envelope.values[0] if envelope.values else None
    if keys != ("status", "command", "data") or not (
        isinstance(status_value, ast.Constant) and status_value.value == "ok"
    ):
        _reject("SUCCESS_ENVELOPE_SHAPE", path, "current JSON success envelope drift")


def force_test_requires_test_env_v1(raw: bytes, path: str) -> bool:
    function = _function_v1(python_tree_v1(raw, path), "is_force_test_enabled", path)
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
        or not requested < requested_guards[0][0] < runtime_env < test_guards[0][0]
        or len(returns) != 3
        or not _body_is_single_bool_return_v1(requested_guards[0][1].body, False)
        or not _body_is_single_bool_return_v1(test_guards[0][1].body, True)
        or not isinstance(body[-1], ast.Return)
        or not isinstance(body[-1].value, ast.Constant)
        or body[-1].value.value is not False
    ):
        return False
    return True


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


def _body_is_single_bool_return_v1(body: list[ast.stmt], expected: bool) -> bool:
    return (
        len(body) == 1
        and isinstance(body[0], ast.Return)
        and isinstance(body[0].value, ast.Constant)
        and body[0].value.value is expected
    )


def historical_force_test_enters_mock_v1(raw: bytes, path: str) -> bool:
    function = _function_v1(
        python_tree_v1(raw, path),
        "start_and_manage_tau_process",
        path,
    )
    prior_return = False
    matches = 0
    for node in function.body:
        if isinstance(node, ast.Return):
            prior_return = True
        if not isinstance(node, ast.If):
            continue
        assigns_mock = any(
            isinstance(child, ast.Assign)
            and any(
                isinstance(target, ast.Name) and target.id == "tau_test_mode"
                for target in child.targets
            )
            and isinstance(child.value, ast.Constant)
            and child.value.value is True
            for child in node.body
        )
        direct_return = any(isinstance(child, ast.Return) for child in node.body)
        if assigns_mock and direct_return and _is_force_test_env_condition_v1(node.test):
            if prior_return:
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
    classes = [
        node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == "ServiceContainer"
    ]
    if len(classes) != 1:
        _reject("COMMAND_REGISTRY_CLASS", path, "expected ServiceContainer")
    builds = [
        node for node in classes[0].body if isinstance(node, ast.FunctionDef) and node.name == "build"
    ]
    if len(builds) != 1:
        _reject("COMMAND_REGISTRY_FUNCTION", path, "expected one build method")
    dictionaries: list[ast.Dict] = []
    for node in builds[0].body:
        if not (
            isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and node.targets[0].id == "command_handlers"
            and isinstance(node.value, ast.BoolOp)
            and isinstance(node.value.op, ast.Or)
            and len(node.value.values) == 2
            and isinstance(node.value.values[1], ast.Dict)
        ):
            continue
        dictionaries.append(node.value.values[1])
    if len(dictionaries) != 1:
        _reject("COMMAND_REGISTRY_SHAPE", path, "expected one reachable literal registry")
    keys: list[str] = []
    for key in dictionaries[0].keys:
        if not isinstance(key, ast.Constant) or type(key.value) is not str:
            _reject("COMMAND_REGISTRY_KEY", path, "registry keys must be exact strings")
        keys.append(key.value)
    if len(keys) != len(set(keys)):
        _reject("COMMAND_REGISTRY_DUPLICATE", path, "duplicate command key")
    return tuple(keys)


def historical_apply_app_tx_bridge_v1(raw: bytes, path: str) -> bool:
    function = _function_v1(python_tree_v1(raw, path), "_call_app_bridge", path)
    calls = [
        node
        for node in ast.walk(function)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "bridge"
        and node.func.attr == "apply_app_tx"
    ]
    if len(calls) != 1:
        return False
    for statement in function.body:
        if isinstance(statement, ast.Try):
            return any(calls[0] is child for child in ast.walk(statement))
    return False


def single_profile_value_v1(raw: bytes, path: str, key: str) -> str:
    text = raw.decode("utf-8")
    pattern = re.compile(rf'^\s+{re.escape(key)}:\s*"([^"]+)"\s*$', re.MULTILINE)
    matches = pattern.findall(text)
    if len(matches) != 1:
        _reject("PROFILE_KEY_SHAPE", path, f"expected one quoted {key} value")
    return matches[0]


def signing_vector_sha256_v1(fields: tuple[str, ...]) -> str:
    payload = {key: _SAMPLE_PAYLOAD_V1[key] for key in fields}
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def success_envelope_v1() -> str:
    return json.dumps(
        {"status": "ok", "command": "sendtx", "data": {"tx_hash": "aa" * 32}},
        separators=(",", ":"),
    )


def success_envelope_sha256_v1() -> str:
    return hashlib.sha256(success_envelope_v1().encode()).hexdigest()
