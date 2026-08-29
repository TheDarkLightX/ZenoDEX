"""Pure O-003B model for retired Tau bridge inventory and static route guards.

The immutable subject is parent commit P.  An evaluator at P or any descendant
E may replay the model without incorporating E's checker bytes into the subject.
This is bounded static evidence with no value-moving or release authority.  It
does not prove a dynamically selected Python entrypoint or route is unreachable.
"""

from __future__ import annotations

import ast
import hashlib
import json
import re
import shlex
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Final, Mapping, NoReturn, Sequence

SCHEMA_V1: Final = "zenodex/retired-tau-bridge-dependency-inventory/v1"
CHECK_SCHEMA_V1: Final = "zenodex/retired-tau-bridge-dependency-inventory-check/v1"
SUBJECT_MODEL_V1: Final = "PARENT_COMMIT_STATIC_TREE_DESCENDANT_EVALUATOR_V1"
PARENT_COMMIT_V1: Final = "59a3565b77d993a374631c2554734ce152438e15"
PARENT_TREE_V1: Final = "5391c7713a7c4d06a2ece2db64501115034f1b1b"
INVENTORY_PATH_V1: Final = Path(
    "docs/research/ZENODEX_RETIRED_TAU_BRIDGE_DEPENDENCY_INVENTORY_V1.json"
)
EVALUATOR_PATHS_V1: Final = (
    INVENTORY_PATH_V1.as_posix(),
    "tests/integration/test_retired_tau_bridge_startup_refusal_v1.py",
    "tests/test_check_retired_tau_bridge_inventory_v1.py",
    "tools/build_retired_tau_bridge_inventory_v1.py",
    "tools/check_retired_tau_bridge_inventory_v1.py",
    "tools/retired_tau_bridge_inventory_v1.py",
)

MAX_SOURCE_FILES_V1: Final = 4096
MAX_SINGLE_SOURCE_BYTES_V1: Final = 8 * 1024 * 1024
MAX_TOTAL_SOURCE_BYTES_V1: Final = 64 * 1024 * 1024
MAX_ARCHIVE_BYTES_V1: Final = MAX_TOTAL_SOURCE_BYTES_V1 + MAX_SOURCE_FILES_V1 * 2048
MAX_ARTIFACT_BYTES_V1: Final = 2 * 1024 * 1024
MAX_SEMANTIC_WORK_UNITS_V1: Final = 16_000_000
MAX_GIT_COMMANDS_V1: Final = 7
GIT_COMMAND_TIMEOUT_SECONDS_V1: Final = 30

EXPECTED_SCOPED_FILE_COUNT_V1: Final = 3731
EXPECTED_SCOPED_SOURCE_BYTES_V1: Final = 61_785_763
EXPECTED_CANDIDATE_FINGERPRINT_V1: Final = (
    "sha256:2c7c1837e125dc87aabab870ca22223b033530a574dab86a9b26817b6f97812d"
)
EXPECTED_SOURCE_SCOPE_ROOT_V1: Final = (
    "sha256:b0dbfb8c4c449b1a63ed43edd1fb7134601eea973f231e3db2e2ff01e36ebd6e"
)
EXPECTED_ARTIFACT_SHA256_V1: Final = (
    "sha256:2178b6f640c54617c19104f9a1d4802a1975e18a59f147179d764c913709d3c8"
)

CLASSIFICATIONS_V1: Final = frozenset({"QUARANTINED", "RESEARCH_ORACLE", "REMOVED"})
SCOPE_ROOTS_V1: Final = (
    ".docker",
    ".github",
    "bin",
    "config",
    "formal",
    "generated",
    "packages",
    "scripts",
    "src",
    "tests",
    "tools",
    "zk",
)
SCOPE_ROOT_FILES_V1: Final = (
    ".dockerignore",
    ".pre-commit-config.yaml",
    "Cargo.lock",
    "Cargo.toml",
    "Dockerfile",
    "Dockerfile.hashlocked",
    "Dockerfile.operator-tools",
    "Dockerfile.production-hashlocked",
    "Makefile",
    "docker-compose.apparmor.yml",
    "docker-compose.chaos.yml",
    "docker-compose.local-testnet.yml",
    "docker-compose.local.yml",
    "docker-compose.multimachine.yml",
    "docker-compose.permissionless.yml",
    "docker-compose.two-node.yml",
    "docker-compose.yml",
    "package-lock.json",
    "package.json",
    "pyproject.toml",
)
TEXT_SUFFIXES_V1: Final = frozenset(
    {
        ".command",
        ".conf",
        ".js",
        ".json",
        ".jsx",
        ".mjs",
        ".ps1",
        ".py",
        ".rs",
        ".sh",
        ".tau",
        ".toml",
        ".ts",
        ".tsx",
        ".yaml",
        ".yml",
    }
)
SCOPE_CLASSES_V1: Final = (
    "ADAPTER",
    "GENERATED",
    "LAUNCHER_MANIFEST_CONFIG",
    "PYTHON",
    "RUST",
    "SHELL",
    "TAU",
    "TEST",
    "TEXT_SOURCE",
)

RETIRED_ENVIRONMENT_V1: Final = (
    "PERPS_WALLET_API_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLED",
)
EXPECTED_ENVIRONMENT_ALIASES_V1: Final = (
    "PERPS_WALLET_API_ENABLE",
    "PERPS_WALLET_ENABLED",
    "PERPS_API_WALLET_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLE",
    "ZUSD_TAU_WALLET_ENABLED",
    "ZUSD_TAU_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLE",
    "ZUSD_MONETARY_WALLET_ENABLED",
    "ZUSD_MONETARY_API_ENABLED",
    "perps_wallet_api_enabled",
    "perps_wallet_api_enable",
    "perps_wallet_enabled",
    "perps_api_wallet_enabled",
    "zusd_tau_wallet_api_enabled",
    "zusd_tau_wallet_api_enable",
    "zusd_tau_wallet_enabled",
    "zusd_tau_api_enabled",
    "zusd_monetary_wallet_api_enabled",
    "zusd_monetary_wallet_api_enable",
    "zusd_monetary_wallet_enabled",
    "zusd_monetary_api_enabled",
)


@dataclass(frozen=True, slots=True)
class RetiredRouteSpecV1:
    environment: str
    config_field: str
    mount_field: str
    endpoint: str
    handler_method: str
    handler_module: str
    handler_name: str


ROUTE_SPECS_V1: Final = (
    RetiredRouteSpecV1(
        "PERPS_WALLET_API_ENABLED",
        "perps_wallet_enabled",
        "perps_wallet_api_enabled",
        "/api/perps/wallet/",
        "_maybe_handle_perps_wallet_api",
        "src.integration.perps_wallet_api",
        "handle_perps_wallet_request",
    ),
    RetiredRouteSpecV1(
        "ZUSD_TAU_WALLET_API_ENABLED",
        "zusd_tau_wallet_enabled",
        "zusd_tau_wallet_api_enabled",
        "/api/zusd/wallet/",
        "_maybe_handle_zusd_tau_wallet_api",
        "src.integration.zusd_tau_wallet_api",
        "handle_zusd_tau_wallet_request",
    ),
    RetiredRouteSpecV1(
        "ZUSD_MONETARY_WALLET_API_ENABLED",
        "zusd_monetary_wallet_enabled",
        "zusd_monetary_wallet_api_enabled",
        "/api/zusd/monetary/",
        "_maybe_handle_zusd_monetary_wallet_api",
        "src.integration.zusd_monetary_wallet_api",
        "handle_zusd_monetary_wallet_request",
    ),
)

API_SERVER_PATH_V1: Final = "src/integration/api_server.py"
QUARANTINE_POLICY_PATH_V1: Final = "src/integration/local_route_quarantine.py"
COMPOSE_PATH_V1: Final = "docker-compose.local-testnet.yml"
LOCAL_MANIFEST_PATH_V1: Final = "tools/zenoctl_testnet_local/manifest.py"
LOCAL_LIFECYCLE_PATH_V1: Final = "tools/zenoctl_testnet_local/lifecycle.py"
REQUIRED_CLOSURE_PATHS_V1: Final = frozenset(
    {API_SERVER_PATH_V1, QUARANTINE_POLICY_PATH_V1, COMPOSE_PATH_V1, LOCAL_MANIFEST_PATH_V1, LOCAL_LIFECYCLE_PATH_V1}
)

_MODULE_SIGNALS_V1: Final = frozenset(
    {spec.handler_module for spec in ROUTE_SPECS_V1} | {"src.integration.tau_net_client"}
)
_IDENTIFIER_SIGNALS_V1: Final = frozenset(
    set(RETIRED_ENVIRONMENT_V1)
    | {spec.config_field for spec in ROUTE_SPECS_V1}
    | {spec.mount_field for spec in ROUTE_SPECS_V1}
    | {spec.handler_name for spec in ROUTE_SPECS_V1}
)
_ENDPOINT_SIGNALS_V1: Final = tuple(spec.endpoint.rstrip("/") for spec in ROUTE_SPECS_V1)
_PREFILTER_BYTES_V1: Final = tuple(
    value.encode()
    for value in sorted(
        _MODULE_SIGNALS_V1
        | _IDENTIFIER_SIGNALS_V1
        | set(_ENDPOINT_SIGNALS_V1)
        | {module.rsplit(".", 1)[-1] for module in _MODULE_SIGNALS_V1}
        | {"/api/"}
    )
)
_MODULE_PATH_SIGNALS_V1: Final = {
    module.replace(".", "/"): module for module in _MODULE_SIGNALS_V1
}


class InventoryRejectV1(ValueError):
    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


@dataclass(frozen=True, slots=True)
class GitBindingV1:
    commit: str
    tree: str


@dataclass(frozen=True, slots=True)
class TreeEntryV1:
    path: str
    mode: str
    object_id: str
    size: int
    scope_classes: tuple[str, ...]

    def scope_row(self, source_sha256: str) -> dict[str, object]:
        return {
            "git_blob": self.object_id,
            "git_mode": self.mode,
            "path": self.path,
            "scope_classes": list(self.scope_classes),
            "sha256": source_sha256,
            "size_bytes": self.size,
        }


@dataclass(frozen=True, slots=True)
class DependencyCandidateV1:
    source_path: str
    source_sha256: str
    signals: tuple[str, ...]

    def to_row(self) -> dict[str, object]:
        return {
            # Static discovery cannot establish dynamic reachability.  Every
            # discovered source therefore remains quarantined unless a later,
            # exact non-runtime policy is added and independently evidenced.
            "classification": "QUARANTINED",
            "dependency_id": f"static-retired-bridge-reference:{self.source_path}",
            "signals": list(self.signals),
            "source_path": self.source_path,
            "source_sha256": self.source_sha256,
        }


@dataclass(frozen=True, slots=True)
class ScanResultV1:
    source_scope_root: str
    dependencies: tuple[DependencyCandidateV1, ...]
    class_counts: tuple[tuple[str, int], ...]
    file_count: int
    total_source_bytes: int
    semantic_work_units: int
    closure_sources: Mapping[str, bytes]


def reject_v1(code: str, detail: str) -> NoReturn:
    raise InventoryRejectV1(code, detail)


def sha256_prefixed_v1(raw: bytes) -> str:
    return "sha256:" + hashlib.sha256(raw).hexdigest()


def canonical_json_bytes_v1(value: object) -> bytes:
    try:
        text = json.dumps(value, allow_nan=False, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
    except (TypeError, ValueError) as exc:
        reject_v1("NONCANONICAL_VALUE", type(exc).__name__)
    return text.encode() + b"\n"


def scope_classes_v1(path: str, mode: str = "100644") -> tuple[str, ...]:
    pure = PurePosixPath(path)
    if not ((pure.parts and pure.parts[0] in SCOPE_ROOTS_V1) or path in SCOPE_ROOT_FILES_V1):
        return ()
    special = pure.name.startswith("Dockerfile") or pure.name in {".dockerignore", "Makefile"}
    executable_bin_launcher = path.startswith("bin/") and pure.suffix == "" and mode == "100755"
    if pure.suffix not in TEXT_SUFFIXES_V1 and not (special or path in SCOPE_ROOT_FILES_V1 or executable_bin_launcher):
        return ()
    classes = {"TEXT_SOURCE"}
    language = {".py": "PYTHON", ".rs": "RUST", ".sh": "SHELL", ".tau": "TAU"}.get(pure.suffix)
    if language:
        classes.add(language)
    if path.startswith("generated/"):
        classes.add("GENERATED")
    if path.startswith("tests/") or "/tests/" in path:
        classes.add("TEST")
    if path.startswith(("src/integration/", "tools/dex-ui/src/", "tools/zenoctl_testnet_local/")):
        classes.add("ADAPTER")
    if (
        path.startswith((".docker/", ".github/", "bin/", "config/", "scripts/"))
        or path in SCOPE_ROOT_FILES_V1
        or pure.name in {"Cargo.toml", "Dockerfile", "Makefile", "package.json"}
    ):
        classes.add("LAUNCHER_MANIFEST_CONFIG")
    return tuple(sorted(classes))


def _string_signals_v1(value: str) -> set[str]:
    signals: set[str] = set()
    if value in _MODULE_SIGNALS_V1:
        signals.add(f"module:{value}")
    path_value = value[:-3] if value.endswith(".py") else value
    module = _MODULE_PATH_SIGNALS_V1.get(path_value)
    if module is not None:
        signals.add(f"module:{module}")
    if value in _IDENTIFIER_SIGNALS_V1:
        signals.add(f"identifier:{value}")
    for endpoint in _ENDPOINT_SIGNALS_V1:
        if value == endpoint or value.startswith(endpoint + "/"):
            signals.add(f"endpoint:{endpoint}")
            continue
        # Playwright route globs retain the endpoint after a leading glob.  A
        # bounded literal match avoids promoting arbitrary prose containing it.
        if re.fullmatch(rf"\*{{1,2}}{re.escape(endpoint)}(?:/(?:\*{{1,2}}|[A-Za-z0-9_.-]+))*\*{{0,2}}", value):
            signals.add(f"endpoint:{endpoint}")
    return signals


def _python_string_value_v1(node: ast.expr) -> str | None:
    if isinstance(node, ast.Constant) and type(node.value) is str:
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left, right = _python_string_value_v1(node.left), _python_string_value_v1(node.right)
        return left + right if left is not None and right is not None else None
    return None


def _python_import_signals_v1(node: ast.ImportFrom, path: str) -> set[str]:
    if node.level:
        parts = PurePosixPath(path).with_suffix("").parts[:-1]
        if node.level > len(parts):
            return set()
        base = ".".join(parts[: len(parts) - node.level + 1])
        module = ".".join(part for part in (base, node.module or "") if part)
    else:
        module = node.module or ""
    candidates = {module}
    candidates.update(f"{module}.{item.name}" for item in node.names if module)
    return {f"module:{candidate}" for candidate in candidates if candidate in _MODULE_SIGNALS_V1}


def _python_signals_v1(path: str, text: str) -> tuple[set[str], int]:
    try:
        tree = ast.parse(text, filename=path)
    except (MemoryError, RecursionError, SyntaxError, ValueError) as exc:
        reject_v1("SOURCE_PARSE_FAILED", f"{path}:{type(exc).__name__}")
    signals: set[str] = set()
    nodes = tuple(ast.walk(tree))
    for node in nodes:
        if isinstance(node, ast.ImportFrom):
            signals.update(_python_import_signals_v1(node, path))
        elif isinstance(node, ast.Import):
            signals.update(f"module:{item.name}" for item in node.names if item.name in _MODULE_SIGNALS_V1)
        elif isinstance(node, ast.Name) and node.id in _IDENTIFIER_SIGNALS_V1:
            signals.add(f"identifier:{node.id}")
        elif isinstance(node, ast.Attribute) and node.attr in _IDENTIFIER_SIGNALS_V1:
            signals.add(f"identifier:{node.attr}")
        elif isinstance(node, ast.expr):
            value = _python_string_value_v1(node)
            if value is not None:
                signals.update(_string_signals_v1(value))
    return signals, len(nodes)


def _strip_hash_comments_v1(text: str) -> str:
    output: list[str] = []
    for line in text.splitlines(keepends=True):
        quote: str | None = None
        escaped = False
        for character in line:
            if escaped:
                output.append(character)
                escaped = False
                continue
            if character == "\\" and quote in {'"', "'"}:
                output.append(character)
                escaped = True
                continue
            if quote is not None:
                output.append(character)
                if character == quote:
                    quote = None
                continue
            if character in {'"', "'", "`"}:
                quote = character
                output.append(character)
            elif character == "#":
                output.append("\n" if line.endswith("\n") else "")
                break
            else:
                output.append(character)
    return "".join(output)


def _lexical_token_signals_v1(token: str) -> set[str]:
    signals = _string_signals_v1(token)
    if token.endswith(":"):
        signals.update(_string_signals_v1(token[:-1]))
    assignment = token.split("=", 1)
    if len(assignment) == 2 and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", assignment[0]):
        signals.update(_string_signals_v1(assignment[0]))
    return signals


def _lexical_signals_v1(path: str, text: str) -> set[str]:
    suffix = PurePosixPath(path).suffix
    if suffix == ".sh":
        try:
            lexer = shlex.shlex(text, posix=True)
            lexer.commenters = "#"
            lexer.whitespace_split = True
            tokens = tuple(lexer)
        except ValueError as exc:
            reject_v1("SOURCE_PARSE_FAILED", f"{path}:{type(exc).__name__}")
    else:
        if suffix in {".conf", ".ps1", ".toml", ".yaml", ".yml"} or PurePosixPath(path).name.startswith(
            "Dockerfile"
        ):
            text = _strip_hash_comments_v1(text)
        without_comments = re.sub(r"/\*.*?\*/|//[^\n]*", " ", text, flags=re.DOTALL)
        without_comments = re.sub(r"\s*::\s*", "::", without_comments)
        raw_strings = [match.group(2) for match in re.finditer(r"(['\"`])([^'\"`\n]*)\1", without_comments)]
        combined = re.findall(r"(['\"`])([^'\"`\n]*)\1\s*\+\s*(['\"`])([^'\"`\n]*)\3", without_comments)
        raw_identifiers = re.findall(r"[A-Za-z_][A-Za-z0-9_:.-]*", without_comments)
        raw_paths = re.findall(
            r"(?:[A-Za-z_][A-Za-z0-9_.-]*/)+[A-Za-z_][A-Za-z0-9_.-]*(?:\.py)?",
            without_comments,
        )
        tokens = (
            tuple(raw_strings)
            + tuple(left + right for _a, left, _b, right in combined)
            + tuple(token.replace("::", ".") for token in raw_identifiers)
            + tuple(raw_paths)
        )
    signals: set[str] = set()
    for token in tokens:
        signals.update(_lexical_token_signals_v1(token))
    return signals


def discover_source_signals_v1(path: str, raw: bytes) -> tuple[tuple[str, ...], int]:
    """Extract exact tokens; comments and containing prose do not classify."""

    rust_prefilter = tuple(token.replace(b".", b"::") for token in _PREFILTER_BYTES_V1)
    if not any(token in raw for token in _PREFILTER_BYTES_V1 + rust_prefilter):
        return (), 0
    try:
        text = raw.decode()
    except UnicodeDecodeError as exc:
        reject_v1("SOURCE_NOT_UTF8", f"{path}:{exc.start}")
    if PurePosixPath(path).suffix == ".py":
        signals, node_count = _python_signals_v1(path, text)
    else:
        signals, node_count = _lexical_signals_v1(path, text), 0
    return tuple(sorted(signals)), len(raw) + node_count


def candidate_fingerprint_v1(rows: Sequence[dict[str, object]]) -> str:
    return sha256_prefixed_v1(canonical_json_bytes_v1(list(rows)))


def _parse_python_v1(path: str, raw: bytes) -> ast.Module:
    try:
        return ast.parse(raw.decode(), filename=path)
    except (MemoryError, RecursionError, SyntaxError, UnicodeDecodeError, ValueError) as exc:
        reject_v1("ROUTE_CLOSURE_PARSE_FAILED", f"{path}:{type(exc).__name__}")


def _literal_assignment_v1(tree: ast.Module, name: str, path: str) -> object:
    values: list[ast.expr] = []
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name) and target.id == name for target in node.targets):
            values.append(node.value)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == name and node.value:
            values.append(node.value)
    if len(values) != 1:
        reject_v1("STRUCTURAL_ASSIGNMENT_MISMATCH", f"{path}:{name}")
    value = values[0]
    if isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and value.func.id == "frozenset" and len(value.args) == 1:
        value = value.args[0]
    try:
        return ast.literal_eval(value)
    except (MemoryError, RecursionError, SyntaxError, TypeError, ValueError) as exc:
        reject_v1("STRUCTURAL_ASSIGNMENT_MISMATCH", f"{path}:{name}:{type(exc).__name__}")


def _find_function_v1(body: Sequence[ast.stmt], name: str, path: str) -> ast.FunctionDef:
    matches = [node for node in body if isinstance(node, ast.FunctionDef) and node.name == name]
    if len(matches) != 1:
        reject_v1("ROUTE_CLOSURE_FUNCTION_MISMATCH", f"{path}:{name}")
    return matches[0]


def _call_name_v1(call: ast.Call) -> str | None:
    if isinstance(call.func, ast.Name):
        return call.func.id
    return call.func.attr if isinstance(call.func, ast.Attribute) else None


def _statement_call_names_v1(statement: ast.stmt) -> frozenset[str]:
    return frozenset(
        name for node in ast.walk(statement) if isinstance(node, ast.Call) for name in (_call_name_v1(node),) if name
    )


def _single_call_index_v1(body: Sequence[ast.stmt], call_name: str) -> int:
    indexes = [index for index, statement in enumerate(body) if call_name in _statement_call_names_v1(statement)]
    if len(indexes) != 1:
        reject_v1("ROUTE_CLOSURE_CALL_MISMATCH", f"{call_name}:{len(indexes)}")
    return indexes[0]


def _returns_exact_v1(statement: ast.If, value: object) -> bool:
    returns = [node for node in statement.body if isinstance(node, ast.Return)]
    return len(returns) == 1 and isinstance(returns[0].value, ast.Constant) and returns[0].value.value == value


def _assigned_value_v1(statement: ast.stmt, target_name: str) -> ast.expr | None:
    if not isinstance(statement, ast.Assign) or len(statement.targets) != 1:
        return None
    target = statement.targets[0]
    return statement.value if isinstance(target, ast.Name) and target.id == target_name else None


def _verify_policy_v1(tree: ast.Module) -> None:
    values = (
        _literal_assignment_v1(tree, "QUARANTINED_ROUTE_ENVIRONMENT_V1", QUARANTINE_POLICY_PATH_V1),
        _literal_assignment_v1(tree, "QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1", QUARANTINE_POLICY_PATH_V1),
        _literal_assignment_v1(tree, "QUARANTINED_ROUTE_ALLOWED_VALUES_V1", QUARANTINE_POLICY_PATH_V1),
    )
    expected = (RETIRED_ENVIRONMENT_V1, EXPECTED_ENVIRONMENT_ALIASES_V1, ("false", "0"))
    codes = ("QUARANTINE_ENVIRONMENT_SET_MISMATCH", "QUARANTINE_ALIAS_SET_MISMATCH", "QUARANTINE_ALLOWED_VALUES_MISMATCH")
    for actual, wanted, code in zip(values, expected, codes, strict=True):
        if actual != wanted:
            reject_v1(code, repr(actual))


def _is_environment_preflight_v1(statement: ast.stmt) -> bool:
    value = _assigned_value_v1(statement, "environment_refusals")
    if not isinstance(value, ast.Call) or _call_name_v1(value) != "quarantined_route_environment_rejections_v1":
        return False
    if len(value.args) != 1 or value.keywords or not isinstance(value.args[0], ast.Call):
        return False
    snapshot = value.args[0]
    if _call_name_v1(snapshot) != "dict" or len(snapshot.args) != 1 or snapshot.keywords:
        return False
    environment = snapshot.args[0]
    return isinstance(environment, ast.Attribute) and isinstance(environment.value, ast.Name) and (
        environment.value.id,
        environment.attr,
    ) == ("os", "environ")


def _verify_main_v1(tree: ast.Module) -> None:
    main = _find_function_v1(tree.body, "main", API_SERVER_PATH_V1)
    calls = (
        "quarantined_route_environment_rejections_v1",
        "_load_api_server_config",
        "_api_startup_refusal_lines",
        "_prewarm_api_modules",
        "ThreadingHTTPServer",
        "_attach_api_server_state",
        "serve_forever",
    )
    indexes = tuple(_single_call_index_v1(main.body, name) for name in calls)
    if indexes != tuple(sorted(indexes)) or len(set(indexes)) != len(indexes):
        reject_v1("STARTUP_GUARD_ORDER_MISMATCH", repr(indexes))
    environment, config, refusal = indexes[:3]
    if config != environment + 2 or not _is_environment_preflight_v1(main.body[environment]):
        reject_v1("STARTUP_ENVIRONMENT_REFUSAL_MISMATCH", repr(indexes[:2]))
    environment_if = main.body[environment + 1]
    if not isinstance(environment_if, ast.If) or not isinstance(environment_if.test, ast.Name) or (
        environment_if.test.id != "environment_refusals" or not _returns_exact_v1(environment_if, 2)
    ):
        reject_v1("STARTUP_ENVIRONMENT_REFUSAL_MISMATCH", "return")
    config_value = _assigned_value_v1(main.body[config], "config")
    refusal_value = _assigned_value_v1(main.body[refusal], "refusal")
    if not isinstance(config_value, ast.Call) or _call_name_v1(config_value) != "_load_api_server_config" or refusal_value is None:
        reject_v1("STARTUP_CONFIG_REFUSAL_MISMATCH", "binding")
    refusal_if = main.body[refusal + 1] if refusal + 1 < len(main.body) else None
    if not isinstance(refusal_if, ast.If) or not isinstance(refusal_if.test, ast.Compare) or (
        not isinstance(refusal_if.test.left, ast.Name) or refusal_if.test.left.id != "refusal" or not _returns_exact_v1(refusal_if, 2)
    ):
        reject_v1("STARTUP_CONFIG_REFUSAL_MISMATCH", "return")


def _path_guard_v1(statement: ast.stmt, spec: RetiredRouteSpecV1) -> bool:
    if not isinstance(statement, ast.If) or not _returns_exact_v1(statement, False):
        return False
    test = statement.test
    if not isinstance(test, ast.UnaryOp) or not isinstance(test.op, ast.Not) or not isinstance(test.operand, ast.Call):
        return False
    call = test.operand
    return len(call.args) == 1 and not call.keywords and isinstance(call.func, ast.Attribute) and (
        call.func.attr == "startswith"
        and isinstance(call.func.value, ast.Name)
        and call.func.value.id == "path"
        and isinstance(call.args[0], ast.Constant)
        and call.args[0].value == spec.endpoint
    )


def _mount_guard_v1(statement: ast.stmt, spec: RetiredRouteSpecV1) -> bool:
    if not isinstance(statement, ast.If) or not _returns_exact_v1(statement, False):
        return False
    test = statement.test
    if not isinstance(test, ast.UnaryOp) or not isinstance(test.op, ast.Not) or not isinstance(test.operand, ast.Call):
        return False
    call = test.operand
    if _call_name_v1(call) != "getattr" or len(call.args) != 3 or call.keywords:
        return False
    server, field, default = call.args
    return isinstance(server, ast.Attribute) and isinstance(server.value, ast.Name) and (
        server.value.id == "self"
        and server.attr == "server"
        and isinstance(field, ast.Constant)
        and field.value == spec.mount_field
        and isinstance(default, ast.Constant)
        and default.value is False
    )


def _verify_mounts_v1(tree: ast.Module) -> None:
    attach = _find_function_v1(tree.body, "_attach_api_server_state", API_SERVER_PATH_V1)
    guard_index = _single_call_index_v1(attach.body, "refuse_current_local_operator_operation_v1")
    for spec in ROUTE_SPECS_V1:
        assignments = [
            (index, statement.value)
            for index, statement in enumerate(attach.body)
            if isinstance(statement, ast.Assign)
            and any(isinstance(target, ast.Attribute) and target.attr == spec.mount_field for target in statement.targets)
        ]
        if len(assignments) != 1:
            reject_v1("MOUNT_ASSIGNMENT_MISMATCH", spec.mount_field)
        index, value = assignments[0]
        if index <= guard_index or not isinstance(value, ast.Constant) or value.value is not False:
            reject_v1("MOUNT_NOT_HARD_DISABLED", spec.mount_field)


def _verify_handlers_v1(tree: ast.Module) -> None:
    classes = [node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == "_Handler"]
    if len(classes) != 1:
        reject_v1("ROUTE_HANDLER_CLASS_MISMATCH", API_SERVER_PATH_V1)
    for spec in ROUTE_SPECS_V1:
        method = _find_function_v1(classes[0].body, spec.handler_method, API_SERVER_PATH_V1)
        if len(method.body) < 3 or not _path_guard_v1(method.body[0], spec):
            reject_v1("ROUTE_PATH_GUARD_MISMATCH", spec.handler_method)
        if not _mount_guard_v1(method.body[1], spec):
            reject_v1("ROUTE_MOUNT_GUARD_MISMATCH", spec.handler_method)
        imports = [
            (index, node)
            for index, node in enumerate(method.body)
            if isinstance(node, ast.ImportFrom) and node.module == spec.handler_module
        ]
        if len(imports) != 1 or imports[0][0] <= 1 or [item.name for item in imports[0][1].names] != [spec.handler_name]:
            reject_v1("ROUTE_HANDLER_IMPORT_MISMATCH", spec.handler_method)
        later = method.body[imports[0][0] + 1 :]
        calls = [node for statement in later for node in ast.walk(statement) if isinstance(node, ast.Call) and _call_name_v1(node) == spec.handler_name]
        if len(calls) != 1:
            reject_v1("ROUTE_HANDLER_CALL_MISMATCH", spec.handler_method)


def _yaml_scalars_v1(text: str) -> dict[tuple[str, ...], str]:
    values: dict[tuple[str, ...], str] = {}
    stack: list[tuple[int, str]] = []
    for raw_line in text.splitlines():
        if not raw_line.strip() or raw_line.lstrip().startswith("#") or "\t" in raw_line:
            continue
        indent = len(raw_line) - len(raw_line.lstrip())
        matched = re.fullmatch(r"([A-Za-z0-9_.-]+):(?:\s*(.*))?", raw_line.strip())
        if matched is None:
            continue
        key, raw_value = matched.groups()
        while stack and indent <= stack[-1][0]:
            stack.pop()
        path = tuple(name for _depth, name in stack) + (key,)
        value = raw_value or ""
        if not value:
            stack.append((indent, key))
        else:
            values[path] = value[1:-1] if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"" else value
    return values


def _verify_launchers_v1(sources: Mapping[str, bytes]) -> None:
    compose = _yaml_scalars_v1(sources[COMPOSE_PATH_V1].decode())
    for environment in RETIRED_ENVIRONMENT_V1:
        if compose.get(("services", "zenodex-api", "environment", environment)) != "false":
            reject_v1("COMPOSE_ROUTE_NOT_DISABLED", environment)
    manifest = _parse_python_v1(LOCAL_MANIFEST_PATH_V1, sources[LOCAL_MANIFEST_PATH_V1])
    mountable = _literal_assignment_v1(manifest, "LOCAL_TESTNET_MOUNTABLE_LANES", LOCAL_MANIFEST_PATH_V1)
    if mountable != ("DEX_API_ENABLED", "CONFIDENTIAL_ATTESTATION_API_ENABLED"):
        reject_v1("LOCAL_MOUNTABLE_LANES_MISMATCH", repr(mountable))
    lifecycle = _parse_python_v1(LOCAL_LIFECYCLE_PATH_V1, sources[LOCAL_LIFECYCLE_PATH_V1])
    values = [
        node.value
        for node in lifecycle.body
        if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name) and target.id == "LOCAL_TESTNET_ENABLED_LANES" for target in node.targets)
    ]
    if len(values) != 1 or not isinstance(values[0], ast.Attribute) or not isinstance(values[0].value, ast.Name) or (
        values[0].value.id,
        values[0].attr,
    ) != ("mf", "LOCAL_TESTNET_MOUNTABLE_LANES"):
        reject_v1("LOCAL_ENABLED_LANES_BINDING_MISMATCH", LOCAL_LIFECYCLE_PATH_V1)


def verify_route_static_guards_v1(sources: Mapping[str, bytes]) -> tuple[str, ...]:
    if type(sources) is not dict or set(sources) != REQUIRED_CLOSURE_PATHS_V1:
        reject_v1("ROUTE_CLOSURE_SOURCE_SET_MISMATCH", str(len(sources)))
    policy = _parse_python_v1(QUARANTINE_POLICY_PATH_V1, sources[QUARANTINE_POLICY_PATH_V1])
    api = _parse_python_v1(API_SERVER_PATH_V1, sources[API_SERVER_PATH_V1])
    _verify_policy_v1(policy)
    _verify_main_v1(api)
    _verify_mounts_v1(api)
    _verify_handlers_v1(api)
    _verify_launchers_v1(sources)
    return (
        "API_MAIN_ENVIRONMENT_PREFLIGHT_BEFORE_IO",
        "API_MAIN_CONFIG_REFUSAL_BEFORE_PREWARM_AND_SERVER",
        "API_SERVER_MOUNTS_HARD_DISABLED",
        "HANDLER_PATH_AND_MOUNT_GUARDS_PRECEDE_RETIRED_IMPORTS",
        "LOCAL_COMPOSE_RETIRED_ENVIRONMENT_EXACT_FALSE",
        "LOCAL_MANIFEST_EXCLUDES_RETIRED_LANES",
        "LOCAL_LIFECYCLE_DERIVES_ONLY_MOUNTABLE_LANES",
        "QUARANTINE_CANONICAL_ALIAS_AND_ALLOWED_VALUE_SETS_EXACT",
    )


MUTATION_CASES_V1: Final = (
    ("MUTANT_API_MOUNT_FROM_CONFIG", "expected_rejection", "MOUNT_NOT_HARD_DISABLED"),
    ("MUTANT_STARTUP_GUARD_AFTER_SERVER", "expected_rejection", "STARTUP_GUARD_ORDER_MISMATCH"),
    ("MUTANT_STARTUP_GUARD_READS_EMPTY_MAPPING", "expected_rejection", "STARTUP_ENVIRONMENT_REFUSAL_MISMATCH"),
    ("MUTANT_ROUTE_PATH_USES_ENDSWITH", "expected_rejection", "ROUTE_PATH_GUARD_MISMATCH"),
    ("MUTANT_ROUTE_MOUNT_DEFAULTS_TRUE", "expected_rejection", "ROUTE_MOUNT_GUARD_MISMATCH"),
    ("MUTANT_LOCAL_COMPOSE_REENABLES_ROUTE", "expected_rejection", "COMPOSE_ROUTE_NOT_DISABLED"),
    ("MUTANT_LOCAL_MANIFEST_MOUNTS_RETIRED_LANE", "expected_rejection", "LOCAL_MOUNTABLE_LANES_MISMATCH"),
    ("MUTANT_UNSCANNED_RUST_REFERENCE", "expected_observation", "module:src.integration.perps_wallet_api"),
    ("MUTANT_COMMENT_ONLY_REFERENCE", "expected_observation", "NO_DEPENDENCY"),
    ("MUTANT_GLOBALS_MAIN_OVERRIDE", "expected_observation", "STATIC_GUARDS_SURVIVE_DYNAMIC_OVERRIDE"),
)
NONCLAIMS_V1: Final = (
    "O_003B_NOT_CLOSED",
    "NO_DYNAMIC_REACHABILITY_PROOF",
    "NO_DYNAMIC_ENTRYPOINT_BINDING_PROOF",
    "NO_STATIC_GRAMMAR_COMPLETENESS_PROOF",
    "NO_DEPENDENCY_INVENTORY_COMPLETENESS_PROOF",
    "NO_OPERATION_DERIVED_DEPENDENCY_COMPLETENESS_PROOF",
    "NO_GIT_EXECUTABLE_INTEGRITY_PROOF",
    "NO_SELF_BOOTSTRAP_INTEGRITY_PROOF",
    "NO_HOST_RUNTIME_INTEGRITY_PROOF",
    "NO_ESCAPE_RESISTANT_PROCESS_CONTAINMENT",
    "NO_PRODUCTION_AUTHORITY",
    "NO_RELEASE_AUTHORITY",
    "NO_SETTLEMENT_AUTHORITY",
    "NO_VALUE_MOVEMENT_AUTHORITY",
    "NO_VM_GATE_CLOSURE",
    "NO_SUCCESSOR_SOURCE_COVERAGE_BEYOND_PINNED_PARENT",
)


def build_inventory_payload_v1(binding: GitBindingV1, scan: ScanResultV1) -> dict[str, object]:
    dependency_rows = [candidate.to_row() for candidate in scan.dependencies]
    fingerprint = candidate_fingerprint_v1(dependency_rows)
    if EXPECTED_CANDIDATE_FINGERPRINT_V1 != "UNSET" and fingerprint != EXPECTED_CANDIDATE_FINGERPRINT_V1:
        reject_v1("CANDIDATE_FINGERPRINT_MISMATCH", fingerprint)
    if EXPECTED_SOURCE_SCOPE_ROOT_V1 != "UNSET" and scan.source_scope_root != EXPECTED_SOURCE_SCOPE_ROOT_V1:
        reject_v1("SOURCE_SCOPE_ROOT_MISMATCH", scan.source_scope_root)
    class_counts = dict(scan.class_counts)
    if any(class_counts.get(name, 0) <= 0 for name in SCOPE_CLASSES_V1):
        reject_v1("EMPTY_REQUIRED_SCOPE_CLASS", repr(class_counts))
    checks = verify_route_static_guards_v1(scan.closure_sources)
    return {
        "authority": {"production": "NONE", "release": "NONE", "settlement": "NONE", "value_movement": "NONE"},
        "candidate_fingerprint": fingerprint,
        "dependencies": dependency_rows,
        "inventory_subject": {
            "evaluator_head_requirement": "DESCENDANT_OR_EQUAL_TO_PARENT",
            "git_parent_commit": binding.commit,
            "git_parent_tree": binding.tree,
            "model": SUBJECT_MODEL_V1,
            "source_origin": "GIT_BLOBS_AT_PARENT_COMMIT",
        },
        "mutation_cases": [
            {"case_id": case_id, result_key: result_value}
            for case_id, result_key, result_value in MUTATION_CASES_V1
        ],
        "nonclaims": list(NONCLAIMS_V1),
        "route_static_guard_evidence": {
            "checks": list(checks),
            "dynamic_reachability": "NOT_PROVEN",
            "result": "BOUNDED_STATIC_GUARDS_ONLY",
        },
        "schema": SCHEMA_V1,
        "scope_contract": {
            "budgets": {
                "cpu_semantic_work_units": MAX_SEMANTIC_WORK_UNITS_V1,
                "disk_artifact_bytes": MAX_ARTIFACT_BYTES_V1,
                "file_count": MAX_SOURCE_FILES_V1,
                "git_command_count_max": MAX_GIT_COMMANDS_V1,
                "single_source_bytes": MAX_SINGLE_SOURCE_BYTES_V1,
                "time_seconds_per_git_command": GIT_COMMAND_TIMEOUT_SECONDS_V1,
                "total_source_bytes": MAX_TOTAL_SOURCE_BYTES_V1,
            },
            "root_files": list(SCOPE_ROOT_FILES_V1),
            "roots": list(SCOPE_ROOTS_V1),
            "scope_classes": list(SCOPE_CLASSES_V1),
            "text_suffixes": sorted(TEXT_SUFFIXES_V1),
        },
        "scope_summary": {
            "class_file_counts": class_counts,
            "dependency_file_count": len(dependency_rows),
            "scanned_file_count": scan.file_count,
            "semantic_work_units": scan.semantic_work_units,
            "source_file_count": scan.file_count,
            "total_source_bytes": scan.total_source_bytes,
        },
        "source_scope_root": scan.source_scope_root,
        "startup_refusal_evidence": {
            "replay": "TMPDIR=/dev/shm PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -p no:cacheprovider -q tests/integration/test_retired_tau_bridge_startup_refusal_v1.py",
            "test_path": "tests/integration/test_retired_tau_bridge_startup_refusal_v1.py",
        },
        "status": "RESEARCH_ONLY_NO_PROMOTION",
        "vm_gates_closed": [],
    }
