"""Closed, source-bound O-004 operator-surface registry.

The registry records which local-profile routes have positive liveness
references and which retired routes have refusal references.  It binds those
claims to one exact Git subject and grants no runtime, release, settlement, or
value-moving authority.
"""

from __future__ import annotations

import ast
import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Final, NoReturn, cast

import yaml

SCHEMA_V2: Final = "zenodex/operator-surface-registry/v2"
CHECK_SCHEMA_V2: Final = "zenodex/operator-surface-registry-check/v2"
ARTIFACT_RELATIVE_PATH_V2: Final = Path("docs/research/ZENODEX_OPERATOR_SURFACE_REGISTRY_V2.json")
SOURCE_PATHS_V2: Final = (
    "docker-compose.local-testnet.yml",
    "tests/integration/test_api_server_confidential.py",
    "tests/integration/test_dex_ui_live_bridge.py",
    "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py",
    "tests/test_check_operator_surface_registry_v2.py",
    "tests/test_operator_surface_registry_semantic_mutants_v2.py",
    "tests/test_zenodex_oracle_mvp_completion_audit.py",
    "tools/__init__.py",
    "tools/build_operator_surface_registry_v2.py",
    "tools/check_operator_surface_registry_v2.py",
    "tools/dex-ui/public/zenodex-config.json",
    "tools/dex-ui/src/App.jsx",
    "tools/operator_surface_registry_v2.py",
)
ROUTE_IDS_V2: Final = (
    "spot_ledger_api",
    "oracle_api",
    "confidential_attestation_api",
    "perps_wallet_stream_8",
    "zusd_tau_wallet_stream_9",
    "zusd_monetary_wallet_stream_11",
    "autotrader_api",
)
NO_AUTHORITY_V2: Final = {
    "mount": "NONE",
    "production": "NONE",
    "release": "NONE",
    "settlement": "NONE",
    "value_movement": "NONE",
}

MAX_JSON_BYTES_V2: Final = 524_288
MAX_JSON_DEPTH_V2: Final = 32
MAX_JSON_NODES_V2: Final = 32_768
MAX_SOURCE_BYTES_V2: Final = 4_194_304
MAX_GIT_OUTPUT_BYTES_V2: Final = 8_388_608
MAX_AST_NODES_V2: Final = 500_000
MAX_JS_TOKENS_V2: Final = 300_000
GIT_TIMEOUT_SECONDS_V2: Final = 15
_HEX_40_V2 = re.compile(r"[0-9a-f]{40}\Z")
_HEX_64_V2 = re.compile(r"[0-9a-f]{64}\Z")


@dataclass(frozen=True)
class OperatorSurfaceRegistryRejectV2(ValueError):
    """Stable fail-closed rejection at an untrusted boundary."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


@dataclass(frozen=True)
class _JsTokenV2:
    kind: str
    value: str


def _reject_v2(code: str, path: str, detail: str) -> NoReturn:
    raise OperatorSurfaceRegistryRejectV2(code, path, detail)


def sha256_hex_v2(raw: bytes) -> str:
    if type(raw) is not bytes:
        _reject_v2("BYTES_TYPE", "sha256", "input must be exact bytes")
    return hashlib.sha256(raw).hexdigest()


def _validate_json_value_v2(
    value: object,
    *,
    depth: int = 0,
    counter: list[int] | None = None,
) -> None:
    if depth > MAX_JSON_DEPTH_V2:
        _reject_v2("JSON_DEPTH", "json", "maximum depth exceeded")
    seen = counter if counter is not None else [0]
    seen[0] += 1
    if seen[0] > MAX_JSON_NODES_V2:
        _reject_v2("JSON_NODE_LIMIT", "json", "maximum node count exceeded")
    if value is None or type(value) in {bool, int, str}:
        return
    if type(value) is list:
        for item in value:
            _validate_json_value_v2(item, depth=depth + 1, counter=seen)
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                _reject_v2("JSON_KEY_TYPE", "json", "keys must be exact strings")
            _validate_json_value_v2(item, depth=depth + 1, counter=seen)
        return
    _reject_v2("JSON_VALUE_TYPE", "json", type(value).__name__)


def canonical_json_bytes_v2(value: object) -> bytes:
    _validate_json_value_v2(value)
    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def decode_json_object_v2(raw: bytes, label: str) -> dict[str, object]:
    if type(raw) is not bytes:
        _reject_v2("JSON_BYTES_TYPE", label, "input must be exact bytes")
    if len(raw) > MAX_JSON_BYTES_V2:
        _reject_v2("JSON_SIZE", label, "input exceeds the fixed byte limit")

    def reject_float(_value: str) -> NoReturn:
        _reject_v2("JSON_FLOAT", label, "floating point is forbidden")

    def parse_integer(value: str) -> int:
        if len(value.lstrip("-")) > 256:
            _reject_v2("JSON_INTEGER_LIMIT", label, "integer is too large")
        return int(value)

    def exact_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                _reject_v2("JSON_DUPLICATE_KEY", label, key)
            result[key] = value
        return result

    try:
        decoded = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=exact_object,
            parse_constant=reject_float,
            parse_float=reject_float,
            parse_int=parse_integer,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject_v2("JSON_DECODE", label, type(exc).__name__)
    if type(decoded) is not dict:
        _reject_v2("JSON_ROOT_TYPE", label, "root must be an object")
    _validate_json_value_v2(decoded)
    return cast(dict[str, object], decoded)


def project_ui_config_v2(raw: bytes) -> dict[str, object]:
    value = decode_json_object_v2(raw, "tools/dex-ui/public/zenodex-config.json")
    expected = {
        "perpsWalletUiEnabled": False,
        "zusdTauWalletUiEnabled": False,
        "zusdMonetaryWalletUiEnabled": False,
    }
    observed = {key: value.get(key) for key in expected}
    if observed != expected or any(type(observed[key]) is not bool for key in expected):
        _reject_v2(
            "UI_CONFIG_ROUTE_FLAGS",
            "tools/dex-ui/public/zenodex-config.json",
            "retired value-route flags must be exact false Booleans",
        )
    return {"value_route_flags": expected}


def _reject_duplicate_yaml_keys_v2(node: yaml.nodes.Node, path: str) -> None:
    if isinstance(node, yaml.nodes.MappingNode):
        seen: set[str] = set()
        for key_node, value_node in node.value:
            if isinstance(key_node, yaml.nodes.ScalarNode) and key_node.value != "<<":
                if key_node.value in seen:
                    _reject_v2("YAML_DUPLICATE_KEY", path, key_node.value)
                seen.add(key_node.value)
            _reject_duplicate_yaml_keys_v2(value_node, path)
    elif isinstance(node, yaml.nodes.SequenceNode):
        for child in node.value:
            _reject_duplicate_yaml_keys_v2(child, path)


def _exact_mapping_v2(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict or any(type(key) is not str for key in value):
        _reject_v2("MAPPING_TYPE", path, "must be an exact string-keyed object")
    return cast(dict[str, object], value)


def project_compose_v2(raw: bytes) -> dict[str, object]:
    path = "docker-compose.local-testnet.yml"
    if type(raw) is not bytes or len(raw) > MAX_SOURCE_BYTES_V2:
        _reject_v2("SOURCE_SIZE", path, "source exceeds the fixed byte limit")
    try:
        text = raw.decode("utf-8")
        node = yaml.compose(text, Loader=yaml.SafeLoader)
        if node is None:
            _reject_v2("YAML_PARSE", path, "empty document")
        _reject_duplicate_yaml_keys_v2(node, path)
        loaded = yaml.safe_load(text)
    except (UnicodeDecodeError, yaml.YAMLError) as exc:
        _reject_v2("YAML_PARSE", path, type(exc).__name__)
    root = _exact_mapping_v2(loaded, path)
    services = _exact_mapping_v2(root.get("services"), f"{path}.services")
    api = _exact_mapping_v2(services.get("zenodex-api"), f"{path}.services.zenodex-api")
    environment = _exact_mapping_v2(
        api.get("environment"), f"{path}.services.zenodex-api.environment"
    )
    expected = {
        "AUTOTRADER_LIVE_API_ENABLED": "false",
        "CONFIDENTIAL_ATTESTATION_API_ENABLED": "true",
        "DEX_API_ENABLED": "true",
        "PERPS_WALLET_API_ENABLED": "false",
        "ZUSD_MONETARY_WALLET_API_ENABLED": "false",
        "ZUSD_TAU_WALLET_API_ENABLED": "false",
    }
    if {key: environment.get(key) for key in expected} != expected:
        _reject_v2("COMPOSE_ROUTE_ENVIRONMENT", path, "route environment drift")
    if type(services.get("zenodex-oracle")) is not dict:
        _reject_v2("COMPOSE_ORACLE_SERVICE", path, "oracle service is absent")
    return {"route_environment": expected, "zenodex_oracle_service_declared": True}


def _tokenize_js_v2(raw: bytes, path: str) -> tuple[_JsTokenV2, ...]:
    if type(raw) is not bytes or len(raw) > MAX_SOURCE_BYTES_V2:
        _reject_v2("SOURCE_SIZE", path, "source exceeds the fixed byte limit")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        _reject_v2("JS_UTF8", path, "source must be UTF-8")
    tokens: list[_JsTokenV2] = []
    index = 0
    operators = ("===", "!==", "=>", "...", "?.", "&&", "||", "==", "!=", "<=", ">=")
    while index < len(text):
        character = text[index]
        if character.isspace():
            index += 1
            continue
        if text.startswith("//", index):
            newline = text.find("\n", index + 2)
            index = len(text) if newline < 0 else newline + 1
            continue
        if text.startswith("/*", index):
            closing = text.find("*/", index + 2)
            if closing < 0:
                _reject_v2("JS_COMMENT", path, "unterminated block comment")
            index = closing + 2
            continue
        if character in {"'", '"', "`"}:
            quote = character
            start = index
            index += 1
            escaped = False
            while index < len(text):
                current = text[index]
                index += 1
                if escaped:
                    escaped = False
                elif current == "\\":
                    escaped = True
                elif current == quote:
                    break
            else:
                _reject_v2("JS_STRING", path, "unterminated string")
            tokens.append(_JsTokenV2("string", text[start:index]))
        elif character.isalpha() or character in {"_", "$"}:
            start = index
            index += 1
            while index < len(text) and (text[index].isalnum() or text[index] in {"_", "$"}):
                index += 1
            tokens.append(_JsTokenV2("identifier", text[start:index]))
        elif character.isdigit():
            start = index
            index += 1
            while index < len(text) and (text[index].isalnum() or text[index] in {"_", "."}):
                index += 1
            tokens.append(_JsTokenV2("number", text[start:index]))
        else:
            operator = next(
                (candidate for candidate in operators if text.startswith(candidate, index)),
                character,
            )
            tokens.append(_JsTokenV2("punctuation", operator))
            index += len(operator)
        if len(tokens) > MAX_JS_TOKENS_V2:
            _reject_v2("JS_TOKEN_LIMIT", path, "token count exceeds the fixed limit")
    return tuple(tokens)


def _matching_token_v2(
    tokens: tuple[_JsTokenV2, ...], opening_index: int, opening: str, closing: str, path: str
) -> int:
    if opening_index >= len(tokens) or tokens[opening_index].value != opening:
        _reject_v2("JS_STRUCTURE", path, f"expected {opening}")
    depth = 0
    for index in range(opening_index, len(tokens)):
        value = tokens[index].value
        if value == opening:
            depth += 1
        elif value == closing:
            depth -= 1
            if depth == 0:
                return index
    _reject_v2("JS_STRUCTURE", path, f"unclosed {opening}")


def _declaration_v2(tokens: tuple[_JsTokenV2, ...], prefix: tuple[str, ...], path: str) -> int:
    values = tuple(token.value for token in tokens)
    matches = [
        index
        for index in range(len(values) - len(prefix) + 1)
        if values[index : index + len(prefix)] == prefix
    ]
    if len(matches) != 1:
        _reject_v2("JS_DECLARATION", path, f"expected one declaration {prefix}")
    return matches[0]


def _simple_js_string_v2(token: _JsTokenV2, path: str) -> str:
    if token.kind != "string" or token.value[0] not in {"'", '"'} or "\\" in token.value:
        _reject_v2("JS_SIMPLE_STRING", path, "expected a simple quoted string")
    return token.value[1:-1]


def _parse_importers_v2(tokens: tuple[_JsTokenV2, ...], opening: int, path: str) -> dict[str, str]:
    closing = _matching_token_v2(tokens, opening, "{", "}", path)
    index = opening + 1
    result: dict[str, str] = {}
    while index < closing:
        if index + 8 >= closing:
            _reject_v2("JS_NAV_IMPORTER_SET", path, "truncated importer")
        row = tuple(token.value for token in tokens[index : index + 9])
        key = tokens[index]
        if (
            key.kind != "identifier"
            or row[1:8] != (":", "(", ")", "=>", "import", "(", row[7])
            or tokens[index + 7].kind != "string"
            or row[8] != ")"
            or key.value in result
        ):
            _reject_v2("JS_NAV_IMPORTER_SET", path, "importer shape drift")
        result[key.value] = _simple_js_string_v2(tokens[index + 7], path)
        index += 9
        if index < closing:
            if tokens[index].value != ",":
                _reject_v2("JS_NAV_IMPORTER_SET", path, "missing importer separator")
            index += 1
    return result


def _parse_nav_tabs_v2(
    tokens: tuple[_JsTokenV2, ...], opening: int, path: str
) -> list[dict[str, str]]:
    closing = _matching_token_v2(tokens, opening, "[", "]", path)
    index = opening + 1
    result: list[dict[str, str]] = []
    seen: set[str] = set()
    while index < closing:
        if tokens[index].value != "{":
            _reject_v2("JS_NAV_TABS", path, "tab row must be an object")
        row_close = _matching_token_v2(tokens, index, "{", "}", path)
        row = tokens[index + 1 : row_close]
        values = tuple(token.value for token in row)
        if len(values) != 7 or values[0:2] != ("id", ":") or values[3:6] != (",", "label", ":"):
            _reject_v2("JS_NAV_TABS", path, "tab row shape drift")
        tab_id = _simple_js_string_v2(row[2], path)
        label = _simple_js_string_v2(row[6], path)
        if tab_id in seen:
            _reject_v2("JS_NAV_TABS", path, f"duplicate tab {tab_id}")
        seen.add(tab_id)
        result.append({"id": tab_id, "label": label})
        index = row_close + 1
        if index < closing:
            if tokens[index].value != ",":
                _reject_v2("JS_NAV_TABS", path, "missing tab separator")
            index += 1
    return result


def project_app_navigation_v2(raw: bytes) -> dict[str, object]:
    path = "tools/dex-ui/src/App.jsx"
    tokens = _tokenize_js_v2(raw, path)
    importer_start = _declaration_v2(tokens, ("const", "SURFACE_IMPORTERS", "="), path)
    importers = _parse_importers_v2(tokens, importer_start + 3, path)
    expected_importers = {
        "swap": "./components/SwapInterface",
        "pools": "./components/PoolDashboard",
        "stats": "./components/TokenStats",
        "perps": "./components/perps/PerpTradingView",
        "strategy": "./components/StrategyWorkbench.jsx",
        "zusd": "./components/ZUSDWorkbench.jsx",
        "oracle": "./components/ZenoOracleDashboard.jsx",
        "confidential": "./components/ConfidentialWorkbench.jsx",
        "governance": "./components/PerpsGovernanceSurface.jsx",
        "proofs": "./components/ProofMiningWorkbench.jsx",
    }
    if importers != expected_importers:
        _reject_v2("JS_NAV_IMPORTER_SET", path, "surface importer set drift")

    tabs_start = _declaration_v2(tokens, ("const", "NAV_TABS", "="), path)
    tabs = _parse_nav_tabs_v2(tokens, tabs_start + 3, path)
    expected_tabs = [
        {"id": "swap", "label": "Swap"},
        {"id": "pools", "label": "Pools"},
        {"id": "stats", "label": "ZDEX Stats"},
        {"id": "perps", "label": "Perpetuals"},
        {"id": "strategy", "label": "Strategy"},
        {"id": "zusd", "label": "zUSD"},
        {"id": "oracle", "label": "Oracle"},
        {"id": "confidential", "label": "Confidential"},
        {"id": "governance", "label": "Keys"},
    ]
    if tabs != expected_tabs:
        _reject_v2("JS_NAV_TABS", path, "navigation denominator drift")

    route_start = _declaration_v2(tokens, ("const", "ROUTE_TAB_IDS", "="), path)
    route_values = tuple(token.value for token in tokens[route_start : route_start + 24])
    expected_route_values = (
        "const",
        "ROUTE_TAB_IDS",
        "=",
        "new",
        "Set",
        "(",
        "[",
        "...",
        "NAV_TABS",
        ".",
        "map",
        "(",
        "(",
        "tab",
        ")",
        "=>",
        "tab",
        ".",
        "id",
        ")",
        ",",
        "'proofs'",
        "]",
        ")",
    )
    if route_values != expected_route_values:
        _reject_v2("JS_ROUTE_TAB_SET", path, "hidden route declaration drift")

    values = tuple(token.value for token in tokens)
    render_ids: list[str] = []
    for index in range(len(values) - 5):
        if (
            values[index] == "{"
            and values[index + 1 : index + 4] == ("activeTab", "===", values[index + 3])
            and tokens[index + 3].kind == "string"
            and values[index + 4 : index + 6] == ("&&", "(")
        ):
            render_ids.append(_simple_js_string_v2(tokens[index + 3], path))
    expected_render_ids = [
        "swap",
        "pools",
        "stats",
        "perps",
        "strategy",
        "zusd",
        "oracle",
        "confidential",
        "proofs",
        "governance",
    ]
    if render_ids != expected_render_ids:
        _reject_v2("JS_NAV_RENDER_SET", path, "render branch set or order drift")
    return {
        "importers": importers,
        "navigation_tabs": tabs,
        "render_ids": render_ids,
        "hidden_route_ids": ["proofs"],
    }


def validate_evidence_reference_v2(reference: object, source_bytes: dict[str, bytes]) -> None:
    if type(reference) is not dict:
        _reject_v2("EVIDENCE_REFERENCE_SHAPE", "evidence", "reference must be an object")
    row = cast(dict[str, object], reference)
    if set(row) != {"path", "node_id", "evidence_kind"}:
        _reject_v2("EVIDENCE_REFERENCE_SHAPE", "evidence", "closed fields required")
    path = row.get("path")
    node_id = row.get("node_id")
    kind = row.get("evidence_kind")
    if type(path) is not str or type(node_id) is not str or kind not in {"positive", "refusal"}:
        _reject_v2("EVIDENCE_REFERENCE_SHAPE", "evidence", "invalid field types")
    raw = source_bytes.get(path)
    if type(raw) is not bytes:
        _reject_v2("EVIDENCE_SOURCE", path, "source is absent from the closed denominator")
    if len(raw) > MAX_SOURCE_BYTES_V2:
        _reject_v2("SOURCE_SIZE", path, "source exceeds the fixed byte limit")
    try:
        tree = ast.parse(raw.decode("utf-8"), filename=path)
    except (UnicodeDecodeError, SyntaxError) as exc:
        _reject_v2("EVIDENCE_AST_PARSE", path, type(exc).__name__)
    if sum(1 for _ in ast.walk(tree)) > MAX_AST_NODES_V2:
        _reject_v2("EVIDENCE_AST_LIMIT", path, "AST exceeds the fixed node limit")
    matches = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == node_id
    ]
    if len(matches) != 1:
        _reject_v2("EVIDENCE_AST_NODE", path, f"expected one top-level test {node_id}")


def _positive(path: str, node_id: str) -> dict[str, str]:
    return {"path": path, "node_id": node_id, "evidence_kind": "positive"}


def _refusal(path: str, node_id: str) -> dict[str, str]:
    return {"path": path, "node_id": node_id, "evidence_kind": "refusal"}


def _route_registry_v2() -> list[dict[str, object]]:
    retired = "tests/integration/test_retired_tau_bridge_startup_refusal_v2.py"
    return [
        {
            "route_id": "spot_ledger_api",
            "classification": "MOUNTED_LOCAL_PROFILE",
            "positive_test_refs": [
                _positive(
                    "tests/integration/test_dex_ui_live_bridge.py",
                    "test_live_node_serves_ui_pools_and_accepts_ui_swap",
                )
            ],
            "refusal_test_refs": [],
        },
        {
            "route_id": "oracle_api",
            "classification": "MOUNTED_LOCAL_PROFILE",
            "positive_test_refs": [
                _positive(
                    "tests/test_zenodex_oracle_mvp_completion_audit.py",
                    "test_oracle_mvp_completion_audit_accepts_current_local_shell",
                )
            ],
            "refusal_test_refs": [],
        },
        {
            "route_id": "confidential_attestation_api",
            "classification": "MOUNTED_LOCAL_PROFILE",
            "positive_test_refs": [
                _positive(
                    "tests/integration/test_api_server_confidential.py",
                    "test_api_server_confidential_status_endpoint",
                )
            ],
            "refusal_test_refs": [],
        },
        {
            "route_id": "perps_wallet_stream_8",
            "classification": "QUARANTINED",
            "positive_test_refs": [],
            "refusal_test_refs": [
                _refusal(
                    retired,
                    "test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
                )
            ],
        },
        {
            "route_id": "zusd_tau_wallet_stream_9",
            "classification": "QUARANTINED",
            "positive_test_refs": [],
            "refusal_test_refs": [
                _refusal(
                    retired,
                    "test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
                )
            ],
        },
        {
            "route_id": "zusd_monetary_wallet_stream_11",
            "classification": "QUARANTINED",
            "positive_test_refs": [],
            "refusal_test_refs": [
                _refusal(
                    retired,
                    "test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect",
                )
            ],
        },
        {
            "route_id": "autotrader_api",
            "classification": "QUARANTINED",
            "positive_test_refs": [],
            "refusal_test_refs": [
                _refusal(
                    retired,
                    "test_given_direct_autotrader_attachment_when_called_then_rejects_before_state_effects",
                )
            ],
        },
    ]


def _presentation_registry_v2() -> list[dict[str, object]]:
    rows: tuple[tuple[str, str, list[str], str], ...] = (
        ("swap", "Swap", ["spot_ledger_api"], "NAV_TAB"),
        ("pools", "Pools", ["spot_ledger_api"], "NAV_TAB"),
        ("stats", "ZDEX Stats", [], "NAV_TAB"),
        ("perps", "Perpetuals", ["perps_wallet_stream_8"], "NAV_TAB"),
        ("strategy", "Strategy", ["autotrader_api"], "NAV_TAB"),
        ("zusd", "zUSD", ["zusd_tau_wallet_stream_9", "zusd_monetary_wallet_stream_11"], "NAV_TAB"),
        ("oracle", "Oracle", ["oracle_api"], "NAV_TAB"),
        ("confidential", "Confidential", ["confidential_attestation_api"], "NAV_TAB"),
        ("governance", "Keys", [], "NAV_TAB"),
        ("proofs", "Proof Mining", [], "HIDDEN_ROUTE"),
    )
    return [
        {
            "presentation_id": presentation_id,
            "label": label,
            "route_ids": route_ids,
            "status": "RETAINED_PRESENTATION",
            "visibility": visibility,
        }
        for presentation_id, label, route_ids, visibility in rows
    ]


def _git_environment_v2() -> dict[str, str]:
    environment = {
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
        "LANG": "C",
        "LC_ALL": "C",
    }
    path = os.environ.get("PATH")
    if path:
        environment["PATH"] = path
    return environment


def _git_v2(
    root: Path,
    *arguments: str,
    allowed_returncodes: tuple[int, ...] = (0,),
) -> tuple[int, bytes]:
    command = (
        "git",
        "-c",
        "advice.detachedHead=false",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "diff.external=",
        "-C",
        str(root),
        *arguments,
    )
    try:
        result = subprocess.run(
            command,
            check=False,
            capture_output=True,
            env=_git_environment_v2(),
            timeout=GIT_TIMEOUT_SECONDS_V2,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        _reject_v2("GIT_EXECUTION", "git", type(exc).__name__)
    if len(result.stdout) > MAX_GIT_OUTPUT_BYTES_V2 or len(result.stderr) > MAX_GIT_OUTPUT_BYTES_V2:
        _reject_v2("GIT_OUTPUT_LIMIT", "git", "output exceeds the fixed limit")
    if result.returncode not in allowed_returncodes:
        detail = result.stderr[:512].decode("utf-8", errors="replace")
        _reject_v2("GIT_COMMAND", "git", f"exit={result.returncode} {detail}")
    return result.returncode, result.stdout


def _root_v2(root: Path) -> Path:
    try:
        resolved = root.resolve(strict=True)
    except OSError as exc:
        _reject_v2("ROOT_PATH", str(root), type(exc).__name__)
    if not resolved.is_dir():
        _reject_v2("ROOT_PATH", str(root), "root must be a directory")
    _git_v2(resolved, "rev-parse", "--git-dir")
    return resolved


def _commit_v2(root: Path, revision: str = "HEAD") -> str:
    _code, raw = _git_v2(root, "rev-parse", "--verify", f"{revision}^{{commit}}")
    value = raw.decode("ascii", errors="strict").strip()
    if _HEX_40_V2.fullmatch(value) is None:
        _reject_v2("GIT_COMMIT", revision, "expected one full SHA-1 commit identity")
    return value


def _git_blob_v2(root: Path, commit: str, relative_path: str) -> bytes:
    pure = PurePosixPath(relative_path)
    if pure.is_absolute() or ".." in pure.parts or str(pure) != relative_path:
        _reject_v2("SOURCE_PATH", relative_path, "path must be canonical and relative")
    _code, raw = _git_v2(root, "cat-file", "blob", f"{commit}:{relative_path}")
    if len(raw) > MAX_SOURCE_BYTES_V2:
        _reject_v2("SOURCE_SIZE", relative_path, "source exceeds the fixed byte limit")
    return raw


def _source_bytes_v2(root: Path, commit: str) -> dict[str, bytes]:
    return {path: _git_blob_v2(root, commit, path) for path in SOURCE_PATHS_V2}


def _source_manifest_v2(sources: dict[str, bytes]) -> list[dict[str, str]]:
    return [{"path": path, "sha256": sha256_hex_v2(sources[path])} for path in SOURCE_PATHS_V2]


def _build_registry_artifact_at_v2(root: Path, subject: str) -> dict[str, object]:
    sources = _source_bytes_v2(root, subject)
    routes = _route_registry_v2()
    for route in routes:
        for field in ("positive_test_refs", "refusal_test_refs"):
            references = route[field]
            if type(references) is not list:
                _reject_v2("EVIDENCE_REFERENCE_SHAPE", field, "references must be a list")
            for reference in references:
                validate_evidence_reference_v2(reference, sources)
    manifest = _source_manifest_v2(sources)
    projections = {
        "app_navigation": project_app_navigation_v2(sources["tools/dex-ui/src/App.jsx"]),
        "compose": project_compose_v2(sources["docker-compose.local-testnet.yml"]),
        "ui_config": project_ui_config_v2(sources["tools/dex-ui/public/zenodex-config.json"]),
    }
    return {
        "authority": dict(NO_AUTHORITY_V2),
        "closed_gap": "operator_documentation_drift",
        "implementation_subject": subject,
        "nonclaims": [
            "The registry records source-bound local-profile references; it does not execute them.",
            "MOUNTED_LOCAL_PROFILE is an operator-profile classification, not M6 mounted authority.",
            "No release, settlement, production, or value-moving authority is granted.",
            "Git executable integrity and process containment remain external premises.",
        ],
        "presentation_registry": _presentation_registry_v2(),
        "route_registry": routes,
        "runtime_test_execution": "OUTSIDE_DETERMINISTIC_ARTIFACT",
        "schema": SCHEMA_V2,
        "source_manifest": manifest,
        "source_projections": projections,
        "source_root_sha256": sha256_hex_v2(canonical_json_bytes_v2(manifest)),
        "status": "COMPLETE_SOURCE_BOUND_OPERATOR_REFERENCE_REGISTRY",
        "vm_gates_closed": [],
    }


def build_registry_artifact_v2(root: Path) -> dict[str, object]:
    resolved = _root_v2(root)
    return _build_registry_artifact_at_v2(resolved, _commit_v2(resolved))


def build_registry_bytes_v2(root: Path) -> bytes:
    return canonical_json_bytes_v2(build_registry_artifact_v2(root))


def validate_registry_artifact_v2(artifact: object) -> None:
    if type(artifact) is not dict:
        _reject_v2("ARTIFACT_SHAPE", "artifact", "root must be an object")
    value = cast(dict[str, object], artifact)
    expected_fields = {
        "authority",
        "closed_gap",
        "implementation_subject",
        "nonclaims",
        "presentation_registry",
        "route_registry",
        "runtime_test_execution",
        "schema",
        "source_manifest",
        "source_projections",
        "source_root_sha256",
        "status",
        "vm_gates_closed",
    }
    if set(value) != expected_fields:
        _reject_v2("ARTIFACT_SHAPE", "artifact", "closed top-level fields required")
    if value.get("schema") != SCHEMA_V2:
        _reject_v2("SCHEMA", "schema", "schema drift")
    if value.get("status") != "COMPLETE_SOURCE_BOUND_OPERATOR_REFERENCE_REGISTRY":
        _reject_v2("STATUS", "status", "status drift")
    if value.get("closed_gap") != "operator_documentation_drift":
        _reject_v2("CLOSED_GAP", "closed_gap", "gap drift")
    if value.get("authority") != NO_AUTHORITY_V2:
        _reject_v2("AUTHORITY_DRIFT", "authority", "all authority must remain NONE")
    if value.get("runtime_test_execution") != "OUTSIDE_DETERMINISTIC_ARTIFACT":
        _reject_v2("RUNTIME_EXECUTION", "runtime_test_execution", "runtime claim drift")
    if value.get("vm_gates_closed") != []:
        _reject_v2("AUTHORITY_DRIFT", "vm_gates_closed", "no VM gate may close")
    subject = value.get("implementation_subject")
    if type(subject) is not str or _HEX_40_V2.fullmatch(subject) is None:
        _reject_v2("IMPLEMENTATION_SUBJECT", "implementation_subject", "invalid commit")

    routes = value.get("route_registry")
    expected_routes = _route_registry_v2()
    if type(routes) is not list or [
        row.get("route_id") if type(row) is dict else None for row in routes
    ] != list(ROUTE_IDS_V2):
        _reject_v2("ROUTE_DENOMINATOR", "route_registry", "route denominator drift")
    if routes != expected_routes:
        observed_classes = [
            row.get("classification") if type(row) is dict else None for row in routes
        ]
        expected_classes = [row["classification"] for row in expected_routes]
        if observed_classes != expected_classes:
            _reject_v2("ROUTE_CLASSIFICATION", "route_registry", "classification drift")
        _reject_v2("EVIDENCE_POLARITY", "route_registry", "evidence reference drift")

    presentations = value.get("presentation_registry")
    if presentations != _presentation_registry_v2():
        _reject_v2(
            "PRESENTATION_DENOMINATOR",
            "presentation_registry",
            "presentation denominator or mapping drift",
        )

    manifest = value.get("source_manifest")
    if type(manifest) is not list or len(manifest) != len(SOURCE_PATHS_V2):
        _reject_v2("SOURCE_MANIFEST_SHAPE", "source_manifest", "manifest denominator drift")
    normalized: list[dict[str, str]] = []
    for index, row in enumerate(manifest):
        if type(row) is not dict or set(row) != {"path", "sha256"}:
            _reject_v2("SOURCE_MANIFEST_SHAPE", f"source_manifest[{index}]", "row shape")
        path = row.get("path")
        digest = row.get("sha256")
        if type(path) is not str or type(digest) is not str or _HEX_64_V2.fullmatch(digest) is None:
            _reject_v2("SOURCE_MANIFEST_SHAPE", f"source_manifest[{index}]", "row types")
        normalized.append({"path": path, "sha256": digest})
    if [row["path"] for row in normalized] != list(SOURCE_PATHS_V2):
        _reject_v2("SOURCE_MANIFEST_SHAPE", "source_manifest", "path order drift")
    root = value.get("source_root_sha256")
    expected_root = sha256_hex_v2(canonical_json_bytes_v2(normalized))
    if root != expected_root:
        _reject_v2("SOURCE_MANIFEST_SHAPE", "source_root_sha256", "root mismatch")

    projections = value.get("source_projections")
    if type(projections) is not dict or set(projections) != {
        "app_navigation",
        "compose",
        "ui_config",
    }:
        _reject_v2("SOURCE_PROJECTION_SHAPE", "source_projections", "closed projections required")
    nonclaims = value.get("nonclaims")
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(row) is not str for row in nonclaims)
    ):
        _reject_v2("NONCLAIM_SHAPE", "nonclaims", "nonclaims must be nonempty strings")


def _artifact_commit_v2(root: Path) -> str:
    _code, raw = _git_v2(
        root,
        "log",
        "-n",
        "1",
        "--format=%H",
        "--",
        ARTIFACT_RELATIVE_PATH_V2.as_posix(),
    )
    value = raw.decode("ascii", errors="strict").strip()
    if value == "":
        _reject_v2("ARTIFACT_UNAVAILABLE", str(ARTIFACT_RELATIVE_PATH_V2), "no committed artifact")
    if _HEX_40_V2.fullmatch(value) is None:
        _reject_v2("ARTIFACT_TOPOLOGY", str(ARTIFACT_RELATIVE_PATH_V2), "invalid artifact commit")
    return value


def _commit_parents_v2(root: Path, commit: str) -> tuple[str, ...]:
    _code, raw = _git_v2(root, "cat-file", "-p", commit)
    parents: list[str] = []
    for line in raw.splitlines():
        if line.startswith(b"parent "):
            candidate = line[7:].decode("ascii", errors="strict")
            if _HEX_40_V2.fullmatch(candidate) is None:
                _reject_v2("ARTIFACT_TOPOLOGY", commit, "invalid parent identity")
            parents.append(candidate)
        elif line == b"":
            break
    return tuple(parents)


def _artifact_only_child_v2(root: Path, artifact_commit: str) -> str:
    parents = _commit_parents_v2(root, artifact_commit)
    if len(parents) != 1:
        _reject_v2("ARTIFACT_TOPOLOGY", artifact_commit, "artifact commit must have one parent")
    parent = parents[0]
    _code, raw = _git_v2(
        root,
        "diff",
        "--name-only",
        "-z",
        "--no-renames",
        parent,
        artifact_commit,
        "--",
    )
    try:
        paths = tuple(part.decode("utf-8") for part in raw.split(b"\0") if part)
    except UnicodeDecodeError:
        _reject_v2("ARTIFACT_TOPOLOGY", artifact_commit, "non-UTF-8 changed path")
    if paths != (ARTIFACT_RELATIVE_PATH_V2.as_posix(),):
        _reject_v2("ARTIFACT_TOPOLOGY", artifact_commit, "Stage B must change only the artifact")
    return parent


def _worktree_path_dirty_v2(root: Path, paths: tuple[str, ...]) -> bool:
    _code, raw = _git_v2(
        root,
        "status",
        "--porcelain=v1",
        "-z",
        "--untracked-files=all",
        "--",
        *paths,
    )
    return raw != b""


def _report_v2(
    *,
    ok: bool,
    findings: list[dict[str, str]],
    artifact_sha256: str = "",
    implementation_subject: str = "",
    historical_valid: bool = False,
    current_applicable: bool = False,
) -> dict[str, object]:
    return {
        "artifact_sha256": artifact_sha256,
        "authority": dict(NO_AUTHORITY_V2),
        "current_applicable": current_applicable,
        "findings": findings,
        "historical_valid": historical_valid,
        "implementation_subject": implementation_subject,
        "ok": ok,
        "runtime_test_execution": "OUTSIDE_DETERMINISTIC_ARTIFACT",
        "schema": CHECK_SCHEMA_V2,
        "vm_gates_closed": [],
    }


def _failure_report_v2(
    rejection: OperatorSurfaceRegistryRejectV2,
    *,
    artifact_sha256: str = "",
    implementation_subject: str = "",
    historical_valid: bool = False,
    current_applicable: bool = False,
) -> dict[str, object]:
    return _report_v2(
        ok=False,
        findings=[{"code": rejection.code, "path": rejection.path, "detail": rejection.detail}],
        artifact_sha256=artifact_sha256,
        implementation_subject=implementation_subject,
        historical_valid=historical_valid,
        current_applicable=current_applicable,
    )


def check_registry_v2(root: Path) -> dict[str, object]:
    resolved: Path | None = None
    artifact_sha256 = ""
    implementation_subject = ""
    historical_valid = False
    try:
        resolved = _root_v2(root)
        artifact_commit = _artifact_commit_v2(resolved)
        implementation_subject = _artifact_only_child_v2(resolved, artifact_commit)
        committed_raw = _git_blob_v2(
            resolved, artifact_commit, ARTIFACT_RELATIVE_PATH_V2.as_posix()
        )
        artifact_sha256 = sha256_hex_v2(committed_raw)

        worktree_artifact = resolved / ARTIFACT_RELATIVE_PATH_V2
        if worktree_artifact.is_file():
            live_raw = worktree_artifact.read_bytes()
            if live_raw != committed_raw:
                live = decode_json_object_v2(live_raw, str(ARTIFACT_RELATIVE_PATH_V2))
                if canonical_json_bytes_v2(live) != live_raw:
                    _reject_v2(
                        "NONCANONICAL_ARTIFACT",
                        str(ARTIFACT_RELATIVE_PATH_V2),
                        "worktree artifact is not canonical JSON",
                    )
                _reject_v2(
                    "WORKTREE_ARTIFACT_DRIFT",
                    str(ARTIFACT_RELATIVE_PATH_V2),
                    "worktree artifact differs from committed Stage B",
                )

        artifact = decode_json_object_v2(committed_raw, str(ARTIFACT_RELATIVE_PATH_V2))
        if canonical_json_bytes_v2(artifact) != committed_raw:
            _reject_v2(
                "NONCANONICAL_ARTIFACT",
                str(ARTIFACT_RELATIVE_PATH_V2),
                "committed artifact is not canonical JSON",
            )
        validate_registry_artifact_v2(artifact)
        if artifact.get("implementation_subject") != implementation_subject:
            _reject_v2(
                "ARTIFACT_TOPOLOGY",
                "implementation_subject",
                "artifact must bind its direct parent",
            )
        expected = _build_registry_artifact_at_v2(resolved, implementation_subject)
        if artifact != expected:
            _reject_v2(
                "ARTIFACT_PROJECTION_DRIFT",
                str(ARTIFACT_RELATIVE_PATH_V2),
                "artifact differs from the Stage-A projection",
            )
        historical_valid = True

        if _worktree_path_dirty_v2(resolved, SOURCE_PATHS_V2):
            _reject_v2(
                "WORKTREE_SOURCE_DRIFT",
                "source_manifest",
                "critical source paths are dirty",
            )
        head = _commit_v2(resolved)
        current_sources = _source_bytes_v2(resolved, head)
        current_manifest = _source_manifest_v2(current_sources)
        if current_manifest != artifact.get("source_manifest"):
            _reject_v2(
                "CURRENT_SOURCE_DRIFT",
                "source_manifest",
                "current committed sources differ from Stage A",
            )
    except OperatorSurfaceRegistryRejectV2 as exc:
        return _failure_report_v2(
            exc,
            artifact_sha256=artifact_sha256,
            implementation_subject=implementation_subject,
            historical_valid=historical_valid,
            current_applicable=False,
        )
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        rejection = OperatorSurfaceRegistryRejectV2(
            "CHECKER_INPUT_ERROR",
            str(root if resolved is None else resolved),
            type(exc).__name__,
        )
        return _failure_report_v2(
            rejection,
            artifact_sha256=artifact_sha256,
            implementation_subject=implementation_subject,
            historical_valid=historical_valid,
            current_applicable=False,
        )
    return _report_v2(
        ok=True,
        findings=[],
        artifact_sha256=artifact_sha256,
        implementation_subject=implementation_subject,
        historical_valid=True,
        current_applicable=True,
    )
