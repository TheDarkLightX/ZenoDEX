"""Strict JSON, YAML, JavaScript, and evidence projections for O-004 V2."""

from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Final, cast

import yaml

from tools.operator_surface_registry_common_v2 import (
    OperatorSurfaceRegistryRejectV2,
    decode_json_object_v2,
    reject_v2,
)

MAX_SOURCE_BYTES_V2: Final = 4_194_304
MAX_AST_NODES_V2: Final = 500_000
MAX_JS_TOKENS_V2: Final = 300_000
UI_ROUTE_FLAG_ROWS_V2: Final = (
    ("perpsWalletUiEnabled", False),
    ("zusdTauWalletUiEnabled", False),
    ("zusdMonetaryWalletUiEnabled", False),
)
COMPOSE_ROUTE_ROWS_V2: Final = (
    ("AUTOTRADER_LIVE_API_ENABLED", "false"),
    ("CONFIDENTIAL_ATTESTATION_API_ENABLED", "true"),
    ("DEX_API_ENABLED", "true"),
    ("PERPS_WALLET_API_ENABLED", "false"),
    ("ZUSD_MONETARY_WALLET_API_ENABLED", "false"),
    ("ZUSD_TAU_WALLET_API_ENABLED", "false"),
)
IMPORTER_ROWS_V2: Final = (
    ("swap", "./components/SwapInterface"),
    ("pools", "./components/PoolDashboard"),
    ("stats", "./components/TokenStats"),
    ("perps", "./components/perps/PerpTradingView"),
    ("strategy", "./components/StrategyWorkbench.jsx"),
    ("zusd", "./components/ZUSDWorkbench.jsx"),
    ("oracle", "./components/ZenoOracleDashboard.jsx"),
    ("confidential", "./components/ConfidentialWorkbench.jsx"),
    ("governance", "./components/PerpsGovernanceSurface.jsx"),
    ("proofs", "./components/ProofMiningWorkbench.jsx"),
)
NAV_TAB_ROWS_V2: Final = (
    ("swap", "Swap"),
    ("pools", "Pools"),
    ("stats", "ZDEX Stats"),
    ("perps", "Perpetuals"),
    ("strategy", "Strategy"),
    ("zusd", "zUSD"),
    ("oracle", "Oracle"),
    ("confidential", "Confidential"),
    ("governance", "Keys"),
)
RENDER_IDS_V2: Final = (
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
)


@dataclass(frozen=True)
class _JsTokenV2:
    kind: str
    value: str


def project_ui_config_v2(raw: bytes) -> dict[str, object]:
    value = decode_json_object_v2(raw, "tools/dex-ui/public/zenodex-config.json")
    expected = dict(UI_ROUTE_FLAG_ROWS_V2)
    observed = {key: value.get(key) for key in expected}
    if observed != expected or any(type(observed[key]) is not bool for key in expected):
        reject_v2(
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
                    reject_v2("YAML_DUPLICATE_KEY", path, key_node.value)
                seen.add(key_node.value)
            _reject_duplicate_yaml_keys_v2(value_node, path)
    elif isinstance(node, yaml.nodes.SequenceNode):
        for child in node.value:
            _reject_duplicate_yaml_keys_v2(child, path)


def _exact_mapping_v2(value: object, path: str) -> dict[str, object]:
    if type(value) is not dict or any(type(key) is not str for key in value):
        reject_v2("MAPPING_TYPE", path, "must be an exact string-keyed object")
    return cast(dict[str, object], value)


def project_compose_v2(raw: bytes) -> dict[str, object]:
    path = "docker-compose.local-testnet.yml"
    if type(raw) is not bytes or len(raw) > MAX_SOURCE_BYTES_V2:
        reject_v2("SOURCE_SIZE", path, "source exceeds the fixed byte limit")
    try:
        text = raw.decode("utf-8")
        node = yaml.compose(text, Loader=yaml.SafeLoader)
        if node is None:
            reject_v2("YAML_PARSE", path, "empty document")
        _reject_duplicate_yaml_keys_v2(node, path)
        loaded = yaml.safe_load(text)
    except (UnicodeDecodeError, yaml.YAMLError) as exc:
        reject_v2("YAML_PARSE", path, type(exc).__name__)
    root = _exact_mapping_v2(loaded, path)
    services = _exact_mapping_v2(root.get("services"), f"{path}.services")
    api = _exact_mapping_v2(services.get("zenodex-api"), f"{path}.services.zenodex-api")
    environment = _exact_mapping_v2(
        api.get("environment"), f"{path}.services.zenodex-api.environment"
    )
    expected = dict(COMPOSE_ROUTE_ROWS_V2)
    if {key: environment.get(key) for key in expected} != expected:
        reject_v2("COMPOSE_ROUTE_ENVIRONMENT", path, "route environment drift")
    if type(services.get("zenodex-oracle")) is not dict:
        reject_v2("COMPOSE_ORACLE_SERVICE", path, "oracle service is absent")
    return {"route_environment": expected, "zenodex_oracle_service_declared": True}


def _tokenize_js_v2(raw: bytes, path: str) -> tuple[_JsTokenV2, ...]:
    if type(raw) is not bytes or len(raw) > MAX_SOURCE_BYTES_V2:
        reject_v2("SOURCE_SIZE", path, "source exceeds the fixed byte limit")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        reject_v2("JS_UTF8", path, "source must be UTF-8")
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
                reject_v2("JS_COMMENT", path, "unterminated block comment")
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
                reject_v2("JS_STRING", path, "unterminated string")
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
            reject_v2("JS_TOKEN_LIMIT", path, "token count exceeds the fixed limit")
    return tuple(tokens)


def _matching_token_v2(
    tokens: tuple[_JsTokenV2, ...], opening_index: int, opening: str, closing: str, path: str
) -> int:
    if opening_index >= len(tokens) or tokens[opening_index].value != opening:
        reject_v2("JS_STRUCTURE", path, f"expected {opening}")
    depth = 0
    for index in range(opening_index, len(tokens)):
        value = tokens[index].value
        if value == opening:
            depth += 1
        elif value == closing:
            depth -= 1
            if depth == 0:
                return index
    reject_v2("JS_STRUCTURE", path, f"unclosed {opening}")


def _declaration_v2(tokens: tuple[_JsTokenV2, ...], prefix: tuple[str, ...], path: str) -> int:
    values = tuple(token.value for token in tokens)
    matches = [
        index
        for index in range(len(values) - len(prefix) + 1)
        if values[index : index + len(prefix)] == prefix
    ]
    if len(matches) != 1:
        reject_v2("JS_DECLARATION", path, f"expected one declaration {prefix}")
    return matches[0]


def _simple_js_string_v2(token: _JsTokenV2, path: str) -> str:
    if token.kind != "string" or token.value[0] not in {"'", '"'} or "\\" in token.value:
        reject_v2("JS_SIMPLE_STRING", path, "expected a simple quoted string")
    return token.value[1:-1]


def _parse_importers_v2(tokens: tuple[_JsTokenV2, ...], opening: int, path: str) -> dict[str, str]:
    closing = _matching_token_v2(tokens, opening, "{", "}", path)
    index = opening + 1
    result: dict[str, str] = {}
    while index < closing:
        if index + 8 >= closing:
            reject_v2("JS_NAV_IMPORTER_SET", path, "truncated importer")
        row = tuple(token.value for token in tokens[index : index + 9])
        key = tokens[index]
        if (
            key.kind != "identifier"
            or row[1:7] != (":", "(", ")", "=>", "import", "(")
            or tokens[index + 7].kind != "string"
            or row[8] != ")"
            or key.value in result
        ):
            reject_v2("JS_NAV_IMPORTER_SET", path, "importer shape drift")
        result[key.value] = _simple_js_string_v2(tokens[index + 7], path)
        index += 9
        if index < closing:
            if tokens[index].value != ",":
                reject_v2("JS_NAV_IMPORTER_SET", path, "missing importer separator")
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
            reject_v2("JS_NAV_TABS", path, "tab row must be an object")
        row_close = _matching_token_v2(tokens, index, "{", "}", path)
        row = tokens[index + 1 : row_close]
        values = tuple(token.value for token in row)
        if len(values) != 7 or values[0:2] != ("id", ":") or values[3:6] != (",", "label", ":"):
            reject_v2("JS_NAV_TABS", path, "tab row shape drift")
        tab_id = _simple_js_string_v2(row[2], path)
        label = _simple_js_string_v2(row[6], path)
        if tab_id in seen:
            reject_v2("JS_NAV_TABS", path, f"duplicate tab {tab_id}")
        seen.add(tab_id)
        result.append({"id": tab_id, "label": label})
        index = row_close + 1
        if index < closing:
            if tokens[index].value != ",":
                reject_v2("JS_NAV_TABS", path, "missing tab separator")
            index += 1
    return result


def project_app_navigation_v2(raw: bytes) -> dict[str, object]:
    path = "tools/dex-ui/src/App.jsx"
    tokens = _tokenize_js_v2(raw, path)
    importer_start = _declaration_v2(tokens, ("const", "SURFACE_IMPORTERS", "="), path)
    importers = _parse_importers_v2(tokens, importer_start + 3, path)
    if importers != dict(IMPORTER_ROWS_V2):
        reject_v2("JS_NAV_IMPORTER_SET", path, "surface importer set drift")

    tabs_start = _declaration_v2(tokens, ("const", "NAV_TABS", "="), path)
    tabs = _parse_nav_tabs_v2(tokens, tabs_start + 3, path)
    expected_tabs = [{"id": tab_id, "label": label} for tab_id, label in NAV_TAB_ROWS_V2]
    if tabs != expected_tabs:
        reject_v2("JS_NAV_TABS", path, "navigation denominator drift")

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
        reject_v2("JS_ROUTE_TAB_SET", path, "hidden route declaration drift")

    values = tuple(token.value for token in tokens)
    render_ids: list[str] = []
    for index in range(len(values) - 5):
        if (
            values[index : index + 3] == ("{", "activeTab", "===")
            and tokens[index + 3].kind == "string"
            and values[index + 4 : index + 6] == ("&&", "(")
        ):
            render_ids.append(_simple_js_string_v2(tokens[index + 3], path))
    if render_ids != list(RENDER_IDS_V2):
        reject_v2("JS_NAV_RENDER_SET", path, "render branch set or order drift")
    return {
        "importers": importers,
        "navigation_tabs": tabs,
        "render_ids": render_ids,
        "hidden_route_ids": ["proofs"],
    }


def expected_source_projections_v2() -> dict[str, object]:
    return {
        "app_navigation": {
            "hidden_route_ids": ["proofs"],
            "importers": dict(IMPORTER_ROWS_V2),
            "navigation_tabs": [
                {"id": tab_id, "label": label} for tab_id, label in NAV_TAB_ROWS_V2
            ],
            "render_ids": list(RENDER_IDS_V2),
        },
        "compose": {
            "route_environment": dict(COMPOSE_ROUTE_ROWS_V2),
            "zenodex_oracle_service_declared": True,
        },
        "ui_config": {"value_route_flags": dict(UI_ROUTE_FLAG_ROWS_V2)},
    }


def validate_evidence_reference_v2(reference: object, source_bytes: dict[str, bytes]) -> None:
    if type(reference) is not dict:
        reject_v2("EVIDENCE_REFERENCE_SHAPE", "evidence", "reference must be an object")
    row = cast(dict[str, object], reference)
    if set(row) != {"path", "node_id", "evidence_kind"}:
        reject_v2("EVIDENCE_REFERENCE_SHAPE", "evidence", "closed fields required")
    path = row.get("path")
    node_id = row.get("node_id")
    kind = row.get("evidence_kind")
    if type(path) is not str or type(node_id) is not str or kind not in {"positive", "refusal"}:
        reject_v2("EVIDENCE_REFERENCE_SHAPE", "evidence", "invalid field types")
    raw = source_bytes.get(path)
    if type(raw) is not bytes:
        reject_v2("EVIDENCE_SOURCE", path, "source is absent from the closed denominator")
    if len(raw) > MAX_SOURCE_BYTES_V2:
        reject_v2("SOURCE_SIZE", path, "source exceeds the fixed byte limit")
    try:
        tree = ast.parse(raw.decode("utf-8"), filename=path)
    except (UnicodeDecodeError, SyntaxError) as exc:
        reject_v2("EVIDENCE_AST_PARSE", path, type(exc).__name__)
    if sum(1 for _ in ast.walk(tree)) > MAX_AST_NODES_V2:
        reject_v2("EVIDENCE_AST_LIMIT", path, "AST exceeds the fixed node limit")
    matches = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == node_id
    ]
    if len(matches) != 1:
        reject_v2("EVIDENCE_AST_NODE", path, f"expected one top-level test {node_id}")


__all__ = [
    "MAX_SOURCE_BYTES_V2",
    "OperatorSurfaceRegistryRejectV2",
    "expected_source_projections_v2",
    "project_app_navigation_v2",
    "project_compose_v2",
    "project_ui_config_v2",
    "validate_evidence_reference_v2",
]
