#!/usr/bin/env python3
"""Fail closed on drift in the bounded ZenoDEX V3 acceptance index.

The index records source/test linkage and explicit gaps. It does not establish
lifecycle completion, replay qualification, formal closure, release, or
value-movement authority.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, NoReturn, cast

SCHEMA = "zenodex/v3-acceptance-index/v1"
ROOT = Path(__file__).resolve().parents[1]
INDEX_PATH = "docs/research/ZENODEX_V3_ACCEPTANCE.json"
LAYOUT_SHA256 = "ddfc835a2199edbd860142327e9415cceea3de547a8519d3db0af94b570dd3ef"
REPLAY_CASES = {
    "transfer-v2-core": (
        "tests/core/test_asset_transfer_module_v2.py::test_transfer_accepts_one_origin_and_occurrence_bound_command",
        "tests/core/test_asset_transfer_module_v2.py::test_unknown_disabled_and_subject_guards_preserve_rejection_precedence",
        "tests/core/test_asset_transfer_module_v2.py::test_insufficient_balance_rejects_without_partial_application",
    ),
    "custody-transfer-v1": (
        "tests/core/test_asset_transfer_lane_module_custody_v1.py::test_recomputation_refuses_legacy_and_coherent_foreign_outputs",
        "tests/core/test_asset_transfer_lane_module_custody_v1.py::test_balances_only_mutant_is_refused_by_existing_coordinator",
        "tests/core/test_asset_transfer_lane_module_custody_v1.py::test_omitted_port_root_rebind_is_rejected_by_owned_accepted_constructor",
    ),
    "custody-successor-v2-python": (
        "tests/core/test_asset_lane_custody_v2.py::test_given_accounts_and_vault_when_authorized_transfer_then_complete_value_is_preserved",
        "tests/core/test_asset_lane_custody_v2.py::test_issue_then_burn_preserves_custody_and_complete_supply",
        "tests/core/test_asset_lane_custody_v2.py::test_unauthorized_transfer_is_exact_no_effect",
        "tests/core/test_asset_lane_custody_global_v2.py::test_given_backed_claim_when_transfer_then_global_checker_accepts_complete_frame",
        "tests/core/test_asset_lane_custody_global_v2.py::test_semantic_mutants_cannot_pass_the_global_consumer",
        "tests/core/test_asset_lane_custody_global_v2.py::test_wrong_writer_epoch_is_rejected_despite_conserved_totals",
    ),
}
AUTHORITY = {
    "settlement": "NONE",
    "value_movement": "NONE",
    "production": "NONE",
    "release": "NONE",
}
NONCLAIMS = [
    "Inventory completeness is structural only.",
    "A mapped test is bounded linkage evidence and does not qualify a complete lifecycle.",
    "An optional replay is unrecorded unless a separately reviewed evidence path binds it.",
    "This index establishes no formal-core, whole-program, release, or value-movement completion.",
]
JsonObject = dict[str, Any]


def _reject(code: str) -> NoReturn:
    raise ValueError(code)


def _mapping(value: object, code: str) -> JsonObject:
    if type(value) is not dict:
        _reject(code)
    return cast(JsonObject, value)


def _items(value: object, code: str) -> list[Any]:
    if type(value) is not list:
        _reject(code)
    return value


def _text(value: object, code: str) -> str:
    if type(value) is not str or not value:
        _reject(code)
    return value


def _pairs(pairs: list[tuple[str, object]]) -> JsonObject:
    result: JsonObject = {}
    for key, value in pairs:
        if key in result:
            _reject("DUPLICATE_JSON_KEY")
        result[key] = value
    return result


def load_index(path: Path) -> JsonObject:
    try:
        data = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_pairs,
            parse_constant=lambda _: _reject("NONFINITE_JSON"),
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, RecursionError):
        _reject("MALFORMED_INDEX")
    return _mapping(data, "INDEX_SHAPE")


def _file(root: Path, relative: str) -> Path:
    try:
        result = (root / relative).resolve(strict=True)
    except OSError:
        _reject("MISSING_SOURCE")
    if not result.is_relative_to(root.resolve()) or not result.is_file():
        _reject("PATH_ESCAPE")
    return result


def _digest(root: Path, relative: str) -> str:
    return hashlib.sha256(_file(root, relative).read_bytes()).hexdigest()


def _source_json(root: Path, relative: str) -> JsonObject:
    try:
        return _mapping(
            json.loads(_file(root, relative).read_text(encoding="utf-8")), "SOURCE_SHAPE"
        )
    except (UnicodeDecodeError, json.JSONDecodeError):
        _reject("SOURCE_SHAPE")


def _layout(index: JsonObject) -> tuple[JsonObject, list[Any], JsonObject]:
    try:
        layout = {key: index[key] for key in ("source_pins", "components", "case_catalog")}
        encoded = json.dumps(
            layout, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False
        )
    except (KeyError, TypeError, ValueError):
        _reject("LAYOUT_SHAPE")
    if hashlib.sha256(encoded.encode()).hexdigest() != LAYOUT_SHA256:
        _reject("FROZEN_LAYOUT_DRIFT")
    return (
        _mapping(layout["source_pins"], "LAYOUT_SHAPE"),
        _items(layout["components"], "LAYOUT_SHAPE"),
        _mapping(layout["case_catalog"], "LAYOUT_SHAPE"),
    )


def _entry(root: Path, raw: object, code: str) -> tuple[str, str]:
    entry = _mapping(raw, code)
    path, digest = _text(entry.get("path"), code), _text(entry.get("sha256"), code)
    if _digest(root, path) != digest:
        _reject(code)
    return path, digest


def _source_status(value: JsonObject, code: str) -> str:
    status = _text(value.get("source_status", "PINNED"), code)
    if status not in {"PINNED", "PROVISIONAL"}:
        _reject(code)
    return status


def _pins(
    root: Path, pins: JsonObject, components: list[Any]
) -> tuple[JsonObject, set[str], set[str]]:
    names = ("plan_v3", "capability_manifest_v1", "normative_requirements_v1")
    try:
        direct = {name: _mapping(pins[name], "SOURCE_PIN_STALE") for name in names}
        abi = _mapping(pins["abi_v2"], "SOURCE_PIN_STALE")
        sources = [
            *direct.values(),
            *(
                _mapping(item, "SOURCE_PIN_STALE")
                for item in _items(abi.get("sources"), "SOURCE_PIN_STALE")
            ),
        ]
    except KeyError:
        _reject("SOURCE_PIN_STALE")
    trusted = {_entry(root, entry, "SOURCE_PIN_STALE")[0] for entry in sources}
    by_id: JsonObject = {}
    provisional: set[str] = set()
    for raw in components:
        component = _mapping(raw, "COMPONENT_SOURCE_STALE")
        identifier = _text(component.get("id"), "COMPONENT_SOURCE_STALE")
        if identifier in by_id:
            _reject("COMPONENT_SOURCE_STALE")
        by_id[identifier] = component
        status = _source_status(component, "COMPONENT_SOURCE_STALE")
        for entry in _items(component.get("sources"), "COMPONENT_SOURCE_STALE"):
            if status == "PINNED":
                trusted.add(_entry(root, entry, "COMPONENT_SOURCE_STALE")[0])
            else:
                entry = _mapping(entry, "COMPONENT_SOURCE_STALE")
                if set(entry) != {"path"}:
                    _reject("COMPONENT_SOURCE_STALE")
                _file(root, _text(entry.get("path"), "COMPONENT_SOURCE_STALE"))
                provisional.add(identifier)
    return by_id, trusted, provisional


def _inventory(root: Path, pins: JsonObject) -> JsonObject:
    manifest = _source_json(root, _mapping(pins["capability_manifest_v1"], "SOURCE_SHAPE")["path"])
    requirements = _source_json(
        root, _mapping(pins["normative_requirements_v1"], "SOURCE_SHAPE")["path"]
    )
    plan = _source_json(root, _mapping(pins["plan_v3"], "SOURCE_SHAPE")["path"])
    lanes = _items(manifest.get("lanes"), "CANONICAL_INVENTORY")
    capabilities = [
        f"{lane['lane_id']}:{capability}"
        for lane in lanes
        for capability in _mapping(lane, "CANONICAL_INVENTORY")["capabilities"]
    ]
    routes = manifest.get("required_cross_lane_routes")
    exclusions = [
        {"id": item["capability"], "disposition": item["disposition"]}
        for item in manifest.get("explicit_exclusions", [])
    ]
    rows = _items(requirements.get("rows"), "CANONICAL_INVENTORY")
    workflows = [
        row["requirement_id"]
        for row in rows
        if _mapping(row, "CANONICAL_INVENTORY").get("kind") == "WORKFLOW"
    ]
    bdd = [
        row["requirement_id"]
        for row in rows
        if _mapping(row, "CANONICAL_INVENTORY").get("kind") == "BDD"
    ]
    floor = _mapping(plan.get("requirements_floor"), "CANONICAL_INVENTORY")
    inventory = {
        "capability_ids": capabilities,
        "route_ids": routes,
        "exclusions": exclusions,
        "workflow_ids": workflows,
        "bdd_ids": bdd,
    }
    if (
        not all(type(item) is str for item in capabilities + workflows + bdd)
        or type(routes) is not list
        or len(capabilities) != 103
        or len(routes) != 4
        or len(exclusions) != 4
        or len(workflows) != 18
        or len(bdd) != 81
        or len(set(capabilities + routes + workflows + bdd)) != 206
        or floor.get("capability_count") != 103
        or floor.get("route_count") != 4
        or floor.get("exclusion_count") != 4
        or floor.get("lanes") != lanes
        or floor.get("required_cross_lane_routes") != routes
        or floor.get("explicit_exclusions")
        != [{"capability": item["id"], "disposition": item["disposition"]} for item in exclusions]
    ):
        _reject("CANONICAL_INVENTORY")
    return inventory


def _test_info(root: Path, source: str) -> tuple[set[str], set[str]]:
    try:
        tree = ast.parse(_file(root, source).read_text(encoding="utf-8"))
    except (SyntaxError, UnicodeDecodeError):
        _reject("TEST_SOURCE_PARSE")
    imports: set[str] = set()
    for item in ast.walk(tree):
        if isinstance(item, ast.Import):
            imports.update(alias.name for alias in item.names)
        elif isinstance(item, ast.ImportFrom) and item.module:
            imports.add(item.module)
            imports.update(f"{item.module}.{alias.name}" for alias in item.names)
    return imports, {item.name for item in tree.body if isinstance(item, ast.FunctionDef)}


def _cases(
    root: Path,
    catalog: JsonObject,
    components: JsonObject,
    trusted: set[str],
    provisional_components: set[str],
) -> set[str]:
    if set(catalog) != set(REPLAY_CASES):
        _reject("CASE_CATALOG")
    provisional: set[str] = set()
    for name, nodes in REPLAY_CASES.items():
        case = _mapping(catalog[name], "CASE_CATALOG")
        status = _source_status(case, "CASE_CATALOG")
        source_functions: dict[str, set[str]] = {}
        imports: set[str] = set()
        for raw_source in _items(case.get("test_sources"), "CASE_CATALOG"):
            if status == "PINNED":
                source = _entry(root, raw_source, "CASE_TEST_STALE")[0]
            else:
                source_entry = _mapping(raw_source, "CASE_CATALOG")
                if set(source_entry) != {"path"}:
                    _reject("CASE_CATALOG")
                source = _text(source_entry.get("path"), "CASE_CATALOG")
                _file(root, source)
            if source in source_functions:
                _reject("CASE_CATALOG")
            source_imports, source_functions[source] = _test_info(root, source)
            imports.update(source_imports)
        catalog_nodes = [
            _text(node, "CASE_CATALOG") for node in _items(case.get("pytest_nodes"), "CASE_CATALOG")
        ]
        if len(set(catalog_nodes)) != len(catalog_nodes):
            _reject("CASE_CATALOG")
        node_sources: set[str] = set()
        for node in catalog_nodes:
            path, separator, function = node.partition("::")
            if (
                path not in source_functions
                or not separator
                or "::" in function
                or function not in source_functions[path]
            ):
                _reject("NODE_MISSING")
            node_sources.add(path)
        if node_sources != set(source_functions):
            _reject("CASE_CATALOG")
        if catalog_nodes != list(nodes):
            _reject("CASE_CATALOG")
        for implementation in _items(case.get("implementation_paths"), "CASE_CATALOG"):
            module = _text(implementation, "CASE_CATALOG").removesuffix(".py").replace("/", ".")
            if module not in imports:
                _reject("IMPLEMENTATION_UNLINKED")
        semantic_paths = {
            _text(path, "CASE_CATALOG")
            for path in _items(case.get("semantic_spec_paths"), "CASE_CATALOG")
        }
        if not semantic_paths.issubset(trusted):
            _reject("SEMANTIC_SPEC_UNPINNED")
        component_id = _text(case.get("component_id"), "CASE_CATALOG")
        if component_id not in components:
            _reject("CASE_COMPONENT")
        if status == "PROVISIONAL" or component_id in provisional_components:
            provisional.add(name)
    return provisional


def _binding(
    catalog: JsonObject,
    components: JsonObject,
    raw: object,
    identifier: str,
    *,
    successor: bool = False,
) -> None:
    binding = _mapping(raw, "BINDING_SHAPE")
    if set(binding) != {"case_id", "implementation_paths", "limitation"}:
        _reject("BINDING_SHAPE")
    case_id = _text(binding.get("case_id"), "BINDING_SHAPE")
    if case_id not in catalog:
        _reject("UNKNOWN_CASE")
    case = _mapping(catalog[case_id], "CASE_CATALOG")
    if binding["implementation_paths"] != case.get("implementation_paths"):
        _reject("IMPLEMENTATION_COVERAGE")
    if "does not" not in _text(binding.get("limitation"), "LIMITATION").casefold():
        _reject("LIMITATION")
    if successor:
        component = _mapping(
            components.get(_text(case.get("component_id"), "CASE_CATALOG")), "SUCCESSOR_ABI"
        )
        if component.get("abi_version") != "GLOBAL_SETTLEMENT_ABI_V2":
            _reject("SUCCESSOR_ABI")
    elif identifier not in _items(case.get("allowed_ids"), "CASE_CATALOG"):
        _reject("CASE_SCOPE")


def _expected(inventory: JsonObject) -> list[tuple[str, str]]:
    records = [(f"CAPABILITY:{item}", "CAPABILITY") for item in inventory["capability_ids"]]
    records += [(f"ROUTE:{item}", "ROUTE") for item in inventory["route_ids"]]
    records += [(f"EXCLUSION:{item['id']}", "EXCLUSION") for item in inventory["exclusions"]]
    records += [(f"WORKFLOW:{item}", "WORKFLOW") for item in inventory["workflow_ids"]]
    return records + [(f"BDD:{item}", "BDD") for item in inventory["bdd_ids"]]


def _records(
    index: JsonObject,
    expected: list[tuple[str, str]],
    catalog: JsonObject,
    components: JsonObject,
) -> set[str]:
    kinds, mapped, gaps = dict(expected), set(), set()
    for raw in _items(index.get("mappings"), "MAPPING_SHAPE"):
        item = _mapping(raw, "MAPPING_SHAPE")
        if set(item) != {"id", "kind", "mapping", "behavior", "reason", "bindings"}:
            _reject("MAPPING_SHAPE")
        identifier = _text(item.get("id"), "MAPPING_SHAPE")
        if identifier in mapped:
            _reject("DUPLICATE_REQUIREMENT")
        if (
            kinds.get(identifier) != item.get("kind")
            or item.get("mapping") != "MAPPED"
            or not _text(item.get("behavior"), "MAPPING_SHAPE").startswith("BOUNDED_")
            or not _text(item.get("reason"), "MAPPING_SHAPE")
        ):
            _reject("MAPPING_SCOPE")
        bindings = _items(item.get("bindings"), "MAPPING_SHAPE")
        if not bindings:
            _reject("MAPPING_SHAPE")
        for binding in bindings:
            _binding(catalog, components, binding, identifier)
        mapped.add(identifier)
    for raw in _items(index.get("gaps"), "GAP_SHAPE"):
        group = _mapping(raw, "GAP_SHAPE")
        if set(group) != {"kind", "mapping", "ids", "reason"} or group.get("mapping") != "GAP":
            _reject("GAP_SHAPE")
        kind = _text(group.get("kind"), "GAP_SHAPE")
        _text(group.get("reason"), "GAP_SHAPE")
        for raw_id in _items(group.get("ids"), "GAP_SHAPE"):
            identifier = _text(raw_id, "GAP_SHAPE")
            if identifier in mapped or identifier in gaps:
                _reject("DUPLICATE_REQUIREMENT")
            if kinds.get(identifier) != kind:
                _reject("GAP_SCOPE")
            gaps.add(identifier)
    successor = _items(index.get("successors"), "SUCCESSOR_SHAPE")
    if len(successor) != 1:
        _reject("SUCCESSOR_SHAPE")
    item = _mapping(successor[0], "SUCCESSOR_SHAPE")
    if (
        set(item) != {"id", "supersedes", "outcome", "mapping", "behavior", "reason", "binding"}
        or item.get("id") != "V3-PRECOMMIT-REJECTION"
        or item.get("supersedes") != "BDD:BDD-003"
        or item.get("outcome") != "PRECOMMIT_REJECTION"
        or item.get("mapping") != "MAPPED"
        or not _text(item.get("behavior"), "SUCCESSOR_SHAPE").startswith("BOUNDED_")
        or not _text(item.get("reason"), "SUCCESSOR_SHAPE")
    ):
        _reject("SUCCESSOR_SHAPE")
    if "BDD:BDD-003" in mapped or "BDD:BDD-003" in gaps:
        _reject("SUCCESSOR_REUSE")
    _binding(catalog, components, item.get("binding"), "V3-PRECOMMIT-REJECTION", successor=True)
    if set(kinds) != mapped | gaps | {"BDD:BDD-003"}:
        _reject("REQUIREMENT_COVERAGE")
    return gaps


def validate_index(index: JsonObject, root: Path = ROOT) -> dict[str, str]:
    if (
        set(index)
        != {
            "schema",
            "source_pins",
            "components",
            "case_catalog",
            "inventory",
            "mappings",
            "gaps",
            "successors",
            "claim_states",
            "authority",
            "nonclaims",
        }
        or index.get("schema") != SCHEMA
    ):
        _reject("INDEX_SHAPE")
    pins, raw_components, catalog = _layout(index)
    components, trusted, provisional_components = _pins(root, pins, raw_components)
    inventory = _inventory(root, pins)
    if index.get("inventory") != inventory:
        _reject("INVENTORY_DRIFT")
    provisional_cases = _cases(root, catalog, components, trusted, provisional_components)
    expected = _expected(inventory)
    gaps = _records(index, expected, catalog, components)
    state = "FULL_PREREQUISITE_BINDINGS" if not gaps and not provisional_cases else "PARTIAL"
    claims = {
        "inventory": "STRUCTURAL_ONLY",
        "mapped_tests": state,
        "behavior": "NOT_LIFECYCLE_QUALIFIED",
        "replay": "UNRECORDED",
        "full_conformance": "UNESTABLISHED",
    }
    if (
        index.get("claim_states") != claims
        or index.get("authority") != AUTHORITY
        or index.get("nonclaims") != NONCLAIMS
    ):
        _reject("CLAIM_STATE")
    return {
        "mapping": state,
        "next_unmet": next((item for item, _ in expected if item in gaps), ""),
        "case_sources": "PROVISIONAL" if provisional_cases else "PINNED",
        "provisional_cases": ",".join(sorted(provisional_cases)),
    }


def run_replay(case_id: str, root: Path = ROOT) -> None:
    result = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", *REPLAY_CASES[case_id]],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    output = result.stdout + result.stderr
    if result.returncode != 0:
        _reject("REPLAY_FAILED")
    if re.search(r"\b(?:skipped|xfailed|xpassed|failed|error|deselected)\b", output, re.IGNORECASE):
        _reject("REPLAY_NONPASS")
    if not re.search(r"\b[1-9][0-9]* passed\b", output):
        _reject("REPLAY_INCOMPLETE")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--validate", action="store_true", help="check pins and structural inventory")
    mode.add_argument("--check", action="store_true", help="require every applicable binding")
    mode.add_argument(
        "--replay", choices=tuple(REPLAY_CASES), help="run one code-owned bounded pytest case"
    )
    args = parser.parse_args(argv)
    try:
        status = validate_index(load_index(_file(ROOT, INDEX_PATH)))
        if args.replay:
            run_replay(args.replay)
            print(f"REPLAY PASSED {args.replay}; evidence remains unrecorded")
        elif args.validate:
            print(
                "VALID STRUCTURAL_INVENTORY=PASS; "
                f"CASE_SOURCES={status['case_sources']}; acceptance remains unestablished"
            )
        elif args.check and status["next_unmet"]:
            print(f"INCOMPLETE COVERAGE_GAP:{status['next_unmet']}")
            return 2
        elif args.check and status["case_sources"] != "PINNED":
            print(f"INCOMPLETE PROVISIONAL_CASE_SOURCES:{status['provisional_cases']}")
            return 2
        elif args.check:
            print("BINDING_PREREQUISITES_MET; FULL_CONFORMANCE=UNESTABLISHED")
        else:
            print("INVENTORY=STRUCTURAL_ONLY")
            print(f"MAPPED_TESTS={status['mapping']}")
            print(f"CASE_SOURCES={status['case_sources']}")
            print("REPLAY=UNRECORDED")
            print("FULL_CONFORMANCE=UNESTABLISHED")
            print(f"NEXT_UNMET=COVERAGE_GAP:{status['next_unmet']}")
    except ValueError as error:
        print(f"REJECT {error}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
