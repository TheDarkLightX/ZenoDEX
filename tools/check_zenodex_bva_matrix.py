#!/usr/bin/env python3
"""Fail-closed validator for the ZenoDEX value-moving BVA matrix."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

SCHEMA = "zenodex/value-moving-bva-matrix/v1"
VALID_STATUS = {"complete", "partial", "missing", "not_applicable"}
VALID_SOURCE_KIND = {"enum", "dataclass", "function_string_set"}
VALID_SUBJECT = {"command", "field"}


class MatrixError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise MatrixError(f"duplicate JSON key: {key}")
        out[key] = value
    return out


def _load(path: Path) -> Mapping[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_strict_object,
            parse_constant=lambda token: (_ for _ in ()).throw(
                MatrixError(f"non-finite JSON number: {token}")
            ),
        )
    except (OSError, UnicodeError, json.JSONDecodeError, MatrixError) as exc:
        raise MatrixError(f"cannot load matrix: {exc}") from exc
    if not isinstance(value, Mapping):
        raise MatrixError("matrix root must be an object")
    return value


def _keys(value: Mapping[str, Any], expected: set[str], name: str) -> None:
    if set(value) != expected:
        raise MatrixError(
            f"{name} fields mismatch: missing={sorted(expected-set(value))}, "
            f"extra={sorted(set(value)-expected)}"
        )


def _text(value: Any, name: str) -> str:
    if type(value) is not str or not value:
        raise MatrixError(f"{name} must be a non-empty string")
    return value


def _flag(value: Any, name: str) -> bool:
    if type(value) is not bool:
        raise MatrixError(f"{name} must be a bool")
    return value


def _texts(value: Any, name: str, *, empty: bool = False) -> list[str]:
    if not isinstance(value, list) or (not empty and not value):
        raise MatrixError(f"{name} must be a {'possibly empty' if empty else 'non-empty'} list")
    result: list[str] = []
    seen: set[str] = set()
    for index, raw in enumerate(value):
        item = _text(raw, f"{name}[{index}]")
        if item in seen:
            raise MatrixError(f"{name} contains duplicate {item!r}")
        seen.add(item)
        result.append(item)
    return result


def _class(tree: ast.Module, symbol: str) -> ast.ClassDef:
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == symbol:
            return node
    raise MatrixError(f"class {symbol!r} not found")


def _function(tree: ast.Module, symbol: str) -> ast.FunctionDef | ast.AsyncFunctionDef:
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == symbol:
            return node
    raise MatrixError(f"function {symbol!r} not found")


def _extract(repo: Path, source: Mapping[str, Any], name: str) -> tuple[str, list[str]]:
    _keys(source, {"kind", "path", "symbol", "subject"}, name)
    kind = _text(source.get("kind"), f"{name}.kind")
    if kind not in VALID_SOURCE_KIND:
        raise MatrixError(f"{name}.kind unsupported: {kind}")
    subject = _text(source.get("subject"), f"{name}.subject")
    if subject not in VALID_SUBJECT:
        raise MatrixError(f"{name}.subject unsupported: {subject}")
    path = _text(source.get("path"), f"{name}.path")
    symbol = _text(source.get("symbol"), f"{name}.symbol")
    source_path = repo / path
    if not source_path.is_file():
        raise MatrixError(f"{name} source missing: {path}")
    try:
        tree = ast.parse(source_path.read_text(encoding="utf-8"), filename=path)
    except (OSError, UnicodeError, SyntaxError) as exc:
        raise MatrixError(f"cannot parse {path}: {exc}") from exc

    if kind == "dataclass":
        items = [
            node.target.id
            for node in _class(tree, symbol).body
            if isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and not node.target.id.startswith("_")
            and "ClassVar" not in ast.unparse(node.annotation)
        ]
    elif kind == "enum":
        items = []
        for node in _class(tree, symbol).body:
            if isinstance(node, ast.Assign):
                items.extend(
                    target.id
                    for target in node.targets
                    if isinstance(target, ast.Name) and not target.id.startswith("_")
                )
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                if not node.target.id.startswith("_"):
                    items.append(node.target.id)
    else:
        candidates: list[tuple[str, ...]] = []
        for node in ast.walk(_function(tree, symbol)):
            if not isinstance(node, (ast.Set, ast.List, ast.Tuple)):
                continue
            values: list[str] = []
            for element in node.elts:
                if not isinstance(element, ast.Constant) or type(element.value) is not str:
                    values = []
                    break
                values.append(element.value)
            if values:
                candidates.append(tuple(values))
        if not candidates:
            raise MatrixError(f"no string collection found in {path}:{symbol}")
        max_len = max(map(len, candidates))
        largest = {values for values in candidates if len(values) == max_len}
        if len(largest) != 1:
            raise MatrixError(f"ambiguous string collection in {path}:{symbol}")
        items = list(next(iter(largest)))

    if not items or len(items) != len(set(items)):
        raise MatrixError(f"{name} extracted an empty or duplicate inventory")
    return subject, items


@dataclass(frozen=True)
class Evidence:
    path: str
    sha256: str
    commit: str
    toolchain: str
    executed: bool


@dataclass(frozen=True)
class Coverage:
    status: str
    profiles: tuple[str, ...]
    covered_cases: tuple[str, ...]
    evidence: tuple[Evidence, ...]
    note: str


def _evidence(value: Any, name: str, repo: Path, verify_files: bool) -> tuple[Evidence, ...]:
    if not isinstance(value, list):
        raise MatrixError(f"{name} must be a list")
    result: list[Evidence] = []
    for index, raw in enumerate(value):
        if not isinstance(raw, Mapping):
            raise MatrixError(f"{name}[{index}] must be an object")
        _keys(raw, {"path", "sha256", "commit", "toolchain", "executed"}, f"{name}[{index}]")
        item = Evidence(
            path=_text(raw.get("path"), f"{name}[{index}].path"),
            sha256=_text(raw.get("sha256"), f"{name}[{index}].sha256"),
            commit=_text(raw.get("commit"), f"{name}[{index}].commit"),
            toolchain=_text(raw.get("toolchain"), f"{name}[{index}].toolchain"),
            executed=_flag(raw.get("executed"), f"{name}[{index}].executed"),
        )
        if len(item.sha256) != 64 or any(c not in "0123456789abcdef" for c in item.sha256):
            raise MatrixError(f"{name}[{index}].sha256 must be lowercase SHA-256")
        if verify_files:
            evidence_path = repo / item.path
            if not evidence_path.is_file():
                raise MatrixError(f"evidence file missing: {item.path}")
            digest = hashlib.sha256(evidence_path.read_bytes()).hexdigest()
            if digest != item.sha256:
                raise MatrixError(f"evidence hash mismatch: {item.path}")
        result.append(item)
    return tuple(result)


def _coverage(value: Any, name: str, profiles: Mapping[str, tuple[str, ...]], repo: Path, verify_files: bool) -> Coverage:
    if not isinstance(value, Mapping):
        raise MatrixError(f"{name} must be an object")
    _keys(value, {"status", "profiles", "covered_cases", "evidence", "note"}, name)
    status = _text(value.get("status"), f"{name}.status")
    if status not in VALID_STATUS:
        raise MatrixError(f"{name}.status unsupported: {status}")
    profile_names = tuple(_texts(value.get("profiles"), f"{name}.profiles"))
    unknown = sorted(set(profile_names) - set(profiles))
    if unknown:
        raise MatrixError(f"{name} has unknown profiles: {unknown}")
    covered = tuple(_texts(value.get("covered_cases"), f"{name}.covered_cases", empty=True))
    required = {case for profile in profile_names for case in profiles[profile]}
    outside = sorted(set(covered) - required)
    if outside:
        raise MatrixError(f"{name} covers cases outside profiles: {outside}")
    return Coverage(
        status=status,
        profiles=profile_names,
        covered_cases=covered,
        evidence=_evidence(value.get("evidence"), f"{name}.evidence", repo, verify_files),
        note=_text(value.get("note"), f"{name}.note"),
    )


def _profiles(root: Mapping[str, Any]) -> dict[str, tuple[str, ...]]:
    raw = root.get("profiles")
    if not isinstance(raw, Mapping) or not raw:
        raise MatrixError("profiles must be a non-empty object")
    return {
        _text(name, "profile name"): tuple(_texts(cases, f"profiles.{name}"))
        for name, cases in raw.items()
    }


def _manual(value: Any, name: str) -> tuple[list[str], list[str]]:
    if not isinstance(value, Mapping):
        raise MatrixError(f"{name} must be an object")
    _keys(value, {"commands", "fields"}, name)
    return (
        _texts(value.get("commands"), f"{name}.commands", empty=True),
        _texts(value.get("fields"), f"{name}.fields", empty=True),
    )


def check(matrix: Path, repo: Path, *, promotion: bool, verify_files: bool, require_executed: bool) -> dict[str, Any]:
    errors: list[str] = []
    inventory: dict[str, dict[str, list[str]]] = {}
    try:
        root = _load(matrix)
        _keys(root, {"schema", "version", "claim_status", "profiles", "surfaces", "regressions", "nonclaims"}, "root")
        if root.get("schema") != SCHEMA or root.get("version") != 1:
            raise MatrixError("unsupported schema or version")
        claim_status = _text(root.get("claim_status"), "claim_status")
        _texts(root.get("nonclaims"), "nonclaims")
        profiles = _profiles(root)
        raw_surfaces = root.get("surfaces")
        if not isinstance(raw_surfaces, list) or not raw_surfaces:
            raise MatrixError("surfaces must be a non-empty list")
        seen_surfaces: set[str] = set()
        for index, raw in enumerate(raw_surfaces):
            name = f"surfaces[{index}]"
            if not isinstance(raw, Mapping):
                raise MatrixError(f"{name} must be an object")
            _keys(raw, {"id", "source_bound", "sources", "manual", "required_profiles", "coverage", "note"}, name)
            surface_id = _text(raw.get("id"), f"{name}.id")
            if surface_id in seen_surfaces:
                raise MatrixError(f"duplicate surface id: {surface_id}")
            seen_surfaces.add(surface_id)
            source_bound = _flag(raw.get("source_bound"), f"{name}.source_bound")
            raw_sources = raw.get("sources")
            if not isinstance(raw_sources, list):
                raise MatrixError(f"{name}.sources must be a list")
            commands: list[str] = []
            fields: list[str] = []
            for source_index, source in enumerate(raw_sources):
                if not isinstance(source, Mapping):
                    raise MatrixError(f"{name}.sources[{source_index}] must be an object")
                subject, items = _extract(repo, source, f"{name}.sources[{source_index}]")
                (commands if subject == "command" else fields).extend(items)
            manual_commands, manual_fields = _manual(raw.get("manual"), f"{name}.manual")
            commands.extend(manual_commands)
            fields.extend(manual_fields)
            if len(commands) != len(set(commands)) or len(fields) != len(set(fields)):
                raise MatrixError(f"{name} has duplicate inventory items")
            required_profiles = tuple(_texts(raw.get("required_profiles"), f"{name}.required_profiles"))
            if sorted(set(required_profiles) - set(profiles)):
                raise MatrixError(f"{name} has unknown required profiles")
            raw_coverage = raw.get("coverage")
            if not isinstance(raw_coverage, Mapping):
                raise MatrixError(f"{name}.coverage must be an object")
            coverage: dict[str, Coverage] = {}
            for key, value in raw_coverage.items():
                key_text = _text(key, f"{name}.coverage key")
                if ":" not in key_text:
                    raise MatrixError(f"{name}.coverage key must be command:<x> or field:<x>")
                subject, item = key_text.split(":", 1)
                if subject not in VALID_SUBJECT or item not in (commands if subject == "command" else fields):
                    raise MatrixError(f"{name}.coverage key not in inventory: {key_text}")
                parsed_coverage = _coverage(
                    value, f"{name}.coverage.{key_text}", profiles, repo, verify_files
                )
                if not set(parsed_coverage.profiles).issubset(required_profiles):
                    raise MatrixError(
                        f"{name}.coverage.{key_text} uses a profile not declared by the surface"
                    )
                coverage[key_text] = parsed_coverage
            inventory[surface_id] = {"commands": sorted(commands), "fields": sorted(fields)}
            for subject, items in (("command", commands), ("field", fields)):
                for item in items:
                    key = f"{subject}:{item}"
                    item_coverage = coverage.get(key)
                    if not promotion:
                        continue
                    if not source_bound:
                        errors.append(f"{surface_id}: inventory is not fully source-bound")
                    if item_coverage is None:
                        errors.append(f"{surface_id}:{key}: coverage missing")
                        continue
                    required_cases = {
                        case
                        for profile in item_coverage.profiles
                        for case in profiles[profile]
                    }
                    if item_coverage.status != "complete":
                        errors.append(f"{surface_id}:{key}: status={item_coverage.status}")
                    missing_cases = sorted(required_cases - set(item_coverage.covered_cases))
                    if missing_cases:
                        errors.append(f"{surface_id}:{key}: missing cases={missing_cases}")
                    if not item_coverage.evidence:
                        errors.append(f"{surface_id}:{key}: evidence missing")
                    if require_executed and any(not evidence.executed for evidence in item_coverage.evidence):
                        errors.append(f"{surface_id}:{key}: unexecuted evidence")
            _text(raw.get("note"), f"{name}.note")

        raw_regressions = root.get("regressions")
        if not isinstance(raw_regressions, list) or not raw_regressions:
            raise MatrixError("regressions must be a non-empty list")
        vector_seen = False
        for index, raw in enumerate(raw_regressions):
            name = f"regressions[{index}]"
            if not isinstance(raw, Mapping):
                raise MatrixError(f"{name} must be an object")
            _keys(raw, {"id", "critical", "status", "cases", "tests", "note"}, name)
            regression_id = _text(raw.get("id"), f"{name}.id")
            critical = _flag(raw.get("critical"), f"{name}.critical")
            status = _text(raw.get("status"), f"{name}.status")
            cases = _texts(raw.get("cases"), f"{name}.cases")
            tests = _texts(raw.get("tests"), f"{name}.tests")
            _text(raw.get("note"), f"{name}.note")
            if regression_id == "PERP-V3-ML-BVA-112-ORACLE-USABLE":
                vector_seen = True
                required_cases = {"oracle_unseen", "index_price_zero", "stale_by_one", "reject_is_noop"}
                required_tests = {
                    "tests/kernels/test_perp_epoch_isolated_v3_ml_bva_cases.py::test_v3_native_settlement_rejects_unusable_oracle_boundaries",
                    "tests/core/test_perp_v4_parity.py::test_v4_settlement_oracle_boundaries_match_generated_reference",
                }
                if status != "complete" or not required_cases.issubset(cases) or not required_tests.issubset(tests):
                    errors.append("vector 112 regression obligation is incomplete")
            if critical and status != "complete":
                errors.append(f"critical regression incomplete: {regression_id}")
            if verify_files:
                for selector in tests:
                    path_text, _, test_name = selector.partition("::")
                    test_path = repo / path_text
                    if not test_path.is_file() or (test_name and test_name not in test_path.read_text(encoding="utf-8")):
                        errors.append(f"regression selector missing: {selector}")
        if not vector_seen:
            errors.append("vector 112 regression sentinel missing")
        if promotion and claim_status != "complete":
            errors.append(f"claim_status={claim_status}")
    except MatrixError as exc:
        errors.append(str(exc))

    return {
        "schema": "zenodex/value-moving-bva-check/v1",
        "mode": "promotion" if promotion else "critical",
        "status": "accepted" if not errors else "blocked",
        "surface_count": len(inventory),
        "command_count": sum(len(value["commands"]) for value in inventory.values()),
        "field_count": sum(len(value["fields"]) for value in inventory.values()),
        "inventory": inventory,
        "errors": sorted(set(errors)),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--promotion", action="store_true")
    parser.add_argument("--verify-files", action="store_true")
    parser.add_argument("--require-executed-evidence", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    result = check(
        args.matrix,
        args.repo_root,
        promotion=args.promotion,
        verify_files=args.verify_files,
        require_executed=args.require_executed_evidence,
    )
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0 if result["status"] == "accepted" else 1


if __name__ == "__main__":
    raise SystemExit(main())
