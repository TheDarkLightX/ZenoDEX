#!/usr/bin/env python3
"""Build the source-derived FCIS M5-P4A mount ledger.

The ledger records exactly what the final-mount structural checker inspected,
maps every reported violation once, and preserves unresolved reachability as a
blocker.  Static imports and call syntax are useful evidence, but are not
misrepresented as a complete Python runtime call graph.
"""

# ruff: noqa: E402 -- the executable tool must add the repository root before src imports

from __future__ import annotations

import ast
import hashlib
import importlib.util
import json
import subprocess
import sys
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.state.canonical import canonical_json_bytes

_REPORT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_MOUNT_CALL_GRAPH_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-mount-call-graph/v1"
_REVIEWED_START_SHA = "c344bac741c1d4a15511b77f8e2b60f93260a449"
_AUTHORITY_CHECKER = "tools/check_fcis_authority_snapshot_contract.py"
_MOUNT_ROOTS = ("src/core/dex.py", "src/integration/fcis_spot_shadow.py")
_CLOSED_STATUSES = frozenset(
    {
        "EXACT_READY",
        "MIGRATE_IN_P4B",
        "LEGACY_DIFFERENTIAL_ONLY",
        "P5_GATE_REQUIRED",
        "BLOCKER",
        "UNKNOWN",
    }
)


class DuplicateJsonKey(ValueError):
    """Raised when a supposedly canonical JSON object repeats a key."""


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateJsonKey(key)
        result[key] = value
    return result


def _strict_json(raw: str) -> dict[str, object]:
    value = json.loads(raw, object_pairs_hook=_strict_object)
    if type(value) is not dict:
        raise ValueError("authority checker output must be an object")
    return cast(dict[str, object], value)


def _sha256_bytes(raw: bytes) -> str:
    return "0x" + hashlib.sha256(raw).hexdigest()


def _source_sha(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _artifact_bytes(value: dict[str, object]) -> bytes:
    payload = dict(value)
    payload.pop("artifact_sha256", None)
    return canonical_json_bytes(payload)


def _with_artifact_hash(value: dict[str, object]) -> dict[str, object]:
    result = dict(value)
    result["artifact_sha256"] = _sha256_bytes(_artifact_bytes(result))
    return result


def _run_authority_checker() -> dict[str, object]:
    result = subprocess.run(
        [
            sys.executable,
            str(_REPO_ROOT / _AUTHORITY_CHECKER),
            "--profile",
            "final-mount",
            "--json",
        ],
        cwd=_REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    if result.returncode not in {0, 1}:
        raise RuntimeError(
            "final-mount checker escaped its declared result protocol: "
            f"returncode={result.returncode}, stderr={result.stderr.strip()}"
        )
    checker = _strict_json(result.stdout)
    if checker.get("schema") != "zenodex/fcis-authority-snapshot-contract-check/v1":
        raise ValueError("unexpected authority checker schema")
    if checker.get("profile") != "final-mount":
        raise ValueError("authority checker did not execute final-mount profile")
    return checker


@dataclass(frozen=True, slots=True)
class Definition:
    symbol: str
    kind: str
    line: int
    end_line: int


@dataclass(frozen=True, slots=True)
class ImportEdge:
    source: str
    target: str
    line: int


def _module_name(path_str: str) -> str:
    return path_str.removesuffix(".py").replace("/", ".")


def _module_path(module: str) -> str | None:
    if not module.startswith("src."):
        return None
    candidate = module.replace(".", "/") + ".py"
    if (_REPO_ROOT / candidate).is_file():
        return candidate
    package = module.replace(".", "/") + "/__init__.py"
    if (_REPO_ROOT / package).is_file():
        return package
    return None


def _resolved_import_module(path_str: str, node: ast.ImportFrom) -> str | None:
    module = node.module or ""
    if node.level == 0:
        return module
    package = _module_name(path_str).rsplit(".", 1)[0]
    relative = "." * node.level + module
    try:
        return importlib.util.resolve_name(relative, package)
    except ImportError:
        return None


def _definitions(tree: ast.AST) -> tuple[Definition, ...]:
    rows: list[Definition] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            kind = "class" if isinstance(node, ast.ClassDef) else "function"
            rows.append(
                Definition(
                    symbol=node.name,
                    kind=kind,
                    line=node.lineno,
                    end_line=node.end_lineno or node.lineno,
                )
            )
    return tuple(sorted(rows, key=lambda row: (row.line, row.end_line, row.symbol)))


def _enclosing_symbol(definitions: tuple[Definition, ...], line: int) -> str:
    matches = [row for row in definitions if row.line <= line <= row.end_line]
    if not matches:
        return "<module>"
    return min(matches, key=lambda row: (row.end_line - row.line, -row.line)).symbol


def _call_name(node: ast.Call) -> str:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        parts = [func.attr]
        value = func.value
        while isinstance(value, ast.Attribute):
            parts.append(value.attr)
            value = value.value
        if isinstance(value, ast.Name):
            parts.append(value.id)
        return ".".join(reversed(parts))
    return "<dynamic-call>"


def _source_index(
    checked_paths: tuple[str, ...],
) -> tuple[list[dict[str, object]], list[ImportEdge]]:
    rows: list[dict[str, object]] = []
    edges: list[ImportEdge] = []
    for path_str in checked_paths:
        path = _REPO_ROOT / path_str
        raw = path.read_bytes()
        tree = ast.parse(raw, filename=path_str)
        definitions = _definitions(tree)
        imports: set[str] = set()
        calls: list[dict[str, object]] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    target = _module_path(alias.name)
                    if target is not None:
                        imports.add(target)
                        edges.append(ImportEdge(path_str, target, node.lineno))
            elif isinstance(node, ast.ImportFrom):
                module = _resolved_import_module(path_str, node)
                target = _module_path(module) if module is not None else None
                if target is not None:
                    imports.add(target)
                    edges.append(ImportEdge(path_str, target, node.lineno))
            elif isinstance(node, ast.Call):
                calls.append(
                    {
                        "caller": _enclosing_symbol(definitions, node.lineno),
                        "callee_expression": _call_name(node),
                        "line": node.lineno,
                    }
                )
        rows.append(
            {
                "path": path_str,
                "source_sha256": _sha256_bytes(raw),
                "definitions": [
                    {
                        "symbol": row.symbol,
                        "kind": row.kind,
                        "line": row.line,
                        "end_line": row.end_line,
                    }
                    for row in definitions
                ],
                "local_imports": sorted(imports),
                "call_sites": sorted(
                    calls,
                    key=lambda row: (
                        cast(int, row["line"]),
                        cast(str, row["caller"]),
                        cast(str, row["callee_expression"]),
                    ),
                ),
            }
        )
    unique_edges = sorted(set(edges), key=lambda edge: (edge.source, edge.target, edge.line))
    return rows, unique_edges


def _reachable_paths(edges: list[ImportEdge]) -> dict[str, tuple[str, ...]]:
    adjacency: dict[str, set[str]] = defaultdict(set)
    for edge in edges:
        adjacency[edge.source].add(edge.target)
    witnesses: dict[str, tuple[str, ...]] = {}
    queue: deque[tuple[str, tuple[str, ...]]] = deque()
    for root in _MOUNT_ROOTS:
        if (_REPO_ROOT / root).is_file():
            queue.append((root, (root,)))
    while queue:
        current, witness = queue.popleft()
        if current in witnesses:
            continue
        witnesses[current] = witness
        for target in sorted(adjacency.get(current, set())):
            queue.append((target, (*witness, target)))
    return witnesses


def _role_for(path: str) -> str:
    if path == "src/core/dex.py":
        return "mounted_transition_orchestration"
    if path == "src/core/route_settlement.py":
        return "candidate_settlement_construction"
    if path == "src/core/settlement_strong_validator.py":
        return "settlement_validation_and_effect_derivation"
    if path == "src/state/legacy_state_snapshots.py":
        return "legacy_authority_snapshot_admission"
    if path == "src/state/support_root.py":
        return "support_commitment_derivation"
    return "final_mount_profile_surface"


def _authority_type_for(path: str) -> str:
    if path == "src/core/dex.py":
        return "DexState|Intent|Settlement|DexEffects"
    if "settlement" in path:
        return "Settlement|SettlementEffects"
    if path == "src/state/legacy_state_snapshots.py":
        return "CommittedDexStateLegacySnapshot"
    if path == "src/state/support_root.py":
        return "SupportRootV5Preimage"
    return "FinalMountAuthoritySurface"


def _disposition_for(path: str, code: str) -> str:
    if path == "src/state/legacy_state_snapshots.py":
        return "remove legacy snapshot mechanism from mounted authority graph"
    if path == "src/state/support_root.py":
        return "replace broad support-root coercion with exact owned v5 inputs"
    if path == "src/core/route_settlement.py":
        return "admit exact owned route and settlement values before evaluation"
    if path == "src/core/settlement_strong_validator.py":
        return "remove broad/coercive settlement admission from authority path"
    if path == "src/core/dex.py":
        return "replace open mounted boundary types with phase-specific owned values"
    return f"retire {code} before authority switch"


def _checked_paths(checker: dict[str, object]) -> tuple[str, ...]:
    raw = checker.get("checked_paths")
    if type(raw) is not list or any(type(item) is not str for item in raw):
        raise ValueError("authority checker checked_paths is malformed")
    paths = tuple(cast(list[str], raw))
    if tuple(sorted(set(paths))) != paths:
        raise ValueError("authority checker checked_paths must be sorted and unique")
    for path in paths:
        if not (_REPO_ROOT / path).is_file():
            raise ValueError(f"authority checker declared missing source: {path}")
    return paths


def _violations(checker: dict[str, object]) -> tuple[dict[str, object], ...]:
    raw = checker.get("violations")
    if type(raw) is not list or any(type(item) is not dict for item in raw):
        raise ValueError("authority checker violations is malformed")
    rows = tuple(cast(list[dict[str, object]], raw))
    required = {"code", "column", "detail", "line", "path"}
    for row in rows:
        if set(row) != required:
            raise ValueError("authority checker violation fields changed")
        if type(row["code"]) is not str or type(row["path"]) is not str:
            raise ValueError("authority checker violation identity is malformed")
        if type(row["line"]) is not int or type(row["column"]) is not int:
            raise ValueError("authority checker violation location is malformed")
        if type(row["detail"]) is not str:
            raise ValueError("authority checker violation detail is malformed")
    return rows


def _violation_rows(
    violations: tuple[dict[str, object], ...],
    source_rows: list[dict[str, object]],
    reachability: dict[str, tuple[str, ...]],
) -> list[dict[str, object]]:
    definitions_by_path: dict[str, tuple[Definition, ...]] = {}
    for source in source_rows:
        path = cast(str, source["path"])
        definitions_by_path[path] = tuple(
            Definition(
                symbol=cast(str, row["symbol"]),
                kind=cast(str, row["kind"]),
                line=cast(int, row["line"]),
                end_line=cast(int, row["end_line"]),
            )
            for row in cast(list[dict[str, object]], source["definitions"])
        )
    rows: list[dict[str, object]] = []
    identities: set[str] = set()
    for violation in violations:
        path = cast(str, violation["path"])
        line = cast(int, violation["line"])
        column = cast(int, violation["column"])
        code = cast(str, violation["code"])
        detail = cast(str, violation["detail"])
        identity_preimage = f"{path}:{line}:{column}:{code}:{detail}".encode()
        violation_id = _sha256_bytes(identity_preimage)
        if violation_id in identities:
            raise ValueError("duplicate final-mount violation identity")
        identities.add(violation_id)
        witness = reachability.get(path)
        rows.append(
            {
                "violation_id": violation_id,
                "path": path,
                "symbol": _enclosing_symbol(definitions_by_path[path], line),
                "line": line,
                "column": column,
                "checker_code": code,
                "checker_detail": detail,
                "authority_value_type": _authority_type_for(path),
                "read_write_effect_role": _role_for(path),
                "mounted_reachability_evidence": (
                    {
                        "status": "STATIC_IMPORT_WITNESS",
                        "path": list(witness),
                    }
                    if witness is not None
                    else {
                        "status": "UNRESOLVED",
                        "path": [],
                    }
                ),
                "current_mechanism": f"{code}:{detail}",
                "p4b_disposition": _disposition_for(path, code),
                "owner": "M5-P4B",
                "verification_evidence": [],
                "status": "BLOCKER",
            }
        )
    return sorted(
        rows,
        key=lambda row: (
            cast(str, row["path"]),
            cast(int, row["line"]),
            cast(int, row["column"]),
            cast(str, row["checker_code"]),
        ),
    )


def build_mount_call_graph_v1() -> dict[str, object]:
    checker = _run_authority_checker()
    paths = _checked_paths(checker)
    violations = _violations(checker)
    source_rows, edges = _source_index(paths)
    reachability = _reachable_paths(edges)
    for source in source_rows:
        path = cast(str, source["path"])
        witness = reachability.get(path)
        source["source_role"] = _role_for(path)
        source["mounted_reachability_evidence"] = (
            {
                "status": "STATIC_IMPORT_WITNESS",
                "path": list(witness),
            }
            if witness is not None
            else {"status": "UNRESOLVED", "path": []}
        )
    violation_rows = _violation_rows(violations, source_rows, reachability)
    statuses = Counter(cast(str, row["status"]) for row in violation_rows)
    if not set(statuses).issubset(_CLOSED_STATUSES):
        raise AssertionError("builder emitted an unknown mount status")
    checker_source = _REPO_ROOT / _AUTHORITY_CHECKER
    generator_source = Path(__file__).resolve()
    artifact: dict[str, object] = {
        "schema": _SCHEMA,
        "reviewed_start_sha": _REVIEWED_START_SHA,
        "authority_profile": "final-mount",
        "derivation": {
            "authority_checker_path": _AUTHORITY_CHECKER,
            "authority_checker_sha256": _source_sha(checker_source),
            "generator_path": generator_source.relative_to(_REPO_ROOT).as_posix(),
            "generator_sha256": _source_sha(generator_source),
        },
        "checker_result": {
            "ok": checker.get("ok"),
            "checked_path_count": len(paths),
            "violation_count": len(violations),
        },
        "mount_roots": list(_MOUNT_ROOTS),
        "closed_statuses": sorted(_CLOSED_STATUSES),
        "source_rows": source_rows,
        "syntax_edges": [
            {
                "source": edge.source,
                "target": edge.target,
                "line": edge.line,
                "evidence_kind": "STATIC_IMPORT_ONLY",
            }
            for edge in edges
        ],
        "violation_rows": violation_rows,
        "status_counts": dict(sorted(statuses.items())),
        "violation_counts_by_code": dict(
            sorted(Counter(cast(str, row["checker_code"]) for row in violation_rows).items())
        ),
        "violation_counts_by_path": dict(
            sorted(Counter(cast(str, row["path"]) for row in violation_rows).items())
        ),
        "ready_for_mount": len(violation_rows) == 0,
        "graph_completeness": "STATIC_IMPORT_AND_CALL_SYNTAX_ONLY",
        "nonclaims": [
            "Static import and call syntax is not a complete Python runtime call graph.",
            "Unresolved reachability is not evidence that a surface is unmounted.",
            "Every checker violation remains a blocker until replacement evidence is reviewed.",
        ],
    }
    return _with_artifact_hash(artifact)


def _write(artifact: dict[str, object]) -> None:
    _REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    _REPORT_PATH.write_bytes(canonical_json_bytes(artifact))


def main() -> int:
    artifact = build_mount_call_graph_v1()
    expected = canonical_json_bytes(artifact)
    if "--check" in sys.argv:
        if not _REPORT_PATH.is_file():
            print(f"ERROR: missing {_REPORT_PATH.relative_to(_REPO_ROOT)}", file=sys.stderr)
            return 1
        if _REPORT_PATH.read_bytes() != expected:
            print("ERROR: mount call-graph artifact is stale", file=sys.stderr)
            return 1
        print(
            "OK: mount call-graph artifact is current "
            f"(violations={len(cast(list[object], artifact['violation_rows']))})"
        )
        return 0
    _write(artifact)
    print(
        f"OK: wrote {_REPORT_PATH.relative_to(_REPO_ROOT)} "
        f"(ready={artifact['ready_for_mount']}, "
        f"violations={len(cast(list[object], artifact['violation_rows']))})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
