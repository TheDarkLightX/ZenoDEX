#!/usr/bin/env python3
"""Check the source-level M6 value-moving writer and command coverage contract.

The inventory makes legacy writers visible and keeps them explicitly outside
the M6 authority path. A structural pass means the listed symbols still exist,
each has a closed command/lane/workflow row, all eight required release binding
dimensions are present, and no newly discovered entrypoint using the covered
names escaped the manifest. ``--require-release-ready`` fails while any row is
open. This v1 schema cannot encode release-backed bindings, so metadata edits
cannot promote it. The checker does not prove a complete deployment graph,
dynamic reachability, generated-code coverage, validator finality, or
production mounting.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = REPO_ROOT / "tools" / "m6_writer_inventory_manifest_v1.json"
SCHEMA_V1 = "zenodex/m6-writer-inventory/v1"
COVERAGE_SCHEMA_V1 = "zenodex/m6-writer-coverage/v1"
ALLOWED_MOUNT_STATUSES = frozenset(
    {"M6_RESEARCH_ONLY", "SEPARATE_RESEARCH_NOT_M6", "UNMOUNTED_LEGACY"}
)
M6_LANE_IDS: tuple[str, ...] = (
    "ASSET_TRANSFER",
    "SPOT_LIQUIDITY",
    "FARM_INCENTIVES",
    "ZDEX_TOKENOMICS",
    "ZUSD_MONETARY",
    "PERPS_MARKET",
    "ORACLE_MARKET",
    "SEALED_AUCTION",
    "STRATEGY_ESCROW",
    "PROOF_REWARDS",
    "EXTERNAL_CUSTODY",
    "GOVERNANCE_MIGRATION",
)
M6_WORKFLOW_IDS: tuple[str, ...] = tuple(f"WF-{index:02d}" for index in range(1, 19))
REQUIRED_COVERAGE_BINDINGS: tuple[str, ...] = (
    "module_release",
    "transition",
    "canonical_effect_projection",
    "proof_profile",
    "route",
    "terminal_path",
    "adapter",
    "evidence",
)
REQUIRED_ASSURANCE_STATUSES: tuple[str, ...] = (
    "SPECIFIED",
    "IMPLEMENTED",
    "PROVED",
    "MOUNTED",
    "TESTED",
    "TERMINAL_COMPLETE",
    "MIGRATABLE",
    "NO_BYPASS",
    "RELEASE_BACKED",
)
ALLOWED_BINDING_STATUSES = frozenset({"GAP", "LEGACY_ONLY", "RESEARCH_ONLY"})
ALLOWED_ASSURANCE_STATUSES = frozenset(REQUIRED_ASSURANCE_STATUSES)
COMMAND_KIND_RE = re.compile(r"[a-z0-9][a-z0-9._/-]*\Z")
NONCLAIMS: tuple[str, ...] = (
    "the inventory is source-level and initial, not a complete deployment or generated-code graph",
    "dynamic imports, subprocess-loaded writers, credentials, workers, and database callers require separate audits",
    "legacy writers remain outside the M6 commit port and are not certified by this checker",
    "the v1 coverage schema admits only GAP, LEGACY_ONLY, and RESEARCH_ONLY bindings",
    "no validator signature, RISC0 receipt, finality, durability, or production authority is created",
    "a passing result does not mount M6 or establish M6Ready",
)


@dataclass(frozen=True, slots=True)
class WriterSpec:
    entrypoint_id: str
    path: str
    symbol: str
    class_name: str | None
    kind: str
    m6_mount_status: str
    commit_port_route: str
    requires_unique_commit_port: bool
    evidence_markers: tuple[str, ...]

    @property
    def qualified_symbol(self) -> str:
        return f"{self.class_name}.{self.symbol}" if self.class_name else self.symbol

    def to_dict(self, *, line: int | None = None) -> dict[str, object]:
        result: dict[str, object] = {
            "class": self.class_name,
            "commit_port_route": self.commit_port_route,
            "entrypoint_id": self.entrypoint_id,
            "evidence_markers": list(self.evidence_markers),
            "kind": self.kind,
            "m6_mount_status": self.m6_mount_status,
            "path": self.path,
            "requires_unique_commit_port": self.requires_unique_commit_port,
            "symbol": self.symbol,
        }
        if line is not None:
            result["line"] = line
        return result


@dataclass(frozen=True, slots=True)
class CoverageBindingV1:
    reference: str | None
    status: str

    def to_dict(self) -> dict[str, str | None]:
        return {"reference": self.reference, "status": self.status}


@dataclass(frozen=True, slots=True)
class CommandCoverageV1:
    coverage_id: str
    entrypoint_id: str
    command_kind: str
    lane_ids: tuple[str, ...]
    workflow_ids: tuple[str, ...]
    bindings: tuple[tuple[str, CoverageBindingV1], ...]
    assurance_statuses: tuple[str, ...]
    release_status: str

    def binding_map(self) -> dict[str, CoverageBindingV1]:
        return dict(self.bindings)

    def to_dict(self) -> dict[str, object]:
        return {
            "assurance_statuses": list(self.assurance_statuses),
            "bindings": {
                key: binding.to_dict()
                for key, binding in self.bindings
            },
            "command_kind": self.command_kind,
            "coverage_id": self.coverage_id,
            "entrypoint_id": self.entrypoint_id,
            "lane_ids": list(self.lane_ids),
            "release_status": self.release_status,
            "workflow_ids": list(self.workflow_ids),
        }


@dataclass(frozen=True, slots=True)
class WriterInventoryV1:
    entries: tuple[WriterSpec, ...]
    coverage_rows: tuple[CommandCoverageV1, ...]


@dataclass(frozen=True, slots=True)
class WriterFinding:
    path: str
    rule_id: str
    evidence: str

    def to_dict(self) -> dict[str, str]:
        return {"evidence": self.evidence, "path": self.path, "rule_id": self.rule_id}


def _relative(path: Path, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _finding(path: Path, root: Path, rule_id: str, evidence: str) -> WriterFinding:
    return WriterFinding(path=_relative(path, root), rule_id=rule_id, evidence=evidence)


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _read_manifest_json(path: Path) -> Mapping[str, Any]:
    try:
        raw = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
        )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError(f"cannot read writer inventory manifest: {exc}") from exc
    if not isinstance(raw, Mapping):
        raise ValueError("writer inventory manifest root must be an object")
    return raw


def _require_exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    if set(value) != expected:
        missing = sorted(expected - set(value))
        surplus = sorted(set(value) - expected)
        raise ValueError(f"{label} keys mismatch: missing={missing}, surplus={surplus}")


def _require_ordered_subset(
    value: Any,
    universe: tuple[str, ...],
    *,
    label: str,
    allow_empty: bool = False,
) -> tuple[str, ...]:
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
        raise ValueError(f"{label} must be a string list")
    items = tuple(value)
    if not allow_empty and not items:
        raise ValueError(f"{label} must not be empty")
    if len(items) != len(set(items)):
        raise ValueError(f"{label} must not contain duplicates")
    unknown = sorted(set(items) - set(universe))
    if unknown:
        raise ValueError(f"{label} contains unknown values: {unknown}")
    expected_order = tuple(item for item in universe if item in set(items))
    if items != expected_order:
        raise ValueError(f"{label} is not in canonical order")
    return items


def _parse_writer_spec(entry: Any, *, index: int) -> WriterSpec:
    label = f"writer inventory entry {index}"
    if not isinstance(entry, Mapping):
        raise ValueError(f"{label} must be an object")
    _require_exact_keys(
        entry,
        {
        "class",
        "commit_port_route",
        "entrypoint_id",
        "evidence_markers",
        "kind",
        "m6_mount_status",
        "path",
        "requires_unique_commit_port",
        "symbol",
        },
        label=label,
    )
    entry_id, path_value, symbol = (entry[key] for key in ("entrypoint_id", "path", "symbol"))
    if not all(isinstance(value, str) and value for value in (entry_id, path_value, symbol)):
        raise ValueError(f"{label} has invalid identity")
    if Path(path_value).is_absolute() or ".." in Path(path_value).parts:
        raise ValueError(f"{label} path is not repository-relative")
    class_name = entry["class"]
    if class_name is not None and (not isinstance(class_name, str) or not class_name):
        raise ValueError(f"{label} has invalid class")
    markers = entry["evidence_markers"]
    if (
        not isinstance(markers, list)
        or not markers
        or any(not isinstance(marker, str) or not marker for marker in markers)
    ):
        raise ValueError(f"{label} has invalid evidence markers")
    status, route, kind = (entry[key] for key in ("m6_mount_status", "commit_port_route", "kind"))
    if not all(isinstance(value, str) and value for value in (status, route, kind)):
        raise ValueError(f"{label} has invalid classification")
    if status not in ALLOWED_MOUNT_STATUSES:
        raise ValueError(f"{label} has unauthorized mount status")
    requires_port = entry["requires_unique_commit_port"]
    if type(requires_port) is not bool:
        raise ValueError(f"{label} has invalid port requirement")
    spec = WriterSpec(
        entrypoint_id=entry_id,
        path=path_value,
        symbol=symbol,
        class_name=class_name,
        kind=kind,
        m6_mount_status=status,
        commit_port_route=route,
        requires_unique_commit_port=requires_port,
        evidence_markers=tuple(markers),
    )
    if spec.requires_unique_commit_port and status.startswith("UNMOUNTED") and route != "none":
        raise ValueError(f"unmounted writer has a commit route: {spec.entrypoint_id}")
    if status.startswith("M6_") and not route.startswith("M6CommitPortV1"):
        raise ValueError(f"M6 writer is not bound to the M6 commit port: {spec.entrypoint_id}")
    return spec


def _parse_writer_specs(raw: Mapping[str, Any]) -> tuple[WriterSpec, ...]:
    entries = raw.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("writer inventory manifest entries must be non-empty")
    specs: list[WriterSpec] = []
    seen_ids: set[str] = set()
    seen_symbols: set[tuple[str, str, str | None]] = set()
    for index, entry in enumerate(entries):
        spec = _parse_writer_spec(entry, index=index)
        identity = (spec.path, spec.symbol, spec.class_name)
        if spec.entrypoint_id in seen_ids:
            raise ValueError(f"duplicate writer inventory id: {spec.entrypoint_id}")
        if identity in seen_symbols:
            raise ValueError(f"duplicate writer inventory symbol: {spec.qualified_symbol}")
        seen_ids.add(spec.entrypoint_id)
        seen_symbols.add(identity)
        specs.append(spec)
    return tuple(specs)


def _parse_binding(value: Any, *, label: str) -> CoverageBindingV1:
    if not isinstance(value, Mapping):
        raise ValueError(f"{label} must be an object")
    _require_exact_keys(value, {"reference", "status"}, label=label)
    status = value["status"]
    reference = value["reference"]
    if status not in ALLOWED_BINDING_STATUSES:
        raise ValueError(f"{label} has unauthorized status")
    if status == "GAP":
        if reference is not None:
            raise ValueError(f"{label} GAP reference must be null")
    elif not isinstance(reference, str) or not reference:
        raise ValueError(f"{label} non-gap reference must be a nonempty string")
    return CoverageBindingV1(reference=reference, status=status)


def _coverage_contract_rows(raw: Mapping[str, Any]) -> list[Any]:
    contract = raw.get("coverage_contract")
    if not isinstance(contract, Mapping):
        raise ValueError("coverage_contract must be an object")
    _require_exact_keys(
        contract,
        {"schema", "required_bindings", "required_assurance_statuses", "rows"},
        label="coverage_contract",
    )
    if contract["schema"] != COVERAGE_SCHEMA_V1:
        raise ValueError("writer coverage contract schema mismatch")
    if contract["required_bindings"] != list(REQUIRED_COVERAGE_BINDINGS):
        raise ValueError("coverage required_bindings mismatch")
    if contract["required_assurance_statuses"] != list(REQUIRED_ASSURANCE_STATUSES):
        raise ValueError("coverage required_assurance_statuses mismatch")
    rows = contract["rows"]
    if not isinstance(rows, list) or not rows:
        raise ValueError("coverage rows must be a non-empty list")
    return rows


def _parse_coverage_bindings(
    value: Any,
    *,
    label: str,
    spec: WriterSpec,
) -> tuple[tuple[str, CoverageBindingV1], ...]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{label}.bindings must be an object")
    if set(value) != set(REQUIRED_COVERAGE_BINDINGS):
        raise ValueError(f"{label} binding keys mismatch")
    parsed = tuple(
        (name, _parse_binding(value[name], label=f"{label}.bindings.{name}"))
        for name in REQUIRED_COVERAGE_BINDINGS
    )
    adapter = dict(parsed)["adapter"]
    expected_reference = f"{spec.path}::{spec.qualified_symbol}"
    expected_status = (
        "LEGACY_ONLY" if spec.m6_mount_status == "UNMOUNTED_LEGACY" else "RESEARCH_ONLY"
    )
    if adapter.reference != expected_reference or adapter.status != expected_status:
        raise ValueError(f"{label}.bindings.adapter does not bind the inventoried writer")
    return parsed


def _parse_coverage_row(
    row: Any,
    *,
    index: int,
    specs_by_id: Mapping[str, WriterSpec],
) -> CommandCoverageV1:
    label = f"coverage rows[{index}]"
    if not isinstance(row, Mapping):
        raise ValueError(f"{label} must be an object")
    _require_exact_keys(
        row,
        {
            "assurance_statuses",
            "bindings",
            "command_kind",
            "coverage_id",
            "entrypoint_id",
            "lane_ids",
            "release_status",
            "workflow_ids",
        },
        label=label,
    )
    coverage_id, entrypoint_id, command_kind = (
        row[key] for key in ("coverage_id", "entrypoint_id", "command_kind")
    )
    if not all(isinstance(value, str) and value for value in (coverage_id, entrypoint_id, command_kind)):
        raise ValueError(f"{label} has invalid identity")
    if COMMAND_KIND_RE.fullmatch(command_kind) is None:
        raise ValueError(f"{label}.command_kind is not canonical")
    spec = specs_by_id.get(entrypoint_id)
    if spec is None:
        raise ValueError(f"{label} references unknown writer: {entrypoint_id}")
    if row["release_status"] != "OPEN":
        raise ValueError(f"{label}.release_status must remain OPEN in the research schema")
    return CommandCoverageV1(
        coverage_id=coverage_id,
        entrypoint_id=entrypoint_id,
        command_kind=command_kind,
        lane_ids=_require_ordered_subset(row["lane_ids"], M6_LANE_IDS, label=f"{label}.lane_ids"),
        workflow_ids=_require_ordered_subset(
            row["workflow_ids"], M6_WORKFLOW_IDS, label=f"{label}.workflow_ids"
        ),
        bindings=_parse_coverage_bindings(row["bindings"], label=label, spec=spec),
        assurance_statuses=_require_ordered_subset(
            row["assurance_statuses"],
            REQUIRED_ASSURANCE_STATUSES,
            label=f"{label}.assurance_statuses",
            allow_empty=True,
        ),
        release_status="OPEN",
    )


def _parse_coverage_rows(
    raw: Mapping[str, Any],
    specs: tuple[WriterSpec, ...],
) -> tuple[CommandCoverageV1, ...]:
    specs_by_id = {spec.entrypoint_id: spec for spec in specs}
    parsed = tuple(
        _parse_coverage_row(row, index=index, specs_by_id=specs_by_id)
        for index, row in enumerate(_coverage_contract_rows(raw))
    )
    coverage_ids = [row.coverage_id for row in parsed]
    if len(coverage_ids) != len(set(coverage_ids)):
        raise ValueError("coverage IDs must be unique")
    commands = [(row.entrypoint_id, row.command_kind) for row in parsed]
    if len(commands) != len(set(commands)):
        raise ValueError("writer command coverage pairs must be unique")
    covered_writer_ids = {row.entrypoint_id for row in parsed}
    missing = sorted(set(specs_by_id) - covered_writer_ids)
    if missing:
        raise ValueError(f"writer lacks command coverage: {missing}")
    return tuple(parsed)


def load_writer_inventory_manifest(path: Path) -> WriterInventoryV1:
    raw = _read_manifest_json(path)
    _require_exact_keys(
        raw,
        {"coverage_contract", "entries", "schema", "scope"},
        label="writer inventory manifest",
    )
    if raw.get("schema") != SCHEMA_V1:
        raise ValueError("writer inventory manifest schema mismatch")
    if not isinstance(raw.get("scope"), str) or not raw["scope"].strip():
        raise ValueError("writer inventory scope must be a nonempty string")
    specs = _parse_writer_specs(raw)
    coverage_rows = _parse_coverage_rows(raw, specs)
    return WriterInventoryV1(entries=specs, coverage_rows=coverage_rows)


def _load_manifest(path: Path) -> tuple[WriterSpec, ...]:
    return load_writer_inventory_manifest(path).entries


def _definitions(tree: ast.AST) -> dict[str, tuple[ast.AST, ...]]:
    definitions: dict[str, list[ast.AST]] = {}

    def add(name: str, node: ast.AST) -> None:
        definitions.setdefault(name, []).append(node)

    for node in getattr(tree, "body", ()):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            add(node.name, node)
        elif isinstance(node, ast.ClassDef):
            for child in node.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    add(f"{node.name}.{child.name}", child)
    return {name: tuple(nodes) for name, nodes in definitions.items()}


def _source_tokens(node: ast.AST) -> frozenset[str]:
    tokens: set[str] = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Name):
            tokens.add(child.id)
        elif isinstance(child, ast.Attribute):
            tokens.add(child.attr)
        elif isinstance(child, ast.Constant) and isinstance(child.value, str):
            tokens.add(child.value)
    return frozenset(tokens)


def _parse_tree(path: Path, root: Path) -> tuple[ast.Module | None, list[WriterFinding]]:
    try:
        source = path.read_text(encoding="utf-8")
    except OSError as exc:
        return None, [_finding(path, root, "source_read_error", str(exc))]
    try:
        return ast.parse(source, filename=str(path)), []
    except SyntaxError as exc:
        return None, [_finding(path, root, "source_parse_error", str(exc))]


def scan_writer_spec(spec: WriterSpec, *, root: Path = REPO_ROOT) -> tuple[WriterFinding, ...]:
    """Check one manifest entry; exposed for targeted mutation tests."""

    root = root.resolve()
    path = root / spec.path
    tree, findings = _parse_tree(path, root)
    if tree is None:
        return tuple(findings)
    definitions = _definitions(tree)
    nodes = definitions.get(spec.qualified_symbol, ())
    if not nodes:
        findings.append(_finding(path, root, "inventory_symbol_missing", spec.qualified_symbol))
        return tuple(findings)
    if len(nodes) != 1:
        findings.append(_finding(path, root, "inventory_symbol_duplicated", spec.qualified_symbol))
        return tuple(findings)
    tokens = set(_source_tokens(nodes[0]))
    tokens.add(spec.symbol)
    if spec.class_name:
        tokens.add(spec.class_name)
    missing_markers = sorted(marker for marker in spec.evidence_markers if marker not in tokens)
    if missing_markers:
        findings.append(_finding(path, root, "writer_evidence_marker_missing", ",".join(missing_markers)))
    if spec.m6_mount_status.startswith("UNMOUNTED") and spec.commit_port_route != "none":
        findings.append(_finding(path, root, "unmounted_writer_has_route", spec.commit_port_route))
    return tuple(findings)


def _python_files(root: Path) -> tuple[Path, ...]:
    source_root = root / "src"
    if not source_root.is_dir():
        return ()
    return tuple(sorted(path for path in source_root.rglob("*.py") if path.is_file()))


def scan_unregistered_value_writers(
    root: Path = REPO_ROOT,
    *,
    specs: tuple[WriterSpec, ...] | None = None,
) -> tuple[WriterFinding, ...]:
    """Find covered writer names defined outside the manifest."""

    root = root.resolve()
    effective_specs = specs if specs is not None else _load_manifest(MANIFEST_PATH)
    registered = {(spec.path, spec.qualified_symbol) for spec in effective_specs}
    function_names = {spec.symbol for spec in effective_specs if spec.class_name is None}
    class_names = {spec.class_name for spec in effective_specs if spec.class_name is not None}
    method_names = {
        spec.symbol for spec in effective_specs if spec.class_name is not None
    }
    findings: list[WriterFinding] = []
    for path in _python_files(root):
        tree, parse_findings = _parse_tree(path, root)
        findings.extend(parse_findings)
        if tree is None:
            continue
        for node in getattr(tree, "body", ()):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in function_names:
                identity = (_relative(path, root), node.name)
                if identity not in registered:
                    findings.append(_finding(path, root, "unregistered_value_writer", node.name))
            if isinstance(node, ast.ClassDef) and node.name in class_names:
                for child in node.body:
                    if (
                        isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                        and child.name in method_names
                    ):
                        identity = (_relative(path, root), f"{node.name}.{child.name}")
                        if identity not in registered:
                            findings.append(
                                _finding(path, root, "unregistered_value_writer", f"{node.name}.{child.name}")
                            )
    return tuple(findings)


def _render_writer_entry(spec: WriterSpec, *, root: Path) -> dict[str, object]:
    path = root / spec.path
    tree, _parse_findings = _parse_tree(path, root)
    line: int | None = None
    if tree is not None:
        nodes = _definitions(tree).get(spec.qualified_symbol, ())
        if len(nodes) == 1:
            line = getattr(nodes[0], "lineno", None)
    return spec.to_dict(line=line)


def _release_gap(row: CommandCoverageV1) -> dict[str, object]:
    return {
        "assurance_gaps": [
            status for status in REQUIRED_ASSURANCE_STATUSES if status not in row.assurance_statuses
        ],
        "binding_gaps": [
            name for name, binding in row.bindings if binding.status != "RELEASE_BACKED"
        ],
        "command_kind": row.command_kind,
        "coverage_id": row.coverage_id,
        "entrypoint_id": row.entrypoint_id,
        "release_status": row.release_status,
    }


def check_m6_writer_inventory(root: Path = REPO_ROOT) -> dict[str, object]:
    """Return a deterministic inventory report without granting authority."""

    root = root.resolve()
    manifest_path = root / "tools" / MANIFEST_PATH.name
    findings: list[WriterFinding] = []
    try:
        inventory = load_writer_inventory_manifest(manifest_path)
        specs = inventory.entries
        coverage_rows = inventory.coverage_rows
    except ValueError as exc:
        specs = ()
        coverage_rows = ()
        findings.append(_finding(manifest_path, root, "manifest_invalid", str(exc)))
    for spec in specs:
        findings.extend(scan_writer_spec(spec, root=root))
    if specs:
        findings.extend(scan_unregistered_value_writers(root, specs=specs))
    findings = sorted(findings, key=lambda item: (item.path, item.rule_id, item.evidence))
    entries = [_render_writer_entry(spec, root=root) for spec in specs]
    covered_writer_ids = {row.entrypoint_id for row in coverage_rows}
    writers_without_coverage = sorted(
        spec.entrypoint_id for spec in specs if spec.entrypoint_id not in covered_writer_ids
    )
    release_gaps = [_release_gap(row) for row in coverage_rows]
    release_ready = bool(coverage_rows) and not findings and not release_gaps
    return {
        "coverage_row_count": len(coverage_rows),
        "coverage_rows": [row.to_dict() for row in coverage_rows],
        "entrypoint_count": len(entries),
        "entrypoints": entries,
        "findings": [finding.to_dict() for finding in findings],
        "m6_production_mounted": False,
        "nonclaims": list(NONCLAIMS),
        "open_coverage_count": sum(
            1 for row in coverage_rows if row.release_status == "OPEN"
        ),
        "production_authority": False,
        "release_gaps": release_gaps,
        "release_gate_status": (
            "RELEASE_READY" if release_ready else "BLOCKED_OPEN_COVERAGE"
        ),
        "release_ready": release_ready,
        "required_assurance_statuses": list(REQUIRED_ASSURANCE_STATUSES),
        "required_coverage_bindings": list(REQUIRED_COVERAGE_BINDINGS),
        "schema": SCHEMA_V1,
        "unmounted_entrypoint_count": sum(
            1 for entry in entries if str(entry["m6_mount_status"]).startswith("UNMOUNTED")
        ),
        "writers_without_coverage": writers_without_coverage,
        "ok": not findings,
    }


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--require-release-ready",
        action="store_true",
        help="fail until every writer command row is release-backed; v1 remains research-only",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    report = check_m6_writer_inventory(args.root)
    gate_ok = report["ok"] is True and (
        not args.require_release_ready or report["release_ready"] is True
    )
    if args.json or not gate_ok:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            "M6 writer inventory ok; "
            f"{report['open_coverage_count']} command rows remain release-blocking"
        )
    return 0 if gate_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
