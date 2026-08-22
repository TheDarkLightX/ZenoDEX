#!/usr/bin/env python3
"""Inventory Python persistence and publication sinks relevant to M6 value safety.

This source-level checker discovers sinks from operations rather than function
names.  V1 recognizes direct ``os.replace`` calls, literal SQL DML passed to
``execute``/``executemany``, and direct ``self._state`` assignments.  Every
observation must have one closed manifest classification with an exact
occurrence count.  The checker does not establish call-graph reachability,
cross-language completeness, durable finality, or production authority.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

if __package__:
    from tools.check_m6_writer_inventory import load_writer_inventory_manifest
else:
    from check_m6_writer_inventory import load_writer_inventory_manifest

REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = REPO_ROOT / "tools" / "m6_value_sink_manifest_v1.json"
SCHEMA_V1 = "zenodex/m6-value-sink-inventory/v1"
SINK_KINDS = frozenset({"OS_REPLACE", "SQL_DML", "STATE_ATTRIBUTE_ASSIGN"})
CLASSIFICATIONS = frozenset(
    {
        "ADVISORY_CONTROL_STATE",
        "AUTHORITY_CONTROL_STATE",
        "DURABLE_EXTERNAL_EFFECT_STATE",
        "DURABLE_VALUE_STATE",
        "INITIALIZATION_STATE",
        "PUBLICATION_STATE",
    }
)
AUTHORITY_STATUSES = frozenset(
    {"M6_RESEARCH_ONLY", "NON_AUTHORITATIVE", "UNMOUNTED_LEGACY"}
)
SQL_DML_RE = re.compile(r"\s*(?:INSERT|UPDATE|DELETE|REPLACE)\b", re.IGNORECASE)
NONCLAIMS: tuple[str, ...] = (
    "the scan is source-level and limited to Python direct sinks recognized by schema v1",
    "dynamic SQL, ORM mutations, native extensions, Rust, Tau, shell, generated code, and deployment wiring require separate inventories",
    "a classified sink may still be unreachable, unsafe, or outside the unique commit port",
    "the manifest records research classifications and contains no release-backed authority",
    "a passing result does not establish complete mediation, durability, finality, or safe value movement",
)


@dataclass(frozen=True, slots=True, order=True)
class ValueSinkObservationV1:
    path: str
    symbol: str
    sink_kind: str

    def identity(self) -> tuple[str, str, str]:
        return (self.path, self.symbol, self.sink_kind)


@dataclass(frozen=True, slots=True)
class ValueSinkSpecV1:
    sink_id: str
    path: str
    symbol: str
    sink_kind: str
    occurrence_count: int
    classification: str
    authority_status: str
    writer_entrypoint_ids: tuple[str, ...]
    release_binding: None
    rationale: str

    def identity(self) -> tuple[str, str, str]:
        return (self.path, self.symbol, self.sink_kind)

    def to_dict(self) -> dict[str, object]:
        return {
            "authority_status": self.authority_status,
            "classification": self.classification,
            "occurrence_count": self.occurrence_count,
            "path": self.path,
            "rationale": self.rationale,
            "release_binding": self.release_binding,
            "sink_id": self.sink_id,
            "sink_kind": self.sink_kind,
            "symbol": self.symbol,
            "writer_entrypoint_ids": list(self.writer_entrypoint_ids),
        }


@dataclass(frozen=True, slots=True, order=True)
class SinkFindingV1:
    path: str
    rule_id: str
    evidence: str

    def to_dict(self) -> dict[str, str]:
        return {"evidence": self.evidence, "path": self.path, "rule_id": self.rule_id}


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _require_exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    if set(value) != expected:
        missing = sorted(expected - set(value))
        surplus = sorted(set(value) - expected)
        raise ValueError(f"{label} keys mismatch: missing={missing}, surplus={surplus}")


def _parse_spec(value: Any, *, index: int) -> ValueSinkSpecV1:
    label = f"sink entries[{index}]"
    if not isinstance(value, Mapping):
        raise ValueError(f"{label} must be an object")
    _require_exact_keys(
        value,
        {
            "authority_status",
            "classification",
            "occurrence_count",
            "path",
            "rationale",
            "release_binding",
            "sink_id",
            "sink_kind",
            "symbol",
            "writer_entrypoint_ids",
        },
        label=label,
    )
    string_fields = ("sink_id", "path", "symbol", "sink_kind", "classification", "authority_status", "rationale")
    if any(not isinstance(value[name], str) or not value[name] for name in string_fields):
        raise ValueError(f"{label} has an invalid string field")
    path = Path(value["path"])
    if path.is_absolute() or ".." in path.parts or path.suffix != ".py":
        raise ValueError(f"{label}.path must be a repository-relative Python path")
    if value["sink_kind"] not in SINK_KINDS:
        raise ValueError(f"{label}.sink_kind is unknown")
    if value["classification"] not in CLASSIFICATIONS:
        raise ValueError(f"{label}.classification is unknown")
    if value["authority_status"] not in AUTHORITY_STATUSES:
        raise ValueError(f"{label}.authority_status is unknown")
    if type(value["occurrence_count"]) is not int or value["occurrence_count"] <= 0:
        raise ValueError(f"{label}.occurrence_count must be a positive exact integer")
    writer_ids = value["writer_entrypoint_ids"]
    if (
        not isinstance(writer_ids, list)
        or any(not isinstance(item, str) or not item for item in writer_ids)
        or len(writer_ids) != len(set(writer_ids))
        or writer_ids != sorted(writer_ids)
    ):
        raise ValueError(f"{label}.writer_entrypoint_ids must be a unique sorted string list")
    if value["release_binding"] is not None:
        raise ValueError(f"{label}.release_binding must remain null in research schema v1")
    if value["authority_status"] == "NON_AUTHORITATIVE" and value["classification"] != "ADVISORY_CONTROL_STATE":
        raise ValueError(f"{label} uses NON_AUTHORITATIVE outside advisory control state")
    return ValueSinkSpecV1(
        sink_id=value["sink_id"],
        path=value["path"],
        symbol=value["symbol"],
        sink_kind=value["sink_kind"],
        occurrence_count=value["occurrence_count"],
        classification=value["classification"],
        authority_status=value["authority_status"],
        writer_entrypoint_ids=tuple(writer_ids),
        release_binding=None,
        rationale=value["rationale"],
    )


def load_value_sink_manifest_v1(path: Path = MANIFEST_PATH) -> tuple[ValueSinkSpecV1, ...]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError(f"cannot read value sink manifest: {exc}") from exc
    if not isinstance(raw, Mapping):
        raise ValueError("value sink manifest root must be an object")
    _require_exact_keys(raw, {"entries", "schema", "scope"}, label="value sink manifest")
    if raw["schema"] != SCHEMA_V1:
        raise ValueError("value sink manifest schema mismatch")
    if not isinstance(raw["scope"], str) or not raw["scope"].strip():
        raise ValueError("value sink manifest scope must be nonempty")
    entries = raw["entries"]
    if not isinstance(entries, list) or not entries:
        raise ValueError("value sink manifest entries must be nonempty")
    specs = tuple(_parse_spec(entry, index=index) for index, entry in enumerate(entries))
    ids = [spec.sink_id for spec in specs]
    identities = [spec.identity() for spec in specs]
    if len(ids) != len(set(ids)):
        raise ValueError("value sink IDs must be unique")
    if len(identities) != len(set(identities)):
        raise ValueError("value sink identities must be unique")
    if identities != sorted(identities):
        raise ValueError("value sink entries must use canonical identity order")
    return specs


def _python_files(root: Path) -> tuple[Path, ...]:
    source_root = root / "src"
    if not source_root.is_dir():
        return ()
    return tuple(sorted(path for path in source_root.rglob("*.py") if path.is_file()))


def _literal_sql(call: ast.Call) -> str | None:
    if not call.args:
        return None
    value = call.args[0]
    return value.value if isinstance(value, ast.Constant) and isinstance(value.value, str) else None


class _SinkVisitor(ast.NodeVisitor):
    def __init__(
        self,
        *,
        path: str,
        os_names: frozenset[str],
        replace_names: frozenset[str],
        detect_state_assignment: bool,
    ) -> None:
        self._path = path
        self._os_names = os_names
        self._replace_names = replace_names
        self._detect_state_assignment = detect_state_assignment
        self._classes: list[str] = []
        self._functions: list[str] = []
        self.observations: list[ValueSinkObservationV1] = []

    def _symbol(self) -> str:
        names = [*self._classes, *self._functions]
        return ".".join(names) if names else "<module>"

    def _add(self, kind: str) -> None:
        self.observations.append(ValueSinkObservationV1(self._path, self._symbol(), kind))

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._classes.append(node.name)
        self.generic_visit(node)
        self._classes.pop()

    def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
        self._functions.append(node.name)
        self.generic_visit(node)
        self._functions.pop()

    visit_FunctionDef = _visit_function
    visit_AsyncFunctionDef = _visit_function

    def visit_Call(self, node: ast.Call) -> None:
        is_os_replace = (
            isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in self._os_names
            and node.func.attr == "replace"
        ) or (isinstance(node.func, ast.Name) and node.func.id in self._replace_names)
        if is_os_replace:
            self._add("OS_REPLACE")
        if (
            isinstance(node.func, ast.Attribute)
            and node.func.attr in {"execute", "executemany"}
            and (sql := _literal_sql(node)) is not None
            and SQL_DML_RE.match(sql) is not None
        ):
            self._add("SQL_DML")
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        if self._detect_state_assignment and any(
            _is_self_state_attribute(target) for target in node.targets
        ):
            self._add("STATE_ATTRIBUTE_ASSIGN")
        self.generic_visit(node)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if self._detect_state_assignment and _is_self_state_attribute(node.target):
            self._add("STATE_ATTRIBUTE_ASSIGN")
        self.generic_visit(node)


def _is_self_state_attribute(node: ast.AST) -> bool:
    return (
        isinstance(node, ast.Attribute)
        and isinstance(node.value, ast.Name)
        and node.value.id == "self"
        and node.attr == "_state"
    )


def _import_aliases(tree: ast.Module) -> tuple[frozenset[str], frozenset[str]]:
    os_names: set[str] = set()
    replace_names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            os_names.update(
                alias.asname or "os" for alias in node.names if alias.name == "os"
            )
        elif isinstance(node, ast.ImportFrom) and node.module == "os":
            replace_names.update(
                alias.asname or "replace"
                for alias in node.names
                if alias.name == "replace"
            )
    return frozenset(os_names), frozenset(replace_names)


def scan_python_value_sinks_v1(root: Path = REPO_ROOT) -> tuple[ValueSinkObservationV1, ...]:
    root = root.resolve()
    observations: list[ValueSinkObservationV1] = []
    for path in _python_files(root):
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except (OSError, UnicodeError, SyntaxError) as exc:
            relative = path.resolve().relative_to(root).as_posix()
            raise ValueError(f"cannot scan {relative}: {exc}") from exc
        os_names, replace_names = _import_aliases(tree)
        relative = path.resolve().relative_to(root).as_posix()
        visitor = _SinkVisitor(
            path=relative,
            os_names=os_names,
            replace_names=replace_names,
            detect_state_assignment=relative.startswith("src/integration/"),
        )
        visitor.visit(tree)
        observations.extend(visitor.observations)
    return tuple(sorted(observations))


def compare_value_sink_inventory_v1(
    specs: tuple[ValueSinkSpecV1, ...],
    observations: tuple[ValueSinkObservationV1, ...],
) -> tuple[SinkFindingV1, ...]:
    findings: list[SinkFindingV1] = []
    observed_counts: dict[tuple[str, str, str], int] = {}
    for observation in observations:
        observed_counts[observation.identity()] = observed_counts.get(observation.identity(), 0) + 1
    specs_by_identity = {spec.identity(): spec for spec in specs}
    for identity, count in sorted(observed_counts.items()):
        spec = specs_by_identity.get(identity)
        evidence = f"{identity[1]}:{identity[2]}:{count}"
        if spec is None:
            findings.append(SinkFindingV1(identity[0], "unclassified_value_sink", evidence))
        elif spec.occurrence_count != count:
            findings.append(
                SinkFindingV1(identity[0], "value_sink_occurrence_mismatch", f"{evidence}:expected={spec.occurrence_count}")
            )
    for identity, spec in sorted(specs_by_identity.items()):
        if identity not in observed_counts:
            findings.append(SinkFindingV1(spec.path, "classified_value_sink_missing", f"{spec.symbol}:{spec.sink_kind}"))
    return tuple(sorted(findings))


def check_m6_value_sinks_v1(root: Path = REPO_ROOT) -> dict[str, object]:
    root = root.resolve()
    findings: list[SinkFindingV1] = []
    try:
        specs = load_value_sink_manifest_v1(root / "tools" / MANIFEST_PATH.name)
    except ValueError as exc:
        specs = ()
        findings.append(SinkFindingV1("tools/m6_value_sink_manifest_v1.json", "manifest_invalid", str(exc)))
    try:
        observations = scan_python_value_sinks_v1(root)
    except ValueError as exc:
        observations = ()
        findings.append(SinkFindingV1("src", "sink_scan_failed", str(exc)))
    findings.extend(compare_value_sink_inventory_v1(specs, observations))
    try:
        writer_inventory = load_writer_inventory_manifest(
            root / "tools" / "m6_writer_inventory_manifest_v1.json"
        )
    except ValueError as exc:
        known_writer_ids: set[str] = set()
        findings.append(
            SinkFindingV1(
                "tools/m6_writer_inventory_manifest_v1.json",
                "writer_manifest_invalid",
                str(exc),
            )
        )
    else:
        known_writer_ids = {entry.entrypoint_id for entry in writer_inventory.entries}
    for spec in specs:
        unknown = sorted(set(spec.writer_entrypoint_ids) - known_writer_ids)
        if unknown:
            findings.append(
                SinkFindingV1(
                    spec.path,
                    "unknown_linked_writer",
                    f"{spec.sink_id}:{','.join(unknown)}",
                )
            )
    findings.sort()
    authority_relevant = tuple(spec for spec in specs if spec.authority_status != "NON_AUTHORITATIVE")
    release_gaps = [spec.sink_id for spec in authority_relevant if spec.release_binding is None]
    return {
        "classified_identity_count": len(specs),
        "findings": [finding.to_dict() for finding in findings],
        "nonclaims": list(NONCLAIMS),
        "observed_occurrence_count": len(observations),
        "ok": not findings,
        "production_authority": False,
        "release_gaps": release_gaps,
        "release_ready": bool(authority_relevant) and not findings and not release_gaps,
        "schema": SCHEMA_V1,
        "sinks": [spec.to_dict() for spec in specs],
    }


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--require-release-ready", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    report = check_m6_value_sinks_v1(args.root)
    gate_ok = report["ok"] is True and (
        not args.require_release_ready or report["release_ready"] is True
    )
    if args.json or not gate_ok:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            "M6 Python value sink inventory ok; "
            f"{len(report['release_gaps'])} classified sinks remain release-blocking"
        )
    return 0 if gate_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
