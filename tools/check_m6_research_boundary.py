#!/usr/bin/env python3
"""Check that the M6 reference surface is not statically mounted by ``src``.

This is a narrow source-boundary check.  A passing result means that the
production source tree has no statically visible import or re-export of the
research M6 modules.  It does not prove dynamic import safety, complete writer
inventory, runtime reachability, validator finality, or production readiness.
"""

from __future__ import annotations

import argparse
import ast
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMA_V1 = "zenodex/m6-research-boundary/v1"
M6_RESEARCH_MODULE_PATHS: tuple[str, ...] = (
    "src/core/m6_authority_evidence_v1.py",
    "src/core/m6_safe_mount_transition_v1.py",
    "src/core/m6_safe_mount_types_v1.py",
    "src/core/m6_safe_mount_v1.py",
    "src/core/m6_zrpf_v1.py",
    "src/integration/m6_commit_port_v1.py",
    "src/integration/m6_durable_store_v1.py",
    "src/integration/m6_authority_verifier_v1.py",
    "src/integration/m6_external_proof_backend_v1.py",
    "src/integration/m6_outbox_delivery_journal_v1.py",
    "src/integration/m6_outbox_delivery_v1.py",
    "src/core/m6_migration_lifecycle_v1.py",
    "src/integration/m6_migration_authority_v1.py",
    "src/integration/m6_migration_admission_v1.py",
)
M6_RESEARCH_IMPORT_PREFIXES: tuple[str, ...] = (
    "src.core.m6_authority_evidence_",
    "src.core.m6_safe_mount_",
    "src.core.m6_zrpf_",
    "src.integration.m6_commit_port_",
    "src.integration.m6_durable_store_",
    "src.integration.m6_authority_verifier_",
    "src.integration.m6_external_proof_backend_",
    "src.integration.m6_outbox_delivery_",
    "src.core.m6_migration_",
    "src.integration.m6_migration_",
)
M6_RESEARCH_SYMBOLS: frozenset[str] = frozenset(
    {
        "AcceptCandidateV1",
        "AuthenticatedExecutionContextV1",
        "GlobalCommandKindV1",
        "GlobalCommandV1",
        "M6ApplicationStateV1",
        "M6PromotionSubjectV1",
        "RejectNoCommitV1",
        "M6CommitPortV1",
        "M6DurableLedgerStoreV1",
        "M6MigrationAuthorityVerifierV1",
        "M6MigrationAuthorityReceiptV1",
        "M6MigrationDurableStoreV1",
        "M6MigrationStateV1",
        "M6MigrationPlanV1",
        "M6MigrationVerifiedAdmissionV1",
        "VerifiedM6MigrationStepV1",
        "authorize_m6_migration_writer_v1",
        "execute_zrpf_batch_v1",
        "run_m6_transition_v1",
        "verify_zrpf_root_v1",
    }
)
RESEARCH_MARKERS: tuple[str, ...] = ("research-only", "research-grade", "reference")
NONCLAIMS: tuple[str, ...] = (
    "dynamic import and generated-code reachability are not checked",
    "legacy value-moving writers are not replaced or certified by this checker",
    "no validator signature, RISC0 receipt, finality, or deployment evidence is created",
    "a passing result does not mount M6 or establish M6Ready",
)


@dataclass(frozen=True, slots=True)
class BoundaryFinding:
    path: str
    rule_id: str
    evidence: str

    def to_dict(self) -> dict[str, str]:
        return {"evidence": self.evidence, "path": self.path, "rule_id": self.rule_id}


def _relative(path: Path, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _is_research_module(path: Path, root: Path) -> bool:
    return _relative(path, root) in M6_RESEARCH_MODULE_PATHS


def _finding(path: Path, root: Path, rule_id: str, evidence: str) -> BoundaryFinding:
    return BoundaryFinding(path=_relative(path, root), rule_id=rule_id, evidence=evidence)


def _has_m6_module_prefix(value: str) -> bool:
    return any(value.startswith(prefix) for prefix in M6_RESEARCH_IMPORT_PREFIXES)


def _scan_import_node(node: ast.AST, *, path: Path, root: Path) -> list[BoundaryFinding]:
    findings: list[BoundaryFinding] = []
    if isinstance(node, ast.Import):
        for alias in node.names:
            if _has_m6_module_prefix(alias.name):
                findings.append(_finding(path, root, "research_module_import", alias.name))
    elif isinstance(node, ast.ImportFrom):
        module = node.module or ""
        if _has_m6_module_prefix(module) or (node.level > 0 and module.startswith("m6_")):
            findings.append(_finding(path, root, "research_module_import", module or "relative import"))
            return findings
        package_import = module in {"src.core", "src.integration"}
        relative_package_import = node.level > 0 and module in {"", "core", "integration"}
        imported_modules = sorted(
            alias.name
            for alias in node.names
            if alias.name.startswith("m6_")
            and (package_import or relative_package_import)
        )
        if imported_modules:
            findings.append(
                _finding(
                    path,
                    root,
                    "research_module_import",
                    ",".join(imported_modules),
                )
            )
            return findings
        core_import = module == "src.core" or (node.level > 0 and module == "core")
        if core_import and any(alias.name == "*" for alias in node.names):
            findings.append(_finding(path, root, "core_star_import", "from src.core import *"))
        leaked_symbols = sorted(
            alias.name for alias in node.names if alias.name in M6_RESEARCH_SYMBOLS
        )
        if leaked_symbols:
            findings.append(_finding(path, root, "research_symbol_reexport", ",".join(leaked_symbols)))
    return findings


def scan_m6_research_file(path: Path, *, root: Path = REPO_ROOT) -> tuple[BoundaryFinding, ...]:
    """Scan one non-M6 source file for statically visible M6 imports or exports."""

    try:
        source = path.read_text(encoding="utf-8")
    except OSError as exc:
        return (_finding(path, root, "source_read_error", str(exc)),)
    try:
        tree = ast.parse(source, filename=str(path))
    except SyntaxError as exc:
        return (_finding(path, root, "source_parse_error", str(exc)),)
    findings: list[BoundaryFinding] = []
    for node in ast.walk(tree):
        findings.extend(_scan_import_node(node, path=path, root=root))
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            if _has_m6_module_prefix(node.value):
                findings.append(_finding(path, root, "research_module_string_reference", node.value))
    return tuple(findings)


def _python_files(root: Path) -> tuple[Path, ...]:
    source_root = root / "src"
    if not source_root.is_dir():
        return ()
    return tuple(sorted(path for path in source_root.rglob("*.py") if path.is_file()))


def _check_research_markers(root: Path) -> list[BoundaryFinding]:
    findings: list[BoundaryFinding] = []
    for relative in M6_RESEARCH_MODULE_PATHS:
        path = root / relative
        if not path.is_file():
            findings.append(_finding(path, root, "research_module_missing", relative))
            continue
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except (OSError, SyntaxError) as exc:
            findings.append(_finding(path, root, "research_module_unparseable", str(exc)))
            continue
        docstring = (ast.get_docstring(tree) or "").lower()
        if not any(marker in docstring for marker in RESEARCH_MARKERS):
            findings.append(_finding(path, root, "research_marker_missing", ",".join(RESEARCH_MARKERS)))
    return findings


def check_m6_research_boundary(root: Path = REPO_ROOT) -> dict[str, object]:
    """Return a deterministic, non-authorizing M6 source-boundary report."""

    root = root.resolve()
    findings = _check_research_markers(root)
    checked_files: list[str] = []
    for path in _python_files(root):
        if _is_research_module(path, root):
            continue
        checked_files.append(_relative(path, root))
        findings.extend(scan_m6_research_file(path, root=root))
    findings = sorted(findings, key=lambda item: (item.path, item.rule_id, item.evidence))
    return {
        "checked_file_count": len(checked_files),
        "checked_files": checked_files,
        "findings": [item.to_dict() for item in findings],
        "m6_production_mounted": False,
        "nonclaims": list(NONCLAIMS),
        "production_authority": False,
        "schema": SCHEMA_V1,
        "ok": not findings,
    }


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    report = check_m6_research_boundary(args.root)
    if args.json or not report["ok"]:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("M6 research boundary ok; production mounting remains false")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
