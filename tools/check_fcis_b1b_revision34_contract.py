#!/usr/bin/env python3
"""Fail-closed structural gate for the unmounted FCIS B1B-1 carrier slice."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

REPORT_SCHEMA = "zenodex/fcis/b1b-revision34-contract-check/v2"
REVISION_PATH = Path(
    "docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md"
)
REVISION_SHA256 = "cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5"

PYTHON_PATHS = (
    Path("src/core/fcis_b1b_authority_values.py"),
    Path("src/core/fcis_b1b_authority_schema.py"),
    Path("src/core/fcis_b1b_authority_admission.py"),
    Path("src/core/fcis_b1b_authority_codec.py"),
)
RUST_PATH = Path("rust-runtime/crates/zenodex-runtime-core/src/fcis_b1b_authority.rs")
RUST_LIB_PATH = Path("rust-runtime/crates/zenodex-runtime-core/src/lib.rs")
FIXTURE_PATH = Path("tests/fixtures/fcis_b1b_authority_v2_golden.json")
BUILDER_PATH = Path("tools/build_fcis_b1b_authority_v2_golden.py")
CHECKER_PATH = Path("tools/check_fcis_b1b_revision34_contract.py")
TEST_PATHS = (
    Path("tests/core/test_fcis_b1b_authority_values.py"),
    Path("tests/core/test_fcis_b1b_authority_admission.py"),
    Path("tests/core/test_fcis_b1b_authority_golden.py"),
    Path("tests/core/test_fcis_b1b1_carriers.py"),
    Path("tests/tools/test_check_fcis_b1b_revision34_contract.py"),
)

# Mutation tests copy exactly this bounded inventory. Keep it small enough to
# run under a constrained /tmp without cloning the repository.
REQUIRED_PATHS = (
    REVISION_PATH,
    *PYTHON_PATHS,
    RUST_PATH,
    RUST_LIB_PATH,
    FIXTURE_PATH,
    BUILDER_PATH,
    CHECKER_PATH,
    *TEST_PATHS,
)
MAX_MUTATION_FIXTURE_BYTES = 2_000_000

FORBIDDEN_PATH_GLOBS = (
    "src/core/fcis_fee_distribution_configuration_content_validation.py",
    "src/core/fcis_b1b_*migration*candidate*.py",
    "src/core/fcis_b1b_*publication*.py",
    "src/core/fcis_b1b_*state_bound*.py",
    "src/state/*fcis*b1b*",
    "src/integration/*fcis*b1b*",
    "integration/*fcis*b1b*",
)
FORBIDDEN_AUTHORITY_SYMBOLS = (
    "PinnedDeploymentBootstrapVerifierV2",
    "VerifiedV1ToV2MigrationAuthorityV2",
    "V1ToV2MigrationCandidateV2",
    "FCISCommittedStateV2",
    "StateBoundFeeDistributionConfigurationV2",
    "TransitionCauseV2",
    "V2EvaluationCandidate",
    "V2Decision",
    "ConfigurationUpdateCommandClaimV2",
    "AuthenticatedConfigurationUpdateCommandV2",
    "V2CommitBundle",
    "PublishedFCISV2Commit",
)
FORBIDDEN_FUNCTION_PARTS = (
    "advance_authority",
    "advance_header",
    "update_authority",
    "update_header",
    "bind_configuration",
    "construct_pinned",
    "derive_migration",
    "publish",
)
REQUIRED_VALUE_CLASSES = (
    "FCISAuthorityHeaderSourceV2",
    "DeploymentBootstrapAnchorClaimSourceV2",
    "V1ToV2MigrationManifestSourceV2",
    "FCISAuthorityHeaderV2",
    "DeploymentBootstrapAnchorClaimV2",
    "V1ToV2MigrationManifestV2",
    "B1BAuthorityAdmissionRejectV2",
)
EXPECTED_SCHEMA_FIELDS = {
    "zenodex/fcis/state/authority-header/v2": (
        "chain_deployment_id",
        "sequence",
        "fee_distribution_configuration_root",
    ),
    "zenodex/fcis/deployment/bootstrap-anchor-claim/v2": (
        "chain_deployment_id",
        "expected_migration_manifest_root",
    ),
    "zenodex/fcis/migration/v1-to-v2-manifest/v2": (
        "chain_deployment_id",
        "expected_v1_pre_root",
        "fee_distribution_domain_id",
        "expected_initial_configuration_root",
        "initial_sequence",
        "initial_configuration_version",
        "initial_activation_sequence",
        "source_snapshot_version",
        "target_snapshot_version",
    ),
}
EXPECTED_ROOT_DOMAINS = {
    "BOOTSTRAP_ANCHOR_CLAIM_ROOT_DOMAIN_V2": "fcis_deployment_bootstrap_anchor_claim",
    "MIGRATION_MANIFEST_ROOT_DOMAIN_V2": "fcis_v1_to_v2_migration_manifest",
}
RUNTIME_SCAN_ROOTS = (
    Path("src"),
    Path("integration"),
    Path("rust-runtime"),
    Path("zk"),
)


@dataclass(frozen=True, slots=True)
class Finding:
    code: str
    path: str
    detail: str


@dataclass(frozen=True, slots=True)
class Report:
    ok: bool
    findings: tuple[Finding, ...]
    runtime_files_scanned: int


def _read(root: Path, path: Path) -> str:
    return (root / path).read_text(encoding="utf-8")


def _decorator_name(node: ast.expr) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Call):
        return _decorator_name(node.func)
    return None


def _is_final_frozen_slots_dataclass(node: ast.ClassDef) -> bool:
    names = {_decorator_name(decorator) for decorator in node.decorator_list}
    if "final" not in names or "dataclass" not in names:
        return False
    for decorator in node.decorator_list:
        if not isinstance(decorator, ast.Call) or _decorator_name(decorator) != "dataclass":
            continue
        keywords = {keyword.arg: keyword.value for keyword in decorator.keywords}
        frozen = keywords.get("frozen")
        slots = keywords.get("slots")
        return (
            isinstance(frozen, ast.Constant)
            and frozen.value is True
            and isinstance(slots, ast.Constant)
            and slots.value is True
        )
    return False


def _literal_assignment(tree: ast.Module, name: str) -> object | None:
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if any(isinstance(target, ast.Name) and target.id == name for target in node.targets):
            try:
                return ast.literal_eval(node.value)
            except (ValueError, TypeError):
                return None
    return None


def _append_parse_failure(
    findings: list[Finding],
    path: Path,
    exc: SyntaxError,
) -> None:
    findings.append(
        Finding(
            "B1B1_PYTHON_PARSE",
            str(path),
            f"{exc.msg} at line {exc.lineno}",
        )
    )


def _check_revision_blob(root: Path, findings: list[Finding]) -> None:
    digest = hashlib.sha256((root / REVISION_PATH).read_bytes()).hexdigest()
    if digest != REVISION_SHA256:
        findings.append(
            Finding(
                "REV34_BLOB_DRIFT",
                str(REVISION_PATH),
                f"expected {REVISION_SHA256}, got {digest}",
            )
        )


def _check_forbidden_paths(root: Path, findings: list[Finding]) -> None:
    for pattern in FORBIDDEN_PATH_GLOBS:
        for path in sorted(root.glob(pattern)):
            if path.is_file():
                findings.append(
                    Finding(
                        "B1B1_FORBIDDEN_PATH",
                        str(path.relative_to(root)),
                        pattern,
                    )
                )


def _parse_carriers(texts: dict[Path, str], findings: list[Finding]) -> dict[Path, ast.Module]:
    trees: dict[Path, ast.Module] = {}
    for path, text in texts.items():
        try:
            trees[path] = ast.parse(text, filename=str(path))
        except SyntaxError as exc:
            _append_parse_failure(findings, path, exc)
    return trees


def _check_python_carriers(root: Path, findings: list[Finding]) -> None:
    texts = {path: _read(root, path) for path in PYTHON_PATHS}
    combined = "\n".join(texts.values())
    for symbol in FORBIDDEN_AUTHORITY_SYMBOLS:
        if symbol in combined:
            findings.append(Finding("B1B1_PREMATURE_AUTHORITY", "python carriers", symbol))
    trees = _parse_carriers(texts, findings)
    for path, tree in trees.items():
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and any(
                part in node.name for part in FORBIDDEN_FUNCTION_PARTS
            ):
                findings.append(Finding("B1B1_BARE_HEADER_TRANSITION", str(path), node.name))

    value_tree = trees.get(PYTHON_PATHS[0])
    if value_tree is not None:
        classes = {node.name: node for node in value_tree.body if isinstance(node, ast.ClassDef)}
        for name in REQUIRED_VALUE_CLASSES:
            node = classes.get(name)
            code = "B1B1_VALUE_MISSING" if node is None else "B1B1_VALUE_NOT_IMMUTABLE"
            if node is None or not _is_final_frozen_slots_dataclass(node):
                findings.append(Finding(code, str(PYTHON_PATHS[0]), name))
    for schema_id in EXPECTED_SCHEMA_FIELDS:
        if schema_id not in texts[PYTHON_PATHS[0]]:
            findings.append(Finding("B1B1_SCHEMA_ID", str(PYTHON_PATHS[0]), schema_id))

    codec_tree = trees.get(PYTHON_PATHS[3])
    if codec_tree is not None:
        for assignment, expected in EXPECTED_ROOT_DOMAINS.items():
            actual = _literal_assignment(codec_tree, assignment)
            if actual != expected:
                detail = f"{assignment}: {actual!r}"
                findings.append(Finding("B1B1_ROOT_DOMAIN", str(PYTHON_PATHS[3]), detail))


def _rust_struct_block(text: str, name: str) -> str | None:
    match = re.search(rf"pub struct {re.escape(name)}\s*\{{(?P<body>.*?)\n\}}", text, re.DOTALL)
    return match.group("body") if match else None


def _check_rust_carriers(root: Path, findings: list[Finding]) -> None:
    text = _read(root, RUST_PATH)
    expected_fields = {
        "FCISAuthorityHeaderV2": EXPECTED_SCHEMA_FIELDS["zenodex/fcis/state/authority-header/v2"],
        "DeploymentBootstrapAnchorClaimV2": EXPECTED_SCHEMA_FIELDS[
            "zenodex/fcis/deployment/bootstrap-anchor-claim/v2"
        ],
        "V1ToV2MigrationManifestV2": EXPECTED_SCHEMA_FIELDS[
            "zenodex/fcis/migration/v1-to-v2-manifest/v2"
        ],
    }
    for name, fields in expected_fields.items():
        block = _rust_struct_block(text, name)
        if block is None:
            findings.append(Finding("B1B1_RUST_STRUCT", str(RUST_PATH), name))
            continue
        for field in fields:
            if not re.search(rf"^\s*{re.escape(field)}\s*:", block, re.MULTILINE):
                findings.append(Finding("B1B1_RUST_FIELD", str(RUST_PATH), f"{name}.{field}"))
            if re.search(rf"^\s*pub(?:\([^)]*\))?\s+{re.escape(field)}\s*:", block, re.MULTILINE):
                findings.append(
                    Finding("B1B1_RUST_PUBLIC_FIELD", str(RUST_PATH), f"{name}.{field}")
                )

    for symbol in FORBIDDEN_AUTHORITY_SYMBOLS:
        if symbol in text:
            findings.append(Finding("B1B1_RUST_PREMATURE_AUTHORITY", str(RUST_PATH), symbol))
    for part in FORBIDDEN_FUNCTION_PARTS:
        if re.search(rf"\bfn\s+[A-Za-z0-9_]*{re.escape(part)}[A-Za-z0-9_]*\s*\(", text):
            findings.append(Finding("B1B1_RUST_BARE_TRANSITION", str(RUST_PATH), part))
    for assignment, expected in EXPECTED_ROOT_DOMAINS.items():
        token = f'pub const {assignment}: &str = "{expected}";'
        if token not in text:
            findings.append(Finding("B1B1_RUST_ROOT_DOMAIN", str(RUST_PATH), assignment))
    lib_text = _read(root, RUST_LIB_PATH)
    if lib_text.count("pub mod fcis_b1b_authority;") != 1:
        findings.append(
            Finding(
                "B1B1_RUST_MODULE_EXPORT",
                str(RUST_LIB_PATH),
                "expected one carrier module export",
            )
        )


def _runtime_candidate_paths(root: Path) -> tuple[Path, ...]:
    result: set[Path] = set()
    for relative_root in RUNTIME_SCAN_ROOTS:
        scan_root = root / relative_root
        if not scan_root.is_dir():
            continue
        for suffix in ("*.py", "*.rs"):
            result.update(path for path in scan_root.rglob(suffix) if path.is_file())
    return tuple(sorted(result))


def _check_runtime_reachability(root: Path, findings: list[Finding]) -> int:
    allowed = {path.as_posix() for path in (*PYTHON_PATHS, RUST_PATH, RUST_LIB_PATH)}
    markers = (
        "fcis_b1b_authority",
        "FCISAuthorityHeaderV2",
        "DeploymentBootstrapAnchorClaimV2",
        "V1ToV2MigrationManifestV2",
    )
    paths = _runtime_candidate_paths(root)
    for path in paths:
        relative = path.relative_to(root).as_posix()
        if relative in allowed:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        marker = next((candidate for candidate in markers if candidate in text), None)
        if marker is not None:
            findings.append(Finding("B1B1_RUNTIME_REACHABILITY", relative, marker))
    return len(paths)


def check_repository(root: Path) -> Report:
    root = root.resolve()
    findings: list[Finding] = []
    for path in REQUIRED_PATHS:
        if not (root / path).is_file():
            findings.append(Finding("MISSING_PATH", str(path), "required file is absent"))
    if findings:
        return Report(False, tuple(findings), 0)

    _check_revision_blob(root, findings)
    _check_forbidden_paths(root, findings)
    _check_python_carriers(root, findings)
    _check_rust_carriers(root, findings)
    runtime_files_scanned = _check_runtime_reachability(root, findings)
    return Report(not findings, tuple(findings), runtime_files_scanned)


def _payload(report: Report) -> dict[str, object]:
    return {
        "schema": REPORT_SCHEMA,
        "ok": report.ok,
        "required_path_count": len(REQUIRED_PATHS),
        "runtime_files_scanned": report.runtime_files_scanned,
        "findings": [
            {
                "code": finding.code,
                "path": finding.path,
                "detail": finding.detail,
            }
            for finding in report.findings
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = check_repository(args.root)
    payload = _payload(report)
    if args.json:
        print(json.dumps(payload, sort_keys=True))
    else:
        print(f"ok={report.ok}")
        print(f"required_paths={len(REQUIRED_PATHS)}")
        print(f"runtime_files_scanned={report.runtime_files_scanned}")
        for finding in report.findings:
            print(f"{finding.code}: {finding.path}: {finding.detail}")
    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
