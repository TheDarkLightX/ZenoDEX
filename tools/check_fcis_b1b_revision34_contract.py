#!/usr/bin/env python3
"""Fail-closed structural gate for the unmounted FCIS B1B-1 carrier slice."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPORT_SCHEMA = "zenodex/fcis/b1b-revision34-contract-check/v3"
REVISION_PATH = Path(
    "docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md"
)
REVISION_SHA256 = "cae6562b5e0cade2a03827a2a8f591561317b6cf684de4d22d726c25917108c5"

VALUES_PATH = Path("src/core/fcis_b1b_authority_values.py")
SCHEMA_PATH = Path("src/core/fcis_b1b_authority_schema.py")
ADMISSION_PATH = Path("src/core/fcis_b1b_authority_admission.py")
CODEC_PATH = Path("src/core/fcis_b1b_authority_codec.py")
PYTHON_PATHS = (VALUES_PATH, SCHEMA_PATH, ADMISSION_PATH, CODEC_PATH)
CANONICAL_PATH = Path("src/state/canonical.py")
RUST_PATH = Path("rust-runtime/crates/zenodex-runtime-core/src/fcis_b1b_authority.rs")
RUST_LIB_PATH = Path("rust-runtime/crates/zenodex-runtime-core/src/lib.rs")
FIXTURE_PATH = Path("tests/fixtures/fcis_b1b_authority_v2_golden.json")
BUILDER_PATH = Path("tools/build_fcis_b1b_authority_v2_golden.py")
CHECKER_PATH = Path("tools/check_fcis_b1b_revision34_contract.py")
TEST_PATHS = (
    Path("tests/core/test_fcis_b1b_authority_values.py"),
    Path("tests/core/test_fcis_b1b_authority_admission.py"),
    Path("tests/core/test_fcis_b1b_authority_resource_bounds.py"),
    Path("tests/core/test_fcis_b1b_authority_golden.py"),
    Path("tests/core/test_fcis_b1b1_carriers.py"),
    Path("tests/tools/test_check_fcis_b1b_revision34_contract.py"),
)

# Mutation tests copy exactly this bounded inventory. Keep it small enough to
# run under a constrained /tmp without cloning the repository.
REQUIRED_PATHS = (
    REVISION_PATH,
    *PYTHON_PATHS,
    CANONICAL_PATH,
    RUST_PATH,
    RUST_LIB_PATH,
    FIXTURE_PATH,
    BUILDER_PATH,
    CHECKER_PATH,
    *TEST_PATHS,
)
MAX_MUTATION_FIXTURE_BYTES = 2_000_000
MAX_RUNTIME_SOURCE_BYTES = 2_000_000

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
EXPECTED_PYTHON_CLASS_FIELDS = {
    "FCISAuthorityHeaderSourceV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/state/authority-header/v2"
    ],
    "DeploymentBootstrapAnchorClaimSourceV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/deployment/bootstrap-anchor-claim/v2"
    ],
    "V1ToV2MigrationManifestSourceV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/migration/v1-to-v2-manifest/v2"
    ],
    "FCISAuthorityHeaderV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/state/authority-header/v2"
    ],
    "DeploymentBootstrapAnchorClaimV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/deployment/bootstrap-anchor-claim/v2"
    ],
    "V1ToV2MigrationManifestV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/migration/v1-to-v2-manifest/v2"
    ],
    "B1BAuthorityAdmissionRejectV2": ("code", "path"),
}
EXPECTED_SCHEMA_ASSIGNMENTS = {
    "FCIS_AUTHORITY_HEADER_FIELDS_V2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/state/authority-header/v2"
    ],
    "DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_FIELDS_V2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/deployment/bootstrap-anchor-claim/v2"
    ],
    "V1_TO_V2_MIGRATION_MANIFEST_FIELDS_V2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/migration/v1-to-v2-manifest/v2"
    ],
}
EXPECTED_RUST_STRUCT_FIELDS = {
    "FCISAuthorityHeaderV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/state/authority-header/v2"
    ],
    "DeploymentBootstrapAnchorClaimV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/deployment/bootstrap-anchor-claim/v2"
    ],
    "V1ToV2MigrationManifestV2": EXPECTED_SCHEMA_FIELDS[
        "zenodex/fcis/migration/v1-to-v2-manifest/v2"
    ],
}
EXPECTED_RUST_DERIVE = "#[derive(Debug, Clone, PartialEq, Eq)]"
EXPECTED_RUST_METHODS = {
    "FCISAuthorityHeaderV2": (
        "try_new",
        "chain_deployment_id",
        "sequence",
        "fee_distribution_configuration_root",
    ),
    "DeploymentBootstrapAnchorClaimV2": (
        "try_new",
        "chain_deployment_id",
        "expected_migration_manifest_root",
    ),
    "V1ToV2MigrationManifestV2": (
        "try_new",
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

PYTHON_CARRIER_NAMES = frozenset(EXPECTED_PYTHON_CLASS_FIELDS)
RUNTIME_FIELD_CLASS_NAMES = (
    "FCISAuthorityHeaderSourceV2",
    "DeploymentBootstrapAnchorClaimSourceV2",
    "V1ToV2MigrationManifestSourceV2",
    "FCISAuthorityHeaderV2",
    "DeploymentBootstrapAnchorClaimV2",
    "V1ToV2MigrationManifestV2",
)
RUST_CARRIER_NAMES = frozenset(EXPECTED_RUST_STRUCT_FIELDS)
PYTHON_ALLOWED_IMPORTS = {
    VALUES_PATH: frozenset(),
    SCHEMA_PATH: frozenset(
        {
            "FCISAuthorityHeaderSourceV2",
            "DeploymentBootstrapAnchorClaimSourceV2",
            "V1ToV2MigrationManifestSourceV2",
        }
    ),
    ADMISSION_PATH: PYTHON_CARRIER_NAMES,
    CODEC_PATH: frozenset(
        {
            "FCISAuthorityHeaderV2",
            "DeploymentBootstrapAnchorClaimV2",
            "V1ToV2MigrationManifestV2",
        }
    ),
}
PYTHON_ALLOWED_CARRIER_FUNCTIONS = {
    VALUES_PATH: frozenset(),
    SCHEMA_PATH: frozenset(),
    ADMISSION_PATH: frozenset(
        {
            "_reject",
            "scan",
            "_scan_token",
            "_add_node",
            "validate_fcis_b1b_json_resource_bounds_v2",
            "_construct_from_source_v2",
            "admit_fcis_b1b_authority_source_v2",
            "_source_from_mapping_v2",
            "decode_fcis_b1b_authority_v2",
        }
    ),
    CODEC_PATH: frozenset(
        {
            "_authority_header_projection_v2",
            "_bootstrap_anchor_claim_projection_v2",
            "_migration_manifest_projection_v2",
            "encode_fcis_b1b_authority_v2",
            "canonical_bootstrap_anchor_claim_root_v2",
            "canonical_v1_to_v2_migration_manifest_root_v2",
        }
    ),
}
RUST_ALLOWED_FUNCTIONS = frozenset(
    {
        "new",
        "scan",
        "scan_string_character",
        "scan_token",
        "add_node",
        "validate_fcis_b1b_json_resource_bounds_v2",
        "u256_max",
        "text_is_canonical",
        "digest_is_canonical",
        "validate_authority_header_fields_v2",
        "validate_bootstrap_anchor_claim_fields_v2",
        "validate_migration_manifest_fields_v2",
        "as_str",
        "resource",
        "invalid",
        "code",
        "path",
        "try_new",
        "chain_deployment_id",
        "sequence",
        "fee_distribution_configuration_root",
        "expected_migration_manifest_root",
        "expected_v1_pre_root",
        "fee_distribution_domain_id",
        "expected_initial_configuration_root",
        "initial_sequence",
        "initial_configuration_version",
        "initial_activation_sequence",
        "source_snapshot_version",
        "target_snapshot_version",
        "int_json",
        "envelope",
        "authority_header_json",
        "bootstrap_anchor_claim_json",
        "migration_manifest_json",
        "encode_fcis_authority_header_v2",
        "encode_deployment_bootstrap_anchor_claim_v2",
        "encode_v1_to_v2_migration_manifest_v2",
        "canonical_bootstrap_anchor_claim_root_v2",
        "canonical_v1_to_v2_migration_manifest_root_v2",
    }
)
RUST_ALLOWED_PUBLIC_FUNCTIONS = frozenset(
    {
        "validate_fcis_b1b_json_resource_bounds_v2",
        "as_str",
        "code",
        "path",
        "try_new",
        "chain_deployment_id",
        "sequence",
        "fee_distribution_configuration_root",
        "expected_migration_manifest_root",
        "expected_v1_pre_root",
        "fee_distribution_domain_id",
        "expected_initial_configuration_root",
        "initial_sequence",
        "initial_configuration_version",
        "initial_activation_sequence",
        "source_snapshot_version",
        "target_snapshot_version",
        "encode_fcis_authority_header_v2",
        "encode_deployment_bootstrap_anchor_claim_v2",
        "encode_v1_to_v2_migration_manifest_v2",
        "canonical_bootstrap_anchor_claim_root_v2",
        "canonical_v1_to_v2_migration_manifest_root_v2",
    }
)
RUNTIME_SCAN_ROOTS = (Path("src"), Path("integration"), Path("rust-runtime"), Path("zk"))
RUNTIME_EXCLUDED_PARTS = frozenset(
    {".git", ".venv", "__pycache__", "node_modules", "target"}
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


def _has_exact_carrier_decorators(node: ast.ClassDef) -> bool:
    if len(node.decorator_list) != 2:
        return False
    final_decorator, dataclass_decorator = node.decorator_list
    if not isinstance(final_decorator, ast.Name) or final_decorator.id != "final":
        return False
    if (
        not isinstance(dataclass_decorator, ast.Call)
        or _decorator_name(dataclass_decorator) != "dataclass"
        or dataclass_decorator.args
    ):
        return False
    keywords = {keyword.arg: keyword.value for keyword in dataclass_decorator.keywords}
    if set(keywords) != {"frozen", "slots"}:
        return False
    for name in ("frozen", "slots"):
        value = keywords[name]
        if not isinstance(value, ast.Constant) or value.value is not True:
            return False
    return True


def _has_required_immutable_decorators(node: ast.ClassDef) -> bool:
    names = {_decorator_name(decorator) for decorator in node.decorator_list}
    if "final" not in names or "dataclass" not in names:
        return False
    for decorator in node.decorator_list:
        if not isinstance(decorator, ast.Call):
            continue
        if _decorator_name(decorator) != "dataclass":
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
        Finding("B1B1_PYTHON_PARSE", str(path), f"{exc.msg} at line {exc.lineno}")
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


def _parse_python(
    path: Path,
    text: str,
    findings: list[Finding],
) -> ast.Module | None:
    try:
        return ast.parse(text, filename=str(path))
    except SyntaxError as exc:
        _append_parse_failure(findings, path, exc)
        return None


def _direct_annotated_fields(node: ast.ClassDef) -> tuple[str, ...]:
    return tuple(
        child.target.id
        for child in node.body
        if isinstance(child, ast.AnnAssign) and isinstance(child.target, ast.Name)
    )


def _assigned_names(node: ast.AST) -> tuple[str, ...]:
    return tuple(
        child.id for child in ast.walk(node) if isinstance(child, ast.Name)
    )


def _carrier_aliases(tree: ast.Module) -> tuple[set[str], set[str]]:
    aliases = set(PYTHON_CARRIER_NAMES)
    declared_aliases: set[str] = set()
    edges: list[tuple[str, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and (node.module or "").endswith(
            "fcis_b1b_authority_values"
        ):
            for imported in node.names:
                if imported.name not in PYTHON_CARRIER_NAMES:
                    continue
                local_name = imported.asname or imported.name
                aliases.add(local_name)
                if local_name != imported.name:
                    declared_aliases.add(local_name)
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Name):
            for target in node.targets:
                edges.extend((name, node.value.id) for name in _assigned_names(target))
        elif (
            isinstance(node, ast.AnnAssign)
            and node.value is not None
            and isinstance(node.value, ast.Name)
        ):
            edges.extend(
                (name, node.value.id) for name in _assigned_names(node.target)
            )

    changed = True
    while changed:
        changed = False
        for alias_target, alias_source in edges:
            if alias_source in aliases and alias_target not in aliases:
                aliases.add(alias_target)
                declared_aliases.add(alias_target)
                changed = True
    return aliases, declared_aliases


def _expression_references_alias(node: ast.AST, aliases: set[str]) -> bool:
    return any(
        isinstance(child, ast.Name) and child.id in aliases
        for child in ast.walk(node)
    )


def _dynamic_mutation_name(node: ast.expr) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _check_python_identity_mutations(
    path: Path,
    tree: ast.Module,
    findings: list[Finding],
) -> None:
    details: set[str] = set()
    aliases, declared_aliases = _carrier_aliases(tree)
    details.update(f"{name}: carrier class alias" for name in declared_aliases)
    for node in ast.walk(tree):
        targets: tuple[ast.AST, ...] = ()
        if isinstance(node, ast.Assign):
            targets = tuple(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = (node.target,)
        elif isinstance(node, ast.Delete):
            targets = tuple(node.targets)
        for target in targets:
            target_names = {
                child.id
                for child in ast.walk(target)
                if isinstance(child, ast.Name) and child.id in aliases
            }
            for name in target_names:
                details.add(f"{name}: attribute or class replacement")
            if any(
                isinstance(child, ast.Call)
                and _dynamic_mutation_name(child.func) in {"globals", "vars"}
                for child in ast.walk(target)
            ):
                details.add("dynamic namespace replacement")

        assigned_value: ast.expr | None = None
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            assigned_value = node.value
        if (
            isinstance(assigned_value, ast.Attribute)
            and _expression_references_alias(assigned_value.value, aliases)
        ):
            details.add("carrier method or descriptor capture")

        if not isinstance(node, ast.Call):
            continue
        mutation_name = _dynamic_mutation_name(node.func)
        if mutation_name in {"globals", "vars"}:
            details.add(f"dynamic namespace call: {mutation_name}")
        if not node.args:
            continue
        first_argument = node.args[0]
        if (
            mutation_name in {"setattr", "delattr", "__setattr__", "__delattr__"}
            and _expression_references_alias(first_argument, aliases)
        ):
            details.add(f"carrier post-definition call: {mutation_name}")

    for detail in sorted(details):
        findings.append(Finding("B1B1_PYTHON_IDENTITY_MUTATION", str(path), detail))


_RUNTIME_FIELD_PROBE = r"""
import dataclasses
import importlib
import json
import pathlib
import sys
import types

root = pathlib.Path(sys.argv[1])
for package_name, relative_path in (
    ("src", "src"),
    ("src.core", "src/core"),
    ("src.state", "src/state"),
):
    package = types.ModuleType(package_name)
    package.__path__ = [str(root / relative_path)]
    sys.modules[package_name] = package

values = importlib.import_module("src.core.fcis_b1b_authority_values")
names = json.loads(sys.argv[2])
baseline = {}
for name in names:
    carrier = getattr(values, name)
    baseline[name] = {
        "carrier": carrier,
        "post_init": getattr(carrier, "__post_init__", None),
        "eq": carrier.__eq__,
        "hash": carrier.__hash__,
    }

schema = importlib.import_module("src.core.fcis_b1b_authority_schema")
admission = importlib.import_module("src.core.fcis_b1b_authority_admission")
codec = importlib.import_module("src.core.fcis_b1b_authority_codec")

for name in names:
    carrier = getattr(values, name)
    before = baseline[name]
    if carrier is not before["carrier"]:
        raise RuntimeError(f"{name}: class object changed")
    if carrier.__bases__ != (object,):
        raise RuntimeError(f"{name}: base classes changed")
    if getattr(carrier, "__post_init__", None) is not before["post_init"]:
        raise RuntimeError(f"{name}: __post_init__ changed")
    if carrier.__eq__ is not before["eq"] or carrier.__hash__ is not before["hash"]:
        raise RuntimeError(f"{name}: equality identity changed")

module_imports = {
    schema: names[:3],
    admission: names,
    codec: names[3:],
}
for module, imported_names in module_imports.items():
    for name in imported_names:
        if getattr(module, name) is not baseline[name]["carrier"]:
            raise RuntimeError(f"{module.__name__}.{name}: binding changed")

zero = "0x" + ("0" * 64)
invalid_specimens = (
    lambda: values.FCISAuthorityHeaderV2("bypass", -1, "not-a-digest"),
    lambda: values.DeploymentBootstrapAnchorClaimV2("", "not-a-digest"),
    lambda: values.V1ToV2MigrationManifestV2(
        "", "bad", "", "bad", -1, 0, -1, -1, -1
    ),
)
for construct in invalid_specimens:
    try:
        construct()
    except (TypeError, ValueError):
        pass
    else:
        raise RuntimeError("invalid sentinel carrier constructed")

left = values.FCISAuthorityHeaderV2("deployment", 0, zero)
equal = values.FCISAuthorityHeaderV2("deployment", 0, zero)
different = values.FCISAuthorityHeaderV2("deployment", 1, zero)
if left != equal or left == different or hash(left) != hash(equal):
    raise RuntimeError("carrier equality/hash semantics changed")

result = {
    name: [field.name for field in dataclasses.fields(getattr(values, name))]
    for name in names
}
print(json.dumps(result, sort_keys=True, separators=(",", ":")))
"""


def _check_runtime_dataclass_fields(
    root: Path,
    findings: list[Finding],
) -> None:
    try:
        completed = subprocess.run(
            [
                sys.executable,
                "-I",
                "-c",
                _RUNTIME_FIELD_PROBE,
                str(root),
                json.dumps(RUNTIME_FIELD_CLASS_NAMES),
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        findings.append(
            Finding(
                "B1B1_PYTHON_RUNTIME_FIELDS",
                str(VALUES_PATH),
                f"probe failed closed: {exc}",
            )
        )
        return
    if completed.returncode != 0:
        detail = completed.stderr.strip()[-1_000:] or f"exit {completed.returncode}"
        findings.append(Finding("B1B1_PYTHON_RUNTIME_FIELDS", str(VALUES_PATH), detail))
        return
    try:
        actual = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        findings.append(
            Finding(
                "B1B1_PYTHON_RUNTIME_FIELDS",
                str(VALUES_PATH),
                f"invalid probe output: {exc.msg}",
            )
        )
        return
    expected = {
        name: list(EXPECTED_PYTHON_CLASS_FIELDS[name]) for name in RUNTIME_FIELD_CLASS_NAMES
    }
    if actual != expected:
        findings.append(
            Finding(
                "B1B1_PYTHON_RUNTIME_FIELDS",
                str(VALUES_PATH),
                f"expected {expected!r}, got {actual!r}",
            )
        )


def _check_python_class_closure(
    path: Path,
    tree: ast.Module,
    findings: list[Finding],
) -> None:
    classes = {node.name: node for node in tree.body if isinstance(node, ast.ClassDef)}
    source_names = {
        "FCISAuthorityHeaderSourceV2",
        "DeploymentBootstrapAnchorClaimSourceV2",
        "V1ToV2MigrationManifestSourceV2",
    }
    for name, expected_fields in EXPECTED_PYTHON_CLASS_FIELDS.items():
        node = classes.get(name)
        if node is None:
            findings.append(Finding("B1B1_VALUE_MISSING", str(path), name))
            continue
        if not _has_required_immutable_decorators(node):
            findings.append(Finding("B1B1_VALUE_NOT_IMMUTABLE", str(path), name))
        if not _has_exact_carrier_decorators(node):
            findings.append(Finding("B1B1_PYTHON_DECORATORS", str(path), name))
        if node.bases or node.keywords:
            findings.append(
                Finding(
                    "B1B1_PYTHON_CLASS_SHAPE",
                    str(path),
                    f"{name}: bases={len(node.bases)}, keywords={len(node.keywords)}",
                )
            )
        actual_fields = _direct_annotated_fields(node)
        if actual_fields != expected_fields:
            findings.append(
                Finding(
                    "B1B1_PYTHON_FIELD_SET",
                    str(path),
                    f"{name}: expected {expected_fields!r}, got {actual_fields!r}",
                )
            )
        allowed_methods = set() if name in source_names else {"__post_init__"}
        actual_methods = {
            child.name
            for child in node.body
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        if actual_methods != allowed_methods:
            findings.append(
                Finding(
                    "B1B1_PYTHON_IDENTITY",
                    str(path),
                    f"{name}: methods {sorted(actual_methods)!r}",
                )
            )
        if any(isinstance(child, ast.Assign) for child in node.body):
            findings.append(
                Finding("B1B1_PYTHON_FIELD_SET", str(path), f"{name}: class assignment")
            )

def _carrier_references(node: ast.AST) -> set[str]:
    references: set[str] = set()
    for child in ast.walk(node):
        if isinstance(child, ast.Name) and child.id in PYTHON_CARRIER_NAMES:
            references.add(child.id)
        elif isinstance(child, ast.Attribute) and child.attr in PYTHON_CARRIER_NAMES:
            references.add(child.attr)
    return references


def _check_python_imports_and_consumers(
    path: Path,
    tree: ast.Module,
    findings: list[Finding],
) -> None:
    allowed_imports = PYTHON_ALLOWED_IMPORTS[path]
    allowed_functions = PYTHON_ALLOWED_CARRIER_FUNCTIONS[path]
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if "fcis_b1b_authority_values" in alias.name:
                    findings.append(
                        Finding("B1B1_CARRIER_IMPORT", str(path), alias.name)
                    )
        elif isinstance(node, ast.ImportFrom):
            module = node.module or ""
            if not module.endswith("fcis_b1b_authority_values"):
                continue
            for alias in node.names:
                if alias.name == "*" or alias.asname is not None:
                    findings.append(
                        Finding(
                            "B1B1_CARRIER_IMPORT",
                            str(path),
                            f"{alias.name} as {alias.asname}",
                        )
                    )
                if (
                    alias.name in PYTHON_CARRIER_NAMES
                    and alias.name not in allowed_imports
                ):
                    findings.append(
                        Finding("B1B1_CARRIER_IMPORT", str(path), alias.name)
                    )
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            references = _carrier_references(node)
            if references and node.name not in allowed_functions:
                findings.append(
                    Finding(
                        "B1B1_CARRIER_CONSUMER",
                        str(path),
                        f"{node.name}: {sorted(references)!r}",
                    )
                )
            if any(part in node.name for part in FORBIDDEN_FUNCTION_PARTS):
                findings.append(
                    Finding("B1B1_BARE_HEADER_TRANSITION", str(path), node.name)
                )

    # Only the admission constructor may instantiate an exact carrier.
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for call in (child for child in ast.walk(node) if isinstance(child, ast.Call)):
            if (
                isinstance(call.func, ast.Name)
                and call.func.id
                in {
                    "FCISAuthorityHeaderV2",
                    "DeploymentBootstrapAnchorClaimV2",
                    "V1ToV2MigrationManifestV2",
                }
                and not (path == ADMISSION_PATH and node.name == "_construct_from_source_v2")
            ):
                findings.append(
                    Finding(
                        "B1B1_CARRIER_CONSTRUCTOR",
                        str(path),
                        f"{node.name}: {call.func.id}",
                    )
                )


def _check_python_carriers(root: Path, findings: list[Finding]) -> None:
    texts = {path: _read(root, path) for path in PYTHON_PATHS}
    trees: dict[Path, ast.Module] = {}
    for path, text in texts.items():
        tree = _parse_python(path, text, findings)
        if tree is not None:
            trees[path] = tree
            _check_python_imports_and_consumers(path, tree, findings)
            _check_python_identity_mutations(path, tree, findings)

    value_tree = trees.get(VALUES_PATH)
    if value_tree is not None:
        _check_python_class_closure(VALUES_PATH, value_tree, findings)
    for schema_id in EXPECTED_SCHEMA_FIELDS:
        if schema_id not in texts[VALUES_PATH]:
            findings.append(Finding("B1B1_SCHEMA_ID", str(VALUES_PATH), schema_id))

    schema_tree = trees.get(SCHEMA_PATH)
    if schema_tree is not None:
        for assignment, expected in EXPECTED_SCHEMA_ASSIGNMENTS.items():
            actual = _literal_assignment(schema_tree, assignment)
            if actual != expected:
                findings.append(
                    Finding(
                        "B1B1_SCHEMA_FIELD_SET",
                        str(SCHEMA_PATH),
                        f"{assignment}: {actual!r}",
                    )
                )

    codec_tree = trees.get(CODEC_PATH)
    if codec_tree is not None:
        for assignment, expected_domain in EXPECTED_ROOT_DOMAINS.items():
            actual = _literal_assignment(codec_tree, assignment)
            if actual != expected_domain:
                findings.append(
                    Finding(
                        "B1B1_ROOT_DOMAIN",
                        str(CODEC_PATH),
                        f"{assignment}: {actual!r}",
                    )
                )


def _rust_struct_block(text: str, name: str) -> str | None:
    masked = _rust_mask_non_code(text)
    match = re.search(rf"\bpub\s+struct\s+{re.escape(name)}\s*\{{", masked)
    if match is None:
        return None
    opening_brace = masked.find("{", match.start(), match.end())
    return _rust_braced_block(text, opening_brace)


def _rust_raw_string_end(text: str, start: int) -> int | None:
    cursor = start
    if text.startswith(("br", "cr"), cursor):
        cursor += 2
    elif cursor < len(text) and text[cursor] == "r":
        cursor += 1
    else:
        return None
    hash_start = cursor
    while cursor < len(text) and text[cursor] == "#":
        cursor += 1
    if cursor >= len(text) or text[cursor] != '"':
        return None
    delimiter = '"' + "#" * (cursor - hash_start)
    closing = text.find(delimiter, cursor + 1)
    return len(text) if closing < 0 else closing + len(delimiter)


def _rust_quoted_end(text: str, start: int, quote: str) -> int | None:
    cursor = start + 1
    escaped = False
    while cursor < len(text):
        character = text[cursor]
        if character == "\n" and quote == "'":
            return None
        if escaped:
            escaped = False
        elif character == "\\":
            escaped = True
        elif character == quote:
            return cursor + 1
        cursor += 1
    return len(text) if quote == '"' else None


def _rust_blank_non_newlines(buffer: list[str], start: int, end: int) -> None:
    for index in range(start, end):
        if buffer[index] != "\n":
            buffer[index] = " "


def _rust_mask_non_code(text: str) -> str:
    """Return a same-length Rust view with comments and literals blanked."""

    buffer = list(text)
    cursor = 0
    while cursor < len(text):
        if text.startswith("//", cursor):
            end = text.find("\n", cursor + 2)
            end = len(text) if end < 0 else end
            _rust_blank_non_newlines(buffer, cursor, end)
            cursor = end
            continue
        if text.startswith("/*", cursor):
            depth = 1
            end = cursor + 2
            while end < len(text) and depth > 0:
                if text.startswith("/*", end):
                    depth += 1
                    end += 2
                elif text.startswith("*/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            _rust_blank_non_newlines(buffer, cursor, end)
            cursor = end
            continue
        raw_end = _rust_raw_string_end(text, cursor)
        if raw_end is not None:
            _rust_blank_non_newlines(buffer, cursor, raw_end)
            cursor = raw_end
            continue
        if text[cursor] == '"':
            quoted_end = _rust_quoted_end(text, cursor, '"')
            if quoted_end is not None:
                _rust_blank_non_newlines(buffer, cursor, quoted_end)
                cursor = quoted_end
                continue
        if text[cursor] == "'":
            quoted_end = _rust_quoted_end(text, cursor, "'")
            if quoted_end is not None:
                _rust_blank_non_newlines(buffer, cursor, quoted_end)
                cursor = quoted_end
                continue
        cursor += 1
    return "".join(buffer)


def _rust_matching_brace(masked: str, opening_brace: int) -> int | None:
    depth = 0
    for index in range(opening_brace, len(masked)):
        character = masked[index]
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return index
    return None


def _rust_matching_delimiter(
    masked: str,
    opening: int,
    opening_character: str,
    closing_character: str,
) -> int | None:
    depth = 0
    for index in range(opening, len(masked)):
        character = masked[index]
        if character == opening_character:
            depth += 1
        elif character == closing_character:
            depth -= 1
            if depth == 0:
                return index
    return None


def _rust_top_level_at(masked: str, offset: int) -> bool:
    depth = 0
    for character in masked[:offset]:
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
    return depth == 0


def _normalize_rust_attribute(attribute: str) -> str:
    return re.sub(r"\s+", "", attribute)


def _rust_struct_attributes(text: str, name: str) -> tuple[str, ...] | None:
    masked = _rust_mask_non_code(text)
    match = re.search(rf"\bpub\s+struct\s+{re.escape(name)}\s*\{{", masked)
    if match is None:
        return None
    attributes: list[str] = []
    cursor = match.start()
    while True:
        while cursor > 0 and masked[cursor - 1].isspace():
            cursor -= 1
        if cursor == 0 or masked[cursor - 1] != "]":
            break
        bracket_depth = 1
        opening = cursor - 2
        while opening >= 0 and bracket_depth > 0:
            if masked[opening] == "]":
                bracket_depth += 1
            elif masked[opening] == "[":
                bracket_depth -= 1
            opening -= 1
        opening += 1
        attribute_start = opening - 1
        if bracket_depth != 0 or attribute_start < 0 or masked[attribute_start] != "#":
            break
        attributes.append(
            _normalize_rust_attribute(text[attribute_start:cursor].strip())
        )
        cursor = attribute_start
    attributes.reverse()
    return tuple(attributes)


def _rust_braced_block(text: str, opening_brace: int) -> str | None:
    masked = _rust_mask_non_code(text)
    closing_brace = _rust_matching_brace(masked, opening_brace)
    if closing_brace is None:
        return None
    return text[opening_brace + 1 : closing_brace]


def _rust_inherent_impl_blocks(text: str, name: str) -> tuple[str, ...]:
    blocks: list[str] = []
    masked = _rust_mask_non_code(text)
    for match in re.finditer(rf"\bimpl\s+{re.escape(name)}\s*\{{", masked):
        opening_brace = masked.find("{", match.start(), match.end())
        block = _rust_braced_block(text, opening_brace)
        if block is not None:
            blocks.append(block)
    return tuple(blocks)


def _rust_impl_methods(block: str) -> tuple[str, ...]:
    return tuple(
        match.group("name")
        for match in re.finditer(
            r"(?:\bpub(?:\([^)]*\))?\s+)?fn\s+"
            r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\(",
            block,
        )
    )


def _rust_fields(block: str) -> tuple[tuple[str, bool], ...] | None:
    fields: list[tuple[str, bool]] = []
    for raw_line in block.splitlines():
        line = raw_line.split("//", 1)[0].strip()
        if not line or line.startswith("#["):
            continue
        match = re.fullmatch(
            r"(?:(pub(?:\([^)]*\))?)\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:\s*.+,",
            line,
        )
        if match is None:
            return None
        fields.append((match.group(2), match.group(1) is not None))
    return tuple(fields)


def _rust_production_text(text: str) -> str:
    """Blank only top-level modules carrying an exact test-only cfg attribute."""

    masked = _rust_mask_non_code(text)
    pattern = re.compile(
        r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]\s*"
        r"mod\s+[A-Za-z_][A-Za-z0-9_]*\s*\{"
    )
    spans: list[tuple[int, int]] = []
    for match in pattern.finditer(masked):
        if not _rust_top_level_at(masked, match.start()):
            continue
        opening_brace = masked.find("{", match.start(), match.end())
        closing_brace = _rust_matching_brace(masked, opening_brace)
        if closing_brace is not None:
            spans.append((match.start(), closing_brace + 1))
    buffer = list(text)
    for start, end in spans:
        _rust_blank_non_newlines(buffer, start, end)
    return "".join(buffer)


def _check_rust_function_surface(
    text: str,
    findings: list[Finding],
) -> None:
    production = _rust_production_text(text)
    masked = _rust_mask_non_code(production)
    matches = list(
        re.finditer(
            r"(?P<public>\bpub\s+)?fn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>{}]*>)?\s*\(",
            masked,
        )
    )
    for index, match in enumerate(matches):
        name = match.group("name")
        end = matches[index + 1].start() if index + 1 < len(matches) else len(production)
        segment = masked[match.start() : end]
        references = sorted(name for name in RUST_CARRIER_NAMES if name in segment)
        if name not in RUST_ALLOWED_FUNCTIONS:
            findings.append(
                Finding(
                    "B1B1_RUST_CARRIER_CONSUMER",
                    str(RUST_PATH),
                    f"{name}: {references!r}",
                )
            )
        if match.group("public") and name not in RUST_ALLOWED_PUBLIC_FUNCTIONS:
            findings.append(
                Finding("B1B1_RUST_PUBLIC_SURFACE", str(RUST_PATH), name)
            )
        if any(part in name for part in FORBIDDEN_FUNCTION_PARTS):
            findings.append(
                Finding("B1B1_RUST_BARE_TRANSITION", str(RUST_PATH), name)
            )


def _check_rust_struct_shape(
    text: str,
    name: str,
    expected_fields: tuple[str, ...],
    findings: list[Finding],
) -> None:
    attributes = _rust_struct_attributes(text, name)
    expected_attributes = (_normalize_rust_attribute(EXPECTED_RUST_DERIVE),)
    if attributes != expected_attributes:
        findings.append(
            Finding(
                "B1B1_RUST_DERIVE_SURFACE",
                str(RUST_PATH),
                f"{name}: expected {expected_attributes!r}, got {attributes!r}",
            )
        )
    block = _rust_struct_block(text, name)
    if block is None:
        findings.append(Finding("B1B1_RUST_STRUCT", str(RUST_PATH), name))
        return
    parsed = _rust_fields(block)
    if parsed is None:
        findings.append(
            Finding("B1B1_RUST_FIELD_SET", str(RUST_PATH), f"{name}: unparsed")
        )
        return
    actual_fields = tuple(field for field, _ in parsed)
    if actual_fields != expected_fields:
        findings.append(
            Finding(
                "B1B1_RUST_FIELD_SET",
                str(RUST_PATH),
                f"{name}: expected {expected_fields!r}, got {actual_fields!r}",
            )
        )
    for field, public in parsed:
        if public:
            findings.append(
                Finding(
                    "B1B1_RUST_PUBLIC_FIELD",
                    str(RUST_PATH),
                    f"{name}.{field}",
                )
            )


def _check_rust_impl_surface(
    production: str,
    name: str,
    findings: list[Finding],
) -> None:
    masked = _rust_mask_non_code(production)
    trait_impls = tuple(
        match.group("trait").strip()
        for match in re.finditer(
            rf"\bimpl\s+(?P<trait>[^{{;]+?)\s+for\s+{re.escape(name)}\b",
            masked,
        )
    )
    if trait_impls:
        findings.append(
            Finding(
                "B1B1_RUST_IMPL_SURFACE",
                str(RUST_PATH),
                f"{name}: trait impls {trait_impls!r}",
            )
        )
    impl_blocks = _rust_inherent_impl_blocks(production, name)
    if len(impl_blocks) != 1:
        findings.append(
            Finding(
                "B1B1_RUST_IMPL_SURFACE",
                str(RUST_PATH),
                f"{name}: expected one inherent impl, got {len(impl_blocks)}",
            )
        )
        return
    methods = _rust_impl_methods(impl_blocks[0])
    if methods != EXPECTED_RUST_METHODS[name]:
        findings.append(
            Finding(
                "B1B1_RUST_IMPL_SURFACE",
                str(RUST_PATH),
                f"{name}: methods {methods!r}",
            )
        )
    if re.search(
        r"(?:^|\n)\s*(?:pub(?:\([^)]*\))?\s+)?(?:const|type)\b",
        impl_blocks[0],
    ):
        findings.append(
            Finding(
                "B1B1_RUST_IMPL_SURFACE",
                str(RUST_PATH),
                f"{name}: associated const or type",
            )
        )


def _check_rust_macro_surface(
    production: str,
    name: str,
    findings: list[Finding],
) -> None:
    masked = _rust_mask_non_code(production)
    delimiters = {"(": ")", "{": "}", "[": "]"}
    for match in re.finditer(
        r"\b(?P<macro>[A-Za-z_][A-Za-z0-9_]*)!\s*(?P<opening>[({\[])",
        masked,
    ):
        opening_character = match.group("opening")
        opening = masked.find(opening_character, match.start(), match.end())
        closing = _rust_matching_delimiter(
            masked,
            opening,
            opening_character,
            delimiters[opening_character],
        )
        segment_end = len(masked) if closing is None else closing + 1
        segment = masked[match.start():segment_end]
        if name in segment or _rust_top_level_at(masked, match.start()):
            findings.append(
                Finding(
                    "B1B1_RUST_IMPL_SURFACE",
                    str(RUST_PATH),
                    f"{name}: macro-generated surface",
                )
            )
            return
    if "macro_rules!" in masked:
        findings.append(
            Finding(
                "B1B1_RUST_IMPL_SURFACE",
                str(RUST_PATH),
                f"{name}: macro definition surface",
            )
        )


def _check_rust_carrier_data_surface(
    production: str,
    findings: list[Finding],
) -> None:
    masked = _rust_mask_non_code(production)
    for match in re.finditer(
        r"(?:\bpub(?:\([^)]*\))?\s+)?\b(?:const|static|type)\s+"
        r"[A-Za-z_][A-Za-z0-9_]*[^;]*;",
        masked,
        re.DOTALL,
    ):
        if not _rust_top_level_at(masked, match.start()):
            continue
        segment = match.group(0)
        carrier = next((name for name in RUST_CARRIER_NAMES if name in segment), None)
        if carrier is not None:
            findings.append(
                Finding(
                    "B1B1_RUST_IMPL_SURFACE",
                    str(RUST_PATH),
                    f"{carrier}: unchecked const, static, or type surface",
                )
            )


def _check_rust_root_domains(text: str, findings: list[Finding]) -> None:
    for assignment, expected in EXPECTED_ROOT_DOMAINS.items():
        token = f'pub const {assignment}: &str = "{expected}";'
        if token not in text:
            findings.append(
                Finding("B1B1_RUST_ROOT_DOMAIN", str(RUST_PATH), assignment)
            )


def _check_rust_module_export(root: Path, findings: list[Finding]) -> None:
    lib_text = _read(root, RUST_LIB_PATH)
    carrier_lines = tuple(
        line.strip()
        for line in lib_text.splitlines()
        if "fcis_b1b_authority" in line
        or any(name in line for name in RUST_CARRIER_NAMES)
    )
    if carrier_lines != ("pub mod fcis_b1b_authority;",):
        findings.append(
            Finding(
                "B1B1_RUST_MODULE_EXPORT",
                str(RUST_LIB_PATH),
                f"carrier references {carrier_lines!r}",
            )
        )


def _check_rust_carriers(root: Path, findings: list[Finding]) -> None:
    text = _read(root, RUST_PATH)
    production = _rust_production_text(text)
    for name, expected_fields in EXPECTED_RUST_STRUCT_FIELDS.items():
        _check_rust_struct_shape(text, name, expected_fields, findings)
        _check_rust_impl_surface(production, name, findings)
        _check_rust_macro_surface(production, name, findings)
    _check_rust_carrier_data_surface(production, findings)
    _check_rust_root_domains(text, findings)
    _check_rust_function_surface(text, findings)
    _check_rust_module_export(root, findings)


def _runtime_candidate_paths(root: Path) -> tuple[Path, ...]:
    result: set[Path] = set()
    for relative_root in RUNTIME_SCAN_ROOTS:
        scan_root = root / relative_root
        if not scan_root.is_dir():
            continue
        for suffix in ("*.py", "*.rs"):
            result.update(
                path
                for path in scan_root.rglob(suffix)
                if path.is_file()
                and not any(part in RUNTIME_EXCLUDED_PARTS for part in path.parts)
            )
    return tuple(sorted(result))


def _check_runtime_reachability(root: Path, findings: list[Finding]) -> int:
    allowed = {path.as_posix() for path in (*PYTHON_PATHS, RUST_PATH, RUST_LIB_PATH)}
    markers = (
        "fcis_b1b_authority",
        *tuple(PYTHON_CARRIER_NAMES),
        *tuple(RUST_CARRIER_NAMES),
    )
    paths = _runtime_candidate_paths(root)
    for path in paths:
        relative = path.relative_to(root).as_posix()
        if path.stat().st_size > MAX_RUNTIME_SOURCE_BYTES:
            findings.append(
                Finding(
                    "B1B1_RUNTIME_SCAN_LIMIT",
                    relative,
                    f"{path.stat().st_size} bytes",
                )
            )
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as exc:
            findings.append(
                Finding("B1B1_RUNTIME_PARSE", relative, f"UTF-8: {exc.start}")
            )
            continue
        for symbol in FORBIDDEN_AUTHORITY_SYMBOLS:
            if symbol in text:
                findings.append(
                    Finding("B1B1_PREMATURE_AUTHORITY", relative, symbol)
                )
        if relative in allowed:
            continue
        marker = next((candidate for candidate in markers if candidate in text), None)
        if marker is not None:
            code = (
                "B1B1_RUST_CARRIER_CONSUMER"
                if path.suffix == ".rs"
                else "B1B1_RUNTIME_REACHABILITY"
            )
            findings.append(Finding(code, relative, marker))
    return len(paths)


def check_repository(root: Path) -> Report:
    root = root.resolve()
    findings: list[Finding] = []
    for path in REQUIRED_PATHS:
        if not (root / path).is_file():
            findings.append(
                Finding("MISSING_PATH", str(path), "required file is absent")
            )
    if findings:
        return Report(False, tuple(findings), 0)

    _check_revision_blob(root, findings)
    _check_forbidden_paths(root, findings)
    _check_python_carriers(root, findings)
    if not findings:
        _check_runtime_dataclass_fields(root, findings)
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
