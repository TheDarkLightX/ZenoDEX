"""Build the exact O-007B cross-language source and operation projection."""

from __future__ import annotations

import ast
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Sequence

from tools.m6_cross_language_sinks.model import (
    DynamicImportDeclarationV1,
    GeneratedIncludeOwnerV1,
    canonical_root,
)
from tools.m6_cross_language_sinks.operations import (
    generated_python_owner,
    language_operation_definitions,
    scan_generated_python_source,
    scan_rust_source,
    scan_shell_source,
    scan_tau_source,
)
from tools.m6_value_sinks.deployment import derive_python_deployment_closure

MAX_SOURCE_BYTES = 16 * 1024 * 1024
MANIFEST_SCHEMA = "zenodex/m6-cross-language-value-sinks/v1"
PROJECTION_SCHEMA = "zenodex/m6-cross-language-value-sink-projection/v1"

_DYNAMIC_IMPORT_ATTRIBUTES = frozenset(
    {"exec_module", "import_module", "load_module", "spec_from_file_location"}
)
_RISC0_GENERATED_INCLUDE_RE = re.compile(
    r'include!\s*\(\s*concat!\s*\(\s*env!\s*\(\s*"OUT_DIR"\s*\)\s*,\s*"/methods\.rs"'
)
_RUST_LANE_VARIANT_RE = re.compile(r"^\s*(?P<name>[A-Z][A-Z0-9_]*)\s*,\s*$", re.MULTILINE)
_SHELL_SHEBANG_RE = re.compile(rb"\A#![^\n]*\b(?:ba|da|z|k)?sh\b")


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _tracked_paths(root: Path) -> tuple[str, ...]:
    process = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z"],
        check=False,
        capture_output=True,
    )
    if process.returncode != 0:
        stderr = process.stderr.decode("utf-8", errors="replace").strip()
        raise ValueError(f"git ls-files failed: {stderr}")
    try:
        decoded = process.stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise ValueError(f"git path inventory is not UTF-8: {exc}") from exc
    return tuple(sorted(path for path in decoded.split("\0") if path))


def _is_candidate(root: Path, path: str) -> bool:
    if path.endswith((".rs", ".tau", ".sh")):
        return True
    if path.endswith(".py") and (
        path.startswith("generated/")
        or (path.startswith("src/fire/kernel/") and path.endswith("_ref.py"))
    ):
        return True
    if PurePosixPath(path).name.startswith("Dockerfile"):
        return True
    candidate = _contained_regular_file(root, path)
    if candidate is None:
        return False
    try:
        with candidate.open("rb") as source:
            return _SHELL_SHEBANG_RE.search(source.readline(256)) is not None
    except OSError:
        return False


def _language(path: str) -> str:
    if path.endswith(".rs"):
        return "RUST"
    if path.endswith(".tau"):
        return "TAU"
    return "PYTHON" if path.endswith(".py") else "SHELL"


def _provenance(language: str) -> str:
    return "GENERATED_REFERENCE" if language == "PYTHON" else "HANDWRITTEN"


def _source_role(path: str, language: str) -> str:
    parts = PurePosixPath(path).parts
    if path.startswith("deprecated/") or path.startswith("experiments/"):
        return "NONDEPLOYED_RESEARCH_SOURCE"
    if "tests" in parts or "test_methods" in parts or path.startswith("tests/"):
        return "NONDEPLOYED_TEST_SOURCE"
    if language == "RUST":
        if path.endswith("/build.rs"):
            return "RUST_BUILD_GENERATOR_SOURCE"
        if path.startswith(("zk/", "src/kernels/rust/", "tools/")):
            return "PRODUCTION_OR_PROOF_SOURCE"
        return "NONDEPLOYED_UNCLASSIFIED_RUST_SOURCE"
    if language == "TAU":
        if path.startswith("src/tau_specs/"):
            return "TAU_FORMAL_SPEC_SOURCE"
        if path.startswith("tools/logicspec/"):
            return "NONDEPLOYED_TOOL_SPEC_SOURCE"
        return "NONDEPLOYED_UNCLASSIFIED_TAU_SOURCE"
    if language == "SHELL":
        if PurePosixPath(path).name.startswith("Dockerfile"):
            return "CONTAINER_BUILD_SHELL"
        if path.startswith((".docker/", "scripts/", "tools/")):
            return "OPERATOR_OR_DEPLOYMENT_SHELL"
        if path.startswith("bin/"):
            return "DEPLOYED_LAUNCHER_SHELL"
        return "NONDEPLOYED_UNCLASSIFIED_SHELL_SOURCE"
    if language == "PYTHON":
        return "GENERATED_REFERENCE_SOURCE"
    return "NONDEPLOYED_UNCLASSIFIED_SOURCE"


def _contained_regular_file(root: Path, relative: str) -> Path | None:
    if not relative or relative.startswith("/") or "\\" in relative:
        return None
    if any(part in {"", ".", ".."} for part in relative.split("/")):
        return None
    candidate = root / relative
    try:
        resolved = candidate.resolve(strict=True)
    except (OSError, RuntimeError, ValueError):
        return None
    return resolved if resolved.is_relative_to(root) and resolved.is_file() else None


def _read_source(root: Path, relative: str) -> tuple[bytes, str]:
    path = _contained_regular_file(root, relative)
    if path is None:
        raise ValueError(f"{relative}: tracked source is not a contained regular file")
    raw = path.read_bytes()
    if len(raw) > MAX_SOURCE_BYTES:
        raise ValueError(f"{relative}: source exceeds {MAX_SOURCE_BYTES} bytes")
    try:
        return raw, raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{relative}: source is not UTF-8: {exc}") from exc


def discover_dynamic_imports(path: str, source: str) -> tuple[DynamicImportDeclarationV1, ...]:
    tree = ast.parse(source, filename=path)
    declarations: list[DynamicImportDeclarationV1] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        mechanism: str | None = None
        if isinstance(node.func, ast.Name) and node.func.id == "__import__":
            mechanism = "__import__"
        elif isinstance(node.func, ast.Attribute) and node.func.attr in _DYNAMIC_IMPORT_ATTRIBUTES:
            mechanism = node.func.attr
        if mechanism is None:
            continue
        targets = tuple(
            argument.value
            for argument in node.args
            if isinstance(argument, ast.Constant) and isinstance(argument.value, str)
        )
        fingerprint = canonical_root(
            {
                "ast": ast.dump(node, annotate_fields=True, include_attributes=False),
                "line": node.lineno,
                "mechanism": mechanism,
                "path": path,
            }
        )
        declarations.append(
            DynamicImportDeclarationV1(
                path=path,
                line=node.lineno,
                mechanism=mechanism,
                target_status="LITERAL" if targets else "UNRESOLVED",
                targets=targets,
                fingerprint=fingerprint,
            )
        )
    return tuple(sorted(declarations))


def discover_risc0_generated_includes(
    root: Path, rust_paths: Sequence[str]
) -> tuple[tuple[GeneratedIncludeOwnerV1, ...], tuple[str, ...]]:
    owners: list[GeneratedIncludeOwnerV1] = []
    findings: list[str] = []
    for path in sorted(rust_paths):
        source_path = _contained_regular_file(root, path)
        if source_path is None:
            continue
        raw = source_path.read_bytes()
        try:
            text = raw.decode("utf-8", errors="strict")
        except UnicodeDecodeError:
            continue
        if _RISC0_GENERATED_INCLUDE_RE.search(text) is None:
            continue
        parts = PurePosixPath(path).parts
        try:
            source_index = parts.index("src")
        except ValueError:
            findings.append(f"{path}: generated include is outside a crate src directory")
            continue
        crate = PurePosixPath(*parts[:source_index])
        build_path = (crate / "build.rs").as_posix()
        build = _contained_regular_file(root, build_path)
        if build is None:
            findings.append(f"{path}: generated include has no sibling {build_path}")
            continue
        build_raw = build.read_bytes()
        try:
            build_text = build_raw.decode("utf-8", errors="strict")
        except UnicodeDecodeError:
            findings.append(f"{build_path}: RISC0 build owner is not UTF-8")
            continue
        if "risc0_build::embed_methods" not in build_text:
            findings.append(f"{build_path}: generated include owner does not call embed_methods")
            continue
        owners.append(
            GeneratedIncludeOwnerV1(
                path=path,
                build_path=build_path,
                include_kind="RISC0_EMBED_METHODS_OUT_DIR",
                source_sha256=_sha256(raw),
                build_sha256=_sha256(build_raw),
            )
        )
    return tuple(sorted(owners)), tuple(sorted(findings))


def parse_rust_lane_ids(source: str, enum_name: str = "LaneIdV1") -> tuple[str, ...]:
    if enum_name not in {"LaneIdV1", "LaneIdV2"}:
        raise ValueError("Rust lane enum name is unsupported")
    enum_pattern = re.compile(
        rf"pub\s+enum\s+{re.escape(enum_name)}\s*\{{(?P<body>.*?)\}}",
        re.DOTALL,
    )
    match = enum_pattern.search(source)
    if match is None:
        raise ValueError(f"Rust {enum_name} enum is missing")
    lanes = tuple(_RUST_LANE_VARIANT_RE.findall(match.group("body")))
    if not lanes or len(lanes) != len(set(lanes)):
        raise ValueError(f"Rust {enum_name} enum is empty or duplicated")
    return lanes


def validate_command_lane_consistency(
    registry: dict[str, Any],
    rust_lane_ids: Sequence[str],
    governed_route_ids: Sequence[str] = (),
) -> tuple[str, ...]:
    findings: list[str] = []
    lane_set = frozenset(rust_lane_ids)
    route_set = frozenset(governed_route_ids)
    decisions = registry.get("decisions")
    if not isinstance(decisions, list):
        return ("O-006 registry decisions are missing",)
    for row in decisions:
        if not isinstance(row, dict):
            findings.append("O-006 registry decision is not an object")
            continue
        target_kind = row.get("target_kind")
        target = row.get("target_id")
        if target_kind == "LANE":
            if not isinstance(target, str) or target not in lane_set:
                findings.append(f"O-006 lane target {target} is absent from Rust lane enum")
        elif target_kind == "GOVERNED_ROUTE":
            if not isinstance(target, str) or target not in route_set:
                findings.append(
                    f"O-006 governed-route target {target} is absent from capability manifest"
                )
        else:
            findings.append(f"O-006 target kind {target_kind} is unsupported")
    return tuple(sorted(set(findings)))


def _scan_source(
    path: str, language: str, provenance: str, role: str, source: str
) -> tuple[dict[str, object], ...]:
    if language == "RUST":
        values = scan_rust_source(path, source, source_role=role)
    elif language == "TAU":
        values = scan_tau_source(path, source, source_role=role)
    elif language == "SHELL":
        values = scan_shell_source(path, source, source_role=role)
    elif language == "PYTHON" and provenance == "GENERATED_REFERENCE":
        values = scan_generated_python_source(path, source, source_role=role)
    else:
        raise ValueError(f"{path}: unsupported language/provenance pair")
    return tuple(value.to_dict() for value in values)


def _language_roots(rows: Iterable[dict[str, object]]) -> dict[str, str]:
    grouped: dict[str, list[dict[str, object]]] = {
        language: [] for language in ("PYTHON", "RUST", "SHELL", "TAU")
    }
    for row in rows:
        grouped.setdefault(str(row["language"]), []).append(row)
    return {language: canonical_root(values) for language, values in sorted(grouped.items())}


def _operation_occurrence_count(row: dict[str, object]) -> int:
    value = row["occurrence_count"]
    if type(value) is not int:
        raise ValueError("operation occurrence count is not an integer")
    return value


def _source_projection(
    root: Path, candidates: Sequence[str]
) -> tuple[list[dict[str, object]], list[dict[str, object]], list[dict[str, str]], list[str]]:
    sources: list[dict[str, object]] = []
    operations: list[dict[str, object]] = []
    owners: list[dict[str, str]] = []
    findings: list[str] = []
    for path in candidates:
        language = _language(path)
        provenance = _provenance(language)
        role = _source_role(path, language)
        try:
            raw, source = _read_source(root, path)
        except ValueError as exc:
            findings.append(str(exc))
            continue
        sources.append(
            {
                "language": language,
                "path": path,
                "provenance": provenance,
                "role": role,
                "sha256": _sha256(raw),
                "size": len(raw),
            }
        )
        try:
            operations.extend(_scan_source(path, language, provenance, role, source))
            if provenance == "GENERATED_REFERENCE":
                owners.append(generated_python_owner(path, source).to_dict())
        except (SyntaxError, ValueError) as exc:
            findings.append(str(exc))
    return sources, operations, owners, findings


def _dynamic_import_projection(root: Path) -> tuple[list[dict[str, object]], list[str]]:
    declarations: list[dict[str, object]] = []
    findings: list[str] = []
    closure = derive_python_deployment_closure(root)
    for path in closure.modules:
        candidate = _contained_regular_file(root, path)
        if candidate is None:
            continue
        raw = candidate.read_bytes()
        if len(raw) > MAX_SOURCE_BYTES:
            findings.append(f"{path}: dynamic-import source exceeds {MAX_SOURCE_BYTES} bytes")
            continue
        try:
            source = raw.decode("utf-8", errors="strict")
            declarations.extend(item.to_dict() for item in discover_dynamic_imports(path, source))
        except (SyntaxError, UnicodeDecodeError) as exc:
            findings.append(f"{path}: dynamic-import scan failed: {exc}")
    return sorted(declarations, key=lambda item: canonical_root(item)), findings


def _command_lane_projection(root: Path) -> tuple[dict[str, object], list[str]]:
    findings: list[str] = []
    registry_path = root / "docs" / "research" / "ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json"
    capability_path = root / "docs" / "research" / "ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"
    rust_v1_path = root / "zk" / "global_settlement_abi_v1" / "src" / "release.rs"
    rust_v2_path = root / "zk" / "global_settlement_abi_v2" / "src" / "effect_values.rs"
    try:
        registry_raw = registry_path.read_bytes()
        capability_raw = capability_path.read_bytes()
        rust_v1_raw = rust_v1_path.read_bytes()
        rust_v2_raw = rust_v2_path.read_bytes()
        registry = json.loads(registry_raw)
        capabilities = json.loads(capability_raw)
        rust_v1_lanes = parse_rust_lane_ids(
            rust_v1_raw.decode("utf-8", errors="strict"), "LaneIdV1"
        )
        rust_v2_lanes = parse_rust_lane_ids(
            rust_v2_raw.decode("utf-8", errors="strict"), "LaneIdV2"
        )
    except (OSError, UnicodeDecodeError, ValueError, json.JSONDecodeError) as exc:
        return {}, [f"command-to-lane source invalid: {exc}"]
    governed_routes = tuple(capabilities.get("required_cross_lane_routes", ()))
    if not governed_routes or any(type(route) is not str for route in governed_routes):
        findings.append("capability-manifest governed-route declarations are invalid")
        governed_routes = ()
    findings.extend(validate_command_lane_consistency(registry, rust_v1_lanes, governed_routes))
    findings.extend(validate_command_lane_consistency(registry, rust_v2_lanes, governed_routes))
    manifest_lanes = tuple(
        row.get("lane_id") for row in capabilities.get("lanes", []) if isinstance(row, dict)
    )
    if manifest_lanes != rust_v1_lanes:
        findings.append("capability-manifest lane order differs from Rust LaneIdV1")
    if manifest_lanes != rust_v2_lanes:
        findings.append("capability-manifest lane order differs from Rust LaneIdV2")
    if registry.get("registered_command_mapping_complete") is not True:
        findings.append("O-006 registered command mapping is incomplete")
    lane_targets = sorted(
        {
            str(row["target_id"])
            for row in registry.get("decisions", [])
            if isinstance(row, dict) and row.get("target_kind") == "LANE"
        }
    )
    route_targets = sorted(
        {
            str(row["target_id"])
            for row in registry.get("decisions", [])
            if isinstance(row, dict) and row.get("target_kind") == "GOVERNED_ROUTE"
        }
    )
    return (
        {
            "capability_manifest_sha256": _sha256(capability_raw),
            "o006_command_registry_sha256": _sha256(registry_raw),
            "o006_lane_targets": lane_targets,
            "o006_governed_route_targets": route_targets,
            "o006_registry_root": registry.get("registry_root"),
            "rust_lane_ids_v1": list(rust_v1_lanes),
            "rust_lane_ids_v2": list(rust_v2_lanes),
            "rust_lane_source_sha256_v1": _sha256(rust_v1_raw),
            "rust_lane_source_sha256_v2": _sha256(rust_v2_raw),
        },
        findings,
    )


def build_cross_language_projection(
    root: Path, *, tracked_paths: Sequence[str] | None = None
) -> dict[str, object]:
    root = root.resolve()
    strict_repository = tracked_paths is None
    all_tracked = _tracked_paths(root) if tracked_paths is None else tuple(sorted(tracked_paths))
    candidates = tuple(path for path in all_tracked if _is_candidate(root, path))
    sources, operations, generated_owners, findings = _source_projection(root, candidates)
    rust_paths = tuple(path for path in candidates if path.endswith(".rs"))
    include_owners, include_findings = discover_risc0_generated_includes(root, rust_paths)
    findings.extend(include_findings)
    dynamic_imports: list[dict[str, object]] = []
    command_lane: dict[str, object] = {}
    if strict_repository:
        dynamic_imports, dynamic_findings = _dynamic_import_projection(root)
        command_lane, command_findings = _command_lane_projection(root)
        findings.extend(dynamic_findings)
        findings.extend(command_findings)
    source_counts = Counter(str(row["language"]) for row in sources)
    provenance_counts = Counter(str(row["provenance"]) for row in sources)
    operation_row_counts = Counter(str(row["language"]) for row in operations)
    operation_occurrence_counts: Counter[str] = Counter()
    for row in operations:
        operation_occurrence_counts[str(row["language"])] += _operation_occurrence_count(row)
    unmediated = [
        row for row in operations if str(row["mediation_status"]).startswith("UNMEDIATED_")
    ]
    generated_replay_complete = bool(generated_owners) and all(
        owner["replay_binding"] == "PINNED_GENERATOR_REPLAY" for owner in generated_owners
    )
    projection: dict[str, object] = {
        "command_lane_consistency": command_lane,
        "discovery_findings": sorted(set(findings)),
        "dynamic_import_declarations": dynamic_imports,
        "dynamic_import_declarations_root": canonical_root(dynamic_imports),
        "generated_include_owners": [owner.to_dict() for owner in include_owners],
        "generated_include_owners_root": canonical_root(
            [owner.to_dict() for owner in include_owners]
        ),
        "generated_python_owners": generated_owners,
        "generated_python_owners_root": canonical_root(generated_owners),
        "generated_replay_ownership_complete": generated_replay_complete,
        "language_operation_definitions": language_operation_definitions(),
        "operation_occurrence_counts": dict(sorted(operation_occurrence_counts.items())),
        "operation_roots": _language_roots(operations),
        "operation_row_counts": dict(sorted(operation_row_counts.items())),
        "operations": operations,
        "schema": PROJECTION_SCHEMA,
        "source_counts": dict(sorted(source_counts.items())),
        "source_provenance_counts": dict(sorted(provenance_counts.items())),
        "source_roots": _language_roots(sources),
        "sources": sources,
        "tracked_candidate_count": len(candidates),
        "unmediated_operation_count": sum(_operation_occurrence_count(row) for row in unmediated),
        "unmediated_operation_root": canonical_root(unmediated),
    }
    projection["projection_root"] = canonical_root(projection)
    return projection


def compare_projection_to_manifest(
    projection: dict[str, object], manifest: dict[str, object]
) -> tuple[str, ...]:
    if set(manifest) != {"nonclaims", "projection", "review_status", "schema", "scope"}:
        return ("cross-language manifest has an open or incomplete field set",)
    if manifest.get("schema") != MANIFEST_SCHEMA:
        return ("cross-language manifest schema mismatch",)
    if manifest.get("review_status") != "REVIEWED_CURRENT_SUBJECT":
        return ("cross-language manifest is not reviewed for the current subject",)
    if manifest.get("projection") != projection:
        return ("cross-language projection does not match the reviewed manifest",)
    return ()
