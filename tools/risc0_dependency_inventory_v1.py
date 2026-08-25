"""Deterministic source inventory for RISC0 Cargo dependency policy."""

from __future__ import annotations

import hashlib
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

GOVERNED_RISC0_VERSION = "3.0.6"
GOVERNED_RISC0_REQUIREMENT = "=3.0.6"
RISC0_CORE_PACKAGES = frozenset({"risc0-build", "risc0-zkvm"})
DEPENDENCY_SECTIONS = ("dependencies", "dev-dependencies", "build-dependencies")
LEGACY_QUARANTINE_WORKSPACE = "zk/state_proof_risc0"
LEGACY_QUARANTINE_REQUIREMENT = "1.2"
LEGACY_QUARANTINE_RESOLVED_VERSION = "1.2.6"
LEGACY_QUARANTINE_NONCLAIM = (
    "Historical regression source only. This workspace has authority NONE and is ineligible "
    "for governed release, settlement, claim promotion, or production admission."
)


@dataclass(frozen=True)
class PolicyFinding:
    path: str
    code: str
    message: str

    def to_json(self) -> dict[str, str]:
        return {"path": self.path, "code": self.code, "message": self.message}


def quarantine_row_v1() -> dict[str, Any]:
    return {
        "workspace": LEGACY_QUARANTINE_WORKSPACE,
        "authority": "NONE",
        "activation_eligible": False,
        "advisory": "GHSA-jqq4-c7wq-36h7",
        "nonclaim": LEGACY_QUARANTINE_NONCLAIM,
    }


def collect_risc0_dependencies_v1(
    root: Path,
    findings: list[PolicyFinding],
) -> tuple[dict[Path, Mapping[str, Any]], list[dict[str, Any]], dict[str, str]]:
    documents, manifest_hashes = _load_cargo_documents(root, findings)
    dependencies = _collect_risc0_dependencies(root, documents, findings)
    return documents, dependencies, manifest_hashes


def _source_cargo_manifests(root: Path) -> tuple[Path, ...]:
    zk_root = root / "zk"
    if not zk_root.is_dir():
        return ()
    return tuple(
        path
        for path in sorted(zk_root.rglob("Cargo.toml"))
        if path.is_file() and "target" not in path.relative_to(zk_root).parts
    )


def _load_cargo_documents(
    root: Path,
    findings: list[PolicyFinding],
) -> tuple[dict[Path, Mapping[str, Any]], dict[str, str]]:
    documents: dict[Path, Mapping[str, Any]] = {}
    manifest_hashes: dict[str, str] = {}
    for path in _source_cargo_manifests(root):
        rel_path = path.relative_to(root).as_posix()
        if path.is_symlink():
            findings.append(
                PolicyFinding(rel_path, "symlink_manifest", "Cargo manifests must be regular files")
            )
            continue
        try:
            source = path.read_bytes()
            document = tomllib.loads(source.decode("utf-8"))
        except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
            findings.append(
                PolicyFinding(rel_path, "invalid_cargo_manifest", f"cannot parse Cargo manifest: {exc}")
            )
            continue
        documents[path] = document
        manifest_hashes[rel_path] = "sha256:" + hashlib.sha256(source).hexdigest()
    return documents, manifest_hashes


def _iter_dependency_tables(
    document: Mapping[str, Any],
) -> Iterable[tuple[str, Mapping[str, Any]]]:
    for section in DEPENDENCY_SECTIONS:
        table = document.get(section)
        if isinstance(table, Mapping):
            yield section, table
    target = document.get("target")
    if not isinstance(target, Mapping):
        return
    for target_name, target_table in sorted(target.items()):
        if not isinstance(target_table, Mapping):
            continue
        for section in DEPENDENCY_SECTIONS:
            table = target_table.get(section)
            if isinstance(table, Mapping):
                yield f"target.{target_name}.{section}", table


def _workspace_root_for_manifest(
    manifest_path: Path,
    documents: Mapping[Path, Mapping[str, Any]],
    root: Path,
) -> Path:
    zk_root = root / "zk"
    current = manifest_path.parent
    while current == zk_root or zk_root in current.parents:
        document = documents.get(current / "Cargo.toml")
        if document is not None and isinstance(document.get("workspace"), Mapping):
            return current
        if current == zk_root:
            break
        current = current.parent
    return manifest_path.parent


def _workspace_dependency(
    dependency_name: str,
    workspace_root: Path,
    documents: Mapping[Path, Mapping[str, Any]],
) -> Any:
    document = documents.get(workspace_root / "Cargo.toml", {})
    workspace = document.get("workspace")
    if not isinstance(workspace, Mapping):
        return None
    dependencies = workspace.get("dependencies")
    if not isinstance(dependencies, Mapping):
        return None
    return dependencies.get(dependency_name)


def _effective_dependency_spec(
    dependency_name: str,
    raw_spec: Any,
    workspace_root: Path,
    documents: Mapping[Path, Mapping[str, Any]],
    path: str,
    findings: list[PolicyFinding],
) -> Mapping[str, Any] | None:
    if isinstance(raw_spec, str):
        return {"version": raw_spec, "_table_form": False}
    if not isinstance(raw_spec, Mapping):
        findings.append(
            PolicyFinding(path, "invalid_dependency_spec", f"{dependency_name} must be a string or object")
        )
        return None
    if raw_spec.get("workspace") is not True:
        return {**raw_spec, "_table_form": True}

    inherited = _workspace_dependency(dependency_name, workspace_root, documents)
    if inherited is None:
        findings.append(
            PolicyFinding(
                path,
                "missing_workspace_dependency",
                f"{dependency_name} uses workspace inheritance without a workspace declaration",
            )
        )
        return None
    inherited_spec = _effective_dependency_spec(
        dependency_name,
        inherited,
        workspace_root,
        documents,
        path,
        findings,
    )
    if inherited_spec is None:
        return None
    member_spec = {key: value for key, value in raw_spec.items() if key != "workspace"}
    return {**inherited_spec, **member_spec}


def _collect_risc0_dependencies(
    root: Path,
    documents: Mapping[Path, Mapping[str, Any]],
    findings: list[PolicyFinding],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for manifest_path, document in sorted(documents.items()):
        workspace_root = _workspace_root_for_manifest(manifest_path, documents, root)
        workspace_rel = workspace_root.relative_to(root).as_posix()
        manifest_rel = manifest_path.relative_to(root).as_posix()
        for section, table in _iter_dependency_tables(document):
            for dependency_name, raw_spec in sorted(table.items()):
                if not _might_reference_risc0(
                    dependency_name,
                    raw_spec,
                    workspace_root,
                    documents,
                ):
                    continue
                spec = _effective_dependency_spec(
                    dependency_name,
                    raw_spec,
                    workspace_root,
                    documents,
                    manifest_rel,
                    findings,
                )
                if spec is None:
                    continue
                package_name = _package_name(dependency_name, spec, manifest_rel, findings)
                if package_name not in RISC0_CORE_PACKAGES:
                    continue
                rows.append(
                    _audit_risc0_dependency(
                        manifest_rel,
                        workspace_rel,
                        section,
                        dependency_name,
                        package_name,
                        spec,
                        findings,
                    )
                )
    return sorted(rows, key=lambda row: (row["manifest"], row["section"], row["package"]))


def _package_name(
    dependency_name: str,
    spec: Mapping[str, Any],
    manifest: str,
    findings: list[PolicyFinding],
) -> str | None:
    package_name = spec.get("package", dependency_name)
    if isinstance(package_name, str):
        return package_name
    findings.append(
        PolicyFinding(
            manifest,
            "invalid_dependency_package",
            f"{dependency_name} package alias must be a string",
        )
    )
    return None


def _might_reference_risc0(
    dependency_name: str,
    raw_spec: Any,
    workspace_root: Path,
    documents: Mapping[Path, Mapping[str, Any]],
) -> bool:
    if dependency_name in RISC0_CORE_PACKAGES:
        return True
    if isinstance(raw_spec, Mapping) and raw_spec.get("package") in RISC0_CORE_PACKAGES:
        return True
    if not isinstance(raw_spec, Mapping) or raw_spec.get("workspace") is not True:
        return False
    inherited = _workspace_dependency(dependency_name, workspace_root, documents)
    return isinstance(inherited, Mapping) and inherited.get("package") in RISC0_CORE_PACKAGES


def _audit_risc0_dependency(
    manifest: str,
    workspace: str,
    section: str,
    dependency_name: str,
    package_name: str,
    spec: Mapping[str, Any],
    findings: list[PolicyFinding],
) -> dict[str, Any]:
    requirement = spec.get("version")
    status = "quarantined_legacy" if workspace == LEGACY_QUARANTINE_WORKSPACE else "governed"
    expected_requirement = (
        LEGACY_QUARANTINE_REQUIREMENT
        if status == "quarantined_legacy"
        else GOVERNED_RISC0_REQUIREMENT
    )
    if requirement != expected_requirement:
        code = (
            "quarantine_requirement_drift"
            if status == "quarantined_legacy"
            else "non_exact_governed_requirement"
        )
        findings.append(
            PolicyFinding(
                manifest,
                code,
                f"{package_name} requirement must equal {expected_requirement!r}; got {requirement!r}",
            )
        )
    for source_key in ("git", "path", "registry"):
        if source_key in spec:
            findings.append(
                PolicyFinding(
                    manifest,
                    "unsupported_dependency_source",
                    f"{package_name} must use the governed crates.io lock, not {source_key}",
                )
            )
    if status == "governed" and package_name == "risc0-zkvm":
        _audit_zkvm_features(manifest, spec, findings)
    return {
        "manifest": manifest,
        "workspace": workspace,
        "section": section,
        "dependency": dependency_name,
        "package": package_name,
        "requirement": requirement,
        "status": status,
    }


def _audit_zkvm_features(
    manifest: str,
    spec: Mapping[str, Any],
    findings: list[PolicyFinding],
) -> None:
    path_parts = Path(manifest).parts
    verifier_role = "host" in path_parts or "cli" in path_parts
    guest_role = "methods" in path_parts or "test_methods" in path_parts
    features = spec.get("features")
    if features is None:
        feature_set: set[str] = set()
    elif isinstance(features, list) and all(isinstance(value, str) for value in features):
        feature_set = {value for value in features if isinstance(value, str)}
    else:
        findings.append(
            PolicyFinding(
                manifest,
                "invalid_zkvm_features",
                "risc0-zkvm features must be a list of strings",
            )
        )
        feature_set = set()
    if verifier_role and "disable-dev-mode" not in feature_set:
        findings.append(
            PolicyFinding(
                manifest,
                "host_disable_dev_mode_missing",
                "governed host and CLI dependencies must enable disable-dev-mode",
            )
        )
    if guest_role and spec.get("default-features") is not False:
        findings.append(
            PolicyFinding(
                manifest,
                "guest_default_features_enabled",
                "governed guest dependencies must set default-features = false",
            )
        )
    if not verifier_role and not guest_role:
        findings.append(
            PolicyFinding(
                manifest,
                "unknown_zkvm_dependency_role",
                "governed risc0-zkvm dependencies must live in an explicit host, CLI, or methods role",
            )
        )
