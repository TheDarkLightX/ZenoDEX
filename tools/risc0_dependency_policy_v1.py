"""Fail-closed RISC0 manifest and Cargo.lock activation policy."""

from __future__ import annotations

import hashlib
import re
import tomllib
from pathlib import Path
from typing import Any, Mapping

from tools.risc0_dependency_inventory_v1 import (
    GOVERNED_RISC0_REQUIREMENT,
    GOVERNED_RISC0_VERSION,
    LEGACY_QUARANTINE_RESOLVED_VERSION,
    LEGACY_QUARANTINE_WORKSPACE,
    PolicyFinding,
    collect_risc0_dependencies_v1,
    quarantine_row_v1,
)

RISC0_POLICY_SCHEMA = "zenodex/risc0_dependency_policy_check/v1"
HEX_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def audit_risc0_dependency_policy_v1(root: Path) -> dict[str, Any]:
    """Audit every source RISC0 dependency and its workspace lock."""

    root = root.resolve()
    findings: list[PolicyFinding] = []
    documents, dependencies, manifest_hashes = collect_risc0_dependencies_v1(root, findings)
    policy_input_sha256 = _workspace_manifest_hashes(dependencies, manifest_hashes)
    _audit_workspace_locks(root, dependencies, findings, policy_input_sha256)
    if not dependencies:
        findings.append(
            PolicyFinding(
                "zk",
                "no_risc0_dependencies",
                "at least one source RISC0 core dependency must be present",
            )
        )

    quarantined_workspaces = sorted(
        {row["workspace"] for row in dependencies if row["status"] == "quarantined_legacy"}
    )
    quarantines = [
        quarantine_row_v1()
        for path in quarantined_workspaces
        if path == LEGACY_QUARANTINE_WORKSPACE
    ]
    ok = not findings
    activation_eligible = ok and not quarantines
    return {
        "schema": RISC0_POLICY_SCHEMA,
        "ok": ok,
        "status": (
            "activation_eligible"
            if activation_eligible
            else "inventory_valid_quarantined"
            if ok
            else "rejected"
        ),
        "activation_eligible": activation_eligible,
        "governed_version": GOVERNED_RISC0_VERSION,
        "governed_requirement": GOVERNED_RISC0_REQUIREMENT,
        "manifest_count": len(documents),
        "workspace_count": len({row["workspace"] for row in dependencies}),
        "dependency_count": len(dependencies),
        "governed_dependency_count": sum(row["status"] == "governed" for row in dependencies),
        "quarantined_dependency_count": sum(
            row["status"] == "quarantined_legacy" for row in dependencies
        ),
        "dependencies": dependencies,
        "quarantines": quarantines,
        "policy_input_sha256": dict(sorted(policy_input_sha256.items())),
        "findings": [finding.to_json() for finding in findings],
    }


def _workspace_manifest_hashes(
    dependencies: list[dict[str, Any]],
    manifest_hashes: dict[str, str],
) -> dict[str, str]:
    workspaces = {row["workspace"] for row in dependencies}
    return {
        path: digest
        for path, digest in manifest_hashes.items()
        if any(path == f"{workspace}/Cargo.toml" or path.startswith(f"{workspace}/") for workspace in workspaces)
    }


def _audit_workspace_locks(
    root: Path,
    dependencies: list[dict[str, Any]],
    findings: list[PolicyFinding],
    policy_input_sha256: dict[str, str],
) -> None:
    by_workspace: dict[str, set[str]] = {}
    for row in dependencies:
        by_workspace.setdefault(row["workspace"], set()).add(row["package"])
    for workspace, package_names in sorted(by_workspace.items()):
        _audit_workspace_lock(root, workspace, package_names, findings, policy_input_sha256)


def _audit_workspace_lock(
    root: Path,
    workspace: str,
    package_names: set[str],
    findings: list[PolicyFinding],
    policy_input_sha256: dict[str, str],
) -> None:
    lock_path = root / workspace / "Cargo.lock"
    lock_rel = lock_path.relative_to(root).as_posix()
    if not lock_path.is_file() or lock_path.is_symlink():
        findings.append(
            PolicyFinding(lock_rel, "missing_regular_cargo_lock", "workspace Cargo.lock is required")
        )
        return
    try:
        source = lock_path.read_bytes()
        lock = tomllib.loads(source.decode("utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        findings.append(PolicyFinding(lock_rel, "invalid_cargo_lock", f"cannot parse Cargo.lock: {exc}"))
        return
    policy_input_sha256[lock_rel] = "sha256:" + hashlib.sha256(source).hexdigest()
    packages = lock.get("package")
    if not isinstance(packages, list):
        findings.append(PolicyFinding(lock_rel, "invalid_cargo_lock", "Cargo.lock package list is required"))
        return
    for package_name in sorted(package_names):
        matching = [
            package
            for package in packages
            if isinstance(package, Mapping) and package.get("name") == package_name
        ]
        _audit_locked_package(workspace, lock_rel, package_name, matching, findings)


def _audit_locked_package(
    workspace: str,
    lock_rel: str,
    package_name: str,
    packages: list[Mapping[str, Any]],
    findings: list[PolicyFinding],
) -> None:
    if not packages:
        findings.append(
            PolicyFinding(lock_rel, "missing_core_lock_package", f"{package_name} is absent from Cargo.lock")
        )
        return
    if len(packages) != 1:
        findings.append(
            PolicyFinding(
                lock_rel,
                "duplicate_core_lock_package",
                f"{package_name} must have exactly one Cargo.lock package row",
            )
        )
    versions = _locked_versions(packages)
    if len(versions) != 1:
        findings.append(
            PolicyFinding(
                lock_rel,
                "mixed_core_package_versions",
                f"{package_name} resolves to {versions!r}; exactly one version is required",
            )
        )
    _audit_locked_version(workspace, lock_rel, package_name, versions, findings)
    for package in packages:
        _audit_locked_source(lock_rel, package_name, package, findings)


def _locked_versions(packages: list[Mapping[str, Any]]) -> list[str]:
    versions: set[str] = set()
    for package in packages:
        version = package.get("version")
        if isinstance(version, str):
            versions.add(version)
    return sorted(versions)


def _audit_locked_version(
    workspace: str,
    lock_rel: str,
    package_name: str,
    versions: list[str],
    findings: list[PolicyFinding],
) -> None:
    expected_version = (
        LEGACY_QUARANTINE_RESOLVED_VERSION
        if workspace == LEGACY_QUARANTINE_WORKSPACE
        else GOVERNED_RISC0_VERSION
    )
    if versions == [expected_version]:
        return
    code = (
        "quarantine_lock_version_drift"
        if workspace == LEGACY_QUARANTINE_WORKSPACE
        else "wrong_governed_lock_version"
    )
    findings.append(
        PolicyFinding(
            lock_rel,
            code,
            f"{package_name} lock version must equal {expected_version!r}; got {versions!r}",
        )
    )


def _audit_locked_source(
    lock_rel: str,
    package_name: str,
    package: Mapping[str, Any],
    findings: list[PolicyFinding],
) -> None:
    source = package.get("source")
    checksum = package.get("checksum")
    if not isinstance(source, str) or not source.startswith("registry+"):
        findings.append(
            PolicyFinding(
                lock_rel,
                "non_registry_core_package",
                f"{package_name} must resolve from a registry source",
            )
        )
    if not isinstance(checksum, str) or HEX_SHA256_RE.fullmatch(checksum) is None:
        findings.append(
            PolicyFinding(
                lock_rel,
                "registry_checksum_missing",
                f"{package_name} must carry an exact 64-hex Cargo checksum",
            )
        )
