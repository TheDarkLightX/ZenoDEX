#!/usr/bin/env python3
"""Check the recursive STARK Cargo graph against a pinned RISC0 advisory baseline.

The checker is deliberately offline. It validates a committed advisory snapshot,
every Cargo manifest in the recursive STARK workspace, and the resolved lockfile.
It does not claim that the snapshot is a complete current advisory database.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
import tomllib
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SNAPSHOT = ROOT / "config/proof_profiles/risc0_dependency_advisory_baseline.json"
REPORT_SCHEMA = "zenodex/risc0_dependency_advisory_baseline_check/v1"
SNAPSHOT_SCHEMA = "zenodex/risc0_dependency_advisory_baseline/v1"
ADVISORY_ID = "GHSA-jqq4-c7wq-36h7"
CVE_ID = "CVE-2025-61588"
ADVISORY_URL = "https://github.com/advisories/GHSA-jqq4-c7wq-36h7"
EXPECTED_SNAPSHOT_SHA256 = "sha256:b6f17b13168ddcfd4c06ecf83fdcd64d83fabbb306651a3040b2878896737d02"
REQUIRED_ZKVM_VERSION = "3.0.5"
REQUIRED_BUILD_VERSION = "3.0.5"
EXPECTED_PLATFORM_VERSION = "2.2.2"
MINIMUM_PLATFORM_VERSION = (2, 1, 0)
MAXIMUM_PLATFORM_VERSION = (3, 0, 0)
INVALIDATED_EVIDENCE_VERSIONS = ("1.2.6",)
EXPECTED_LOCK_RESOLUTIONS = {
    "risc0-build": {
        "version": "3.0.5",
        "checksum": "f89937fa1c424b188cc4cabf65335736eca9c1e3df79c127f48636f55682f3a4",
    },
    "risc0-zkvm": {
        "version": "3.0.5",
        "checksum": "22b7eafb5d85be59cbd9da83f662cf47d834f1b836e14f675d1530b12c666867",
    },
}
SAFE_PLATFORM_RESOLUTIONS = (
    {
        "version": "2.1.0",
        "checksum": "1e2dcebfc7103d98511f0fcb42f910c390ec5637d4bb3b463441fbcd30feeb1d",
    },
    {
        "version": "2.2.1",
        "checksum": "cfaa10feba15828c788837ddde84b994393936d8f5715228627cfe8625122a40",
    },
    {
        "version": "2.2.2",
        "checksum": "4db893788c416287e2e1a87e6b8f5302511a04a45329e699d6a32a16874fd24f",
    },
)
MAX_SNAPSHOT_BYTES = 1024 * 1024
MAX_MANIFEST_BYTES = 1024 * 1024
MAX_LOCK_BYTES = 32 * 1024 * 1024
MAX_DISCOVERY_ENTRIES = 4096
MAX_DISCOVERED_MANIFESTS = 64
MAX_DISCOVERY_DEPTH = 16
CRATES_IO_SOURCE = "registry+https://github.com/rust-lang/crates.io-index"

EXPECTED_MANIFEST_PATHS = (
    "Cargo.toml",
    "cli/Cargo.toml",
    "methods/Cargo.toml",
    "methods/aggregate/Cargo.toml",
    "methods/guest/Cargo.toml",
    "methods/perps_np_leaf/Cargo.toml",
    "methods/spot_leaf/Cargo.toml",
    "methods/summary_leaf/Cargo.toml",
    "methods/zusd_leaf/Cargo.toml",
    "shared/Cargo.toml",
)

EXPECTED_DIRECT_DEPENDENCIES: tuple[dict[str, Any], ...] = (
    {
        "manifest": "cli/Cargo.toml",
        "section": "dependencies",
        "crate": "risc0-zkvm",
        "version": "=3.0.5",
        "default_features": True,
        "features": ["disable-dev-mode"],
        "role": "host",
    },
    {
        "manifest": "methods/Cargo.toml",
        "section": "build-dependencies",
        "crate": "risc0-build",
        "version": "=3.0.5",
        "default_features": True,
        "features": [],
        "role": "build",
    },
    *(
        {
            "manifest": manifest,
            "section": "dependencies",
            "crate": "risc0-zkvm",
            "version": "=3.0.5",
            "default_features": False,
            "features": [],
            "role": "guest",
        }
        for manifest in (
            "methods/aggregate/Cargo.toml",
            "methods/guest/Cargo.toml",
            "methods/perps_np_leaf/Cargo.toml",
            "methods/spot_leaf/Cargo.toml",
            "methods/summary_leaf/Cargo.toml",
            "methods/zusd_leaf/Cargo.toml",
        )
    ),
)

RISC0_CRATES = frozenset({"risc0-zkvm", "risc0-build", "risc0-zkvm-platform"})
DEPENDENCY_SECTIONS = ("dependencies", "dev-dependencies", "build-dependencies")
STABLE_SEMVER_RE = re.compile(r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class BaselineInputError(ValueError):
    """Malformed local baseline input."""


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in out:
            raise BaselineInputError(f"duplicate JSON key: {key}")
        out[key] = value
    return out


def _reject_float(value: str) -> object:
    raise BaselineInputError(f"floating-point JSON value is forbidden: {value}")


def _read_bounded(path: Path, *, max_bytes: int) -> bytes:
    absolute = Path(os.path.abspath(path))
    try:
        resolved_parent = absolute.parent.resolve(strict=True)
    except OSError as exc:
        raise BaselineInputError(f"cannot resolve parent of {path.name}") from exc
    if resolved_parent != absolute.parent:
        raise BaselineInputError(f"ancestor symlink is forbidden: {path.name}")
    flags = os.O_RDONLY | _required_flag("O_NOFOLLOW") | getattr(os, "O_CLOEXEC", 0)
    descriptor: int | None = None
    try:
        descriptor = os.open(absolute, flags)
        return _read_bounded_fd(descriptor, max_bytes=max_bytes, label=path.name)
    except OSError as exc:
        raise BaselineInputError(f"cannot safely open {path.name}") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


def _load_snapshot(path: Path) -> tuple[Mapping[str, Any], str]:
    raw = _read_bounded(path, max_bytes=MAX_SNAPSHOT_BYTES)
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise BaselineInputError(f"advisory snapshot is invalid JSON: {exc}") from exc
    if not isinstance(value, Mapping):
        raise BaselineInputError("advisory snapshot must be an object")
    return value, "sha256:" + hashlib.sha256(raw).hexdigest()


def _parse_toml(raw: bytes, *, label: str) -> Mapping[str, Any]:
    try:
        value = tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise BaselineInputError(f"{label} is invalid TOML: {exc}") from exc
    if not isinstance(value, Mapping):
        raise BaselineInputError(f"{label} must be a TOML table")
    return value


def _read_bounded_fd(descriptor: int, *, max_bytes: int, label: str) -> bytes:
    before = os.fstat(descriptor)
    if not stat.S_ISREG(before.st_mode):
        raise BaselineInputError(f"{label} is not a regular file")
    if before.st_size > max_bytes:
        raise BaselineInputError(f"{label} exceeds size limit")
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = os.read(descriptor, min(1024 * 1024, max_bytes + 1 - total))
        if not chunk:
            break
        total += len(chunk)
        if total > max_bytes:
            raise BaselineInputError(f"{label} exceeds size limit")
        chunks.append(chunk)
    after = os.fstat(descriptor)
    before_identity = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
    after_identity = (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns)
    if total != before.st_size or before_identity != after_identity:
        raise BaselineInputError(f"{label} changed while it was read")
    return b"".join(chunks)


def _read_workspace_file(
    workspace: Path,
    relative_path: str,
    *,
    max_bytes: int,
) -> bytes:
    parts = _normalized_relative_parts(relative_path)
    directory_flags = os.O_RDONLY | _required_flag("O_DIRECTORY") | _required_flag(
        "O_NOFOLLOW"
    )
    directory_flags |= getattr(os, "O_CLOEXEC", 0)
    file_flags = os.O_RDONLY | _required_flag("O_NOFOLLOW") | getattr(os, "O_CLOEXEC", 0)
    directory_fds: list[int] = []
    file_fd: int | None = None
    try:
        directory_fds.append(os.open(workspace, directory_flags))
        current_fd = directory_fds[0]
        for component in parts[:-1]:
            component_stat = os.stat(component, dir_fd=current_fd, follow_symlinks=False)
            if stat.S_ISLNK(component_stat.st_mode):
                raise BaselineInputError(f"ancestor symlink is forbidden: {relative_path}")
            if not stat.S_ISDIR(component_stat.st_mode):
                raise BaselineInputError(f"non-directory path component: {relative_path}")
            current_fd = os.open(component, directory_flags, dir_fd=current_fd)
            directory_fds.append(current_fd)

        leaf_stat = os.stat(parts[-1], dir_fd=current_fd, follow_symlinks=False)
        if stat.S_ISLNK(leaf_stat.st_mode):
            raise BaselineInputError(f"symlink is forbidden: {relative_path}")
        if not stat.S_ISREG(leaf_stat.st_mode):
            raise BaselineInputError(f"{relative_path} is not a regular file")
        file_fd = os.open(parts[-1], file_flags, dir_fd=current_fd)
        opened_stat = os.fstat(file_fd)
        if (leaf_stat.st_dev, leaf_stat.st_ino) != (opened_stat.st_dev, opened_stat.st_ino):
            raise BaselineInputError(f"{relative_path} changed while it was opened")
        return _read_bounded_fd(file_fd, max_bytes=max_bytes, label=relative_path)
    except BaselineInputError:
        raise
    except OSError as exc:
        raise BaselineInputError(f"cannot safely open {relative_path}") from exc
    finally:
        if file_fd is not None:
            os.close(file_fd)
        for descriptor in reversed(directory_fds):
            os.close(descriptor)


def _normalized_relative_parts(value: str) -> tuple[str, ...]:
    if "\x00" in value or "\\" in value:
        raise BaselineInputError("workspace input path is not normalized")
    try:
        value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise BaselineInputError("workspace input path must contain ASCII only") from exc
    parsed = PurePosixPath(value)
    if (
        not value
        or parsed.is_absolute()
        or any(part in ("", ".", "..") for part in parsed.parts)
        or parsed.as_posix() != value
    ):
        raise BaselineInputError("workspace input path is not normalized")
    return parsed.parts


def _required_flag(name: str) -> int:
    value = getattr(os, name, None)
    if not isinstance(value, int):
        raise BaselineInputError(f"platform lacks required {name} support")
    return value


def _strict_semver(value: object) -> tuple[int, int, int] | None:
    if not isinstance(value, str):
        return None
    match = STABLE_SEMVER_RE.fullmatch(value)
    if match is None:
        return None
    return (int(match.group(1)), int(match.group(2)), int(match.group(3)))


def _snapshot_errors(snapshot: Mapping[str, Any], *, snapshot_hash: str) -> list[str]:
    errors: list[str] = []
    if snapshot_hash != EXPECTED_SNAPSHOT_SHA256:
        errors.append("snapshot SHA-256 mismatch")
    if snapshot.get("schema") != SNAPSHOT_SCHEMA:
        errors.append("snapshot schema mismatch")
    if snapshot.get("snapshot_id") != "risc0-ghsa-jqq4-c7wq-36h7-20260709":
        errors.append("snapshot id mismatch")
    source = snapshot.get("source")
    if not isinstance(source, Mapping):
        errors.append("snapshot source must be an object")
    else:
        expected_source = {
            "advisory_id": ADVISORY_ID,
            "cve_id": CVE_ID,
            "published": "2025-10-01",
            "severity": "critical",
            "updated": "2025-10-02",
            "url": ADVISORY_URL,
        }
        if dict(source) != expected_source:
            errors.append("snapshot advisory source mismatch")
    for key in ("advisory", "claims", "workspace_policy"):
        if not isinstance(snapshot.get(key), Mapping):
            errors.append(f"snapshot {key} must be an object")
    return errors


def _canonical_inspection_root(path: Path) -> Path:
    absolute = Path(os.path.abspath(path))
    try:
        resolved = absolute.resolve(strict=True)
        root_stat = absolute.lstat()
    except OSError as exc:
        raise BaselineInputError("inspection root is missing or inaccessible") from exc
    if resolved != absolute or stat.S_ISLNK(root_stat.st_mode):
        raise BaselineInputError("inspection root must not traverse symbolic links")
    if not stat.S_ISDIR(root_stat.st_mode):
        raise BaselineInputError("inspection root is not a directory")
    return absolute


def _canonical_workspace(root: Path) -> Path:
    workspace = root / "zk/state_proof_risc0"
    try:
        canonical = _canonical_inspection_root(workspace)
        canonical.relative_to(root)
    except (BaselineInputError, ValueError) as exc:
        raise BaselineInputError(
            "recursive STARK workspace is missing, unsafe, or outside the inspection root"
        ) from exc
    return canonical


def _discover_manifests(workspace: Path) -> tuple[list[str], list[str]]:
    paths: list[str] = []
    errors: list[str] = []
    entries_seen = 0
    stack: list[tuple[Path, tuple[str, ...]]] = [(workspace, ())]
    while stack:
        directory, relative_parts = stack.pop()
        try:
            entries: list[os.DirEntry[str]] = []
            with os.scandir(directory) as iterator:
                for entry in iterator:
                    entries_seen += 1
                    if entries_seen > MAX_DISCOVERY_ENTRIES:
                        raise BaselineInputError("Cargo manifest discovery entry cap exceeded")
                    entries.append(entry)
        except BaselineInputError:
            raise
        except OSError as exc:
            raise BaselineInputError("Cargo manifest discovery failed") from exc

        for entry in sorted(entries, key=lambda item: item.name, reverse=True):
            child_parts = (*relative_parts, entry.name)
            relative = "/".join(child_parts)
            if entry.is_symlink():
                errors.append(f"symlink entry is forbidden during discovery: {relative}")
                continue
            if entry.name == "Cargo.toml":
                if not entry.is_file(follow_symlinks=False):
                    errors.append(f"Cargo manifest is not a regular file: {relative}")
                    continue
                try:
                    _normalized_relative_parts(relative)
                except BaselineInputError as exc:
                    errors.append(f"Cargo manifest path rejected: {relative}: {exc}")
                    continue
                paths.append(relative)
                if len(paths) > MAX_DISCOVERED_MANIFESTS:
                    raise BaselineInputError("Cargo manifest discovery count cap exceeded")
                continue
            if entry.is_dir(follow_symlinks=False):
                if entry.name == "target":
                    continue
                if len(child_parts) > MAX_DISCOVERY_DEPTH:
                    raise BaselineInputError("Cargo manifest discovery depth cap exceeded")
                stack.append((Path(entry.path), child_parts))
                continue
    return sorted(paths), errors


def _input_record(relative_path: str, raw: bytes) -> dict[str, Any]:
    return {
        "path": f"zk/state_proof_risc0/{relative_path}",
        "sha256": "sha256:" + hashlib.sha256(raw).hexdigest(),
        "size_bytes": len(raw),
    }


def _input_root_sha256(records: Sequence[Mapping[str, Any]]) -> str:
    canonical = json.dumps(
        list(records),
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("ascii")
    return "sha256:" + hashlib.sha256(canonical).hexdigest()


def _dependency_sections(manifest: Mapping[str, Any]) -> list[tuple[str, Mapping[str, Any]]]:
    sections: list[tuple[str, Mapping[str, Any]]] = []
    for section_name in DEPENDENCY_SECTIONS:
        section = manifest.get(section_name)
        if isinstance(section, Mapping):
            sections.append((section_name, section))

    workspace = manifest.get("workspace")
    if isinstance(workspace, Mapping):
        section = workspace.get("dependencies")
        if isinstance(section, Mapping):
            sections.append(("workspace.dependencies", section))

    targets = manifest.get("target")
    if isinstance(targets, Mapping):
        for target_name in sorted(str(key) for key in targets):
            target = targets.get(target_name)
            if not isinstance(target, Mapping):
                continue
            for section_name in DEPENDENCY_SECTIONS:
                section = target.get(section_name)
                if isinstance(section, Mapping):
                    sections.append((f"target.{target_name}.{section_name}", section))
    return sections


def _dependency_record(
    *,
    manifest_path: str,
    section_name: str,
    crate: str,
    raw: object,
    errors: list[str],
) -> dict[str, Any]:
    prefix = f"{manifest_path}:{section_name}:{crate}"
    version: object
    if isinstance(raw, str):
        version = raw
        default_features = True
        features: list[str] = []
    elif isinstance(raw, Mapping):
        version = raw.get("version")
        default_features = raw.get("default-features", True)
        raw_features = raw.get("features", [])
        forbidden_sources = sorted(
            key for key in ("branch", "git", "package", "path", "registry", "rev", "tag", "workspace") if key in raw
        )
        if forbidden_sources:
            errors.append(f"{prefix} uses forbidden dependency source keys: {','.join(forbidden_sources)}")
        if not isinstance(raw_features, list) or any(
            not isinstance(feature, str) or not feature for feature in raw_features
        ):
            errors.append(f"{prefix} features must be a list of non-empty strings")
            features = []
        else:
            features = list(raw_features)
            if len(features) != len(set(features)):
                errors.append(f"{prefix} features contain duplicates")
    else:
        errors.append(f"{prefix} dependency declaration is malformed")
        version = None
        default_features = None
        features = []

    if not isinstance(version, str) or not version:
        errors.append(f"{prefix} must declare an exact version")
        version_text = ""
    else:
        version_text = version
    if not isinstance(default_features, bool):
        errors.append(f"{prefix} default-features must be boolean")
        default_features = False
    if version_text.removeprefix("=") in INVALIDATED_EVIDENCE_VERSIONS:
        errors.append(
            f"{prefix} uses invalidated vulnerable RISC0 version "
            f"{version_text.removeprefix('=')}"
        )

    return {
        "manifest": manifest_path,
        "section": section_name,
        "crate": crate,
        "version": version_text,
        "default_features": default_features,
        "features": sorted(features),
    }


def _manifest_dependency_records(
    workspace: Path,
    manifest_paths: Sequence[str],
    errors: list[str],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    records: list[dict[str, Any]] = []
    inputs: list[dict[str, Any]] = []
    for rel_path in manifest_paths:
        try:
            raw = _read_workspace_file(
                workspace,
                rel_path,
                max_bytes=MAX_MANIFEST_BYTES,
            )
        except BaselineInputError as exc:
            errors.append(str(exc))
            continue
        inputs.append(_input_record(rel_path, raw))
        try:
            manifest = _parse_toml(raw, label=rel_path)
        except BaselineInputError as exc:
            errors.append(str(exc))
            continue
        for section_name, section in _dependency_sections(manifest):
            risc0_entries: list[tuple[str, object]] = []
            for dependency_name, declaration in section.items():
                effective_crate = dependency_name
                if isinstance(declaration, Mapping):
                    package = declaration.get("package")
                    if isinstance(package, str):
                        effective_crate = package
                if effective_crate in RISC0_CRATES or dependency_name in RISC0_CRATES:
                    risc0_entries.append((str(effective_crate), declaration))
            for crate, declaration in sorted(risc0_entries, key=lambda item: item[0]):
                records.append(
                    _dependency_record(
                        manifest_path=rel_path,
                        section_name=section_name,
                        crate=crate,
                        raw=declaration,
                        errors=errors,
                    )
                )
    records.sort(key=lambda item: (item["manifest"], item["section"], item["crate"]))
    inputs.sort(key=lambda item: item["path"])
    return records, inputs


def _direct_dependency_errors(records: Sequence[Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    expected_without_role = [
        {key: value for key, value in item.items() if key != "role"}
        for item in EXPECTED_DIRECT_DEPENDENCIES
    ]
    expected_without_role.sort(key=lambda item: (item["manifest"], item["section"], item["crate"]))
    if list(records) != expected_without_role:
        errors.append("direct RISC0 dependency topology does not match the pinned baseline")

    host_records = [item for item in records if item.get("crate") == "risc0-zkvm" and item.get("manifest") == "cli/Cargo.toml"]
    if len(host_records) != 1:
        errors.append("host must declare exactly one risc0-zkvm dependency")
    elif host_records[0].get("features") != ["disable-dev-mode"]:
        errors.append("host risc0-zkvm dependency must enable only disable-dev-mode")

    for item in records:
        if item.get("crate") == "risc0-zkvm" and item.get("manifest") != "cli/Cargo.toml":
            if item.get("default_features") is not False:
                errors.append(f"guest {item.get('manifest')} must disable risc0-zkvm default features")
            if "disable-dev-mode" in item.get("features", []):
                errors.append(f"guest {item.get('manifest')} must not enable host-only disable-dev-mode")
    return errors


def _lock_errors(
    lock: Mapping[str, Any],
) -> tuple[list[str], dict[str, list[str]], dict[str, Any]]:
    errors: list[str] = []
    advisory_safety: dict[str, Any] = {
        "zkvm_affected_ranges": ["<2.3.2", ">=3.0.0,<3.0.3"],
        "platform_safe_range": {
            "minimum_inclusive": "2.1.0",
            "maximum_exclusive": "3.0.0",
        },
        "platform_versions_in_safe_range": False,
        "platform_resolution_in_reviewed_safe_set": False,
    }
    if lock.get("version") != 4:
        errors.append("Cargo.lock format version must be 4")
    packages = lock.get("package")
    if not isinstance(packages, list):
        return [*errors, "Cargo.lock package must be an array"], {}, advisory_safety

    by_name: dict[str, list[Mapping[str, Any]]] = {name: [] for name in RISC0_CRATES}
    for index, package in enumerate(packages):
        if not isinstance(package, Mapping):
            errors.append(f"Cargo.lock package[{index}] must be an object")
            continue
        name = package.get("name")
        if name in by_name:
            by_name[str(name)].append(package)

    versions: dict[str, list[str]] = {}
    for crate in sorted(RISC0_CRATES):
        rows = by_name[crate]
        versions[crate] = sorted(str(row.get("version", "")) for row in rows)
        if len(rows) != 1:
            errors.append(f"Cargo.lock must resolve exactly one {crate} package, found {len(rows)}")
        for row in rows:
            version = row.get("version")
            if _strict_semver(version) is None:
                errors.append(f"Cargo.lock {crate} version is malformed or unsupported: {version!r}")
            if row.get("source") != CRATES_IO_SOURCE:
                errors.append(f"Cargo.lock {crate} must resolve from crates.io")
            checksum = row.get("checksum")
            if not isinstance(checksum, str) or SHA256_RE.fullmatch(checksum) is None:
                errors.append(f"Cargo.lock {crate} checksum must be lowercase SHA-256")

    zkvm_versions = versions.get("risc0-zkvm", [])
    if zkvm_versions != [REQUIRED_ZKVM_VERSION]:
        errors.append(f"Cargo.lock risc0-zkvm must resolve only {REQUIRED_ZKVM_VERSION}")
    for version in zkvm_versions:
        parsed = _strict_semver(version)
        if parsed is not None and (parsed < (2, 3, 2) or (3, 0, 0) <= parsed < (3, 0, 3)):
            errors.append(f"Cargo.lock risc0-zkvm {version} is affected by {ADVISORY_ID}")

    build_versions = versions.get("risc0-build", [])
    if build_versions != [REQUIRED_BUILD_VERSION]:
        errors.append(f"Cargo.lock risc0-build must resolve only {REQUIRED_BUILD_VERSION}")

    for crate, expected in EXPECTED_LOCK_RESOLUTIONS.items():
        rows = by_name[crate]
        if len(rows) == 1 and (
            rows[0].get("version") != expected["version"]
            or rows[0].get("checksum") != expected["checksum"]
        ):
            errors.append(f"Cargo.lock {crate} resolution does not match the pinned checksum")

    platform_versions = versions.get("risc0-zkvm-platform", [])
    parsed_platform_versions = [
        parsed
        for version in platform_versions
        if (parsed := _strict_semver(version)) is not None
    ]
    advisory_safety["platform_versions_in_safe_range"] = (
        len(parsed_platform_versions) == 1
        and len(platform_versions) == 1
        and MINIMUM_PLATFORM_VERSION
        <= parsed_platform_versions[0]
        < MAXIMUM_PLATFORM_VERSION
    )
    if platform_versions != [EXPECTED_PLATFORM_VERSION]:
        errors.append(
            "Cargo.lock risc0-zkvm-platform must resolve exactly 2.2.2 "
            "for baseline acceptance"
        )
    for version in platform_versions:
        parsed = _strict_semver(version)
        if parsed is None:
            continue
        if not MINIMUM_PLATFORM_VERSION <= parsed < MAXIMUM_PLATFORM_VERSION:
            errors.append(
                "Cargo.lock risc0-zkvm-platform must be a stable version in [2.1.0,3.0.0)"
            )
        if parsed < MINIMUM_PLATFORM_VERSION:
            errors.append(f"Cargo.lock risc0-zkvm-platform {version} is affected by {ADVISORY_ID}")
    platform_rows = by_name["risc0-zkvm-platform"]
    if len(platform_rows) == 1:
        resolution = {
            "version": platform_rows[0].get("version"),
            "checksum": platform_rows[0].get("checksum"),
        }
        advisory_safety["platform_resolution_in_reviewed_safe_set"] = (
            resolution in SAFE_PLATFORM_RESOLUTIONS
        )
        if resolution not in SAFE_PLATFORM_RESOLUTIONS:
            errors.append("Cargo.lock risc0-zkvm-platform resolution is not in the pinned safe set")
    return errors, versions, advisory_safety


def check_risc0_dependency_advisory_baseline(
    *,
    root: Path = ROOT,
    snapshot_path: Path = DEFAULT_SNAPSHOT,
) -> dict[str, Any]:
    errors: list[str] = []
    snapshot_hash = ""
    try:
        snapshot, snapshot_hash = _load_snapshot(snapshot_path)
    except BaselineInputError as exc:
        snapshot = {}
        errors.append(str(exc))
    errors.extend(_snapshot_errors(snapshot, snapshot_hash=snapshot_hash))

    inspected_root: Path | None = None
    workspace: Path | None = None
    discovered_paths: list[str] = []
    dependency_records: list[dict[str, Any]] = []
    lock_versions: dict[str, list[str]] = {}
    advisory_safety: dict[str, Any] = {
        "zkvm_affected_ranges": ["<2.3.2", ">=3.0.0,<3.0.3"],
        "platform_safe_range": {
            "minimum_inclusive": "2.1.0",
            "maximum_exclusive": "3.0.0",
        },
        "platform_versions_in_safe_range": False,
        "platform_resolution_in_reviewed_safe_set": False,
    }
    inspected_inputs: list[dict[str, Any]] = []
    try:
        inspected_root = _canonical_inspection_root(root)
        workspace = _canonical_workspace(inspected_root)
        discovered_paths, discovery_errors = _discover_manifests(workspace)
        errors.extend(discovery_errors)
    except BaselineInputError as exc:
        errors.append(str(exc))

    if workspace is not None:
        if discovered_paths != list(EXPECTED_MANIFEST_PATHS):
            errors.append("Cargo manifest path set does not match the pinned baseline")
        dependency_records, manifest_inputs = _manifest_dependency_records(
            workspace, discovered_paths, errors
        )
        inspected_inputs.extend(manifest_inputs)
        errors.extend(_direct_dependency_errors(dependency_records))

        try:
            lock_raw = _read_workspace_file(
                workspace,
                "Cargo.lock",
                max_bytes=MAX_LOCK_BYTES,
            )
            inspected_inputs.append(_input_record("Cargo.lock", lock_raw))
            lock = _parse_toml(lock_raw, label="Cargo.lock")
        except BaselineInputError as exc:
            errors.append(str(exc))
        else:
            lock_failures, lock_versions, advisory_safety = _lock_errors(lock)
            errors.extend(lock_failures)

    errors = list(dict.fromkeys(errors))
    inspected_inputs.sort(key=lambda item: item["path"])
    claims_value = snapshot.get("claims")
    claims: Mapping[str, Any] = claims_value if isinstance(claims_value, Mapping) else {}
    platform_versions = lock_versions.get("risc0-zkvm-platform", [])
    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "offline": True,
        "snapshot_sha256": snapshot_hash,
        "advisory_id": ADVISORY_ID,
        "inspected_root": str(inspected_root) if inspected_root is not None else None,
        "input_root_sha256": _input_root_sha256(inspected_inputs),
        "inspected_inputs": inspected_inputs,
        "manifest_count": len(discovered_paths),
        "manifest_paths": discovered_paths,
        "direct_dependencies": dependency_records,
        "lock_versions": lock_versions,
        "platform_matches_expected": platform_versions == [EXPECTED_PLATFORM_VERSION],
        "advisory_safety": advisory_safety,
        "invalidated_evidence_versions": list(INVALIDATED_EVIDENCE_VERSIONS),
        "old_evidence_status": claims.get("old_evidence_status", ""),
        "claim_scope": "dependency_and_advisory_baseline_only",
        "production_ready": False,
    }


def _print_human(report: Mapping[str, Any]) -> None:
    if report.get("ok") is True:
        print(
            f"ok {report['advisory_id']} "
            f"risc0-zkvm={report['lock_versions']['risc0-zkvm'][0]}"
        )
        return
    print("error: RISC0 dependency advisory baseline check failed", file=sys.stderr)
    for error in report.get("errors", []):
        print(f"  - {error}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--snapshot", type=Path, default=DEFAULT_SNAPSHOT)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = check_risc0_dependency_advisory_baseline(
        root=args.root,
        snapshot_path=args.snapshot,
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_human(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
