#!/usr/bin/env python3
"""Validate the pinned local RISC0 recursive-STARK toolchain lock."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tomllib
from collections.abc import Callable, Iterator, Mapping, Sequence
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, TypeAlias

ROOT = Path(__file__).resolve().parents[1]
LOCK_PATH = ROOT / "config/proof_profiles/risc0_recursive_toolchain_lock.json"

LOCK_SCHEMA = "zenodex/risc0_recursive_toolchain_lock/v1"
REPORT_SCHEMA = "zenodex/risc0_recursive_toolchain_lock_check/v1"
EXPECTED_CANONICAL_LOCK_SHA256 = (
    "a43db82911a5c3ba75112cd0c0b2d311e8d0bda6ef0c1d988ac1fa268c41e13a"
)
EXPECTED_SCOPE = "local_recursive_stark_toolchain_pin"
EXPECTED_CLAIM = "local_installed_toolchain_matches_pinned_artifacts"
EXPECTED_ARTIFACT_IDS = (
    "cargo-risczero",
    "r0vm",
    "rustc",
    "rustdoc",
    "cargo",
    "guest-libcore",
)
EXPECTED_RUSTUP_ARTIFACTS = ("rustc", "cargo")
MAX_LOCK_BYTES = 1024 * 1024
MAX_COMMAND_OUTPUT_BYTES = 16 * 1024
COMMAND_TIMEOUT_SECONDS = 15
HASH_CHUNK_BYTES = 1024 * 1024


class LockError(ValueError):
    """A deterministic lock validation or installed-file rejection."""


@dataclass(frozen=True)
class CommandResult:
    returncode: int
    stdout: bytes
    stderr: bytes


CommandRunner: TypeAlias = Callable[
    [Sequence[str], Mapping[str, str], tuple[int, ...]], CommandResult
]


def load_lock_manifest(path: Path = LOCK_PATH) -> Any:
    """Load a bounded, regular JSON file while rejecting duplicate keys."""

    raw = _read_regular_path(path, max_size_bytes=MAX_LOCK_BYTES)
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise LockError("lock file must be UTF-8") from exc
    try:
        return json.loads(
            text,
            object_pairs_hook=_unique_json_object,
            parse_float=_reject_json_float,
            parse_constant=_reject_json_constant,
        )
    except LockError:
        raise
    except json.JSONDecodeError as exc:
        raise LockError("lock file must contain valid JSON") from exc


def validate_lock_manifest(manifest: Any) -> dict[str, Any]:
    """Validate the committed policy object against its canonical digest."""

    errors: list[str] = []
    if not isinstance(manifest, Mapping):
        errors.append("manifest must be an object")
        return _manifest_report(manifest, errors, canonical_sha256=None)

    if manifest.get("schema") != LOCK_SCHEMA:
        errors.append("schema mismatch")
    if manifest.get("version") != 1:
        errors.append("version must be 1")
    if manifest.get("scope") != EXPECTED_SCOPE:
        errors.append("scope mismatch")

    expected_claims = {
        "accepted_claim": EXPECTED_CLAIM,
        "production_ready": False,
        "reproducible_build": False,
        "requires_verify_installed": True,
        "settlement_authorization": False,
    }
    if manifest.get("claims") != expected_claims:
        errors.append("claims policy mismatch")

    expected_security_policy = {
        "advisory_id": "GHSA-jqq4-c7wq-36h7",
        "advisory_url": (
            "https://github.com/risc0/risc0/security/advisories/"
            "GHSA-jqq4-c7wq-36h7"
        ),
        "invalidated_sdk_versions": ["1.2.6"],
        "minimum_patched_3_x": "3.0.3",
        "required_sdk_version": "3.0.5",
    }
    if manifest.get("security_policy") != expected_security_policy:
        errors.append("security policy mismatch")

    artifacts = manifest.get("installed_artifacts")
    if not isinstance(artifacts, list):
        errors.append("installed_artifacts must be a list")
    else:
        artifact_ids: list[str] = []
        for index, artifact in enumerate(artifacts):
            if not isinstance(artifact, Mapping):
                errors.append(f"installed_artifacts[{index}] must be an object")
                continue
            artifact_id = artifact.get("id")
            if isinstance(artifact_id, str):
                artifact_ids.append(artifact_id)
            else:
                errors.append(f"installed_artifacts[{index}].id must be a string")
            _validate_relative_path(
                artifact.get("relative_path"),
                f"installed_artifacts[{index}].relative_path",
                errors,
            )
            _validate_sha256(
                artifact.get("sha256"),
                f"installed_artifacts[{index}].sha256",
                errors,
            )
            _validate_size_pair(artifact, f"installed_artifacts[{index}]", errors)
        if tuple(artifact_ids) != EXPECTED_ARTIFACT_IDS:
            errors.append("installed artifact ids or order mismatch")

    settings = manifest.get("rzup_settings")
    if not isinstance(settings, Mapping):
        errors.append("rzup_settings must be an object")
    else:
        _validate_relative_path(
            settings.get("relative_path"), "rzup_settings.relative_path", errors
        )

    _validate_declared_hashes(manifest, errors)
    canonical_sha256 = _canonical_manifest_sha256(manifest)
    if canonical_sha256 != EXPECTED_CANONICAL_LOCK_SHA256:
        errors.append("canonical lock policy digest mismatch")
    return _manifest_report(manifest, errors, canonical_sha256=canonical_sha256)


def check_risc0_recursive_toolchain_lock(
    *,
    path: Path = LOCK_PATH,
    verify_installed: bool = False,
    risc0_home: Path | None = None,
    runner: CommandRunner | None = None,
    rustup_path: Path | None = None,
) -> dict[str, Any]:
    """Check the exact manifest, optionally verifying a local installation."""

    try:
        manifest = load_lock_manifest(path)
    except (LockError, OSError) as exc:
        return _base_report(
            mode="installed" if verify_installed else "manifest",
            errors=[str(exc)],
            canonical_sha256=None,
        )

    report = validate_lock_manifest(manifest)
    if not verify_installed or not report["ok"]:
        return report

    if risc0_home is None:
        errors = ["RISC0_HOME is required with --verify-installed"]
        return _merge_installed_report(report, errors=errors)

    command_runner = runner or _default_command_runner
    installed = _verify_installed_toolchain(
        manifest,
        risc0_home=risc0_home,
        runner=command_runner,
        rustup_path=rustup_path,
    )
    return _merge_installed_report(
        report,
        errors=installed["errors"],
        verified_artifacts=installed["verified_artifacts"],
        settings_verified=installed["settings_verified"],
        rustup_aliases_verified=installed["rustup_aliases_verified"],
    )


def _verify_installed_toolchain(
    manifest: Mapping[str, Any],
    *,
    risc0_home: Path,
    runner: CommandRunner,
    rustup_path: Path | None,
) -> dict[str, Any]:
    errors: list[str] = []
    verified_artifacts: list[str] = []
    settings_verified = False
    rustup_aliases_verified: list[str] = []

    try:
        canonical_home = _canonical_directory_without_symlinks(risc0_home)
    except LockError as exc:
        errors.append(f"RISC0_HOME: {exc}")
        return {
            "errors": errors,
            "verified_artifacts": verified_artifacts,
            "settings_verified": settings_verified,
            "rustup_aliases_verified": rustup_aliases_verified,
        }

    settings = manifest["rzup_settings"]
    try:
        _verify_rzup_settings(canonical_home, settings)
        settings_verified = True
    except LockError as exc:
        errors.append(f"rzup_settings: {exc}")

    artifacts_by_id: dict[str, Mapping[str, Any]] = {}
    for artifact in manifest["installed_artifacts"]:
        artifact_id = str(artifact["id"])
        artifacts_by_id[artifact_id] = artifact
        try:
            _verify_installed_artifact(
                canonical_home,
                artifact,
                runner=runner,
            )
            verified_artifacts.append(artifact_id)
        except LockError as exc:
            errors.append(f"installed_artifacts[{artifact_id}]: {exc}")

    if all(artifact_id in verified_artifacts for artifact_id in EXPECTED_RUSTUP_ARTIFACTS):
        try:
            rustup_aliases_verified = _verify_rustup_aliases(
                canonical_home,
                artifacts_by_id,
                runner=runner,
                rustup_path=rustup_path,
            )
        except LockError as exc:
            errors.append(f"rustup: {exc}")

    return {
        "errors": errors,
        "verified_artifacts": verified_artifacts,
        "settings_verified": settings_verified,
        "rustup_aliases_verified": rustup_aliases_verified,
    }


def _verify_rzup_settings(root: Path, settings: Mapping[str, Any]) -> None:
    relative_path = str(settings["relative_path"])
    max_size_bytes = int(settings["max_size_bytes"])
    with _open_regular_under_root(
        root,
        relative_path,
        max_size_bytes=max_size_bytes,
        exact_size_bytes=None,
        require_executable=False,
    ) as descriptor:
        raw, _snapshot = _read_and_hash_descriptor(
            descriptor, max_size_bytes=max_size_bytes, retain_bytes=True
        )
    try:
        decoded = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise LockError("settings.toml must be UTF-8") from exc
    try:
        parsed = tomllib.loads(decoded)
    except tomllib.TOMLDecodeError as exc:
        raise LockError("settings.toml must contain valid TOML") from exc
    expected = {"default_versions": dict(settings["default_versions"])}
    if parsed != expected:
        raise LockError("settings.toml defaults mismatch")


def _verify_installed_artifact(
    root: Path,
    artifact: Mapping[str, Any],
    *,
    runner: CommandRunner,
) -> None:
    relative_path = str(artifact["relative_path"])
    max_size_bytes = int(artifact["max_size_bytes"])
    exact_size_bytes = int(artifact["size_bytes"])
    executable = bool(artifact["executable"])
    with _open_regular_under_root(
        root,
        relative_path,
        max_size_bytes=max_size_bytes,
        exact_size_bytes=exact_size_bytes,
        require_executable=executable,
    ) as descriptor:
        digest, snapshot = _read_and_hash_descriptor(
            descriptor, max_size_bytes=max_size_bytes, retain_bytes=False
        )
        if digest != artifact["sha256"]:
            raise LockError("sha256 mismatch")
        version_check = artifact.get("version_check")
        if version_check is not None:
            _verify_version_output(descriptor, version_check, runner=runner)
        _require_unchanged_descriptor(descriptor, snapshot)


def _verify_version_output(
    descriptor: int,
    version_check: Mapping[str, Any],
    *,
    runner: CommandRunner,
) -> None:
    proc_path = f"/proc/self/fd/{descriptor}"
    if not Path(proc_path).exists():
        raise LockError("descriptor execution is unavailable")
    arguments = [str(value) for value in version_check["arguments"]]
    try:
        result = runner(
            [proc_path, *arguments],
            _sanitized_command_environment(include_rustup_home=False),
            (descriptor,),
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise LockError("version command could not be executed") from exc
    stdout = _checked_command_stdout(result, purpose="version command")
    output_format = version_check["format"]
    if output_format == "exact_stdout":
        if stdout != version_check["expected_stdout"]:
            raise LockError("sanitized version output mismatch")
        return
    if output_format != "key_value_stdout":
        raise LockError("unsupported version output format")
    _verify_key_value_version_output(stdout, version_check)


def _verify_key_value_version_output(
    stdout: str, version_check: Mapping[str, Any]
) -> None:
    if not stdout.endswith("\n") or "\n\n" in stdout:
        raise LockError("malformed version output")
    lines = stdout[:-1].split("\n")
    if not lines or lines[0] != version_check["expected_summary"]:
        raise LockError("sanitized version summary mismatch")

    fields: dict[str, str] = {}
    for line in lines[1:]:
        key, separator, value = line.partition(": ")
        if not separator or not key or not value:
            raise LockError("malformed version output field")
        if key in fields:
            raise LockError("duplicate version output field")
        fields[key] = value

    expected_fields = dict(version_check["expected_fields"])
    for key, value in expected_fields.items():
        if fields.get(key) != value:
            raise LockError(f"sanitized version field mismatch: {key}")
    allowed_fields = set(expected_fields) | set(version_check["allowed_extra_fields"])
    unexpected = sorted(set(fields) - allowed_fields)
    if unexpected:
        raise LockError("unexpected version output fields")


def _verify_rustup_aliases(
    root: Path,
    artifacts_by_id: Mapping[str, Mapping[str, Any]],
    *,
    runner: CommandRunner,
    rustup_path: Path | None,
) -> list[str]:
    if rustup_path is None:
        discovered = shutil.which("rustup")
        if discovered is None:
            raise LockError("rustup executable was not found")
        rustup_path = Path(discovered)
    try:
        executable = rustup_path.resolve(strict=True)
    except OSError as exc:
        raise LockError("rustup executable could not be resolved") from exc
    try:
        executable_stat = executable.stat()
    except OSError as exc:
        raise LockError("rustup executable could not be inspected") from exc
    if not stat.S_ISREG(executable_stat.st_mode) or not os.access(executable, os.X_OK):
        raise LockError("rustup executable is not an executable regular file")

    verified: list[str] = []
    for artifact_id in EXPECTED_RUSTUP_ARTIFACTS:
        artifact = artifacts_by_id[artifact_id]
        try:
            result = runner(
                [str(executable), "+risc0", "which", artifact_id],
                _sanitized_command_environment(include_rustup_home=True),
                (),
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise LockError(f"+risc0 {artifact_id} resolution failed") from exc
        stdout = _checked_command_stdout(
            result, purpose=f"rustup +risc0 which {artifact_id}"
        )
        if not stdout.endswith("\n") or stdout.count("\n") != 1:
            raise LockError(f"+risc0 {artifact_id} returned a malformed path")
        resolved_text = stdout[:-1]
        resolved_path = Path(resolved_text)
        if not resolved_path.is_absolute():
            raise LockError(f"+risc0 {artifact_id} returned a relative path")
        try:
            resolved = resolved_path.resolve(strict=True)
            expected = (root / str(artifact["relative_path"])).resolve(strict=True)
        except OSError as exc:
            raise LockError(f"+risc0 {artifact_id} path could not be resolved") from exc
        if resolved != expected:
            raise LockError(f"+risc0 {artifact_id} resolves outside the pinned toolchain")
        verified.append(artifact_id)
    return verified


def _canonical_directory_without_symlinks(path: Path) -> Path:
    absolute = Path(os.path.abspath(path))
    try:
        resolved = absolute.resolve(strict=True)
        path_stat = absolute.lstat()
    except OSError as exc:
        raise LockError("directory is missing or inaccessible") from exc
    if resolved != absolute or stat.S_ISLNK(path_stat.st_mode):
        raise LockError("directory path must not traverse symbolic links")
    if not stat.S_ISDIR(path_stat.st_mode):
        raise LockError("path is not a directory")
    return absolute


@contextmanager
def _open_regular_under_root(
    root: Path,
    relative_path: str,
    *,
    max_size_bytes: int,
    exact_size_bytes: int | None,
    require_executable: bool,
) -> Iterator[int]:
    parts = _relative_path_parts(relative_path)
    directory_flags = _required_open_flag("O_DIRECTORY") | _required_open_flag(
        "O_NOFOLLOW"
    )
    directory_flags |= os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    file_flags = os.O_RDONLY | _required_open_flag("O_NOFOLLOW")
    file_flags |= getattr(os, "O_CLOEXEC", 0)

    directory_descriptors: list[int] = []
    file_descriptor: int | None = None
    try:
        root_descriptor = os.open(root, directory_flags)
        directory_descriptors.append(root_descriptor)
        current_descriptor = root_descriptor
        for component in parts[:-1]:
            component_stat = os.stat(
                component, dir_fd=current_descriptor, follow_symlinks=False
            )
            if stat.S_ISLNK(component_stat.st_mode):
                raise LockError("relative path contains a symbolic link")
            if not stat.S_ISDIR(component_stat.st_mode):
                raise LockError("relative path contains a non-directory component")
            next_descriptor = os.open(
                component, directory_flags, dir_fd=current_descriptor
            )
            directory_descriptors.append(next_descriptor)
            current_descriptor = next_descriptor

        leaf = parts[-1]
        leaf_stat = os.stat(leaf, dir_fd=current_descriptor, follow_symlinks=False)
        if stat.S_ISLNK(leaf_stat.st_mode):
            raise LockError("artifact path is a symbolic link")
        if not stat.S_ISREG(leaf_stat.st_mode):
            raise LockError("artifact path is not a regular file")
        file_descriptor = os.open(leaf, file_flags, dir_fd=current_descriptor)
        opened_stat = os.fstat(file_descriptor)
        if (leaf_stat.st_dev, leaf_stat.st_ino) != (
            opened_stat.st_dev,
            opened_stat.st_ino,
        ):
            raise LockError("artifact changed while it was opened")
        if not stat.S_ISREG(opened_stat.st_mode):
            raise LockError("artifact path is not a regular file")
        if opened_stat.st_size > max_size_bytes:
            raise LockError("artifact exceeds its maximum size")
        if exact_size_bytes is not None and opened_stat.st_size != exact_size_bytes:
            raise LockError("artifact size mismatch")
        if require_executable and opened_stat.st_mode & 0o111 == 0:
            raise LockError("artifact is not executable")
        yield file_descriptor
    except LockError:
        raise
    except OSError as exc:
        raise LockError("artifact path is missing or unsafe") from exc
    finally:
        if file_descriptor is not None:
            os.close(file_descriptor)
        for descriptor in reversed(directory_descriptors):
            os.close(descriptor)


def _read_and_hash_descriptor(
    descriptor: int,
    *,
    max_size_bytes: int,
    retain_bytes: bool,
) -> tuple[Any, os.stat_result]:
    before = os.fstat(descriptor)
    os.lseek(descriptor, 0, os.SEEK_SET)
    digest = hashlib.sha256()
    retained = bytearray()
    total = 0
    while True:
        chunk = os.read(descriptor, HASH_CHUNK_BYTES)
        if not chunk:
            break
        total += len(chunk)
        if total > max_size_bytes:
            raise LockError("artifact exceeds its maximum size")
        digest.update(chunk)
        if retain_bytes:
            retained.extend(chunk)
    after = os.fstat(descriptor)
    if total != before.st_size or _stat_identity(before) != _stat_identity(after):
        raise LockError("artifact changed while it was read")
    if retain_bytes:
        return bytes(retained), after
    return digest.hexdigest(), after


def _require_unchanged_descriptor(
    descriptor: int, expected: os.stat_result
) -> None:
    current = os.fstat(descriptor)
    if _stat_identity(current) != _stat_identity(expected):
        raise LockError("artifact changed during verification")


def _stat_identity(value: os.stat_result) -> tuple[int, int, int, int, int]:
    return (
        value.st_dev,
        value.st_ino,
        value.st_size,
        value.st_mtime_ns,
        value.st_ctime_ns,
    )


def _read_regular_path(path: Path, *, max_size_bytes: int) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    flags |= _required_open_flag("O_NOFOLLOW")
    descriptor: int | None = None
    try:
        descriptor = os.open(path, flags)
        file_stat = os.fstat(descriptor)
        if not stat.S_ISREG(file_stat.st_mode):
            raise LockError("lock path is not a regular file")
        if file_stat.st_size > max_size_bytes:
            raise LockError("lock file exceeds its maximum size")
        raw, _snapshot = _read_and_hash_descriptor(
            descriptor, max_size_bytes=max_size_bytes, retain_bytes=True
        )
        return raw
    except LockError:
        raise
    except OSError as exc:
        raise LockError("lock file is missing or unsafe") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)


def _default_command_runner(
    argv: Sequence[str], env: Mapping[str, str], pass_fds: tuple[int, ...]
) -> CommandResult:
    completed = subprocess.run(
        list(argv),
        check=False,
        capture_output=True,
        env=dict(env),
        pass_fds=pass_fds,
        timeout=COMMAND_TIMEOUT_SECONDS,
    )
    return CommandResult(
        returncode=completed.returncode,
        stdout=completed.stdout,
        stderr=completed.stderr,
    )


def _sanitized_command_environment(*, include_rustup_home: bool) -> dict[str, str]:
    env = {
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    if include_rustup_home:
        for name in ("HOME", "RUSTUP_HOME"):
            value = os.environ.get(name)
            if value:
                env[name] = value
    return env


def _checked_command_stdout(result: CommandResult, *, purpose: str) -> str:
    if result.returncode != 0:
        raise LockError(f"{purpose} failed")
    if result.stderr:
        raise LockError(f"{purpose} wrote to stderr")
    if len(result.stdout) > MAX_COMMAND_OUTPUT_BYTES:
        raise LockError(f"{purpose} output exceeds its maximum size")
    try:
        stdout = result.stdout.decode("ascii")
    except UnicodeDecodeError as exc:
        raise LockError(f"{purpose} output must be ASCII") from exc
    if any(character != "\n" and not (" " <= character <= "~") for character in stdout):
        raise LockError(f"{purpose} output contains control characters")
    return stdout


def _manifest_report(
    manifest: Any,
    errors: list[str],
    *,
    canonical_sha256: str | None,
) -> dict[str, Any]:
    report = _base_report(
        mode="manifest", errors=errors, canonical_sha256=canonical_sha256
    )
    if isinstance(manifest, Mapping):
        report["manifest_schema"] = manifest.get("schema")
        report["sdk_version"] = _nested_value(
            manifest, "security_policy", "required_sdk_version"
        )
        report["guest_rust_release"] = _nested_value(
            manifest, "source_pins", "guest_rust", "release_tag"
        )
        report["artifact_count"] = _safe_length(manifest.get("installed_artifacts"))
        report["crate_count"] = _safe_length(manifest.get("crate_archives"))
    return report


def _base_report(
    *, mode: str, errors: list[str], canonical_sha256: str | None
) -> dict[str, Any]:
    ok = not errors
    claim = "manifest_policy_valid" if ok and mode == "manifest" else "none"
    return {
        "schema": REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "mode": mode,
        "claim": claim,
        "errors": errors,
        "canonical_lock_sha256": (
            f"sha256:{canonical_sha256}" if canonical_sha256 is not None else None
        ),
        "non_claims": [
            "reproducible_build",
            "production_readiness",
            "settlement_authorization",
        ],
    }


def _merge_installed_report(
    report: Mapping[str, Any],
    *,
    errors: list[str],
    verified_artifacts: list[str] | None = None,
    settings_verified: bool = False,
    rustup_aliases_verified: list[str] | None = None,
) -> dict[str, Any]:
    merged_errors = [*report["errors"], *errors]
    ok = not merged_errors
    return {
        **report,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "mode": "installed",
        "claim": EXPECTED_CLAIM if ok else "none",
        "errors": merged_errors,
        "verified_artifacts": verified_artifacts or [],
        "settings_verified": settings_verified,
        "rustup_aliases_verified": rustup_aliases_verified or [],
    }


def _validate_declared_hashes(manifest: Mapping[str, Any], errors: list[str]) -> None:
    for group_name in ("release_archives", "crate_archives"):
        group = manifest.get(group_name)
        if not isinstance(group, list):
            errors.append(f"{group_name} must be a list")
            continue
        for index, entry in enumerate(group):
            if not isinstance(entry, Mapping):
                errors.append(f"{group_name}[{index}] must be an object")
                continue
            _validate_sha256(entry.get("sha256"), f"{group_name}[{index}].sha256", errors)
            _validate_positive_int(
                entry.get("size_bytes"), f"{group_name}[{index}].size_bytes", errors
            )
            url = entry.get("url")
            if not isinstance(url, str) or not url.startswith("https://"):
                errors.append(f"{group_name}[{index}].url must use HTTPS")

    kernel = manifest.get("recursion_kernel")
    if not isinstance(kernel, Mapping):
        errors.append("recursion_kernel must be an object")
    else:
        _validate_sha256(kernel.get("sha256"), "recursion_kernel.sha256", errors)
        _validate_positive_int(
            kernel.get("size_bytes"), "recursion_kernel.size_bytes", errors
        )
        _validate_relative_path(
            kernel.get("crate_member_path"),
            "recursion_kernel.crate_member_path",
            errors,
        )

    source_pins = manifest.get("source_pins")
    if not isinstance(source_pins, Mapping):
        errors.append("source_pins must be an object")
        return
    for source_name in ("risc0", "guest_rust"):
        source = source_pins.get(source_name)
        if not isinstance(source, Mapping):
            errors.append(f"source_pins.{source_name} must be an object")
            continue
        for key in ("git_commit_sha1", "git_tree_sha1"):
            value = source.get(key)
            if not isinstance(value, str) or len(value) != 40 or not _is_lower_hex(value):
                errors.append(f"source_pins.{source_name}.{key} must be 40 lowercase hex")


def _validate_size_pair(
    artifact: Mapping[str, Any], name: str, errors: list[str]
) -> None:
    size = _validate_positive_int(artifact.get("size_bytes"), f"{name}.size_bytes", errors)
    maximum = _validate_positive_int(
        artifact.get("max_size_bytes"), f"{name}.max_size_bytes", errors
    )
    if size is not None and maximum is not None and size > maximum:
        errors.append(f"{name}.size_bytes exceeds max_size_bytes")


def _validate_positive_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return value
    errors.append(f"{name} must be a positive integer")
    return None


def _validate_sha256(value: Any, name: str, errors: list[str]) -> None:
    if not isinstance(value, str) or len(value) != 64 or not _is_lower_hex(value):
        errors.append(f"{name} must be 64 lowercase hex")


def _is_lower_hex(value: str) -> bool:
    return all(character in "0123456789abcdef" for character in value)


def _validate_relative_path(value: Any, name: str, errors: list[str]) -> None:
    if not isinstance(value, str):
        errors.append(f"{name} must be a string")
        return
    try:
        _relative_path_parts(value)
    except LockError as exc:
        errors.append(f"{name}: {exc}")


def _relative_path_parts(value: str) -> tuple[str, ...]:
    if not value or "\\" in value:
        raise LockError("path must be a non-empty POSIX relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in ("", ".", "..") for part in path.parts):
        raise LockError("path must not be absolute or traverse parents")
    if str(path) != value:
        raise LockError("path must be canonical")
    return path.parts


def _canonical_manifest_sha256(manifest: Mapping[str, Any]) -> str:
    canonical = json.dumps(
        manifest,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    )
    return hashlib.sha256((canonical + "\n").encode("ascii")).hexdigest()


def _unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise LockError(f"lock file contains duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_json_float(value: str) -> Any:
    raise LockError(f"lock file must not contain floating-point value: {value}")


def _reject_json_constant(value: str) -> Any:
    raise LockError(f"lock file must not contain non-finite value: {value}")


def _required_open_flag(name: str) -> int:
    value = getattr(os, name, None)
    if not isinstance(value, int):
        raise LockError(f"platform does not provide required {name} support")
    return value


def _nested_value(value: Mapping[str, Any], *keys: str) -> Any:
    current: Any = value
    for key in keys:
        if not isinstance(current, Mapping):
            return None
        current = current.get(key)
    return current


def _safe_length(value: Any) -> int | None:
    return len(value) if isinstance(value, list) else None


def _print_human(report: Mapping[str, Any]) -> None:
    if report["ok"]:
        if report["mode"] == "installed":
            print("ok: local RISC0 toolchain matches the recursive-STARK lock")
        else:
            print("ok: recursive-STARK toolchain lock policy is exact")
        return
    print("error: recursive-STARK toolchain lock check failed", file=sys.stderr)
    for error in report["errors"]:
        print(f"  - {error}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--verify-installed",
        action="store_true",
        help="hash and version-check the installed local RISC0 toolchain",
    )
    parser.add_argument(
        "--risc0-home",
        type=Path,
        help="RISC0 home to verify (or set RISC0_HOME)",
    )
    parser.add_argument("--json", action="store_true", help="emit a JSON report")
    args = parser.parse_args(argv)

    risc0_home = args.risc0_home
    if risc0_home is None:
        env_home = os.environ.get("RISC0_HOME")
        if env_home:
            risc0_home = Path(env_home)
    report = check_risc0_recursive_toolchain_lock(
        verify_installed=args.verify_installed,
        risc0_home=risc0_home,
    )
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_human(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
