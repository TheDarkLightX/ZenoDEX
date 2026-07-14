#!/usr/bin/env python3
"""Bounded privacy scan for the exact final V6 local-evidence artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

if __package__:
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
    from tools import zrpf_v3_artifact_privacy as privacy
else:
    sys.path.insert(0, Path(__file__).resolve().parents[1].as_posix())
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
    from tools import zrpf_v3_artifact_privacy as privacy

REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_artifact_privacy_scan/v1"
REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BUILD_RECORD = (
    REPO_ROOT
    / "docs/research/ZRPF_SOURCE_OPENED_SPOT_V6_BUILD_RECORD_20260712.json"
)
BUILD_RECORD_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_build_record/v3"
MAX_BUILD_RECORD_BYTES = 256 * 1024
RISC0_PROGRAM_BINARY_MAGIC = b"R0BF"
RISC0_PROGRAM_BINARY_ROLES = frozenset(
    {
        "leaf_program_binary",
        "level_one_program_binary",
        "level_two_program_binary",
        "settlement_program_binary",
    }
)
_HOME_PATH_PATTERN = re.compile(rb"/(?:home|Users)/")
_ROOT_PATH_PATTERN = re.compile(rb"/root[^/\x00\s]*/")
_PATH_CONTINUATION_BYTES = frozenset(
    b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._~/-"
)
_BUILD_RECORD_ROOT_FIELDS = {
    "schema",
    "recorded_at",
    "source_observation",
    "toolchain",
    "programs",
    "publisher_reported_observations",
    "claims",
}
_BUILD_RECORD_PROGRAM_FIELDS = {
    "stage",
    "package",
    "artifact_file",
    "program_binary_bytes",
    "program_binary_sha256",
    "image_id_hex",
    "image_id_words_le",
    "verified_child_stage",
    "verified_child_image_id",
}
_BUILD_RECORD_FALSE_AUTHORITY_FIELDS = {
    "release_authority",
    "settlement_authority",
    "production_authority",
}


@dataclass(frozen=True, order=True)
class UpstreamPathException:
    """One exact public upstream path retained by a pinned RISC0 artifact."""

    component_id: str
    exact_path: bytes
    governed_source_artifact_sha256: str
    rule_id: str


@dataclass(frozen=True, order=True)
class ProgramArtifactBinding:
    """Candidate build-record identity for one complete combined program."""

    role: str
    sha256: str
    size_bytes: int


@dataclass(frozen=True)
class CandidateBuildRecordBinding:
    """Unanchored program identities parsed from one candidate build record."""

    record_sha256: str
    programs: tuple[ProgramArtifactBinding, ...]

    def program_for_role(self, role: str) -> ProgramArtifactBinding | None:
        return next((program for program in self.programs if program.role == role), None)


@dataclass(frozen=True)
class _HeldArtifactDescriptor:
    """One governed artifact held open until snapshot finalization."""

    descriptor: int
    expected_identity: tuple[int, ...]
    relative_path: str
    role: str


_V1COMPAT_COMPONENT_ID = "risc0_zkos_v1compat_2_2_2_elf"
_RUSTC_DEMANGLE_COMPONENT_ID = "risc0_rust_sysroot_rustc_demangle_rlib"
_APPROVED_COMPONENT_SHA256 = {
    _V1COMPAT_COMPONENT_ID: (
        "7ffd942e4e8babd771094f549ad080cfea8ecb2c05c986e275c011f41979d921"
    ),
    _RUSTC_DEMANGLE_COMPONENT_ID: (
        "a537a077bbf3d117dc44b0a96f2e20e2835b0206c7ad87611d73a00082896f04"
    ),
}
_APPROVED_PATH_SHA256 = {
    (
        _V1COMPAT_COMPONENT_ID,
        "posix_home_path",
    ): frozenset(
        {
            "562bbf33cc4f34d75921b1ae566162dbd7cc8434f16a87e4b75674318199105b",
        }
    ),
    (
        _RUSTC_DEMANGLE_COMPONENT_ID,
        "posix_root_path",
    ): frozenset(
        {
            "5e8205190dc05b990e20521bcac7ec99153dc1d70615b7d0f0ef4a4b5cf5d72c",
            "6a488a10f0d8381e0b5d8d5a0df6ad54d3b9a7a56bb1fb95aafe1ce2597569df",
            "7d30e6904ce54fd8e624f2b5f048ef49344ed33391d67a04979eb0df11969dcf",
        }
    ),
}
UPSTREAM_PATH_EXCEPTIONS: tuple[UpstreamPathException, ...] = (
    UpstreamPathException(
        component_id=_V1COMPAT_COMPONENT_ID,
        exact_path=(
            b"/".join(
                (
                    b"",
                    b"home",
                    b"remi",
                    b".cargo",
                    b"registry",
                    b"src",
                    b"index.crates.io-1949cf8c6b5b557f",
                    b"no_std_strings-0.1.3",
                    b"src",
                    b"tiny_internal.rs",
                )
            )
        ),
        governed_source_artifact_sha256=_APPROVED_COMPONENT_SHA256[
            _V1COMPAT_COMPONENT_ID
        ],
        rule_id="posix_home_path",
    ),
    *(
        UpstreamPathException(
            component_id=_RUSTC_DEMANGLE_COMPONENT_ID,
            exact_path=(
                b"/root/.cargo/registry/src/"
                b"index.crates.io-1949cf8c6b5b557f/"
                b"rustc-demangle-0.1.26/src/" + leaf
            ),
            governed_source_artifact_sha256=_APPROVED_COMPONENT_SHA256[
                _RUSTC_DEMANGLE_COMPONENT_ID
            ],
            rule_id="posix_root_path",
        )
        for leaf in (b"legacy.rs", b"lib.rs", b"v0.rs")
    ),
)

FINAL_ARTIFACTS: tuple[privacy.ArtifactSpec, ...] = tuple(
    privacy.ArtifactSpec(path, artifact_id)
    for artifact_id, path, _kind in evidence.ARTIFACT_SPECS
)


def scan_artifact_directory(
    root: Path,
    *,
    build_record_path: Path | None = None,
) -> dict[str, Any]:
    """Scan one stable descriptor-relative snapshot of the governed inventory."""

    base, raw_by_path, observed_names, inventory_errors = _capture_snapshot(root)
    build_binding, build_binding_errors = _load_candidate_build_record_binding(
        build_record_path
    )
    exceptions, policy_errors = _validate_upstream_path_exception_policy()
    findings, exception_errors, allowed_exceptions = _apply_upstream_path_exceptions(
        base,
        raw_by_path,
        exceptions,
        build_binding,
    )
    errors = [
        *base["errors"],
        *inventory_errors,
        *build_binding_errors,
        *policy_errors,
        *exception_errors,
    ]
    errors.sort(key=lambda row: (row["path"], row["role"], row["code"]))
    return _render_report(
        base,
        observed_names,
        errors,
        findings,
        allowed_exceptions,
        build_binding,
    )


def _render_report(
    base: dict[str, Any],
    observed_names: list[str],
    errors: list[dict[str, str]],
    findings: list[dict[str, Any]],
    allowed_exceptions: list[dict[str, Any]],
    build_binding: CandidateBuildRecordBinding | None,
) -> dict[str, Any]:
    return {
        "allowed_upstream_path_exception_count": len(allowed_exceptions),
        "allowed_upstream_path_exceptions": allowed_exceptions,
        "artifact_count_expected": len(FINAL_ARTIFACTS),
        "artifact_count_observed": len(observed_names),
        "artifact_count_scanned": base["artifact_count_scanned"],
        "artifact_set_sha256": _artifact_set_sha256(base["artifacts"]),
        "artifacts": base["artifacts"],
        "build_record_anchor_checked": False,
        "build_record_sha256": (
            build_binding.record_sha256 if build_binding is not None else None
        ),
        "complete_artifact_privacy_verified": False,
        "error_count": len(errors),
        "errors": errors,
        "finding_count": len(findings),
        "findings": findings,
        "inventory_names_sha256": _inventory_names_sha256(observed_names),
        "negative_knowledge": (
            "This bounded denylist detects the configured path, email, token, "
            "credential, and private-key patterns in the exact V6 artifact set. "
            "Exact role-scoped public paths already embedded in candidate-build-record "
            "bound RISC0 program binaries are recorded as bounded exceptions. Upstream "
            "component digests remain publisher records rather than reconstructed "
            "component provenance. The build record and exception policy are unanchored. "
            "A clean scan does not prove complete artifact privacy or the absence "
            "of unmodeled secrets, covert channels, or side channels."
        ),
        "ok": (
            not errors
            and not findings
            and base["artifact_count_scanned"] == len(FINAL_ARTIFACTS)
        ),
        "schema": REPORT_SCHEMA,
        "snapshot_root_identity_verified": base["snapshot_root_identity_verified"],
        "total_bytes_scanned": base["total_bytes_scanned"],
        "upstream_path_exception_policy_anchored": False,
        "upstream_path_exception_policy_authority": False,
        "upstream_path_exception_policy_sha256": (
            _upstream_path_exception_policy_sha256()
        ),
    }


def _capture_snapshot(
    root: Path,
) -> tuple[dict[str, Any], dict[str, bytes], list[str], list[dict[str, str]]]:
    ordered, specification_errors = privacy._validate_artifact_specs(FINAL_ARTIFACTS)
    expected_names = {artifact.relative_path for artifact in ordered}
    if len(ordered) > privacy.MAX_ARTIFACT_COUNT:
        specification_errors.append(
            _error(".", "inventory", "artifact_count_limit_exceeded")
        )
        ordered = ordered[: privacy.MAX_ARTIFACT_COUNT]
    try:
        root_descriptor = privacy._open_root(root)
    except privacy.ArtifactReadError as exc:
        errors = [*specification_errors, _error(".", "inventory", exc.code)]
        return _base_scan([], [], errors, 0, False), {}, [], []
    held_artifacts: list[_HeldArtifactDescriptor] = []
    try:
        before = os.fstat(root_descriptor)
        try:
            observed_names = _list_inventory(root_descriptor)
            inventory_errors = _inventory_errors(observed_names, expected_names)
        except privacy.ArtifactReadError as exc:
            observed_names = []
            inventory_errors = [_error(".", "inventory", exc.code)]
        artifacts, raw_by_path, findings, errors, total = _read_snapshot_artifacts(
            root_descriptor,
            ordered,
            specification_errors,
            held_artifacts,
        )
        snapshot_ok, snapshot_errors = _finish_snapshot(
            root,
            root_descriptor,
            before,
            observed_names,
            held_artifacts,
        )
        errors.extend(snapshot_errors)
    finally:
        for held in held_artifacts:
            os.close(held.descriptor)
        os.close(root_descriptor)
    return (
        _base_scan(artifacts, findings, errors, total, snapshot_ok),
        raw_by_path,
        observed_names,
        inventory_errors,
    )


def _read_snapshot_artifacts(
    root_descriptor: int,
    artifacts: list[privacy.ArtifactSpec],
    specification_errors: list[dict[str, str]],
    held_artifacts: list[_HeldArtifactDescriptor],
) -> tuple[
    list[dict[str, Any]],
    dict[str, bytes],
    list[dict[str, Any]],
    list[dict[str, str]],
    int,
]:
    scanned: list[dict[str, Any]] = []
    raw_by_path: dict[str, bytes] = {}
    findings: list[dict[str, Any]] = []
    errors = list(specification_errors)
    total = 0
    for artifact in artifacts:
        remaining = privacy.MAX_TOTAL_BYTES - total
        if remaining <= 0:
            errors.append(
                _error(artifact.relative_path, artifact.role, "total_size_limit_exceeded")
            )
            continue
        try:
            raw, held = _read_and_hold_regular_bounded(
                root_descriptor,
                artifact,
                min(privacy.MAX_ARTIFACT_BYTES, remaining),
            )
        except privacy.ArtifactReadError as exc:
            errors.append(_error(artifact.relative_path, artifact.role, exc.code))
            continue
        held_artifacts.append(held)
        total += len(raw)
        raw_by_path[artifact.relative_path] = raw
        scanned.append(_artifact_identity(artifact, raw))
        additions, exceeded = privacy._scan_bytes(
            artifact,
            raw,
            privacy.MAX_FINDINGS - len(findings),
        )
        findings.extend(additions)
        if exceeded:
            errors.append(
                _error(artifact.relative_path, artifact.role, "finding_limit_exceeded")
            )
            break
    return scanned, raw_by_path, findings, errors, total


def _read_and_hold_regular_bounded(
    root_descriptor: int,
    artifact: privacy.ArtifactSpec,
    maximum: int,
) -> tuple[bytes, _HeldArtifactDescriptor]:
    descriptor = _open_artifact_at(root_descriptor, artifact.relative_path)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise privacy.ArtifactReadError("artifact_not_regular")
        if before.st_size <= 0 or before.st_size > maximum:
            raise privacy.ArtifactReadError("artifact_size_out_of_bounds")
        raw = privacy._read_descriptor_bounded(descriptor, maximum)
        after = os.fstat(descriptor)
        expected_identity = privacy._identity_tuple(after)
        if (
            privacy._identity_tuple(before) != expected_identity
            or len(raw) != after.st_size
        ):
            raise privacy.ArtifactReadError("artifact_changed_during_read")
        return raw, _HeldArtifactDescriptor(
            descriptor=descriptor,
            expected_identity=expected_identity,
            relative_path=artifact.relative_path,
            role=artifact.role,
        )
    except BaseException:
        os.close(descriptor)
        raise


def _open_artifact_at(root_descriptor: int, relative_path: str) -> int:
    parts = PurePosixPath(relative_path).parts
    directory_descriptor = os.dup(root_descriptor)
    try:
        for part in parts[:-1]:
            next_descriptor = privacy._open_directory_at(directory_descriptor, part)
            os.close(directory_descriptor)
            directory_descriptor = next_descriptor
        return privacy._open_file_at(directory_descriptor, parts[-1])
    finally:
        os.close(directory_descriptor)


def _finish_snapshot(
    root: Path,
    root_descriptor: int,
    before: os.stat_result,
    observed_names: list[str],
    held_artifacts: list[_HeldArtifactDescriptor],
) -> tuple[bool, list[dict[str, str]]]:
    errors: list[dict[str, str]] = []
    errors.extend(_verify_held_artifact_bindings(root_descriptor, held_artifacts))
    try:
        final_names = _list_inventory(root_descriptor)
        after = os.fstat(root_descriptor)
    except (OSError, privacy.ArtifactReadError):
        return False, [_error(".", "inventory", "snapshot_finalization_unavailable")]
    if final_names != observed_names:
        errors.append(_error(".", "inventory", "inventory_changed_during_snapshot"))
    if privacy._identity_tuple(before) != privacy._identity_tuple(after):
        errors.append(_error(".", "inventory", "root_changed_during_snapshot"))
    if not _root_path_still_names_descriptor(root, after):
        errors.append(_error(".", "inventory", "root_path_replaced_during_snapshot"))
    return not errors, errors


def _verify_held_artifact_bindings(
    root_descriptor: int,
    held_artifacts: list[_HeldArtifactDescriptor],
) -> list[dict[str, str]]:
    errors: list[dict[str, str]] = []
    for held in held_artifacts:
        try:
            held_identity = privacy._identity_tuple(os.fstat(held.descriptor))
        except OSError:
            errors.append(
                _error(held.relative_path, held.role, "artifact_finalization_unavailable")
            )
            continue
        held_changed = held_identity != held.expected_identity
        if held_changed:
            errors.append(
                _error(held.relative_path, held.role, "artifact_changed_after_read")
            )
        _verify_artifact_name_binding(
            root_descriptor,
            held,
            held_changed=held_changed,
            errors=errors,
        )
    return errors


def _verify_artifact_name_binding(
    root_descriptor: int,
    held: _HeldArtifactDescriptor,
    *,
    held_changed: bool,
    errors: list[dict[str, str]],
) -> None:
    try:
        rebound_descriptor = _open_artifact_at(root_descriptor, held.relative_path)
    except privacy.ArtifactReadError:
        errors.append(
            _error(held.relative_path, held.role, "artifact_name_binding_unavailable")
        )
        return
    try:
        rebound_identity = privacy._identity_tuple(os.fstat(rebound_descriptor))
    except OSError:
        errors.append(
            _error(held.relative_path, held.role, "artifact_name_binding_unavailable")
        )
        return
    finally:
        os.close(rebound_descriptor)
    if rebound_identity[:2] != held.expected_identity[:2]:
        errors.append(_error(held.relative_path, held.role, "artifact_name_rebound"))
    elif rebound_identity != held.expected_identity and not held_changed:
        errors.append(
            _error(held.relative_path, held.role, "artifact_changed_after_read")
        )


def _root_path_still_names_descriptor(root: Path, expected: os.stat_result) -> bool:
    try:
        observed = os.stat(root, follow_symlinks=False)
    except (OSError, ValueError):
        return False
    return (
        stat.S_ISDIR(observed.st_mode)
        and observed.st_dev == expected.st_dev
        and observed.st_ino == expected.st_ino
        and observed.st_mode == expected.st_mode
    )


def _list_inventory(root_descriptor: int) -> list[str]:
    try:
        return sorted(os.listdir(root_descriptor))
    except OSError as exc:
        raise privacy.ArtifactReadError("inventory_unavailable") from exc


def _inventory_errors(
    observed_names: list[str],
    expected_names: set[str],
) -> list[dict[str, str]]:
    observed = set(observed_names)
    errors = [
        _error(path, "inventory", "governed_artifact_missing")
        for path in sorted(expected_names - observed)
    ]
    if observed - expected_names:
        errors.append(_error(".", "inventory", "extra_governed_inventory"))
    return errors


def _artifact_identity(
    artifact: privacy.ArtifactSpec,
    raw: bytes,
) -> dict[str, Any]:
    return {
        "path": artifact.relative_path,
        "role": artifact.role,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "size_bytes": len(raw),
    }


def _base_scan(
    artifacts: list[dict[str, Any]],
    findings: list[dict[str, Any]],
    errors: list[dict[str, str]],
    total_bytes: int,
    snapshot_ok: bool,
) -> dict[str, Any]:
    findings.sort(key=lambda row: (row["path"], row["byte_offset"], row["rule_id"]))
    errors.sort(key=lambda row: (row["path"], row["role"], row["code"]))
    return {
        "artifact_count_scanned": len(artifacts),
        "artifacts": artifacts,
        "errors": errors,
        "findings": findings,
        "snapshot_root_identity_verified": snapshot_ok,
        "total_bytes_scanned": total_bytes,
    }


def _load_candidate_build_record_binding(
    path: Path | None,
) -> tuple[CandidateBuildRecordBinding | None, list[dict[str, str]]]:
    if path is None:
        return None, []
    try:
        raw = _read_stable_build_record(path)
        document = _decode_build_record(raw)
        programs = _program_bindings_from_record(document)
    except (OSError, ValueError, privacy.ArtifactReadError):
        return None, [_error(".", "build_record", "build_record_binding_rejected")]
    return CandidateBuildRecordBinding(hashlib.sha256(raw).hexdigest(), programs), []


def _read_stable_build_record(path: Path) -> bytes:
    try:
        descriptor = os.open(
            path,
            os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK,
        )
    except (OSError, ValueError) as exc:
        raise privacy.ArtifactReadError("build_record_unavailable") from exc
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > MAX_BUILD_RECORD_BYTES
        ):
            raise privacy.ArtifactReadError("build_record_size_out_of_bounds")
        raw = privacy._read_descriptor_bounded(descriptor, MAX_BUILD_RECORD_BYTES)
        after = os.fstat(descriptor)
        if privacy._identity_tuple(before) != privacy._identity_tuple(after):
            raise privacy.ArtifactReadError("build_record_changed_during_read")
        if len(raw) != after.st_size:
            raise privacy.ArtifactReadError("build_record_changed_during_read")
        return raw
    finally:
        os.close(descriptor)


def _decode_build_record(raw: bytes) -> dict[str, Any]:
    def reject_float(_value: str) -> None:
        raise ValueError("floating-point build-record numbers are forbidden")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise ValueError("duplicate build-record key")
            output[key] = value
        return output

    document = json.loads(
        raw,
        object_pairs_hook=reject_duplicates,
        parse_float=reject_float,
        parse_constant=reject_float,
    )
    if type(document) is not dict or set(document) != _BUILD_RECORD_ROOT_FIELDS:
        raise ValueError("build-record root schema mismatch")
    if document["schema"] != BUILD_RECORD_SCHEMA:
        raise ValueError("build-record schema mismatch")
    canonical = (json.dumps(document, indent=2, sort_keys=False) + "\n").encode()
    if raw != canonical:
        raise ValueError("build-record bytes are noncanonical")
    claims = document["claims"]
    if type(claims) is not dict or any(
        claims.get(field) is not False for field in _BUILD_RECORD_FALSE_AUTHORITY_FIELDS
    ):
        raise ValueError("build-record authority claims must remain false")
    return document


def _program_bindings_from_record(
    document: dict[str, Any],
) -> tuple[ProgramArtifactBinding, ...]:
    programs = document["programs"]
    if type(programs) is not list:
        raise ValueError("build-record programs must be a list")
    roles_by_file = {
        artifact.relative_path: artifact.role
        for artifact in FINAL_ARTIFACTS
        if artifact.role in RISC0_PROGRAM_BINARY_ROLES
    }
    bindings: list[ProgramArtifactBinding] = []
    for row in programs:
        bindings.append(_program_binding_from_row(row, roles_by_file))
    bindings.sort()
    if {binding.role for binding in bindings} != set(roles_by_file.values()):
        raise ValueError("build-record program inventory mismatch")
    if len(bindings) != len(roles_by_file):
        raise ValueError("duplicate build-record program binding")
    return tuple(bindings)


def _program_binding_from_row(
    row: Any,
    roles_by_file: dict[str, str],
) -> ProgramArtifactBinding:
    if type(row) is not dict or set(row) != _BUILD_RECORD_PROGRAM_FIELDS:
        raise ValueError("build-record program schema mismatch")
    role = roles_by_file.get(row["artifact_file"])
    size = row["program_binary_bytes"]
    digest = row["program_binary_sha256"]
    if role is None:
        raise ValueError("unknown build-record program artifact")
    if type(size) is not int or not 8 < size <= privacy.MAX_ARTIFACT_BYTES:
        raise ValueError("build-record program size mismatch")
    if (
        type(digest) is not str
        or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        or digest == "0" * 64
    ):
        raise ValueError("build-record program digest mismatch")
    return ProgramArtifactBinding(role=role, sha256=digest, size_bytes=size)


def _validate_upstream_path_exception_policy(
) -> tuple[tuple[UpstreamPathException, ...], list[dict[str, str]]]:
    errors: list[dict[str, str]] = []
    ordered = tuple(sorted(UPSTREAM_PATH_EXCEPTIONS))
    if len(set(ordered)) != len(ordered):
        errors.append(_error(".", "upstream_path_policy", "duplicate_exception"))
    for exception in ordered:
        approved_component_sha256 = _APPROVED_COMPONENT_SHA256.get(
            exception.component_id
        )
        approved_paths = _APPROVED_PATH_SHA256.get(
            (exception.component_id, exception.rule_id)
        )
        path_sha256 = hashlib.sha256(exception.exact_path).hexdigest()
        if (
            approved_component_sha256 is None
            or exception.governed_source_artifact_sha256
            != approved_component_sha256
            or approved_paths is None
            or path_sha256 not in approved_paths
            or exception.rule_id not in {"posix_home_path", "posix_root_path"}
        ):
            errors.append(
                _error(".", "upstream_path_policy", "invalid_exception_binding")
            )
    if errors:
        return (), errors
    return ordered, []


def _apply_upstream_path_exceptions(
    base: dict[str, Any],
    raw_by_path: dict[str, bytes],
    exceptions: tuple[UpstreamPathException, ...],
    build_binding: CandidateBuildRecordBinding | None,
) -> tuple[list[dict[str, Any]], list[dict[str, str]], list[dict[str, Any]]]:
    findings = [dict(row) for row in base["findings"]]
    additional, errors = _scan_snapshot_additional_paths(raw_by_path, findings)
    findings.extend(additional)
    retained, allowed = _filter_upstream_path_exceptions(
        findings,
        raw_by_path,
        exceptions,
        build_binding,
    )
    return retained, errors, allowed


def _scan_snapshot_additional_paths(
    raw_by_path: dict[str, bytes],
    base_findings: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, str]]]:
    additional: list[dict[str, Any]] = []
    errors: list[dict[str, str]] = []
    for artifact in FINAL_ARTIFACTS:
        raw = raw_by_path.get(artifact.relative_path)
        if raw is None:
            continue
        new_findings, exceeded = _scan_additional_paths(
            artifact,
            raw,
            privacy.MAX_FINDINGS - len(base_findings) - len(additional),
            {
                (row["rule_id"], row["byte_offset"])
                for row in [*base_findings, *additional]
                if row["path"] == artifact.relative_path
            },
        )
        additional.extend(new_findings)
        if exceeded:
            errors.append(
                _error(artifact.relative_path, artifact.role, "finding_limit_exceeded")
            )
            break
    return additional, errors


def _filter_upstream_path_exceptions(
    findings: list[dict[str, Any]],
    raw_by_path: dict[str, bytes],
    exceptions: tuple[UpstreamPathException, ...],
    build_binding: CandidateBuildRecordBinding | None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    artifacts_by_path = {
        artifact.relative_path: artifact for artifact in FINAL_ARTIFACTS
    }
    use_count: dict[tuple[str, str, str], int] = {}
    retained: list[dict[str, Any]] = []
    allowed: list[dict[str, Any]] = []
    for finding in sorted(
        findings,
        key=lambda row: (row["path"], row["byte_offset"], row["rule_id"]),
    ):
        raw = raw_by_path.get(finding["path"])
        artifact = artifacts_by_path.get(finding["path"])
        if artifact is None or raw is None:
            retained.append(finding)
            continue
        exception = _matching_exception(
            artifact,
            raw,
            finding,
            exceptions,
            build_binding,
        )
        if exception is None:
            retained.append(finding)
            continue
        usage_key = (
            artifact.relative_path,
            exception.component_id,
            hashlib.sha256(exception.exact_path).hexdigest(),
        )
        if use_count.get(usage_key, 0) != 0:
            retained.append(finding)
            continue
        use_count[usage_key] = 1
        allowed.append(_allowed_exception_row(artifact, raw, finding, exception))
    allowed.sort(
        key=lambda row: (
            row["artifact_path"],
            row["byte_offset"],
            row["component_id"],
        )
    )
    return retained, allowed


def _allowed_exception_row(
    artifact: privacy.ArtifactSpec,
    raw: bytes,
    finding: dict[str, Any],
    exception: UpstreamPathException,
) -> dict[str, Any]:
    return {
        "artifact_path": artifact.relative_path,
        "artifact_role": artifact.role,
        "byte_offset": finding["byte_offset"],
        "component_id": exception.component_id,
        "governed_source_artifact_sha256": (
            exception.governed_source_artifact_sha256
        ),
        "governed_program_binary_sha256": hashlib.sha256(raw).hexdigest(),
        "path_sha256": hashlib.sha256(exception.exact_path).hexdigest(),
        "rule_id": exception.rule_id,
    }


def _scan_additional_paths(
    artifact: privacy.ArtifactSpec,
    raw: bytes,
    remaining_findings: int,
    existing: set[tuple[str, int]],
) -> tuple[list[dict[str, Any]], bool]:
    findings: list[dict[str, Any]] = []
    for rule_id, pattern in (
        ("posix_home_path", _HOME_PATH_PATTERN),
        ("posix_root_path", _ROOT_PATH_PATTERN),
    ):
        for match in pattern.finditer(raw):
            if (rule_id, match.start()) in existing:
                continue
            if len(findings) >= remaining_findings:
                return findings, True
            findings.append(
                {
                    "byte_offset": match.start(),
                    "match_length": match.end() - match.start(),
                    "match_sha256": hashlib.sha256(match.group()).hexdigest(),
                    "path": artifact.relative_path,
                    "role": artifact.role,
                    "rule_id": rule_id,
                }
            )
    return findings, False


def _matching_exception(
    artifact: privacy.ArtifactSpec,
    raw: bytes,
    finding: dict[str, Any],
    exceptions: tuple[UpstreamPathException, ...],
    build_binding: CandidateBuildRecordBinding | None,
) -> UpstreamPathException | None:
    program = (
        build_binding.program_for_role(artifact.role)
        if build_binding is not None
        else None
    )
    if (
        artifact.role not in RISC0_PROGRAM_BINARY_ROLES
        or not raw.startswith(RISC0_PROGRAM_BINARY_MAGIC)
        or program is None
        or len(raw) != program.size_bytes
        or hashlib.sha256(raw).hexdigest() != program.sha256
    ):
        return None
    offset = finding.get("byte_offset")
    if not isinstance(offset, int) or isinstance(offset, bool) or offset < 0:
        return None
    match_length = finding.get("match_length")
    if (
        not isinstance(match_length, int)
        or isinstance(match_length, bool)
        or match_length <= 0
        or offset + match_length > len(raw)
    ):
        return None
    for exception in exceptions:
        if exception.rule_id != finding.get("rule_id"):
            continue
        prefix_pattern = (
            _ROOT_PATH_PATTERN.match(raw, offset)
            if exception.rule_id == "posix_root_path"
            else _HOME_PATH_PATTERN.match(raw, offset)
        )
        if prefix_pattern is None:
            continue
        if (
            finding.get("match_sha256")
            != hashlib.sha256(raw[offset : offset + match_length]).hexdigest()
            or raw[offset : offset + len(exception.exact_path)]
            != exception.exact_path
            or not _has_exact_path_boundaries(raw, offset, len(exception.exact_path))
        ):
            continue
        return exception
    return None


def _has_exact_path_boundaries(raw: bytes, offset: int, length: int) -> bool:
    end = offset + length
    starts_cleanly = offset == 0 or raw[offset - 1] not in _PATH_CONTINUATION_BYTES
    ends_cleanly = end == len(raw) or raw[end] == 0
    return starts_cleanly and ends_cleanly


def _upstream_path_exception_policy_sha256() -> str:
    rows = [
        {
            "component_id": exception.component_id,
            "governed_source_artifact_sha256": (
                exception.governed_source_artifact_sha256
            ),
            "path_sha256": hashlib.sha256(exception.exact_path).hexdigest(),
            "rule_id": exception.rule_id,
        }
        for exception in sorted(UPSTREAM_PATH_EXCEPTIONS)
    ]
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(
        b"zenodex.zrpf.source_opened_spot_v6.upstream_path_policy.v1\0"
        + payload
    ).hexdigest()


def _inventory_names_sha256(names: list[str]) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.zrpf.source_opened_spot_v6.inventory.v1\0")
    for name in names:
        encoded = name.encode("utf-8", errors="surrogateescape")
        hasher.update(len(encoded).to_bytes(4, "big"))
        hasher.update(encoded)
    return hasher.hexdigest()


def _artifact_set_sha256(artifacts: list[dict[str, Any]]) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.zrpf.source_opened_spot_v6.artifact_set.v1\0")
    for artifact in artifacts:
        path = artifact["path"].encode("utf-8")
        role = artifact["role"].encode("utf-8")
        digest = bytes.fromhex(artifact["sha256"])
        size = artifact["size_bytes"]
        hasher.update(len(path).to_bytes(4, "big"))
        hasher.update(path)
        hasher.update(len(role).to_bytes(4, "big"))
        hasher.update(role)
        hasher.update(size.to_bytes(8, "big"))
        hasher.update(digest)
    return hasher.hexdigest()


def _error(path: str, role: str, code: str) -> dict[str, str]:
    return {"code": code, "path": path, "role": role}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-directory", type=Path, required=True)
    parser.add_argument("--build-record", type=Path, default=DEFAULT_BUILD_RECORD)
    arguments = parser.parse_args(argv)
    report = scan_artifact_directory(
        arguments.artifact_directory,
        build_record_path=arguments.build_record,
    )
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
