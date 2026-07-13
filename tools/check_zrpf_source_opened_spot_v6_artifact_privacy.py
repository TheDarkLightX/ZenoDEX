#!/usr/bin/env python3
"""Bounded privacy scan for the exact final V6 local-evidence artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__:
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
    from tools import zrpf_v3_artifact_privacy as privacy
else:
    sys.path.insert(0, Path(__file__).resolve().parents[1].as_posix())
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
    from tools import zrpf_v3_artifact_privacy as privacy

REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_artifact_privacy_scan/v1"
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


@dataclass(frozen=True, order=True)
class UpstreamPathException:
    """One exact public upstream path retained by a pinned RISC0 artifact."""

    component_id: str
    exact_path: bytes
    governed_source_artifact_sha256: str
    rule_id: str


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
            b"/home/remi/.cargo/registry/src/"
            b"index.crates.io-1949cf8c6b5b557f/"
            b"no_std_strings-0.1.3/src/tiny_internal.rs"
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


def scan_artifact_directory(root: Path) -> dict[str, Any]:
    """Scan exactly the governed flat V6 inventory under one supplied root."""

    expected_names = {artifact.relative_path for artifact in FINAL_ARTIFACTS}
    observed_names, inventory_errors = _read_exact_inventory(root, expected_names)
    base = privacy.scan_artifacts(root, FINAL_ARTIFACTS)
    exceptions, policy_errors = _validate_upstream_path_exception_policy()
    findings, exception_errors, allowed_exceptions = _apply_upstream_path_exceptions(
        root,
        base,
        exceptions,
    )
    errors = [
        *base["errors"],
        *inventory_errors,
        *policy_errors,
        *exception_errors,
    ]
    errors.sort(key=lambda row: (row["path"], row["role"], row["code"]))
    artifact_set_sha256 = _artifact_set_sha256(base["artifacts"])
    return {
        "allowed_upstream_path_exception_count": len(allowed_exceptions),
        "allowed_upstream_path_exceptions": allowed_exceptions,
        "artifact_count_expected": len(FINAL_ARTIFACTS),
        "artifact_count_observed": len(observed_names),
        "artifact_count_scanned": base["artifact_count_scanned"],
        "artifact_set_sha256": artifact_set_sha256,
        "artifacts": base["artifacts"],
        "complete_artifact_privacy_verified": False,
        "error_count": len(errors),
        "errors": errors,
        "finding_count": len(findings),
        "findings": findings,
        "inventory_names_sha256": _inventory_names_sha256(observed_names),
        "negative_knowledge": (
            "This bounded denylist detects the configured path, email, token, "
            "credential, and private-key patterns in the exact V6 artifact set. "
            "Exact role-scoped public paths already embedded in hash-pinned "
            "upstream RISC0 kernel or sysroot artifacts are recorded as provenance "
            "exceptions; this scanner does not independently rebuild those artifacts. "
            "A clean scan does not prove complete artifact privacy or the absence "
            "of unmodeled secrets, covert channels, or side channels."
        ),
        "ok": (
            not errors
            and not findings
            and base["artifact_count_scanned"] == len(FINAL_ARTIFACTS)
        ),
        "schema": REPORT_SCHEMA,
        "total_bytes_scanned": base["total_bytes_scanned"],
        "upstream_path_exception_policy_sha256": (
            _upstream_path_exception_policy_sha256()
        ),
    }


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
    root: Path,
    base: dict[str, Any],
    exceptions: tuple[UpstreamPathException, ...],
) -> tuple[list[dict[str, Any]], list[dict[str, str]], list[dict[str, Any]]]:
    findings = [dict(row) for row in base["findings"]]
    raw_by_path, additional, errors = _read_exception_scan_artifacts(
        root,
        base["artifacts"],
        findings,
    )
    findings.extend(additional)
    retained, allowed = _filter_upstream_path_exceptions(
        findings,
        raw_by_path,
        exceptions,
    )
    return retained, errors, allowed


def _read_exception_scan_artifacts(
    root: Path,
    scanned_artifacts: list[dict[str, Any]],
    base_findings: list[dict[str, Any]],
) -> tuple[dict[str, bytes], list[dict[str, Any]], list[dict[str, str]]]:
    scanned_by_path = {row["path"]: row for row in scanned_artifacts}
    raw_by_path: dict[str, bytes] = {}
    additional: list[dict[str, Any]] = []
    errors: list[dict[str, str]] = []
    try:
        root_descriptor = privacy._open_root(root)
    except privacy.ArtifactReadError:
        return raw_by_path, additional, errors
    try:
        for artifact in FINAL_ARTIFACTS:
            scanned = scanned_by_path.get(artifact.relative_path)
            if scanned is None:
                continue
            raw, error_code = _read_stable_exception_candidate(
                root_descriptor,
                artifact,
                scanned,
            )
            if error_code is not None:
                errors.append(_error(artifact.relative_path, artifact.role, error_code))
                continue
            raw_by_path[artifact.relative_path] = raw
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
                    _error(
                        artifact.relative_path,
                        artifact.role,
                        "finding_limit_exceeded",
                    )
                )
                break
    finally:
        os.close(root_descriptor)
    return raw_by_path, additional, errors


def _read_stable_exception_candidate(
    root_descriptor: int,
    artifact: privacy.ArtifactSpec,
    scanned: dict[str, Any],
) -> tuple[bytes, str | None]:
    try:
        raw = privacy._read_regular_bounded(
            root_descriptor,
            artifact.relative_path,
            privacy.MAX_ARTIFACT_BYTES,
        )
    except privacy.ArtifactReadError:
        return b"", "upstream_exception_scan_unavailable"
    if (
        len(raw) != scanned["size_bytes"]
        or hashlib.sha256(raw).hexdigest() != scanned["sha256"]
    ):
        return b"", "artifact_changed_between_privacy_scans"
    return raw, None


def _filter_upstream_path_exceptions(
    findings: list[dict[str, Any]],
    raw_by_path: dict[str, bytes],
    exceptions: tuple[UpstreamPathException, ...],
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
        exception = _matching_exception(artifact, raw, finding, exceptions)
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
        allowed.append(
            {
                "artifact_path": artifact.relative_path,
                "artifact_role": artifact.role,
                "byte_offset": finding["byte_offset"],
                "component_id": exception.component_id,
                "governed_source_artifact_sha256": (
                    exception.governed_source_artifact_sha256
                ),
                "path_sha256": hashlib.sha256(exception.exact_path).hexdigest(),
                "rule_id": exception.rule_id,
            }
        )
    allowed.sort(
        key=lambda row: (
            row["artifact_path"],
            row["byte_offset"],
            row["component_id"],
        )
    )
    return retained, allowed


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
) -> UpstreamPathException | None:
    if (
        artifact.role not in RISC0_PROGRAM_BINARY_ROLES
        or not raw.startswith(RISC0_PROGRAM_BINARY_MAGIC)
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


def _read_exact_inventory(
    root: Path,
    expected_names: set[str],
) -> tuple[list[str], list[dict[str, str]]]:
    try:
        descriptor = privacy._open_root(root)
    except privacy.ArtifactReadError as exc:
        return [], [_error(".", "inventory", exc.code)]
    try:
        observed_names = sorted(os.listdir(descriptor))
    except OSError:
        return [], [_error(".", "inventory", "inventory_unavailable")]
    finally:
        os.close(descriptor)

    observed = set(observed_names)
    errors = [
        _error(path, "inventory", "governed_artifact_missing")
        for path in sorted(expected_names - observed)
    ]
    if observed - expected_names:
        # Extra names are not echoed because their names may themselves leak data.
        errors.append(_error(".", "inventory", "extra_governed_inventory"))
    return observed_names, errors


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
    arguments = parser.parse_args(argv)
    report = scan_artifact_directory(arguments.artifact_directory)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
