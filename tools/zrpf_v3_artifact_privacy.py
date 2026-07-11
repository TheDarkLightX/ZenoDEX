#!/usr/bin/env python3
"""Fail-closed privacy scan for committed public ZRPF V3 artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
REPORT_SCHEMA = "zenodex/zrpf_v3_artifact_privacy_scan/v1"
MAX_ARTIFACT_COUNT = 64
MAX_ARTIFACT_BYTES = 16 * 1024 * 1024
MAX_TOTAL_BYTES = 64 * 1024 * 1024
MAX_FINDINGS = 256
EVIDENCE_RELATIVE_PATH = "docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260711.json"


@dataclass(frozen=True, order=True)
class ArtifactSpec:
    relative_path: str
    role: str


@dataclass(frozen=True)
class PrivacyRule:
    rule_id: str
    pattern: re.Pattern[bytes]


FIRECRACKER_RUNTIME_PUBLIC_ARTIFACTS: tuple[ArtifactSpec, ...] = (
    ArtifactSpec(
        "config/proof_profiles/zrpf_firecracker_guest_kernel_build_record_v1.json",
        "guest_kernel_build_record",
    ),
    ArtifactSpec(
        "config/proof_profiles/zrpf_firecracker_runtime_image_build_record_v1.json",
        "runtime_image_build_record",
    ),
    ArtifactSpec(
        "config/proof_profiles/zrpf_v3_firecracker_replay_intent_v1.json",
        "firecracker_replay_intent",
    ),
    ArtifactSpec(
        "config/proof_profiles/zrpf_v3_firecracker_runtime_artifact_manifest_v1.json",
        "runtime_artifact_manifest",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_FIRECRACKER_GOVERNED_DIRECT_REPLAY_EVIDENCE_20260711.json",
        "governed_direct_replay_evidence",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_FIRECRACKER_RUNTIME_CONTRACT_20260711.md",
        "firecracker_runtime_contract",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/firecracker-governed-output-payload.json",
        "governed_firecracker_output_payload",
    ),
    ArtifactSpec(
        "tools/build_zrpf_v3_firecracker_guest_images.sh",
        "guest_image_build_recipe",
    ),
)


DEFAULT_ARTIFACTS: tuple[ArtifactSpec, ...] = (
    ArtifactSpec(
        "config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json",
        "sandbox_candidate_profile",
    ),
    ArtifactSpec(
        "config/proof_profiles/zrpf_v1_retained_source_anchor_v1.json",
        "retained_source_anchor",
    ),
    ArtifactSpec(
        "config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json",
        "source_policy",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V1_SPOT_ADAPTER_TEMPORARY_LOCAL_EVIDENCE_20260710.json",
        "adapter_evidence",
    ),
    ArtifactSpec(
        "docs/research/RISC0_RETAINED_IMAGE_DEPENDENCY_DISPOSITION_20260711.md",
        "dependency_disposition",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260710.json",
        "historical_source_closure_evidence",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260711.json",
        "source_closure_evidence",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_RETAINED_REPLAY_CHANNEL_MATRIX_20260710.json",
        "channel_analysis",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_RETAINED_REPLAY_THREAT_MODEL_20260710.md",
        "threat_model",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_STRUCTURAL_TREE_TEMPORARY_LOCAL_EVIDENCE_20260710.json",
        "structural_evidence",
    ),
    ArtifactSpec(
        "docs/research/ZRPF_V3_CORRECT_BY_CONSTRUCTION_SPEC_20260710.md",
        "correct_by_construction_spec",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/README.md",
        "artifact_documentation",
    ),
    ArtifactSpec("zk/zrpf_risc0/README.md", "workspace_documentation"),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/adapter-leaf-0.receipt.json",
        "retained_receipt",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/adapter-leaf-1.receipt.json",
        "retained_receipt",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/adapter-leaf-2.receipt.json",
        "retained_receipt",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/adapter-leaf-3.receipt.json",
        "retained_receipt",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/structural-l1-left.receipt.json",
        "retained_receipt",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/structural-l1-right.receipt.json",
        "retained_receipt",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/structural-l2-root.receipt.json",
        "retained_receipt",
    ),
    ArtifactSpec(
        "evidence/zrpf-v3-retained-structural-replay-v1/receipts/"
        "structural-l2-root.seal-word-1-xor-lsb.receipt.json",
        "retained_receipt",
    ),
    *FIRECRACKER_RUNTIME_PUBLIC_ARTIFACTS,
)
PRE_RECORD_ARTIFACTS = tuple(
    artifact for artifact in DEFAULT_ARTIFACTS if artifact.relative_path != EVIDENCE_RELATIVE_PATH
)
EVIDENCE_ARTIFACT = next(
    artifact for artifact in DEFAULT_ARTIFACTS if artifact.relative_path == EVIDENCE_RELATIVE_PATH
)

PRIVACY_RULES: tuple[PrivacyRule, ...] = (
    PrivacyRule(
        "posix_home_path",
        re.compile(rb"(?<![A-Za-z0-9])/(?:home|Users)/[A-Za-z0-9._-]+"),
    ),
    PrivacyRule(
        "posix_workspace_path",
        re.compile(
            rb"(?<![A-Za-z0-9])/(?:workspace|workspaces|builds|runner/_work|media|mnt)/"
            rb"[A-Za-z0-9._-]+"
        ),
    ),
    PrivacyRule(
        "posix_temporary_build_path",
        re.compile(rb"(?<![A-Za-z0-9])/(?:tmp|var/tmp)/[A-Za-z0-9._-]+"),
    ),
    PrivacyRule(
        "windows_home_or_workspace_path",
        re.compile(
            rb"(?i)(?<![A-Za-z0-9])[A-Z]:[\\/](?:Users|workspace|workspaces|builds)"
            rb"[\\/][A-Za-z0-9._ -]+"
        ),
    ),
    PrivacyRule(
        "email_address",
        re.compile(
            rb"(?i)(?<![A-Z0-9.!#$%&'*+/=?^_`{|}~-])"
            rb"[A-Z0-9.!#$%&'*+/=?^_`{|}~-]+@"
            rb"[A-Z0-9](?:[A-Z0-9-]{0,61}[A-Z0-9])?"
            rb"(?:\.[A-Z0-9](?:[A-Z0-9-]{0,61}[A-Z0-9])?)+"
        ),
    ),
    PrivacyRule(
        "private_key_pem",
        re.compile(rb"-----BEGIN [A-Z0-9 ]*PRIVATE KEY-----"),
    ),
    PrivacyRule(
        "url_basic_credentials",
        re.compile(rb"(?i)\b(?:https?|git|ssh|ftp)://[^\s/@:]+:[^\s/@]+@[^\s/]+"),
    ),
    PrivacyRule(
        "url_long_userinfo_credential",
        re.compile(rb"(?i)\b(?:https?|git|ssh|ftp)://[A-Z0-9._~-]{20,}@[^\s/]+"),
    ),
    PrivacyRule(
        "url_secret_query",
        re.compile(
            rb"(?i)\b(?:https?|git|ssh|ftp)://[^\s?#]+[?&]"
            rb"(?:access_token|api_key|password|secret|token)=[^\s&#]+"
        ),
    ),
    PrivacyRule(
        "aws_access_key_id",
        re.compile(rb"\b(?:AKIA|ASIA)[0-9A-Z]{16}\b"),
    ),
    PrivacyRule(
        "aws_secret_access_key_assignment",
        re.compile(rb"(?i)\baws_secret_access_key\s*[:=]\s*[A-Za-z0-9/+]{40}(?:==?)?"),
    ),
    PrivacyRule(
        "google_api_key",
        re.compile(rb"\bAIza[0-9A-Za-z_-]{35}\b"),
    ),
    PrivacyRule(
        "azure_storage_account_key",
        re.compile(rb"(?i)\bAccountKey=[A-Za-z0-9+/]{40,}(?:==?)?"),
    ),
    PrivacyRule(
        "github_legacy_token",
        re.compile(rb"\bgh[pousr]_[A-Za-z0-9]{20,255}\b"),
    ),
    PrivacyRule(
        "github_fine_grained_token",
        re.compile(rb"\bgithub_pat_[A-Za-z0-9_]{20,255}\b"),
    ),
    PrivacyRule(
        "bearer_token",
        re.compile(rb"(?i)\bAuthorization\s*:\s*Bearer\s+[A-Za-z0-9._~+/-]{20,}"),
    ),
)


class ArtifactReadError(Exception):
    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


def scan_default_artifacts(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    """Scan the complete governed ZRPF artifact inventory in this repository."""

    return scan_artifacts(repo_root, DEFAULT_ARTIFACTS)


def scan_candidate_bytes(artifact: ArtifactSpec, raw: bytes) -> dict[str, Any]:
    """Scan one bounded in-memory candidate before it becomes a public artifact."""

    specifications, errors = _validate_artifact_specs((artifact,))
    if not raw or len(raw) > MAX_ARTIFACT_BYTES:
        errors.append(_error(artifact.relative_path, artifact.role, "artifact_size_out_of_bounds"))
    findings: list[dict[str, Any]] = []
    if not errors and specifications:
        findings, exceeded = _scan_bytes(specifications[0], raw, MAX_FINDINGS)
        if exceeded:
            errors.append(_error(artifact.relative_path, artifact.role, "finding_limit_exceeded"))
    findings.sort(key=lambda row: (row["byte_offset"], row["rule_id"]))
    errors.sort(key=lambda row: (row["path"], row["role"], row["code"]))
    return {
        "complete_artifact_privacy_verified": False,
        "error_count": len(errors),
        "errors": errors,
        "finding_count": len(findings),
        "findings": findings,
        "ok": not errors and not findings,
        "schema": REPORT_SCHEMA,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "size_bytes": len(raw),
    }


def scan_artifacts(root: Path, artifacts: Sequence[ArtifactSpec]) -> dict[str, Any]:
    """Scan bounded regular artifacts and return a deterministic fail-closed report."""

    ordered, specification_errors = _validate_artifact_specs(artifacts)
    if len(ordered) > MAX_ARTIFACT_COUNT:
        specification_errors.append(_error(".", "inventory", "artifact_count_limit_exceeded"))
        ordered = ordered[:MAX_ARTIFACT_COUNT]

    scanned: list[dict[str, Any]] = []
    findings: list[dict[str, Any]] = []
    errors = list(specification_errors)
    total_bytes = 0
    try:
        root_descriptor = _open_root(root)
    except ArtifactReadError as exc:
        errors.append(_error(".", "inventory", exc.code))
        root_descriptor = None

    if root_descriptor is not None:
        try:
            for artifact in ordered:
                remaining_bytes = MAX_TOTAL_BYTES - total_bytes
                if remaining_bytes <= 0:
                    errors.append(
                        _error(
                            artifact.relative_path,
                            artifact.role,
                            "total_size_limit_exceeded",
                        )
                    )
                    continue
                try:
                    raw = _read_regular_bounded(
                        root_descriptor,
                        artifact.relative_path,
                        min(MAX_ARTIFACT_BYTES, remaining_bytes),
                    )
                except ArtifactReadError as exc:
                    errors.append(_error(artifact.relative_path, artifact.role, exc.code))
                    continue
                total_bytes += len(raw)
                scanned.append(
                    {
                        "path": artifact.relative_path,
                        "role": artifact.role,
                        "sha256": hashlib.sha256(raw).hexdigest(),
                        "size_bytes": len(raw),
                    }
                )
                new_findings, exceeded = _scan_bytes(
                    artifact,
                    raw,
                    MAX_FINDINGS - len(findings),
                )
                findings.extend(new_findings)
                if exceeded:
                    errors.append(
                        _error(artifact.relative_path, artifact.role, "finding_limit_exceeded")
                    )
                    break
        finally:
            os.close(root_descriptor)

    findings.sort(key=lambda row: (row["path"], row["byte_offset"], row["rule_id"]))
    errors.sort(key=lambda row: (row["path"], row["role"], row["code"]))
    return {
        "artifact_count_expected": len(artifacts),
        "artifact_count_scanned": len(scanned),
        "artifacts": scanned,
        "complete_artifact_privacy_verified": False,
        "error_count": len(errors),
        "errors": errors,
        "finding_count": len(findings),
        "findings": findings,
        "negative_knowledge": (
            "This bounded denylist detects specified public leakage patterns. "
            "Complete artifact privacy remains unverified, including generic "
            "toolchain paths documented by the Firecracker evidence. "
            "A clean result does not prove the absence of all confidential information, "
            "covert channels, or side channels."
        ),
        "ok": not errors and not findings and len(scanned) == len(artifacts),
        "schema": REPORT_SCHEMA,
        "total_bytes_scanned": total_bytes,
    }


def _validate_artifact_specs(
    artifacts: Sequence[ArtifactSpec],
) -> tuple[list[ArtifactSpec], list[dict[str, str]]]:
    ordered = sorted(artifacts)
    errors: list[dict[str, str]] = []
    valid: list[ArtifactSpec] = []
    seen: set[str] = set()
    for artifact in ordered:
        if artifact.relative_path in seen:
            errors.append(_error(artifact.relative_path, artifact.role, "duplicate_artifact"))
            continue
        seen.add(artifact.relative_path)
        if not artifact.role or not _safe_relative_path(artifact.relative_path):
            errors.append(_error(artifact.relative_path, artifact.role, "invalid_artifact_spec"))
            continue
        valid.append(artifact)
    return valid, errors


def _safe_relative_path(value: str) -> bool:
    path = PurePosixPath(value)
    return all(
        (
            bool(value),
            value != ".",
            "\0" not in value,
            "\\" not in value,
            not path.is_absolute(),
            bool(path.parts),
            all(part not in {"", ".", ".."} for part in path.parts),
        )
    )


def _open_root(root: Path) -> int:
    try:
        descriptor = os.open(
            root,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
    except (OSError, ValueError) as exc:
        raise ArtifactReadError("root_directory_unavailable") from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISDIR(metadata.st_mode):
            raise ArtifactReadError("root_not_directory")
    except BaseException:
        os.close(descriptor)
        raise
    return descriptor


def _read_regular_bounded(root_descriptor: int, relative_path: str, maximum: int) -> bytes:
    parts = PurePosixPath(relative_path).parts
    directory_descriptor = os.dup(root_descriptor)
    try:
        for part in parts[:-1]:
            next_descriptor = _open_directory_at(directory_descriptor, part)
            os.close(directory_descriptor)
            directory_descriptor = next_descriptor
        descriptor = _open_file_at(directory_descriptor, parts[-1])
    finally:
        os.close(directory_descriptor)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise ArtifactReadError("artifact_not_regular")
        if before.st_size <= 0 or before.st_size > maximum:
            raise ArtifactReadError("artifact_size_out_of_bounds")
        raw = _read_descriptor_bounded(descriptor, maximum)
        after = os.fstat(descriptor)
        if _identity_tuple(before) != _identity_tuple(after) or len(raw) != after.st_size:
            raise ArtifactReadError("artifact_changed_during_read")
        return raw
    finally:
        os.close(descriptor)


def _open_directory_at(parent_descriptor: int, name: str) -> int:
    try:
        descriptor = os.open(
            name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
            dir_fd=parent_descriptor,
        )
    except (OSError, ValueError) as exc:
        raise ArtifactReadError("artifact_parent_unavailable") from exc
    metadata = os.fstat(descriptor)
    if not stat.S_ISDIR(metadata.st_mode):
        os.close(descriptor)
        raise ArtifactReadError("artifact_parent_not_directory")
    return descriptor


def _open_file_at(parent_descriptor: int, name: str) -> int:
    try:
        return os.open(
            name,
            os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK,
            dir_fd=parent_descriptor,
        )
    except (OSError, ValueError) as exc:
        raise ArtifactReadError("artifact_unavailable") from exc


def _read_descriptor_bounded(descriptor: int, maximum: int) -> bytes:
    output = bytearray()
    while True:
        chunk = os.read(descriptor, min(64 * 1024, maximum + 1 - len(output)))
        if not chunk:
            return bytes(output)
        output.extend(chunk)
        if len(output) > maximum:
            raise ArtifactReadError("artifact_size_out_of_bounds")


def _identity_tuple(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _scan_bytes(
    artifact: ArtifactSpec,
    raw: bytes,
    remaining_findings: int,
) -> tuple[list[dict[str, Any]], bool]:
    findings: list[dict[str, Any]] = []
    for rule in PRIVACY_RULES:
        for match in rule.pattern.finditer(raw):
            if len(findings) >= remaining_findings:
                return findings, True
            findings.append(
                {
                    "byte_offset": match.start(),
                    "match_length": match.end() - match.start(),
                    "match_sha256": hashlib.sha256(match.group()).hexdigest(),
                    "path": artifact.relative_path,
                    "role": artifact.role,
                    "rule_id": rule.rule_id,
                }
            )
    return findings, False


def _error(path: str, role: str, code: str) -> dict[str, str]:
    return {"code": code, "path": path, "role": role}


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--artifact", action="append", default=[])
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    artifacts = (
        tuple(ArtifactSpec(path, "explicit_artifact") for path in args.artifact)
        if args.artifact
        else DEFAULT_ARTIFACTS
    )
    report = scan_artifacts(args.root, artifacts)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
