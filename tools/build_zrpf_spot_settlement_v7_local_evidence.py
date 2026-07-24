#!/usr/bin/env python3
"""Assemble one canonical, authority-neutral Spot V7 proof-evidence bundle."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import os
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping

if __package__:
    checker = importlib.import_module("tools.check_zrpf_spot_settlement_v7_local_evidence")
else:
    sys.path.insert(0, Path(__file__).resolve().parents[1].as_posix())
    checker = importlib.import_module("tools.check_zrpf_spot_settlement_v7_local_evidence")


class EvidenceBuildError(ValueError):
    """Stable fail-closed evidence-assembly rejection."""


@dataclass(frozen=True)
class BuildResult:
    evidence_path: Path
    bundle_directory: Path
    evidence_sha256: str
    artifact_count: int
    candidate_bundle_built: bool = True
    receipt_seals_cryptographically_verified: bool = False
    governed_source_build_verified: bool = False
    firecracker_execution_verified: bool = False
    bundle_and_evidence_publication_atomic: bool = False
    release_authority: bool = False
    settlement_authority: bool = False
    production_authority: bool = False


def build_evidence(
    *,
    recorded_at: str,
    artifact_paths: Mapping[str, Path],
    bundle_directory: Path,
    evidence_path: Path,
) -> BuildResult:
    """Snapshot, derive, self-check, and publish one exact candidate bundle.

    No verification status, program identity, commitment, or authority Boolean
    is accepted from the caller. Every evidence field is derived from the exact
    bounded artifact bytes.
    """

    expected_ids = {spec[0] for spec in checker.ARTIFACT_SPECS_V1}
    if set(artifact_paths) != expected_ids:
        raise EvidenceBuildError("artifact input IDs mismatch")
    _require_new_output(bundle_directory, "bundle directory")
    _require_new_output(evidence_path, "evidence path")
    if bundle_directory.parent != evidence_path.parent:
        raise EvidenceBuildError("bundle and evidence must share one publication parent")
    artifact_raw = _snapshot_inputs(artifact_paths)
    try:
        document = checker.compose_evidence_document_v1(
            recorded_at=recorded_at,
            artifact_raw=artifact_raw,
        )
    except checker.EvidenceError as exc:
        raise EvidenceBuildError(f"artifact relation rejected: {exc}") from exc
    evidence_raw = checker.canonical_evidence_bytes(document)
    evidence_sha256 = hashlib.sha256(evidence_raw).hexdigest()
    _stage_self_check_and_publish(
        artifact_raw=artifact_raw,
        evidence_raw=evidence_raw,
        evidence_sha256=evidence_sha256,
        bundle_directory=bundle_directory,
        evidence_path=evidence_path,
    )
    return BuildResult(
        evidence_path=evidence_path,
        bundle_directory=bundle_directory,
        evidence_sha256=evidence_sha256,
        artifact_count=len(artifact_raw),
    )


def _stage_self_check_and_publish(
    *,
    artifact_raw: Mapping[str, bytes],
    evidence_raw: bytes,
    evidence_sha256: str,
    bundle_directory: Path,
    evidence_path: Path,
) -> None:
    staged_bundle = bundle_directory.with_name(f".{bundle_directory.name}.candidate-staging")
    staged_evidence = evidence_path.with_name(f".{evidence_path.name}.candidate-staging")
    _require_new_output(staged_bundle, "staged bundle directory")
    _require_new_output(staged_evidence, "staged evidence path")
    published_bundle = False
    try:
        os.mkdir(staged_bundle, 0o700)
        _write_bundle(staged_bundle, artifact_raw)
        _write_new_file(staged_evidence, evidence_raw)
        _fsync_directory(staged_bundle)
        _fsync_directory(staged_bundle.parent)
        checker.check_evidence(
            staged_evidence,
            artifact_directory=staged_bundle,
            expected_evidence_sha256=evidence_sha256,
        )
        os.replace(staged_bundle, bundle_directory)
        published_bundle = True
        os.replace(staged_evidence, evidence_path)
        _fsync_directory(bundle_directory.parent)
    except (OSError, checker.EvidenceError) as exc:
        if published_bundle:
            shutil.rmtree(bundle_directory, ignore_errors=True)
        _cleanup(staged_bundle, staged_evidence)
        if isinstance(exc, checker.EvidenceError):
            raise EvidenceBuildError(f"candidate self-check rejected: {exc}") from exc
        raise EvidenceBuildError("candidate publication failed") from exc


def _snapshot_inputs(artifact_paths: Mapping[str, Path]) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    total = 0
    for artifact_id, _file_name, _kind, maximum in checker.ARTIFACT_SPECS_V1:
        try:
            raw = checker.read_bounded_regular_file_v1(
                artifact_paths[artifact_id],
                maximum_bytes=maximum,
                label=f"artifact input {artifact_id}",
            )
        except checker.EvidenceError as exc:
            raise EvidenceBuildError(str(exc)) from exc
        total += len(raw)
        if total > checker.MAX_TOTAL_ARTIFACT_BYTES_V1:
            raise EvidenceBuildError("total artifact input exceeds governed bound")
        result[artifact_id] = raw
    return result


def _write_bundle(directory: Path, artifact_raw: Mapping[str, bytes]) -> None:
    for artifact_id, file_name, _kind, _maximum in checker.ARTIFACT_SPECS_V1:
        _write_new_file(directory / file_name, artifact_raw[artifact_id])


def _write_new_file(path: Path, raw: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0)
    descriptor = os.open(path, flags, 0o600)
    try:
        view = memoryview(raw)
        offset = 0
        while offset < len(view):
            written = os.write(descriptor, view[offset:])
            if written <= 0:
                raise OSError("short evidence write")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _require_new_output(path: Path, label: str) -> None:
    try:
        if path.exists() or path.is_symlink():
            raise EvidenceBuildError(f"{label} already exists")
        parent = path.parent
        parent_stat = parent.lstat()
    except FileNotFoundError as exc:
        raise EvidenceBuildError(f"{label} parent is unavailable") from exc
    except OSError as exc:
        raise EvidenceBuildError(f"{label} path check failed") from exc
    if not parent.is_dir() or parent.is_symlink() or parent_stat.st_nlink < 1:
        raise EvidenceBuildError(f"{label} parent must be a real directory")


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_CLOEXEC", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _cleanup(staged_bundle: Path, staged_evidence: Path) -> None:
    shutil.rmtree(staged_bundle, ignore_errors=True)
    try:
        staged_evidence.unlink(missing_ok=True)
    except OSError:
        pass


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recorded-at", required=True)
    for artifact_id, _file_name, _kind, _maximum in checker.ARTIFACT_SPECS_V1:
        parser.add_argument(f"--{artifact_id.replace('_', '-')}", type=Path, required=True)
    parser.add_argument("--bundle-directory", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    artifact_paths = {
        artifact_id: getattr(args, artifact_id)
        for artifact_id, _file_name, _kind, _maximum in checker.ARTIFACT_SPECS_V1
    }
    try:
        result = build_evidence(
            recorded_at=args.recorded_at,
            artifact_paths=artifact_paths,
            bundle_directory=args.bundle_directory,
            evidence_path=args.evidence,
        )
        report = {
            "ok": True,
            "schema": "zenodex/zrpf_spot_settlement_v7_local_evidence_build/v1",
            "artifact_count": result.artifact_count,
            "bundle_directory": result.bundle_directory.as_posix(),
            "evidence_path": result.evidence_path.as_posix(),
            "evidence_sha256": result.evidence_sha256,
            "receipt_seals_cryptographically_verified": False,
            "governed_source_build_verified": False,
            "firecracker_execution_verified": False,
            "bundle_and_evidence_publication_atomic": False,
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        }
    except EvidenceBuildError as exc:
        report = {
            "ok": False,
            "schema": "zenodex/zrpf_spot_settlement_v7_local_evidence_build/v1",
            "error": str(exc),
        }
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print("ok" if report["ok"] else f"rejected: {report['error']}")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
