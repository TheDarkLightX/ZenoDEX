from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping


ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_BUNDLE_VERIFY_SCHEMA = (
    "zenodex/zenograph-autotrader-ranking-review-bundle-verify/v1"
)


@dataclass(frozen=True)
class ZenoGraphRankingReviewBundleArtifactStatus:
    name: str
    path: str
    exists: bool
    bytes_match: bool
    sha256_match: bool
    actual_bytes: int | None
    actual_sha256: str | None

    @property
    def ok(self) -> bool:
        return bool(self.exists and self.bytes_match and self.sha256_match)

    def to_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "path": self.path,
            "exists": bool(self.exists),
            "bytes_match": bool(self.bytes_match),
            "sha256_match": bool(self.sha256_match),
            "actual_bytes": self.actual_bytes,
            "actual_sha256": self.actual_sha256,
            "ok": bool(self.ok),
        }


@dataclass(frozen=True)
class ZenoGraphRankingReviewBundleVerifyResult:
    manifest_path: str
    bundle_dir: str | None
    artifacts: tuple[ZenoGraphRankingReviewBundleArtifactStatus, ...]
    schema: str = ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_BUNDLE_VERIFY_SCHEMA

    @property
    def ok(self) -> bool:
        return all(artifact.ok for artifact in self.artifacts)

    @property
    def missing_artifacts(self) -> tuple[str, ...]:
        return tuple(artifact.name for artifact in self.artifacts if not artifact.exists)

    @property
    def bytes_mismatches(self) -> tuple[str, ...]:
        return tuple(
            artifact.name
            for artifact in self.artifacts
            if artifact.exists and not artifact.bytes_match
        )

    @property
    def sha256_mismatches(self) -> tuple[str, ...]:
        return tuple(
            artifact.name
            for artifact in self.artifacts
            if artifact.exists and not artifact.sha256_match
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema": self.schema,
            "manifest_path": self.manifest_path,
            "bundle_dir": self.bundle_dir,
            "ok": bool(self.ok),
            "missing_artifacts": list(self.missing_artifacts),
            "bytes_mismatches": list(self.bytes_mismatches),
            "sha256_mismatches": list(self.sha256_mismatches),
            "artifacts": [artifact.to_dict() for artifact in self.artifacts],
        }


def verify_zenograph_ranking_review_bundle_manifest(
    *,
    manifest_path: Path,
    payload: Mapping[str, object],
) -> ZenoGraphRankingReviewBundleVerifyResult:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be a mapping")
    if payload.get("schema") != "zenodex/zenograph-autotrader-ranking-review-bundle/v1":
        raise ValueError("unsupported ranking review bundle manifest schema")

    artifacts_raw = payload.get("artifacts")
    if not isinstance(artifacts_raw, Mapping):
        raise ValueError("manifest must contain an artifacts object")

    statuses: list[ZenoGraphRankingReviewBundleArtifactStatus] = []
    for name, artifact in sorted(artifacts_raw.items()):
        if not isinstance(name, str):
            raise TypeError("artifact names must be strings")
        if not isinstance(artifact, Mapping):
            raise TypeError(f"artifact {name!r} must be an object")
        path = _require_str(artifact.get("path"), name=f"artifacts.{name}.path")
        expected_bytes = _require_int(
            artifact.get("bytes"), name=f"artifacts.{name}.bytes"
        )
        expected_sha256 = _require_str(
            artifact.get("sha256"), name=f"artifacts.{name}.sha256"
        )
        artifact_path = Path(path)
        if artifact_path.exists():
            data = artifact_path.read_bytes()
            actual_bytes = len(data)
            actual_sha256 = hashlib.sha256(data).hexdigest()
            exists = True
            bytes_match = actual_bytes == expected_bytes
            sha256_match = actual_sha256 == expected_sha256
        else:
            actual_bytes = None
            actual_sha256 = None
            exists = False
            bytes_match = False
            sha256_match = False
        statuses.append(
            ZenoGraphRankingReviewBundleArtifactStatus(
                name=name,
                path=path,
                exists=exists,
                bytes_match=bytes_match,
                sha256_match=sha256_match,
                actual_bytes=actual_bytes,
                actual_sha256=actual_sha256,
            )
        )

    bundle_dir = payload.get("bundle_dir")
    if bundle_dir is not None and not isinstance(bundle_dir, str):
        raise TypeError("bundle_dir must be a string or null")
    return ZenoGraphRankingReviewBundleVerifyResult(
        manifest_path=str(manifest_path),
        bundle_dir=bundle_dir,
        artifacts=tuple(statuses),
    )


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    return value


def _require_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return value
