"""Exact committed-byte binding for the whole-program plan artifacts.

The caller supplies an anchored repository root and an already checked exact
HEAD. This module reads both ``HEAD:path`` blobs before opening either worktree
artifact, captures each worktree file in a write-sealed descriptor, and accepts
the pair only when the held bytes equal the corresponding committed blob.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from tools.live_gate_registry_v1 import (
    AnchoredDirectoryV1,
    AnchoredFileV1,
    git_bytes_v1,
)


@dataclass(frozen=True, slots=True)
class PlanArtifactSpecV1:
    """One fixed repository-relative artifact and its byte ceiling."""

    path: str
    max_bytes: int


@dataclass(frozen=True, slots=True)
class PlanArtifactBindingFindingV1:
    """Typed refusal produced before plan semantics or observers are used."""

    rule_id: str
    subject: str
    evidence: str


@dataclass(slots=True)
class BoundPlanArtifactV1:
    """Held sealed bytes plus the source descriptor retained for drift checks."""

    spec: PlanArtifactSpecV1
    source: AnchoredFileV1
    data: bytes
    sha256: str

    @property
    def is_open(self) -> bool:
        return self.source.is_open

    def close(self) -> None:
        self.source.close()


@dataclass(slots=True)
class BoundPlanArtifactsV1:
    """The JSON/Markdown pair bound to exact blobs of one checked commit."""

    head: str
    artifacts: tuple[BoundPlanArtifactV1, ...]

    @property
    def is_open(self) -> bool:
        return bool(self.artifacts) and all(artifact.is_open for artifact in self.artifacts)

    @property
    def digests(self) -> tuple[tuple[str, str], ...]:
        return tuple((artifact.spec.path, artifact.sha256) for artifact in self.artifacts)

    def bytes_for(self, path: str) -> bytes:
        for artifact in self.artifacts:
            if artifact.spec.path == path:
                return artifact.data
        raise KeyError(path)

    def source_findings(self) -> tuple[PlanArtifactBindingFindingV1, ...]:
        findings: list[PlanArtifactBindingFindingV1] = []
        for artifact in self.artifacts:
            if not artifact.is_open:
                findings.append(
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_binding_closed",
                        artifact.spec.path,
                        "held artifact descriptors are closed",
                    )
                )
                continue
            try:
                observed = artifact.source.rehash()
            except OSError as exc:
                findings.append(
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_source_unavailable",
                        artifact.spec.path,
                        f"{type(exc).__name__}: {exc}",
                    )
                )
                continue
            if observed != artifact.sha256:
                findings.append(
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_source_drift",
                        artifact.spec.path,
                        f"bound={artifact.sha256} observed={observed}",
                    )
                )
        return tuple(findings)

    def close(self) -> None:
        pending: BaseException | None = None
        for artifact in self.artifacts:
            try:
                artifact.close()
            except BaseException as exc:
                if pending is None:
                    pending = exc
        if pending is not None:
            raise pending


def _close_artifacts(artifacts: tuple[BoundPlanArtifactV1, ...] | list[BoundPlanArtifactV1]) -> None:
    pending: BaseException | None = None
    for artifact in artifacts:
        try:
            artifact.close()
        except BaseException as exc:
            if pending is None:
                pending = exc
    if pending is not None:
        raise pending


def _head_blob(
    root: AnchoredDirectoryV1, head: str, spec: PlanArtifactSpecV1
) -> bytes | None:
    return git_bytes_v1(
        root,
        ("cat-file", "blob", f"{head}:{spec.path}"),
        max_output_bytes=spec.max_bytes + 1,
    )


def _read_head_blobs(
    root: AnchoredDirectoryV1,
    head: str,
    specs: tuple[PlanArtifactSpecV1, ...],
) -> tuple[tuple[bytes, ...] | None, tuple[PlanArtifactBindingFindingV1, ...]]:
    blobs: list[bytes] = []
    findings: list[PlanArtifactBindingFindingV1] = []
    for spec in specs:
        blob = _head_blob(root, head, spec)
        if blob is None:
            findings.append(
                PlanArtifactBindingFindingV1(
                    "plan_artifact_head_blob_unavailable",
                    spec.path,
                    f"cannot read exact blob {head}:{spec.path}",
                )
            )
        elif len(blob) > spec.max_bytes:
            findings.append(
                PlanArtifactBindingFindingV1(
                    "plan_artifact_size_refused",
                    spec.path,
                    f"HEAD blob exceeds {spec.max_bytes} bytes",
                )
            )
        else:
            blobs.append(blob)
    return (None, tuple(findings)) if findings else (tuple(blobs), ())


def _open_worktree_artifacts(
    root: AnchoredDirectoryV1,
    specs: tuple[PlanArtifactSpecV1, ...],
) -> tuple[tuple[BoundPlanArtifactV1, ...] | None, tuple[PlanArtifactBindingFindingV1, ...]]:
    artifacts: list[BoundPlanArtifactV1] = []
    try:
        for spec in specs:
            source: AnchoredFileV1 | None = None
            try:
                source = root.open_file(spec.path)
                data = source.read(spec.max_bytes)
            except OSError as exc:
                if source is not None:
                    source.close()
                _close_artifacts(artifacts)
                return None, (
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_binding_refused",
                        spec.path,
                        f"{type(exc).__name__}: {exc}",
                    ),
                )
            if data is None:
                source.close()
                _close_artifacts(artifacts)
                return None, (
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_size_refused",
                        spec.path,
                        f"worktree artifact exceeds {spec.max_bytes} bytes",
                    ),
                )
            artifacts.append(BoundPlanArtifactV1(spec, source, data, source.sha256))
        return tuple(artifacts), ()
    except BaseException:
        _close_artifacts(artifacts)
        raise


def _blob_mismatch_findings(
    artifacts: tuple[BoundPlanArtifactV1, ...],
    committed_blobs: tuple[bytes, ...],
) -> tuple[PlanArtifactBindingFindingV1, ...]:
    findings: list[PlanArtifactBindingFindingV1] = []
    for artifact, committed in zip(artifacts, committed_blobs, strict=True):
        if artifact.data != committed:
            findings.append(
                PlanArtifactBindingFindingV1(
                    "plan_artifact_head_blob_mismatch",
                    artifact.spec.path,
                    f"sealed={artifact.sha256} committed={hashlib.sha256(committed).hexdigest()}",
                )
            )
    return tuple(findings)


def bind_plan_artifacts_v1(
    root: AnchoredDirectoryV1,
    head: str,
    specs: tuple[PlanArtifactSpecV1, ...],
) -> tuple[BoundPlanArtifactsV1 | None, tuple[PlanArtifactBindingFindingV1, ...]]:
    """Bind every artifact to its exact pre-read ``head:path`` blob.

    All committed blobs are obtained first. Worktree files are then opened and
    retained as sealed snapshots. Any unavailable, oversized, unsealable, or
    byte-mismatched artifact closes the entire partial set and refuses.
    """

    head_blobs, findings = _read_head_blobs(root, head, specs)
    if head_blobs is None:
        return None, findings
    artifacts, findings = _open_worktree_artifacts(root, specs)
    if artifacts is None:
        return None, findings
    findings = _blob_mismatch_findings(artifacts, head_blobs)
    if findings:
        _close_artifacts(artifacts)
        return None, findings
    return BoundPlanArtifactsV1(head, artifacts), ()
