"""Exact committed-byte binding for the whole-program plan artifacts.

The caller supplies an anchored repository root and an already checked exact
HEAD. This module reads both ``HEAD:path`` blobs before opening either worktree
artifact, captures each worktree file in a write-sealed descriptor, and accepts
the pair only when the held bytes equal the corresponding committed blob.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Final

from tools.bounded_json_v1 import PLAN_JSON_LIMITS_V1
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


PLAN_JSON_ARTIFACT_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V1.json"
PLAN_MARKDOWN_ARTIFACT_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V1.md"
MAX_PLAN_MARKDOWN_BYTES_V1: Final = 1024 * 1024
PLAN_ARTIFACT_SPECS_V1: Final[tuple[PlanArtifactSpecV1, PlanArtifactSpecV1]] = (
    PlanArtifactSpecV1(PLAN_JSON_ARTIFACT_PATH_V1, PLAN_JSON_LIMITS_V1.max_bytes),
    PlanArtifactSpecV1(PLAN_MARKDOWN_ARTIFACT_PATH_V1, MAX_PLAN_MARKDOWN_BYTES_V1),
)


@dataclass(frozen=True, slots=True)
class PlanArtifactBindingFindingV1:
    """Typed refusal produced before plan semantics or observers are used."""

    rule_id: str
    subject: str
    evidence: str


@dataclass(frozen=True, slots=True)
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


@dataclass(frozen=True, slots=True)
class BoundPlanArtifactsV1:
    """The JSON/Markdown pair bound to exact blobs of one checked commit."""

    head: str
    artifacts: tuple[BoundPlanArtifactV1, BoundPlanArtifactV1]

    @property
    def is_open(self) -> bool:
        return bool(self.artifacts) and all(artifact.is_open for artifact in self.artifacts)

    @property
    def digests(self) -> tuple[tuple[str, str], ...]:
        return tuple((artifact.spec.path, artifact.sha256) for artifact in self.artifacts)

    def bytes_for(self, path: str) -> bytes | None:
        for artifact in self.artifacts:
            if artifact.spec.path == path:
                return artifact.data
        return None

    def integrity_findings(
        self, root: AnchoredDirectoryV1, *, expected_head: str
    ) -> tuple[PlanArtifactBindingFindingV1, ...]:
        """Recheck the complete ordered JSON/Markdown binding before any consumer uses bytes.

        These Python values remain caller-constructible conventions inside one
        process. This method nevertheless makes accidental mutation, partial
        construction, reordered records, source drift, and Git/blob drift
        explicit typed failures at every consumer boundary.
        """

        shape_findings = _bound_artifact_shape_findings_v1(self, expected_head)
        if shape_findings:
            return shape_findings
        findings: list[PlanArtifactBindingFindingV1] = []
        head_blobs, head_findings = _read_head_blobs(
            root, expected_head, PLAN_ARTIFACT_SPECS_V1
        )
        if head_blobs is None:
            return head_findings
        for artifact, committed in zip(self.artifacts, head_blobs, strict=True):
            data_digest = hashlib.sha256(artifact.data).hexdigest()
            if data_digest != artifact.sha256:
                findings.append(
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_data_digest_mismatch",
                        artifact.spec.path,
                        f"bound={artifact.sha256} observed={data_digest}",
                    )
                )
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
            if artifact.data != committed:
                findings.append(
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_head_blob_mismatch",
                        artifact.spec.path,
                        f"sealed={data_digest} committed={hashlib.sha256(committed).hexdigest()}",
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


def _close_artifacts_preserving_primary_v1(
    artifacts: tuple[BoundPlanArtifactV1, ...] | list[BoundPlanArtifactV1],
) -> BaseException | None:
    """Attempt every close without replacing an earlier construction failure."""

    try:
        _close_artifacts(artifacts)
    except BaseException as exc:
        return exc
    return None


def _close_current_source_v1(source: AnchoredFileV1 | None) -> BaseException | None:
    """Close the source that has not yet transferred into an immutable record."""

    if source is None:
        return None
    try:
        source.close()
    except BaseException as exc:
        return exc
    return None


def _specs_findings_v1(specs: object) -> tuple[PlanArtifactBindingFindingV1, ...]:
    """Reject any caller-selected artifact set before opening paths or calling Git."""

    if type(specs) is not tuple or len(specs) != len(PLAN_ARTIFACT_SPECS_V1):
        return (
            PlanArtifactBindingFindingV1(
                "plan_artifact_specs_invalid",
                "plan_artifacts",
                "expected exactly the canonical JSON then Markdown artifact pair",
            ),
        )
    for actual, expected in zip(specs, PLAN_ARTIFACT_SPECS_V1, strict=True):
        if (
            type(actual) is not PlanArtifactSpecV1
            or type(actual.path) is not str
            or type(actual.max_bytes) is not int
            or actual.path != expected.path
            or actual.max_bytes != expected.max_bytes
        ):
            return (
                PlanArtifactBindingFindingV1(
                    "plan_artifact_specs_invalid",
                    "plan_artifacts",
                    "expected exactly the canonical JSON then Markdown artifact pair",
                ),
            )
    return ()


def _bound_artifact_shape_findings_v1(
    artifacts: object, expected_head: object
) -> tuple[PlanArtifactBindingFindingV1, ...]:
    """Check exact two-item record structure before dereferencing held values."""

    if type(artifacts) is not BoundPlanArtifactsV1 or type(expected_head) is not str:
        return (
            PlanArtifactBindingFindingV1(
                "plan_artifact_binding_shape_invalid",
                "plan_artifacts",
                "bound artifact context or expected HEAD is malformed",
            ),
        )
    if type(artifacts.head) is not str or artifacts.head != expected_head:
        return (
            PlanArtifactBindingFindingV1(
                "plan_artifact_binding_context_mismatch",
                "plan_artifacts",
                "artifact commit differs from the expected context HEAD",
            ),
        )
    if type(artifacts.artifacts) is not tuple or len(artifacts.artifacts) != len(PLAN_ARTIFACT_SPECS_V1):
        return (
            PlanArtifactBindingFindingV1(
                "plan_artifact_binding_shape_invalid",
                "plan_artifacts",
                "expected exactly the canonical JSON then Markdown bound pair",
            ),
        )
    specs = tuple(artifact.spec for artifact in artifacts.artifacts if type(artifact) is BoundPlanArtifactV1)
    if len(specs) != len(PLAN_ARTIFACT_SPECS_V1):
        return (
            PlanArtifactBindingFindingV1(
                "plan_artifact_binding_shape_invalid",
                "plan_artifacts",
                "expected exactly the canonical JSON then Markdown bound pair",
            ),
        )
    spec_findings = _specs_findings_v1(specs)
    if spec_findings:
        return (
            PlanArtifactBindingFindingV1(
                "plan_artifact_binding_shape_invalid",
                "plan_artifacts",
                "expected exactly the canonical JSON then Markdown bound pair",
            ),
        )
    for artifact in artifacts.artifacts:
        if (
            type(artifact) is not BoundPlanArtifactV1
            or type(artifact.source) is not AnchoredFileV1
            or type(artifact.data) is not bytes
            or type(artifact.sha256) is not str
        ):
            return (
                PlanArtifactBindingFindingV1(
                    "plan_artifact_binding_shape_invalid",
                    "plan_artifacts",
                    "bound artifact fields must be exact immutable record values",
                ),
            )
    return ()


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
    specs: tuple[PlanArtifactSpecV1, PlanArtifactSpecV1],
) -> tuple[tuple[BoundPlanArtifactV1, ...] | None, tuple[PlanArtifactBindingFindingV1, ...]]:
    artifacts: list[BoundPlanArtifactV1] = []
    for spec in specs:
        source: AnchoredFileV1 | None = None
        transferred = False
        failure: PlanArtifactBindingFindingV1 | None = None
        current_cleanup_error: BaseException | None = None
        try:
            source = root.open_file(spec.path)
            data = source.read(spec.max_bytes)
            if data is None:
                failure = PlanArtifactBindingFindingV1(
                    "plan_artifact_size_refused",
                    spec.path,
                    f"worktree artifact exceeds {spec.max_bytes} bytes",
                )
            else:
                artifacts.append(BoundPlanArtifactV1(spec, source, data, source.sha256))
                transferred = True
        except OSError as exc:
            failure = PlanArtifactBindingFindingV1(
                "plan_artifact_binding_refused",
                spec.path,
                f"{type(exc).__name__}: {exc}",
            )
        except BaseException:
            _close_artifacts_preserving_primary_v1(artifacts)
            raise
        finally:
            if not transferred:
                current_cleanup_error = _close_current_source_v1(source)
        if failure is not None:
            artifact_cleanup_error = _close_artifacts_preserving_primary_v1(artifacts)
            findings = [failure]
            cleanup_error = current_cleanup_error or artifact_cleanup_error
            if cleanup_error is not None:
                findings.append(
                    PlanArtifactBindingFindingV1(
                        "plan_artifact_cleanup_refused",
                        spec.path,
                        f"{type(cleanup_error).__name__}: {cleanup_error}",
                    )
                )
            return None, tuple(findings)
    return tuple(artifacts), ()


def bind_plan_artifacts_v1(
    root: AnchoredDirectoryV1,
    head: str,
    specs: object = PLAN_ARTIFACT_SPECS_V1,
) -> tuple[BoundPlanArtifactsV1 | None, tuple[PlanArtifactBindingFindingV1, ...]]:
    """Bind every artifact to its exact pre-read ``head:path`` blob.

    All committed blobs are obtained first. Worktree files are then opened and
    retained as sealed snapshots. Any unavailable, oversized, unsealable, or
    byte-mismatched artifact closes the entire partial set and refuses.
    """

    specs_findings = _specs_findings_v1(specs)
    if specs_findings:
        return None, specs_findings
    if type(head) is not str:
        return None, (
            PlanArtifactBindingFindingV1(
                "plan_artifact_binding_shape_invalid",
                "plan_artifacts",
                "expected HEAD must be an exact string",
            ),
        )
    exact_specs = PLAN_ARTIFACT_SPECS_V1
    head_blobs, findings = _read_head_blobs(root, head, exact_specs)
    if head_blobs is None:
        return None, findings
    artifacts, findings = _open_worktree_artifacts(root, exact_specs)
    if artifacts is None:
        return None, findings
    bound = BoundPlanArtifactsV1(head, (artifacts[0], artifacts[1]))
    findings = bound.integrity_findings(root, expected_head=head)
    if findings:
        _close_artifacts(artifacts)
        return None, findings
    return bound, ()
