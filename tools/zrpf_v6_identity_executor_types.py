"""Typed boundary shared by the Spot V6 identity executor and build runner."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Protocol


class ExecutionError(ValueError):
    """A deterministic execution or artifact boundary rejected."""


class IncompleteContainerCleanupError(ExecutionError):
    """A failed build may retain an owned container and recovery evidence."""


class BuildKind(str, Enum):
    GUEST = "guest"
    HOST_VERIFIER = "host_verifier"
    ARCHIVE = "archive"


@dataclass(frozen=True)
class ArchiveMember:
    """One exact file copied into a deterministic build-result archive."""

    source: str
    name: str
    executable: bool


@dataclass(frozen=True)
class BuildRequest:
    kind: BuildKind
    pass_id: str
    stage_id: str
    source_commit: str
    source_snapshot: Path
    target_directory: Path
    output_directory: Path
    container_target_directory: str
    container_output_directory: str
    artifact_file: str
    command: tuple[str, ...]
    extraction_source: str
    companion_artifact_file: str | None = None
    companion_extraction_source: str | None = None
    archive_members: tuple[ArchiveMember, ...] = ()


@dataclass(frozen=True)
class BuildResult:
    artifact_bytes: int
    artifact_sha256: str
    image_id: str | None


class BuildRunner(Protocol):
    """Narrow imperative shell used by the deterministic executor core."""

    def security_posture(self) -> dict[str, Any]:
        """Return the exact candidate-evidence posture before any build."""

    def run(self, request: BuildRequest) -> BuildResult:
        """Execute one exact build/extraction request."""
