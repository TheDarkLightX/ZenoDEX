"""Authority-neutral publication effects for validated ZRPF worker captures."""

from __future__ import annotations

import ctypes
import errno
import os
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Callable, Mapping, Sequence

from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools import zrpf_remote_reproof_stage_publication_marker_v1 as marker_protocol
from tools.zrpf_remote_reproof_worker_v2_contract import (
    ArtifactContract,
    ValidatedStage,
    WorkerError,
)


@dataclass(slots=True)
class PreparedPublication:
    directory_fd: int
    parent_parts: tuple[str, ...]
    destination_name: str
    temporary_fd: int | None = None
    linked: bool = False


class PublicationCommitIndeterminate(WorkerError):
    """A completion marker became visible but durable acknowledgement is uncertain."""


def publish_validated_capture_outputs(
    stage: ValidatedStage,
    capture_id: str,
    captured_outputs: Sequence[Mapping[str, object]],
    output_root: Path,
    artifact_root: Path,
    *,
    precommit_check: Callable[[], None],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    """Publish one complete stage and expose its completion marker last."""

    expected_outputs = _captured_output_records(stage, captured_outputs)
    _validate_output_records(stage, output_root, expected_outputs, "stage output")
    marker = marker_protocol.build_stage_publication_marker_v1(
        handoff_id=stage.handoff_id,
        execution_packet_id=stage.execution_packet_id,
        task_id=stage.task_id,
        stage_id=stage.stage_id,
        ordinal=stage.ordinal,
        capture_id=capture_id,
        outputs=expected_outputs,
    )
    root_fd = _open_publication_root(artifact_root)
    outputs: list[PreparedPublication] = []
    marker_publication: PreparedPublication | None = None
    try:
        marker_publication = _prepare_marker_publication(root_fd, stage)
        if _publication_destination_exists(marker_publication):
            outputs = _prepare_output_publications(
                root_fd,
                stage.outputs,
                require_destinations_absent=False,
            )
            _reconcile_existing_publication(
                root_fd,
                artifact_root,
                stage,
                expected_outputs,
                marker,
                [*outputs, marker_publication],
                precommit_check,
            )
            return expected_outputs, marker

        outputs = _prepare_output_publications(
            root_fd,
            stage.outputs,
            require_destinations_absent=True,
        )
        _write_output_temporaries(outputs, stage, output_root, expected_outputs)
        _write_marker_temporary(marker_publication, marker)

        # The marker is linked only after the complete output set and late
        # repository checks pass. Partial output publication therefore remains
        # unusable by downstream packet construction.
        _validate_output_records(stage, output_root, expected_outputs, "stage output")
        _commit_output_publications(outputs)
        _validate_published_records(stage, artifact_root, expected_outputs)
        precommit_check()
        _require_publication_namespaces(
            root_fd,
            artifact_root,
            [*outputs, marker_publication],
        )
        _commit_marker_last(
            marker_publication,
            root_fd,
            artifact_root,
            stage,
            expected_outputs,
            marker,
            [*outputs, marker_publication],
        )
        return expected_outputs, marker
    except (handoff.HandoffError, marker_protocol.StagePublicationMarkerError) as exc:
        raise WorkerError(str(exc)) from exc
    finally:
        _close_publications(outputs)
        if marker_publication is not None:
            _close_publications([marker_publication])
        _best_effort_close(root_fd)


def _captured_output_records(
    stage: ValidatedStage,
    captured_outputs: object,
) -> list[dict[str, object]]:
    if isinstance(captured_outputs, (str, bytes, bytearray)) or not isinstance(
        captured_outputs, Sequence
    ):
        raise WorkerError("captured outputs must be a sequence")
    rows = list(captured_outputs)
    if len(rows) != len(stage.outputs) or any(type(row) is not dict for row in rows):
        raise WorkerError("captured output inventory mismatch")
    return [dict(row) for row in rows if type(row) is dict]


def _prepare_output_publications(
    root_fd: int,
    contracts: Sequence[ArtifactContract],
    *,
    require_destinations_absent: bool,
) -> list[PreparedPublication]:
    prepared: list[PreparedPublication] = []
    try:
        for contract in contracts:
            relative = PurePosixPath(contract.path)
            directory_fd = _open_or_create_publication_parent(root_fd, relative.parent.parts)
            publication = PreparedPublication(
                directory_fd=directory_fd,
                parent_parts=tuple(relative.parent.parts),
                destination_name=relative.name,
            )
            prepared.append(publication)
            if require_destinations_absent:
                _require_publication_destination_absent(directory_fd, relative.name)
        return prepared
    except WorkerError:
        _close_publications(prepared)
        raise


def _prepare_marker_publication(
    root_fd: int,
    stage: ValidatedStage,
) -> PreparedPublication:
    relative = PurePosixPath(
        marker_protocol.stage_publication_marker_relative_path_v1(stage.ordinal, stage.stage_id)
    )
    directory_fd = _open_or_create_publication_parent(root_fd, relative.parent.parts)
    publication = PreparedPublication(
        directory_fd=directory_fd,
        parent_parts=tuple(relative.parent.parts),
        destination_name=relative.name,
    )
    return publication


def _write_output_temporaries(
    prepared: Sequence[PreparedPublication],
    stage: ValidatedStage,
    output_root: Path,
    expected_outputs: Sequence[Mapping[str, object]],
) -> None:
    observed: list[dict[str, object]] = []
    for publication, contract, expected in zip(
        prepared, stage.outputs, expected_outputs, strict=True
    ):
        raw = _read_output(contract, output_root, "validated stage output")
        record = handoff._artifact_record_from_bytes(contract.raw, contract.path, raw)
        if not handoff._canonical_values_equal(record, expected):
            raise WorkerError("stage output bytes differ from validated capture")
        observed.append(record)
        _write_publication_temporary(publication, raw, contract.maximum_bytes)
    handoff._require_aggregate_artifact_bound(observed)


def _write_marker_temporary(
    publication: PreparedPublication,
    marker: Mapping[str, object],
) -> None:
    raw = marker_protocol.canonical_json_bytes_v1(marker)
    _write_publication_temporary(publication, raw, marker_protocol.MAX_MARKER_BYTES)


def _validate_output_records(
    stage: ValidatedStage,
    root: Path,
    expected_outputs: Sequence[Mapping[str, object]],
    label: str,
) -> None:
    observed: list[dict[str, object]] = []
    for contract, expected in zip(stage.outputs, expected_outputs, strict=True):
        raw = _read_output(contract, root, label)
        record = handoff._artifact_record_from_bytes(contract.raw, contract.path, raw)
        if not handoff._canonical_values_equal(record, expected):
            raise WorkerError(f"{label} bytes differ from validated capture")
        observed.append(record)
    handoff._require_aggregate_artifact_bound(observed)


def _validate_published_records(
    stage: ValidatedStage,
    artifact_root: Path,
    expected_outputs: Sequence[Mapping[str, object]],
) -> None:
    _validate_output_records(stage, artifact_root, expected_outputs, "published artifact")


def _read_output(contract: ArtifactContract, root: Path, label: str) -> bytes:
    try:
        return handoff._stable_read_beneath(
            root,
            contract.path,
            f"{contract.role} {label}",
            contract.maximum_bytes,
        )
    except handoff.HandoffError as exc:
        raise WorkerError(str(exc)) from exc


def _commit_output_publications(prepared: Sequence[PreparedPublication]) -> None:
    for publication in prepared:
        _link_owned_temporary(publication)
        _fsync_directory(publication.directory_fd)


def _commit_marker_last(
    publication: PreparedPublication,
    root_fd: int,
    artifact_root: Path,
    stage: ValidatedStage,
    expected_outputs: Sequence[Mapping[str, object]],
    marker: Mapping[str, object],
    all_publications: Sequence[PreparedPublication],
) -> None:
    # Linking the marker is the visibility transition. Every subsequent
    # failure is reported as indeterminate because the exact marker may
    # already be visible or durable. A retry reconciles the complete marker
    # and output set rather than overwriting it.
    _link_owned_temporary(publication)
    try:
        _fsync_directory(publication.directory_fd)
        _require_publication_namespaces(root_fd, artifact_root, all_publications)
        _validate_complete_publication(stage, artifact_root, expected_outputs, marker)
    except (WorkerError, handoff.HandoffError, marker_protocol.StagePublicationMarkerError) as exc:
        raise PublicationCommitIndeterminate(
            "stage publication commit is indeterminate; reconcile the exact marker and outputs"
        ) from exc


def _reconcile_existing_publication(
    root_fd: int,
    artifact_root: Path,
    stage: ValidatedStage,
    expected_outputs: Sequence[Mapping[str, object]],
    marker: Mapping[str, object],
    publications: Sequence[PreparedPublication],
    precommit_check: Callable[[], None],
) -> None:
    try:
        _validate_complete_publication(stage, artifact_root, expected_outputs, marker)
        precommit_check()
        _require_publication_namespaces(root_fd, artifact_root, publications)
        _fsync_linked_publications(publications)
        _require_publication_namespaces(root_fd, artifact_root, publications)
        _validate_complete_publication(stage, artifact_root, expected_outputs, marker)
    except (WorkerError, handoff.HandoffError, marker_protocol.StagePublicationMarkerError) as exc:
        raise PublicationCommitIndeterminate(
            "existing stage publication could not be durably reconciled"
        ) from exc


def _link_owned_temporary(publication: PreparedPublication) -> None:
    descriptor = publication.temporary_fd
    if descriptor is None or publication.linked:
        raise WorkerError("published artifact temporary is not owned by this invocation")
    facts = os.fstat(descriptor)
    if not stat.S_ISREG(facts.st_mode) or facts.st_nlink != 0:
        raise WorkerError("published artifact temporary is not one unnamed regular file")
    _link_fd_noreplace(
        descriptor,
        publication.directory_fd,
        publication.destination_name,
    )
    publication.linked = True


def _fsync_linked_publications(publications: Sequence[PreparedPublication]) -> None:
    synced_directories: set[tuple[int, int]] = set()
    # O_NONBLOCK ensures a hostile FIFO leaf cannot block reconciliation
    # before the post-open regular-file check rejects it.
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    for publication in publications:
        descriptor: int | None = None
        try:
            descriptor = os.open(
                publication.destination_name,
                flags,
                dir_fd=publication.directory_fd,
            )
            facts = os.fstat(descriptor)
            if not stat.S_ISREG(facts.st_mode) or facts.st_nlink != 1:
                raise WorkerError("reconciled publication is not one linked regular file")
            os.fsync(descriptor)
        except WorkerError:
            raise
        except OSError as exc:
            raise WorkerError("reconciled publication file fsync failed") from exc
        finally:
            if descriptor is not None:
                _best_effort_close(descriptor)
        directory_facts = os.fstat(publication.directory_fd)
        directory_identity = (directory_facts.st_dev, directory_facts.st_ino)
        if directory_identity not in synced_directories:
            _fsync_directory(publication.directory_fd)
            synced_directories.add(directory_identity)


def _close_publications(prepared: Sequence[PreparedPublication]) -> None:
    for publication in prepared:
        if publication.temporary_fd is not None:
            _best_effort_close(publication.temporary_fd)
            publication.temporary_fd = None
        _best_effort_close(publication.directory_fd)


def _best_effort_close(descriptor: int) -> None:
    try:
        os.close(descriptor)
    except OSError:
        pass


def _open_publication_root(artifact_root: Path) -> int:
    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_DIRECTORY"):
        raise WorkerError("descriptor-safe artifact publication is unavailable")
    descriptor: int | None = None
    try:
        resolved = artifact_root.resolve(strict=True)
        before = artifact_root.lstat()
        descriptor = os.open(
            artifact_root,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0),
        )
        opened = os.fstat(descriptor)
    except OSError as exc:
        if descriptor is not None:
            os.close(descriptor)
        raise WorkerError("artifact publication root is unavailable") from exc
    if (
        resolved != artifact_root
        or not stat.S_ISDIR(before.st_mode)
        or _publication_file_identity(before) != _publication_file_identity(opened)
    ):
        os.close(descriptor)
        raise WorkerError("artifact publication root must be one real canonical directory")
    return descriptor


def _open_or_create_publication_parent(root_fd: int, parts: Sequence[str]) -> int:
    directory_fd = os.dup(root_fd)
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    try:
        for part in parts:
            if part in {"", ".", ".."}:
                raise WorkerError("published artifact parent is not canonical")
            try:
                os.mkdir(part, mode=0o700, dir_fd=directory_fd)
                _fsync_directory(directory_fd)
            except FileExistsError:
                pass
            next_fd = os.open(part, flags, dir_fd=directory_fd)
            if not stat.S_ISDIR(os.fstat(next_fd).st_mode):
                os.close(next_fd)
                raise WorkerError("published artifact parent is not a directory")
            os.close(directory_fd)
            directory_fd = next_fd
        return directory_fd
    except WorkerError:
        os.close(directory_fd)
        raise
    except OSError as exc:
        os.close(directory_fd)
        raise WorkerError("published artifact parent could not be opened") from exc


def _require_publication_destination_absent(directory_fd: int, name: str) -> None:
    try:
        os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    except OSError as exc:
        raise WorkerError("published artifact destination could not be inspected") from exc
    raise WorkerError("published artifact destination must begin absent")


def _publication_destination_exists(publication: PreparedPublication) -> bool:
    try:
        os.stat(
            publication.destination_name,
            dir_fd=publication.directory_fd,
            follow_symlinks=False,
        )
    except FileNotFoundError:
        return False
    except OSError as exc:
        raise WorkerError("publication marker destination could not be inspected") from exc
    return True


def _write_publication_temporary(
    publication: PreparedPublication,
    raw: bytes,
    maximum_bytes: int,
) -> None:
    if not 0 < len(raw) <= maximum_bytes:
        raise WorkerError("published artifact bytes exceed their governed bound")
    if publication.temporary_fd is not None:
        raise WorkerError("published artifact temporary was already prepared")
    if not hasattr(os, "O_TMPFILE"):
        raise WorkerError("unnamed descriptor publication is unavailable")
    descriptor: int | None = None
    try:
        descriptor = os.open(
            ".",
            os.O_RDWR | os.O_TMPFILE | getattr(os, "O_CLOEXEC", 0),
            0o600,
            dir_fd=publication.directory_fd,
        )
        created = os.fstat(descriptor)
        if not stat.S_ISREG(created.st_mode) or created.st_nlink != 0:
            raise WorkerError("published artifact temporary is not one unnamed regular file")
        _write_all(descriptor, raw)
        os.fchmod(descriptor, 0o400)
        os.fsync(descriptor)
        publication.temporary_fd = descriptor
        descriptor = None
    except WorkerError:
        raise
    except OSError as exc:
        if exc.errno in {errno.EISDIR, errno.EOPNOTSUPP, errno.EINVAL, errno.ENOSYS}:
            raise WorkerError("unnamed descriptor publication is unavailable") from exc
        raise WorkerError("published artifact temporary write failed") from exc
    finally:
        if descriptor is not None:
            _best_effort_close(descriptor)


def _write_all(descriptor: int, raw: bytes) -> None:
    offset = 0
    while offset < len(raw):
        written = os.write(descriptor, raw[offset : offset + 1024 * 1024])
        if written <= 0:
            raise WorkerError("published artifact temporary write made no progress")
        offset += written


def _link_fd_noreplace(file_fd: int, directory_fd: int, destination_name: str) -> None:
    try:
        libc = ctypes.CDLL(None, use_errno=True)
        linkat = libc.linkat
    except (OSError, AttributeError) as exc:
        raise WorkerError("exact-descriptor no-replace publication is unavailable") from exc
    linkat.argtypes = (
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
    )
    linkat.restype = ctypes.c_int
    result = linkat(
        file_fd,
        b"",
        directory_fd,
        os.fsencode(destination_name),
        0x1000,  # Linux AT_EMPTY_PATH.
    )
    if result == 0:
        return
    error = ctypes.get_errno()
    if error in {errno.EEXIST, errno.ENOTEMPTY}:
        raise WorkerError("published artifact destination must begin absent")
    if error in {errno.ENOSYS, errno.EINVAL, errno.EOPNOTSUPP, errno.EPERM}:
        raise WorkerError("exact-descriptor no-replace publication is unavailable")
    raise WorkerError("exact-descriptor no-replace publication failed")


def _require_publication_namespaces(
    root_fd: int,
    artifact_root: Path,
    publications: Sequence[PreparedPublication],
) -> None:
    try:
        path_facts = artifact_root.lstat()
        opened_root = os.fstat(root_fd)
        if artifact_root.resolve(strict=True) != artifact_root or _publication_file_identity(
            path_facts
        ) != _publication_file_identity(opened_root):
            raise WorkerError("artifact publication root namespace changed")
        for publication in publications:
            reopened = _open_existing_publication_parent(root_fd, publication.parent_parts)
            try:
                if _publication_file_identity(os.fstat(reopened)) != _publication_file_identity(
                    os.fstat(publication.directory_fd)
                ):
                    raise WorkerError("artifact publication parent namespace changed")
            finally:
                _best_effort_close(reopened)
    except WorkerError:
        raise
    except OSError as exc:
        raise WorkerError("artifact publication namespace could not be revalidated") from exc


def _open_existing_publication_parent(root_fd: int, parts: Sequence[str]) -> int:
    descriptor = os.dup(root_fd)
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    try:
        for part in parts:
            next_fd = os.open(part, flags, dir_fd=descriptor)
            _best_effort_close(descriptor)
            descriptor = next_fd
        return descriptor
    except OSError:
        _best_effort_close(descriptor)
        raise


def _validate_complete_publication(
    stage: ValidatedStage,
    artifact_root: Path,
    expected_outputs: Sequence[Mapping[str, object]],
    marker: Mapping[str, object],
) -> None:
    _validate_published_records(stage, artifact_root, expected_outputs)
    marker_relative = marker_protocol.stage_publication_marker_relative_path_v1(
        stage.ordinal, stage.stage_id
    )
    try:
        raw = handoff._stable_read_beneath(
            artifact_root,
            marker_relative,
            "stage publication marker",
            marker_protocol.MAX_MARKER_BYTES,
        )
        decoded = handoff.strict_json_loads(raw)
    except handoff.HandoffError as exc:
        raise WorkerError("stage publication marker could not be reconciled") from exc
    if type(decoded) is not dict:
        raise WorkerError("stage publication marker must be one object")
    marker_protocol.validate_stage_publication_marker_v1(
        decoded,
        expected_handoff_id=stage.handoff_id,
        expected_execution_packet_id=stage.execution_packet_id,
        expected_task_id=stage.task_id,
        expected_stage_id=stage.stage_id,
        expected_ordinal=stage.ordinal,
        expected_outputs=expected_outputs,
    )
    if raw != marker_protocol.canonical_json_bytes_v1(marker):
        raise WorkerError("stage publication marker differs from this exact capture")


def _fsync_directory(directory_fd: int) -> None:
    try:
        os.fsync(directory_fd)
    except OSError as exc:
        raise WorkerError("published artifact directory fsync failed") from exc


def _publication_file_identity(value: os.stat_result) -> tuple[int, int, int]:
    return (value.st_dev, value.st_ino, value.st_mode)
