"""Bounded canonical stdout protocol for V6 build artifacts."""

from __future__ import annotations

import base64
import hashlib
import os
import re
from dataclasses import dataclass
from pathlib import Path

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools.zrpf_v6_identity_executor_types import (
    BuildKind,
    BuildRequest,
    BuildResult,
    ExecutionError,
)

RUNNER_OUTPUT_PREFIX = b"ZRPF_BUILD_RESULT_V2"
RUNNER_OUTPUT_SUFFIX = b"ZRPF_END\n"
MAX_BUILD_OUTPUT_BYTES = 2 * ((planner.MAX_HOST_BINARY_BYTES + 2) // 3 * 4) + 4_096


@dataclass(frozen=True)
class RunnerPayload:
    result: BuildResult
    artifact: bytes
    companion: bytes | None


def parse_runner_payload(raw: bytes, request: BuildRequest) -> RunnerPayload:
    """Decode one exact, bounded, canonical build-result frame."""

    header_end = raw.find(b"\n")
    if header_end <= 0 or header_end > 1_024:
        raise ExecutionError("container runner header framing rejected")
    fields = raw[:header_end].split(b" ")
    if len(fields) != 9 or fields[0] != RUNNER_OUTPUT_PREFIX:
        raise ExecutionError("container runner header framing rejected")
    header = _parse_header(fields, request.kind)
    cursor = header_end + 1
    artifact_encoded, cursor = _take_exact_line(
        raw,
        cursor,
        header.artifact_base64_bytes,
    )
    companion_encoded, cursor = _take_exact_line(
        raw,
        cursor,
        header.companion_base64_bytes,
    )
    if raw[cursor:] != RUNNER_OUTPUT_SUFFIX:
        raise ExecutionError("container runner trailing framing rejected")
    artifact = _decode_canonical_base64(artifact_encoded, "artifact")
    _require_artifact_binding(header, artifact)
    companion = _validate_companion_payload(request, header, companion_encoded)
    result = parse_runner_result(
        (f"{header.artifact_bytes} {header.artifact_sha256} {header.image_id}\n").encode("ascii"),
        request.kind,
    )
    return RunnerPayload(result, artifact, companion)


def materialize_runner_payload(
    request: BuildRequest,
    payload: RunnerPayload,
) -> None:
    """Write a verified frame into the fresh host output directory."""

    require_output_name(request.artifact_file)
    write_new_file(
        request.output_directory / request.artifact_file,
        payload.artifact,
        0o444 if request.kind is BuildKind.GUEST else 0o555,
    )
    if request.companion_artifact_file is not None:
        require_output_name(request.companion_artifact_file)
        if payload.companion is None:
            raise ExecutionError("container runner omitted the companion payload")
        write_new_file(
            request.output_directory / request.companion_artifact_file,
            payload.companion,
            0o555,
        )
    elif payload.companion is not None:
        raise ExecutionError("container runner returned an unexpected companion payload")
    _sync_directory(request.output_directory)


def parse_runner_result(raw: bytes, kind: BuildKind) -> BuildResult:
    pattern = rb"([1-9][0-9]{0,19}) ([0-9a-f]{64}) ([0-9a-f]{64}|-)\n"
    match = re.fullmatch(pattern, raw)
    if match is None:
        raise ExecutionError("container runner result framing rejected")
    size = int(match.group(1))
    image = match.group(3).decode("ascii")
    if kind is BuildKind.GUEST and image == "-":
        raise ExecutionError("guest runner omitted image ID")
    if kind is BuildKind.HOST_VERIFIER and image != "-":
        raise ExecutionError("host runner returned an image ID")
    return BuildResult(
        artifact_bytes=size,
        artifact_sha256=match.group(2).decode("ascii"),
        image_id=None if image == "-" else image,
    )


def write_new_file(path: Path, raw: bytes, mode: int) -> None:
    """Create, write, chmod, and synchronize one exact new regular file."""

    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_EXCL
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    try:
        descriptor = os.open(path, flags, 0o600)
    except OSError as exc:
        raise ExecutionError("runner output creation failed") from exc
    try:
        view = memoryview(raw)
        offset = 0
        while offset < len(view):
            written = os.write(descriptor, view[offset:])
            if written <= 0:
                raise ExecutionError("runner output write failed")
            offset += written
        os.fchmod(descriptor, mode)
        os.fsync(descriptor)
    except BaseException:
        path.unlink(missing_ok=True)
        raise
    finally:
        os.close(descriptor)


def require_output_name(name: str) -> None:
    if (
        not name
        or len(name) > 128
        or name in {".", ".."}
        or "/" in name
        or "\\" in name
        or any(ord(character) < 33 or ord(character) == 127 for character in name)
    ):
        raise ExecutionError("runner output filename is noncanonical")


@dataclass(frozen=True)
class _PayloadHeader:
    kind: str
    artifact_bytes: int
    artifact_sha256: str
    image_id: str
    artifact_base64_bytes: int
    companion_bytes: int
    companion_sha256: str
    companion_base64_bytes: int


def _parse_header(fields: list[bytes], kind: BuildKind) -> _PayloadHeader:
    try:
        parsed = _PayloadHeader(
            kind=fields[1].decode("ascii", errors="strict"),
            artifact_bytes=_parse_bounded_decimal(
                fields[2], _maximum_artifact_bytes(kind), "artifact bytes"
            ),
            artifact_sha256=_parse_sha256(fields[3], "artifact SHA-256"),
            image_id=fields[4].decode("ascii", errors="strict"),
            artifact_base64_bytes=_parse_bounded_decimal(
                fields[5],
                _base64_size(_maximum_artifact_bytes(kind)),
                "artifact base64 bytes",
            ),
            companion_bytes=_parse_bounded_decimal(
                fields[6],
                planner.MAX_HOST_BINARY_BYTES,
                "companion bytes",
                allow_zero=True,
            ),
            companion_sha256=fields[7].decode("ascii", errors="strict"),
            companion_base64_bytes=_parse_bounded_decimal(
                fields[8],
                _base64_size(planner.MAX_HOST_BINARY_BYTES),
                "companion base64 bytes",
                allow_zero=True,
            ),
        )
    except UnicodeDecodeError as exc:
        raise ExecutionError("container runner header is not ASCII") from exc
    if parsed.kind != kind.value:
        raise ExecutionError("container runner build kind mismatch")
    return parsed


def _require_artifact_binding(header: _PayloadHeader, artifact: bytes) -> None:
    if (
        len(artifact) != header.artifact_bytes
        or _base64_size(header.artifact_bytes) != header.artifact_base64_bytes
        or hashlib.sha256(artifact).hexdigest() != header.artifact_sha256
    ):
        raise ExecutionError("container runner artifact binding rejected")


def _validate_companion_payload(
    request: BuildRequest,
    header: _PayloadHeader,
    encoded: bytes,
) -> bytes | None:
    if request.companion_artifact_file is None:
        if (
            header.companion_bytes != 0
            or header.companion_sha256 != "-"
            or header.companion_base64_bytes != 0
            or encoded
        ):
            raise ExecutionError("container runner emitted an unexpected companion")
        return None
    if (
        header.companion_bytes == 0
        or re.fullmatch(r"[0-9a-f]{64}", header.companion_sha256) is None
        or header.companion_base64_bytes != _base64_size(header.companion_bytes)
    ):
        raise ExecutionError("container runner companion binding is malformed")
    companion = _decode_canonical_base64(encoded, "companion")
    if (
        len(companion) != header.companion_bytes
        or hashlib.sha256(companion).hexdigest() != header.companion_sha256
    ):
        raise ExecutionError("container runner companion binding rejected")
    return companion


def _parse_bounded_decimal(
    raw: bytes,
    maximum: int,
    label: str,
    *,
    allow_zero: bool = False,
) -> int:
    pattern = rb"0|[1-9][0-9]{0,19}" if allow_zero else rb"[1-9][0-9]{0,19}"
    if re.fullmatch(pattern, raw) is None:
        raise ExecutionError(f"container runner {label} is malformed")
    value = int(raw)
    if value > maximum:
        raise ExecutionError(f"container runner {label} exceeds its bound")
    return value


def _parse_sha256(raw: bytes, label: str) -> str:
    if re.fullmatch(rb"[0-9a-f]{64}", raw) is None:
        raise ExecutionError(f"container runner {label} is malformed")
    return raw.decode("ascii")


def _take_exact_line(raw: bytes, cursor: int, length: int) -> tuple[bytes, int]:
    end = cursor + length
    if end >= len(raw) or raw[end : end + 1] != b"\n":
        raise ExecutionError("container runner payload framing rejected")
    return raw[cursor:end], end + 1


def _decode_canonical_base64(raw: bytes, label: str) -> bytes:
    try:
        decoded = base64.b64decode(raw, validate=True)
    except (ValueError, TypeError) as exc:
        raise ExecutionError(f"container runner {label} base64 rejected") from exc
    if base64.b64encode(decoded) != raw:
        raise ExecutionError(f"container runner {label} base64 is noncanonical")
    return decoded


def _maximum_artifact_bytes(kind: BuildKind) -> int:
    if kind is BuildKind.GUEST:
        return planner.MAX_PROGRAM_BINARY_BYTES
    if kind is BuildKind.HOST_VERIFIER:
        return planner.MAX_HOST_BINARY_BYTES
    raise ExecutionError("unknown build kind")


def _base64_size(raw_bytes: int) -> int:
    return (raw_bytes + 2) // 3 * 4


def _sync_directory(directory: Path) -> None:
    try:
        descriptor = os.open(
            directory,
            os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    except OSError as exc:
        raise ExecutionError("runner output directory synchronization failed") from exc
