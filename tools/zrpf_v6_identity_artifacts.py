"""Artifact collection and exact repinning for the V6 identity executor."""

from __future__ import annotations

import hashlib
import os
import re
from pathlib import Path
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools.zrpf_v6_identity_executor_types import (
    BuildRequest,
    BuildResult,
    ExecutionError,
)
from tools.zrpf_v6_identity_source_snapshot import (
    MAX_SOURCE_FILE_BYTES,
    V2_CANDIDATE_PATHS,
    read_bounded_regular,
    replace_regular,
    resolve_snapshot_path,
)


def collect_guest_outputs(
    request: BuildRequest,
    result: BuildResult,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    """Re-read and bind one guest artifact to the runner observation."""

    raw = read_bounded_regular(
        request.output_directory / request.artifact_file,
        f"{request.pass_id} program artifact",
        planner.MAX_PROGRAM_BINARY_BYTES,
    )
    if not raw.startswith(bytes.fromhex("52304246")):
        raise ExecutionError(f"{request.pass_id} artifact is not an R0BF program")
    digest = hashlib.sha256(raw).hexdigest()
    _require_runner_binding(result, len(raw), digest, require_image=True)
    image_id = result.image_id
    if image_id is None or re.fullmatch(r"[0-9a-f]{64}", image_id) is None:
        raise ExecutionError("runner image ID is not exact lowercase hexadecimal")
    expected_names = {request.artifact_file}
    companion = _collect_companion(request, expected_names)
    _require_output_inventory(request.output_directory, expected_names)
    image_raw = bytes.fromhex(image_id)
    return (
        {
            "artifact_file": request.artifact_file,
            "program_binary_bytes": len(raw),
            "program_binary_sha256": digest,
            "image_id": image_id,
            "image_id_words": [
                int.from_bytes(image_raw[index : index + 4], "little")
                for index in range(0, 32, 4)
            ],
        },
        companion,
    )


def collect_host_output(
    request: BuildRequest,
    result: BuildResult,
) -> dict[str, Any]:
    """Re-read and bind the host verifier binary to the runner observation."""

    raw = read_bounded_regular(
        request.output_directory / request.artifact_file,
        "host verifier binary",
        planner.MAX_HOST_BINARY_BYTES,
    )
    digest = hashlib.sha256(raw).hexdigest()
    _require_runner_binding(result, len(raw), digest, require_image=False)
    _require_output_inventory(request.output_directory, {request.artifact_file})
    return {
        "binary_file": request.artifact_file,
        "binary_bytes": len(raw),
        "binary_sha256": digest,
    }


def apply_stage_repins(
    snapshot_root: Path,
    spec: planner.StageSpec,
    row: dict[str, Any],
) -> None:
    """Apply exactly the repins declared by one governed stage."""

    observed = row["repins"]
    if len(observed) != len(spec.repins):
        raise ExecutionError("stage repin inventory mismatch")
    for expected, candidate in zip(spec.repins, observed, strict=True):
        if any(
            candidate[field] != getattr(expected, field)
            for field in ("path", "symbol", "value_kind", "visibility")
        ):
            raise ExecutionError("undeclared repin rejected")
        repin_rust_constant(
            resolve_snapshot_path(snapshot_root, expected.path),
            expected.symbol,
            expected.value_kind,
            candidate["value"],
        )


def repin_rust_constant(
    path: Path,
    symbol: str,
    value_kind: str,
    value: list[int],
) -> None:
    """Replace one exact Rust array constant and reject ambiguous declarations."""

    if re.fullmatch(r"[A-Z][A-Z0-9_]*", symbol) is None:
        raise ExecutionError("repin symbol is invalid")
    type_name, width, maximum = _repin_shape(value_kind)
    if (
        type(value) is not list
        or len(value) != width
        or any(type(item) is not int or not 0 <= item <= maximum for item in value)
    ):
        raise ExecutionError("repin value shape is invalid")
    raw = read_bounded_regular(path, f"repin source {symbol}", MAX_SOURCE_FILE_BYTES)
    try:
        source = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise ExecutionError("repin source is not UTF-8") from exc
    pattern = re.compile(
        rf"^pub const {re.escape(symbol)}: \[{type_name}; {width}\] = \[[^\]]*\];$",
        re.MULTILINE,
    )
    matches = list(pattern.finditer(source))
    if len(matches) != 1:
        raise ExecutionError(f"repin symbol {symbol} must occur exactly once")
    values = "\n".join(f"    {item}," for item in value)
    declaration = f"pub const {symbol}: [{type_name}; {width}] = [\n{values}\n];"
    updated = source[: matches[0].start()] + declaration + source[matches[0].end() :]
    replace_regular(path, updated.encode("utf-8"))


def write_candidate_document(
    snapshot_root: Path,
    relative: str,
    document: dict[str, Any],
) -> None:
    """Replace only one governed V2 candidate document."""

    if relative not in V2_CANDIDATE_PATHS:
        raise ExecutionError("candidate document path is not governed")
    replace_regular(
        resolve_snapshot_path(snapshot_root, relative),
        planner.canonical_bytes(document),
    )


def _collect_companion(
    request: BuildRequest,
    expected_names: set[str],
) -> dict[str, Any] | None:
    if request.companion_artifact_file is None:
        return None
    expected_names.add(request.companion_artifact_file)
    raw = read_bounded_regular(
        request.output_directory / request.companion_artifact_file,
        f"{request.pass_id} companion host binary",
        planner.MAX_HOST_BINARY_BYTES,
    )
    return {
        "binary_file": request.companion_artifact_file,
        "binary_bytes": len(raw),
        "binary_sha256": hashlib.sha256(raw).hexdigest(),
    }


def _require_runner_binding(
    result: BuildResult,
    size: int,
    digest: str,
    *,
    require_image: bool,
) -> None:
    if type(result.artifact_bytes) is not int or result.artifact_bytes != size:
        raise ExecutionError("runner artifact byte length mismatch")
    if result.artifact_sha256 != digest:
        raise ExecutionError("runner artifact SHA-256 mismatch")
    if require_image and result.image_id is None:
        raise ExecutionError("runner omitted program image ID")
    if not require_image and result.image_id is not None:
        raise ExecutionError("host verifier runner returned an unexpected image ID")


def _repin_shape(value_kind: str) -> tuple[str, int, int]:
    if value_kind == "image_id_words_le":
        return "u32", 8, 0xFFFFFFFF
    if value_kind in {"sha256_bytes", "source_closure_root_bytes"}:
        return "u8", 32, 0xFF
    raise ExecutionError("unsupported repin value kind")


def _require_output_inventory(directory: Path, expected: set[str]) -> None:
    try:
        names = {entry.name for entry in os.scandir(directory)}
    except OSError as exc:
        raise ExecutionError("build output directory is unavailable") from exc
    if names != expected:
        raise ExecutionError("build output inventory mismatch")
