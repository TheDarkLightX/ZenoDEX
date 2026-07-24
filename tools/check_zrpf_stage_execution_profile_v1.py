#!/usr/bin/env python3
"""Validate one authority-neutral ZRPF execution profile against exact bytes."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import stat
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn, Sequence

SCHEMA = "zenodex/zrpf_risc0_stage_execution_profile/v1"
STATUS = "exact_execution_observed_without_proof_or_accelerator_authority"
PROOF_PROFILE = "risc0_succinct_poseidon2_resolve_3_0_5_v1"
PROFILE_ID_DOMAIN = b"zenodex/zrpf-risc0-stage-execution-profile-id/v1\0"
ZERO_SHA256 = "0" * 64
MAX_PROFILE_BYTES = 2 * 1024 * 1024
MAX_PROGRAM_BYTES = 64 * 1024 * 1024
MAX_GUEST_INPUT_BYTES = 16 * 1024 * 1024
MAX_ASSUMPTION_BYTES = 16 * 1024 * 1024
MAX_R0VM_BYTES = 512 * 1024 * 1024
MAX_SEGMENTS = 65_536
SEGMENT_LIMIT_PO2 = 20
MIN_SEGMENT_PO2 = 13
COMPUTE_PROFILES = {
    "risc0_ipc_cpu_v1",
    "risc0_ipc_cuda_single_visible_device_build_request_v1",
}
NON_CLAIMS = [
    "execution profiling generates no RISC0 receipt or proof",
    "execution profiling does not establish CUDA or other accelerator execution",
    "the observed r0vm bytes have no source-to-binary or release authority",
    "the profile grants no settlement or ledger authority",
    "the profile grants no production authority",
]
ROOT_FIELDS = [
    "schema",
    "status",
    "profile_record_id",
    "stage_id",
    "proof_profile_id",
    "prover_compute_profile_id",
    "program",
    "r0vm",
    "guest_input",
    "assumptions",
    "expected_journal",
    "observed_journal",
    "receipt_claim_sha256",
    "segment_limit_po2",
    "segments",
    "segment_count",
    "total_user_cycles",
    "total_padded_cycle_capacity",
    "exit_system",
    "exit_user",
    "duration_milliseconds",
    "authority",
    "non_claims",
]
ARTIFACT_FIELDS = ["sha256", "size_bytes"]
PROGRAM_FIELDS = ["artifact", "image_id"]
ASSUMPTION_FIELDS = [
    "ordinal",
    "receipt",
    "expected_image_id",
    "journal_sha256",
    "journal_bytes",
]
SEGMENT_FIELDS = ["ordinal", "po2", "user_cycles", "padded_cycle_capacity"]
AUTHORITY_FIELDS = [
    "proof_generated",
    "accelerator_execution_verified",
    "proof_authority",
    "release_authority",
    "settlement_authority",
    "production_authority",
]


class ProfileCheckError(ValueError):
    """Stable fail-closed profile rejection."""


@dataclass(frozen=True, slots=True)
class ArtifactIdentity:
    sha256: str
    size_bytes: int

    def record(self) -> dict[str, object]:
        return {"sha256": self.sha256, "size_bytes": self.size_bytes}


def check_profile(
    profile_path: Path,
    program_path: Path,
    guest_input_path: Path,
    assumption_paths: Sequence[Path],
    r0vm_path: Path,
    *,
    expected_stage: str,
    expected_compute_profile: str,
) -> dict[str, object]:
    raw = _stable_read(profile_path, "execution profile", MAX_PROFILE_BYTES)
    document = _strict_json(raw)
    _validate_document(document, raw, expected_stage, expected_compute_profile)
    program = _object(document["program"], "program")
    _require_artifact(
        program["artifact"],
        _stable_identity(program_path, "program", MAX_PROGRAM_BYTES, executable=False),
        "program",
    )
    _require_artifact(
        document["guest_input"],
        _stable_identity(
            guest_input_path, "guest input", MAX_GUEST_INPUT_BYTES, executable=False
        ),
        "guest input",
    )
    _require_artifact(
        document["r0vm"],
        _stable_identity(r0vm_path, "r0vm", MAX_R0VM_BYTES, executable=True),
        "r0vm",
    )
    assumptions = _list(document["assumptions"], "assumptions")
    if len(assumptions) != len(assumption_paths):
        raise ProfileCheckError("assumption artifact count mismatch")
    for ordinal, (row, path) in enumerate(zip(assumptions, assumption_paths, strict=True)):
        assumption = _object(row, f"assumption {ordinal}")
        _require_artifact(
            assumption["receipt"],
            _stable_identity(path, f"assumption {ordinal}", MAX_ASSUMPTION_BYTES, executable=False),
            f"assumption {ordinal}",
        )
    return document


def _validate_document(
    document: dict[str, object],
    raw: bytes,
    expected_stage: str,
    expected_compute_profile: str,
) -> None:
    _require_ordered_fields(document, ROOT_FIELDS, "execution profile")
    if _canonical_bytes(document) != raw:
        raise ProfileCheckError("execution profile JSON is not canonical")
    if document["schema"] != SCHEMA or document["status"] != STATUS:
        raise ProfileCheckError("execution profile schema or status mismatch")
    _require_identifier(document["stage_id"], "stage ID")
    if document["stage_id"] != expected_stage:
        raise ProfileCheckError("execution profile stage mismatch")
    if document["proof_profile_id"] != PROOF_PROFILE:
        raise ProfileCheckError("execution profile proof profile mismatch")
    if (
        expected_compute_profile not in COMPUTE_PROFILES
        or document["prover_compute_profile_id"] != expected_compute_profile
    ):
        raise ProfileCheckError("execution profile compute profile mismatch")
    _validate_program(document["program"])
    for label in ("r0vm", "guest_input", "expected_journal", "observed_journal"):
        _validate_artifact(document[label], label)
    if document["expected_journal"] != document["observed_journal"]:
        raise ProfileCheckError("expected and observed journals differ")
    _require_sha256(document["receipt_claim_sha256"], "receipt claim", nonzero=True)
    if _exact_int(document["segment_limit_po2"], "segment limit") != SEGMENT_LIMIT_PO2:
        raise ProfileCheckError("segment limit policy mismatch")
    _validate_assumptions(document["assumptions"])
    segment_count, total_user, total_padded = _validate_segments(document["segments"])
    if _exact_int(document["segment_count"], "segment count") != segment_count:
        raise ProfileCheckError("segment count mismatch")
    if _exact_int(document["total_user_cycles"], "total user cycles") != total_user:
        raise ProfileCheckError("total user cycles mismatch")
    if (
        _exact_int(document["total_padded_cycle_capacity"], "total padded cycles")
        != total_padded
    ):
        raise ProfileCheckError("total padded cycle capacity mismatch")
    if (
        _exact_int(document["exit_system"], "exit system") != 0
        or _exact_int(document["exit_user"], "exit user") != 0
    ):
        raise ProfileCheckError("execution profile exit status is not successful")
    _nonnegative_int(document["duration_milliseconds"], "duration")
    _validate_authority(document["authority"])
    if document["non_claims"] != NON_CLAIMS:
        raise ProfileCheckError("execution profile non-claims mismatch")
    _require_sha256(document["profile_record_id"], "profile record ID", nonzero=True)
    if document["profile_record_id"] != _derive_record_id(document):
        raise ProfileCheckError("execution profile record ID mismatch")


def _validate_program(value: object) -> None:
    row = _object(value, "program")
    _require_ordered_fields(row, PROGRAM_FIELDS, "program")
    _validate_artifact(row["artifact"], "program artifact")
    _require_sha256(row["image_id"], "program image ID", nonzero=True)


def _validate_assumptions(value: object) -> None:
    rows = _list(value, "assumptions")
    if len(rows) > MAX_SEGMENTS:
        raise ProfileCheckError("assumption set exceeds bound")
    for ordinal, value in enumerate(rows):
        row = _object(value, f"assumption {ordinal}")
        _require_ordered_fields(row, ASSUMPTION_FIELDS, f"assumption {ordinal}")
        if _exact_int(row["ordinal"], "assumption ordinal") != ordinal:
            raise ProfileCheckError("assumption ordering mismatch")
        _validate_artifact(row["receipt"], f"assumption {ordinal} receipt")
        _require_sha256(row["expected_image_id"], "assumption image ID", nonzero=True)
        _require_sha256(row["journal_sha256"], "assumption journal", nonzero=False)
        if _positive_int(row["journal_bytes"], "assumption journal bytes") > 16 * 1024 * 1024:
            raise ProfileCheckError("assumption journal exceeds bound")


def _validate_segments(value: object) -> tuple[int, int, int]:
    rows = _list(value, "segments")
    if not rows or len(rows) > MAX_SEGMENTS:
        raise ProfileCheckError("segment set is empty or oversized")
    total_user = 0
    total_padded = 0
    for ordinal, value in enumerate(rows):
        row = _object(value, f"segment {ordinal}")
        _require_ordered_fields(row, SEGMENT_FIELDS, f"segment {ordinal}")
        if _exact_int(row["ordinal"], "segment ordinal") != ordinal:
            raise ProfileCheckError("segment ordering mismatch")
        po2 = _exact_int(row["po2"], "segment po2")
        if not MIN_SEGMENT_PO2 <= po2 <= SEGMENT_LIMIT_PO2:
            raise ProfileCheckError("segment po2 is outside the governed range")
        capacity = 1 << po2
        user_cycles = _nonnegative_int(row["user_cycles"], "segment user cycles")
        if (
            _exact_int(row["padded_cycle_capacity"], "segment padded capacity")
            != capacity
            or user_cycles > capacity
        ):
            raise ProfileCheckError("segment row is inconsistent")
        total_user = _checked_u64_add(total_user, user_cycles, "total user cycles")
        total_padded = _checked_u64_add(total_padded, capacity, "total padded cycles")
    return len(rows), total_user, total_padded


def _validate_authority(value: object) -> None:
    row = _object(value, "authority")
    _require_ordered_fields(row, AUTHORITY_FIELDS, "authority")
    if any(type(row[field]) is not bool or row[field] for field in AUTHORITY_FIELDS):
        raise ProfileCheckError("execution profile authority must remain false")


def _validate_artifact(value: object, label: str) -> None:
    row = _object(value, label)
    _require_ordered_fields(row, ARTIFACT_FIELDS, label)
    _require_sha256(row["sha256"], f"{label} SHA-256", nonzero=False)
    _positive_int(row["size_bytes"], f"{label} size")


def _require_artifact(value: object, expected: ArtifactIdentity, label: str) -> None:
    _validate_artifact(value, label)
    if value != expected.record():
        raise ProfileCheckError(f"{label} bytes differ from execution profile")


def _derive_record_id(document: dict[str, object]) -> str:
    candidate = copy.deepcopy(document)
    candidate["profile_record_id"] = ZERO_SHA256
    payload = _canonical_bytes(candidate)
    framed = PROFILE_ID_DOMAIN + len(payload).to_bytes(8, "big") + payload
    return hashlib.sha256(framed).hexdigest()


def _strict_json(raw: bytes) -> dict[str, object]:
    try:
        text = raw.decode("utf-8", errors="strict")
        value = json.loads(
            text,
            object_pairs_hook=_pairs_without_duplicates,
            parse_float=_reject_noninteger,
            parse_constant=_reject_noninteger,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ProfileCheckError) as exc:
        raise ProfileCheckError("execution profile JSON decode failed") from exc
    return _object(value, "execution profile")


def _pairs_without_duplicates(pairs: list[tuple[str, object]]) -> dict[str, object]:
    value: dict[str, object] = {}
    for key, item in pairs:
        if key in value:
            raise ProfileCheckError("duplicate JSON object key")
        value[key] = item
    return value


def _reject_noninteger(value: str) -> NoReturn:
    raise ProfileCheckError(f"non-integer JSON number rejected: {value}")


def _canonical_bytes(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def _stable_read(path: Path, label: str, maximum: int) -> bytes:
    identity, raw = _stable_file(path, label, maximum, executable=False, retain=True)
    if identity.size_bytes != len(raw):
        raise ProfileCheckError(f"{label} size changed while read")
    return raw


def _stable_identity(path: Path, label: str, maximum: int, *, executable: bool) -> ArtifactIdentity:
    identity, _ = _stable_file(path, label, maximum, executable=executable, retain=False)
    return identity


def _stable_file(
    path: Path,
    label: str,
    maximum: int,
    *,
    executable: bool,
    retain: bool,
) -> tuple[ArtifactIdentity, bytes]:
    try:
        before = path.lstat()
    except OSError as exc:
        raise ProfileCheckError(f"{label} metadata failed") from exc
    if (
        not stat.S_ISREG(before.st_mode)
        or stat.S_ISLNK(before.st_mode)
        or not 0 < before.st_size <= maximum
        or (executable and before.st_mode & 0o111 == 0)
    ):
        raise ProfileCheckError(f"{label} is not a bounded regular file")
    digest = hashlib.sha256()
    chunks: list[bytes] = []
    total = 0
    try:
        with path.open("rb") as handle:
            opened = os.fstat(handle.fileno())
            if not _same_file_version(before, opened):
                raise ProfileCheckError(f"{label} path changed while opened")
            while True:
                chunk = handle.read(min(1024 * 1024, maximum - total + 1))
                if not chunk:
                    break
                total += len(chunk)
                if total > maximum:
                    raise ProfileCheckError(f"{label} exceeds byte bound")
                digest.update(chunk)
                if retain:
                    chunks.append(chunk)
            after = os.fstat(handle.fileno())
    except OSError as exc:
        raise ProfileCheckError(f"{label} read failed") from exc
    if not _same_file_version(opened, after) or total != opened.st_size:
        raise ProfileCheckError(f"{label} changed while read")
    return ArtifactIdentity(digest.hexdigest(), total), b"".join(chunks)


def _same_file_version(left: os.stat_result, right: os.stat_result) -> bool:
    return (
        left.st_dev,
        left.st_ino,
        left.st_mode,
        left.st_size,
        left.st_mtime_ns,
        left.st_ctime_ns,
    ) == (
        right.st_dev,
        right.st_ino,
        right.st_mode,
        right.st_size,
        right.st_mtime_ns,
        right.st_ctime_ns,
    )


def _require_ordered_fields(row: dict[str, object], fields: list[str], label: str) -> None:
    if list(row) != fields:
        raise ProfileCheckError(f"{label} field order or inventory mismatch")


def _object(value: object, label: str) -> dict[str, object]:
    if type(value) is not dict:
        raise ProfileCheckError(f"{label} must be an object")
    return value


def _list(value: object, label: str) -> list[object]:
    if type(value) is not list:
        raise ProfileCheckError(f"{label} must be a list")
    return value


def _require_identifier(value: object, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"[a-z0-9_./-]{1,128}", value) is None:
        raise ProfileCheckError(f"{label} is not a canonical identifier")
    return value


def _require_sha256(value: object, label: str, *, nonzero: bool) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ProfileCheckError(f"{label} is not lowercase hexadecimal")
    if nonzero and value == ZERO_SHA256:
        raise ProfileCheckError(f"{label} is zero")
    return value


def _exact_int(value: object, label: str) -> int:
    if type(value) is not int:
        raise ProfileCheckError(f"{label} must be an integer")
    return value


def _positive_int(value: object, label: str) -> int:
    result = _exact_int(value, label)
    if not 0 < result <= (1 << 64) - 1:
        raise ProfileCheckError(f"{label} is outside its positive u64 bound")
    return result


def _nonnegative_int(value: object, label: str) -> int:
    result = _exact_int(value, label)
    if not 0 <= result <= (1 << 64) - 1:
        raise ProfileCheckError(f"{label} is outside its nonnegative u64 bound")
    return result


def _checked_u64_add(left: int, right: int, label: str) -> int:
    result = left + right
    if result > (1 << 64) - 1:
        raise ProfileCheckError(f"{label} overflows u64")
    return result


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", type=Path, required=True)
    parser.add_argument("--program", type=Path, required=True)
    parser.add_argument("--guest-input", type=Path, required=True)
    parser.add_argument("--assumption", type=Path, action="append", default=[])
    parser.add_argument("--r0vm", type=Path, required=True)
    parser.add_argument("--expected-stage", required=True)
    parser.add_argument("--expected-compute-profile", required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        check_profile(
            args.profile,
            args.program,
            args.guest_input,
            args.assumption,
            args.r0vm,
            expected_stage=args.expected_stage,
            expected_compute_profile=args.expected_compute_profile,
        )
    except ProfileCheckError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
