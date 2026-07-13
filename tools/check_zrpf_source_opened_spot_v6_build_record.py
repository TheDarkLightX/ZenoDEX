#!/usr/bin/env python3
"""Fail-closed checker for the source-opened Spot V6 build record.

The record captures one same-host build and the exact policy-pinned guest
dependency chain. Optional artifact verification rechecks the four guest ELFs.
It does not establish proof generation, reproducibility, or release authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
from datetime import date
from pathlib import Path, PurePosixPath
from typing import Any, NoReturn

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECORD = (
    REPO_ROOT
    / "docs/research/ZRPF_SOURCE_OPENED_SPOT_V6_BUILD_RECORD_20260712.json"
)
RECORD_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_build_record/v1"
REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_build_record_check/v1"
MAX_RECORD_BYTES = 256 * 1024
MAX_ARTIFACT_BYTES = 64 * 1024 * 1024

SOURCE_SPOT_IMAGE_ID = "1275ef413f6513e7671bce019d22fbdcf10bffe1b71dcf68731a056e710a7403"
ADAPTER_IMAGE_ID = "4caf9aa0a1ed0e1f08d43549bafd0f25a2e75125862cd7e31edbbfa520cd8760"
LEAF_IMAGE_ID = "f2dcf75133ff7d0a909e47cb265ea46fc4b24edc80a485667089c22bccbcc89b"
L1_IMAGE_ID = "b1235676d99422acebac73dd016fa40819cc013919870a3621f678b54377e9fa"
L2_IMAGE_ID = "6fc6972b7ed5e1410f12ba68f627deafebfe96ba080415e7e02ac137e9f5f2ef"
SETTLEMENT_IMAGE_ID = "10e5106603ce32b9cb543a54e74e935eb127433f3cf268b989e42ed5a540f783"

PROGRAM_SPECS = (
    (
        "spot_value_leaf_v6",
        "zenodex-zrpf-risc0-spot-value-leaf-v6",
        "spot_value_leaf_v6.elf",
        LEAF_IMAGE_ID,
        "adapter_v3",
        ADAPTER_IMAGE_ID,
    ),
    (
        "spot_value_aggregate_l1_v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-l1-v6",
        "spot_value_aggregate_l1_v6.elf",
        L1_IMAGE_ID,
        "spot_value_leaf_v6",
        LEAF_IMAGE_ID,
    ),
    (
        "spot_value_aggregate_l2_v6",
        "zenodex-zrpf-risc0-spot-value-aggregate-l2-v6",
        "spot_value_aggregate_l2_v6.elf",
        L2_IMAGE_ID,
        "spot_value_aggregate_l1_v6",
        L1_IMAGE_ID,
    ),
    (
        "source_opened_spot_settlement_v6",
        "zenodex-zrpf-risc0-source-opened-spot-settlement-v6",
        "source_opened_spot_settlement_v6.elf",
        SETTLEMENT_IMAGE_ID,
        "spot_value_aggregate_l2_v6",
        L2_IMAGE_ID,
    ),
)

POLICY_SPECS = (
    (
        "zk/zrpf_risc0/spot_value_leaf_v6_shared/src/lib.rs",
        "PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID",
        ADAPTER_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_value_aggregate_l1_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6",
        LEAF_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_value_aggregate_l2_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6",
        L1_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_value_aggregate_root_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6",
        L2_IMAGE_ID,
    ),
    (
        "zk/zrpf_risc0/spot_settlement_root_policy_v6/src/lib.rs",
        "PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6",
        SETTLEMENT_IMAGE_ID,
    ),
)

EXECUTED_COMMAND_FIELDS = {
    "artifact_hashes_recorded",
    "cargo_build_locked",
    "clean_external_target_verified",
    "image_ids_recomputed_from_elfs",
    "policy_dependencies_compiled",
    "risc0_guests_built",
    "source_snapshot_captured",
}
TRUE_CLAIMS = {
    "dependency_chain_exactly_bound",
    "four_guest_elf_hashes_recorded",
    "same_host_current_v6_images_built",
}
FALSE_CLAIMS = {
    "complete_build_input_closure_verified",
    "cross_host_reproducible_build",
    "durable_atomic_admission_verified",
    "proofs_generated",
    "release_authority",
    "settlement_authority",
    "source_to_elf_reproducibility_verified",
    "production_authority",
}


class BuildRecordError(ValueError):
    """Stable fail-closed build-record rejection."""


def _reject_float(_value: str) -> NoReturn:
    raise BuildRecordError("floating-point JSON numbers are forbidden")


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise BuildRecordError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def canonical_bytes(document: Any) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=False) + "\n").encode("utf-8")


def load_record(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    if not raw or len(raw) > MAX_RECORD_BYTES:
        raise BuildRecordError("build record byte length is unsupported")
    try:
        document = json.loads(
            raw,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, BuildRecordError) as exc:
        raise BuildRecordError(f"build record JSON rejected: {exc}") from exc
    if type(document) is not dict:
        raise BuildRecordError("build record root must be an object")
    if canonical_bytes(document) != raw:
        raise BuildRecordError("build record bytes are noncanonical")
    return document, raw


def validate_record(
    document: dict[str, Any],
    raw: bytes,
    *,
    repo_root: Path = REPO_ROOT,
    artifact_directory: Path | None = None,
    expected_record_sha256: str | None = None,
) -> dict[str, Any]:
    record = _exact_object(
        document,
        {
            "schema",
            "recorded_at",
            "source_snapshot",
            "toolchain",
            "programs",
            "executed_commands",
            "claims",
        },
        "record",
    )
    _require_equal(record["schema"], RECORD_SCHEMA, "record.schema")
    _require_date(record["recorded_at"], "record.recorded_at")
    observed_record_sha256 = hashlib.sha256(raw).hexdigest()
    anchor_checked = expected_record_sha256 is not None
    if expected_record_sha256 is not None:
        _require_hash(expected_record_sha256, "expected_record_sha256")
        if observed_record_sha256 != expected_record_sha256:
            raise BuildRecordError("build record SHA-256 differs from supplied anchor")

    _validate_source_snapshot(record["source_snapshot"])
    _validate_toolchain(record["toolchain"])
    _validate_programs(record["programs"])
    _require_true_fields(
        record["executed_commands"],
        EXECUTED_COMMAND_FIELDS,
        "record.executed_commands",
    )
    _validate_claims(record["claims"])
    _validate_policy_sources(repo_root)
    artifacts_checked = 0
    if artifact_directory is not None:
        artifacts_checked = _validate_external_artifacts(
            artifact_directory,
            record["programs"],
        )
    return {
        "ok": True,
        "schema": REPORT_SCHEMA,
        "record_sha256": observed_record_sha256,
        "governed_anchor_checked": anchor_checked,
        "policy_dependencies_checked": len(POLICY_SPECS),
        "external_artifact_files_checked": artifacts_checked,
        "leaf_image_id": LEAF_IMAGE_ID,
        "level_one_image_id": L1_IMAGE_ID,
        "level_two_image_id": L2_IMAGE_ID,
        "settlement_image_id": SETTLEMENT_IMAGE_ID,
        "proofs_generated": False,
        "release_authority": False,
        "production_authority": False,
    }


def _validate_source_snapshot(value: Any) -> None:
    source = _exact_object(
        value,
        {
            "repository_commit",
            "repository_tree",
            "repository_dirty",
            "source_root_sha256",
            "source_file_count",
            "source_bytes",
        },
        "record.source_snapshot",
    )
    _require_hex(source["repository_commit"], 40, "repository_commit")
    _require_hex(source["repository_tree"], 40, "repository_tree")
    _require_exact_bool(source["repository_dirty"], "repository_dirty")
    _require_hash(source["source_root_sha256"], "source_root_sha256")
    _require_positive_int(source["source_file_count"], "source_file_count")
    _require_positive_int(source["source_bytes"], "source_bytes")


def _validate_toolchain(value: Any) -> None:
    toolchain = _exact_object(
        value,
        {
            "rustc",
            "cargo",
            "r0vm",
            "cargo_risczero",
            "risc0_zkvm",
            "cargo_lock_sha256",
            "target",
            "build_jobs",
            "offline",
            "locked",
        },
        "record.toolchain",
    )
    for field in ("rustc", "cargo", "r0vm", "cargo_risczero", "risc0_zkvm", "target"):
        _require_text(toolchain[field], f"toolchain.{field}")
    _require_hash(toolchain["cargo_lock_sha256"], "toolchain.cargo_lock_sha256")
    if toolchain["risc0_zkvm"] != "3.0.5":
        raise BuildRecordError("toolchain.risc0_zkvm must be exactly 3.0.5")
    if type(toolchain["build_jobs"]) is not int or not 1 <= toolchain["build_jobs"] <= 2:
        raise BuildRecordError("toolchain.build_jobs must be an integer in 1..=2")
    _require_exact_bool(toolchain["offline"], "toolchain.offline", expected=True)
    _require_exact_bool(toolchain["locked"], "toolchain.locked", expected=True)


def _validate_programs(value: Any) -> None:
    if type(value) is not list or len(value) != len(PROGRAM_SPECS):
        raise BuildRecordError("record.programs must contain the four ordered V6 programs")
    for index, (row, spec) in enumerate(zip(value, PROGRAM_SPECS, strict=True)):
        stage, package, artifact_file, image_id, child_stage, child_image_id = spec
        program = _exact_object(
            row,
            {
                "stage",
                "package",
                "artifact_file",
                "raw_elf_bytes",
                "raw_elf_sha256",
                "image_id_hex",
                "image_id_words_le",
                "verified_child_stage",
                "verified_child_image_id",
            },
            f"record.programs[{index}]",
        )
        for field, expected in (
            ("stage", stage),
            ("package", package),
            ("artifact_file", artifact_file),
            ("image_id_hex", image_id),
            ("verified_child_stage", child_stage),
            ("verified_child_image_id", child_image_id),
        ):
            _require_equal(program[field], expected, f"programs[{index}].{field}")
        _require_positive_int(program["raw_elf_bytes"], f"programs[{index}].raw_elf_bytes")
        if program["raw_elf_bytes"] > MAX_ARTIFACT_BYTES:
            raise BuildRecordError(f"programs[{index}].raw_elf_bytes exceeds bound")
        _require_hash(program["raw_elf_sha256"], f"programs[{index}].raw_elf_sha256")
        if program["raw_elf_sha256"] == "0" * 64:
            raise BuildRecordError(f"programs[{index}].raw_elf_sha256 is zero")
        expected_words = _image_words_le(image_id)
        if program["image_id_words_le"] != expected_words:
            raise BuildRecordError(f"programs[{index}].image_id_words_le mismatch")


def _validate_claims(value: Any) -> None:
    claims = _exact_object(value, TRUE_CLAIMS | FALSE_CLAIMS, "record.claims")
    for field in TRUE_CLAIMS:
        _require_exact_bool(claims[field], f"claims.{field}", expected=True)
    for field in FALSE_CLAIMS:
        _require_exact_bool(claims[field], f"claims.{field}", expected=False)


def _validate_policy_sources(repo_root: Path) -> None:
    for relative, symbol, expected_image in POLICY_SPECS:
        path = repo_root / relative
        raw = path.read_bytes()
        if not raw or len(raw) > 256 * 1024:
            raise BuildRecordError(f"policy source byte length unsupported: {relative}")
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise BuildRecordError(f"policy source is not UTF-8: {relative}") from exc
        pattern = re.compile(
            rf"pub const {re.escape(symbol)}: \[u32; 8\] = \[(.*?)\];",
            re.DOTALL,
        )
        match = pattern.search(text)
        if match is None:
            raise BuildRecordError(f"policy symbol is unavailable: {symbol}")
        numbers = [
            int(value.replace("_", ""))
            for value in re.findall(r"[0-9][0-9_]*", match.group(1))
        ]
        if len(numbers) != 8 or any(value > 0xFFFF_FFFF for value in numbers):
            raise BuildRecordError(f"policy image words malformed: {symbol}")
        observed = b"".join(value.to_bytes(4, "little") for value in numbers).hex()
        if observed != expected_image:
            raise BuildRecordError(f"policy image mismatch: {symbol}")


def _validate_external_artifacts(directory: Path, programs: Any) -> int:
    root = directory.resolve(strict=True)
    if not root.is_dir():
        raise BuildRecordError("artifact directory is not a directory")
    checked = 0
    for row in programs:
        filename = row["artifact_file"]
        path = _resolve_artifact(root, filename)
        size, digest = _stable_file_facts(path)
        if size != row["raw_elf_bytes"] or digest != row["raw_elf_sha256"]:
            raise BuildRecordError(f"external artifact identity mismatch: {filename}")
        checked += 1
    return checked


def _resolve_artifact(root: Path, relative: str) -> Path:
    if type(relative) is not str:
        raise BuildRecordError("artifact path must be a string")
    pure = PurePosixPath(relative)
    if pure.is_absolute() or len(pure.parts) != 1 or pure.name in {"", ".", ".."}:
        raise BuildRecordError(f"artifact path is not one bounded filename: {relative}")
    candidate = root / pure.name
    if candidate.is_symlink():
        raise BuildRecordError(f"artifact symlink rejected: {relative}")
    return candidate


def _stable_file_facts(path: Path) -> tuple[int, str]:
    before = path.stat(follow_symlinks=False)
    if (
        not stat.S_ISREG(before.st_mode)
        or before.st_size <= 0
        or before.st_size > MAX_ARTIFACT_BYTES
    ):
        raise BuildRecordError(f"artifact is not a bounded regular file: {path.name}")
    hasher = hashlib.sha256()
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        opened = os.fstat(descriptor)
        if (opened.st_dev, opened.st_ino, opened.st_size) != (
            before.st_dev,
            before.st_ino,
            before.st_size,
        ):
            raise BuildRecordError(f"artifact changed before read: {path.name}")
        total = 0
        while chunk := os.read(descriptor, min(1 << 20, MAX_ARTIFACT_BYTES + 1 - total)):
            total += len(chunk)
            if total > MAX_ARTIFACT_BYTES:
                raise BuildRecordError(f"artifact exceeds bound: {path.name}")
            hasher.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns) != (
        opened.st_dev,
        opened.st_ino,
        opened.st_size,
        opened.st_mtime_ns,
    ) or total != opened.st_size:
        raise BuildRecordError(f"artifact changed during read: {path.name}")
    return total, hasher.hexdigest()


def _exact_object(value: Any, fields: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise BuildRecordError(f"{label} must be an object")
    observed = set(value)
    if observed != fields:
        raise BuildRecordError(
            f"{label} field set mismatch: missing={sorted(fields - observed)}, "
            f"unknown={sorted(observed - fields)}"
        )
    return value


def _require_true_fields(value: Any, fields: set[str], label: str) -> None:
    obj = _exact_object(value, fields, label)
    for field in fields:
        _require_exact_bool(obj[field], f"{label}.{field}", expected=True)


def _require_exact_bool(value: Any, label: str, *, expected: bool | None = None) -> None:
    if type(value) is not bool or (expected is not None and value is not expected):
        suffix = "a Boolean" if expected is None else f"exactly {expected}"
        raise BuildRecordError(f"{label} must be {suffix}")


def _require_positive_int(value: Any, label: str) -> None:
    if type(value) is not int or value <= 0:
        raise BuildRecordError(f"{label} must be a positive integer")


def _require_text(value: Any, label: str) -> None:
    if (
        type(value) is not str
        or not value
        or len(value) > 256
        or any(character in value for character in "\r\n\0")
    ):
        raise BuildRecordError(f"{label} must be bounded single-line text")


def _require_equal(value: Any, expected: str, label: str) -> None:
    if type(value) is not str or value != expected:
        raise BuildRecordError(f"{label} mismatch")


def _require_hash(value: Any, label: str) -> None:
    _require_hex(value, 64, label)


def _require_hex(value: Any, length: int, label: str) -> None:
    if type(value) is not str or len(value) != length or re.fullmatch(r"[0-9a-f]+", value) is None:
        raise BuildRecordError(f"{label} must be {length} lowercase hexadecimal characters")


def _require_date(value: Any, label: str) -> None:
    if type(value) is not str:
        raise BuildRecordError(f"{label} must be an ISO date")
    try:
        parsed = date.fromisoformat(value)
    except ValueError as exc:
        raise BuildRecordError(f"{label} must be an ISO date") from exc
    if parsed.isoformat() != value:
        raise BuildRecordError(f"{label} must be a canonical ISO date")


def _image_words_le(image_id: str) -> list[int]:
    raw = bytes.fromhex(image_id)
    return [int.from_bytes(raw[offset : offset + 4], "little") for offset in range(0, 32, 4)]


def check_record(
    path: Path = DEFAULT_RECORD,
    *,
    artifact_directory: Path | None = None,
    expected_record_sha256: str | None = None,
) -> dict[str, Any]:
    try:
        document, raw = load_record(path)
        return validate_record(
            document,
            raw,
            artifact_directory=artifact_directory,
            expected_record_sha256=expected_record_sha256,
        )
    except (OSError, BuildRecordError) as exc:
        return {
            "ok": False,
            "schema": REPORT_SCHEMA,
            "errors": [str(exc)],
            "governed_anchor_checked": False,
            "external_artifact_files_checked": 0,
            "proofs_generated": False,
            "release_authority": False,
            "production_authority": False,
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--record", type=Path, default=DEFAULT_RECORD)
    parser.add_argument("--artifact-directory", type=Path)
    parser.add_argument("--expected-record-sha256")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    report = check_record(
        arguments.record,
        artifact_directory=arguments.artifact_directory,
        expected_record_sha256=arguments.expected_record_sha256,
    )
    if arguments.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print("accepted" if report["ok"] else "rejected")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
