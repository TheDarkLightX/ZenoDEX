#!/usr/bin/env python3
"""Fail-closed static checker for the V5 L1/L2 program build record."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, NoReturn

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECORD = (
    REPO_ROOT
    / "docs/research/ZRPF_VALUE_AGGREGATE_V5_PROGRAM_BUILD_RECORD_20260712.json"
)
EXPECTED_RECORD_SHA256 = (
    "8f406f81ab6ee9c9db8ed324fd4b7c5c4532d0b6a3db407800e44665cd3725fc"
)
EXPECTED_SCHEMA = "zenodex/zrpf_value_aggregate_v5_program_build_record/v2"
EXPECTED_CARGO_LOCK_SHA256 = (
    "08b48d69d359a6f4134f4f1082c6fc17a52a8f4e3e85eba316ff406fbc28547f"
)
EXPECTED_SPOT_IMAGE = "d81406cf27ff2f776aed9e20fee3128b859387e4475d517c75f25e8e564f6a70"
EXPECTED_L1_IMAGE = "99027bd4ff71de02c86b10309a923d37c38d273c01049f08bccfa11412bdf97d"
EXPECTED_L2_IMAGE = "49c94dc5618c5e82372265cc75ee77d0985d9ab1b7b223f036e513870d6742f8"
EXPECTED_SPOT_WORDS = [
    3473282264,
    1999634215,
    547286378,
    2333271038,
    3834090373,
    2085707079,
    2388587125,
    1886015318,
]
EXPECTED_L1_WORDS = [
    3564831385,
    48132607,
    806382536,
    926782106,
    1009225155,
    144638977,
    346148796,
    2113518866,
]
FALSE_CLAIMS = {
    "cross_host_reproducible_build",
    "level_one_receipt_generated",
    "level_two_receipt_generated",
    "settlement_semantics_verified",
    "durable_atomic_admission_verified",
    "release_authority",
    "settlement_authority",
    "production_authority",
}


class RecordError(ValueError):
    """Stable fail-closed build-record rejection."""


def _reject_float(_value: str) -> NoReturn:
    raise RecordError("floating-point JSON numbers are forbidden")


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise RecordError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def canonical_bytes(document: Any) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=False) + "\n").encode("utf-8")


def load_record(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    if not raw or len(raw) > 64 * 1024:
        raise RecordError("build record byte length is unsupported")
    try:
        document = json.loads(
            raw,
            object_pairs_hook=_object_no_duplicates,
            parse_float=_reject_float,
            parse_constant=_reject_float,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecordError) as exc:
        raise RecordError(f"build record JSON rejected: {exc}") from exc
    if type(document) is not dict:
        raise RecordError("build record root must be an object")
    if canonical_bytes(document) != raw:
        raise RecordError("build record bytes are noncanonical")
    return document, raw


def _exact_keys(value: Any, expected: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise RecordError(f"{label} must be an object")
    observed = set(value)
    if observed != expected:
        raise RecordError(
            f"{label} field set mismatch: missing={sorted(expected - observed)}, "
            f"unknown={sorted(observed - expected)}"
        )
    return value


def _require_exact_bool(value: Any, expected: bool, label: str) -> None:
    if type(value) is not bool or value is not expected:
        raise RecordError(f"{label} must be exactly {expected}")


def _git_tree(commit: str, repo_root: Path) -> str:
    completed = subprocess.run(
        ["/usr/bin/git", "show", "-s", "--format=%T", f"{commit}^{{commit}}"],
        cwd=repo_root,
        check=False,
        capture_output=True,
        timeout=10,
    )
    if completed.returncode != 0 or completed.stderr:
        raise RecordError("source commit is unavailable")
    return completed.stdout.decode("ascii").strip()


def validate_record(
    document: dict[str, Any],
    raw: bytes,
    *,
    repo_root: Path = REPO_ROOT,
    require_anchor: bool = True,
) -> dict[str, Any]:
    _exact_keys(
        document,
        {
            "schema",
            "recorded_at",
            "profile",
            "toolchain",
            "spot_value_leaf_v4",
            "level_one",
            "level_two",
            "claims",
        },
        "record",
    )
    if document["schema"] != EXPECTED_SCHEMA:
        raise RecordError("build record schema mismatch")
    observed_sha = hashlib.sha256(raw).hexdigest()
    if require_anchor and observed_sha != EXPECTED_RECORD_SHA256:
        raise RecordError("build record SHA-256 differs from governed anchor")

    toolchain = _exact_keys(
        document["toolchain"],
        {
            "rustc",
            "cargo",
            "r0vm",
            "risc0_zkvm",
            "risc0_binfmt",
            "risc0_zkos_v1compat",
            "cargo_lock_sha256",
            "target",
            "cargo_build_jobs",
            "offline",
            "locked",
        },
        "toolchain",
    )
    if toolchain["cargo_lock_sha256"] != EXPECTED_CARGO_LOCK_SHA256:
        raise RecordError("Cargo.lock digest mismatch")
    if toolchain["cargo_build_jobs"] != 2:
        raise RecordError("build job budget mismatch")
    _require_exact_bool(toolchain["offline"], True, "toolchain.offline")
    _require_exact_bool(toolchain["locked"], True, "toolchain.locked")

    artifact_keys = {
        "source_commit",
        "source_tree",
        "package",
        "raw_elf_bytes",
        "raw_elf_sha256",
        "combined_program_binary_bytes",
        "combined_program_binary_sha256",
        "image_id_hex",
        "image_id_words_le",
    }
    spot = _exact_keys(
        document["spot_value_leaf_v4"],
        artifact_keys,
        "spot_value_leaf_v4",
    )
    level_one = _exact_keys(
        document["level_one"],
        artifact_keys | {"self_identity_absent_from_normal_build_dev_closure"},
        "level_one",
    )
    level_two = _exact_keys(
        document["level_two"],
        artifact_keys | {"pinned_level_one_image_id"},
        "level_two",
    )
    if spot["image_id_hex"] != EXPECTED_SPOT_IMAGE:
        raise RecordError("Spot V4 image ID mismatch")
    if spot["image_id_words_le"] != EXPECTED_SPOT_WORDS:
        raise RecordError("Spot V4 image words mismatch")
    if level_one["image_id_hex"] != EXPECTED_L1_IMAGE:
        raise RecordError("L1 image ID mismatch")
    if level_one["image_id_words_le"] != EXPECTED_L1_WORDS:
        raise RecordError("L1 image words mismatch")
    if level_two["image_id_hex"] != EXPECTED_L2_IMAGE:
        raise RecordError("L2 image ID mismatch")
    if level_two["pinned_level_one_image_id"] != EXPECTED_L1_IMAGE:
        raise RecordError("L2 pinned L1 image mismatch")
    _require_exact_bool(
        level_one["self_identity_absent_from_normal_build_dev_closure"],
        True,
        "level_one.self_identity_absent_from_normal_build_dev_closure",
    )
    for level, section in (
        ("spot_value_leaf_v4", spot),
        ("level_one", level_one),
        ("level_two", level_two),
    ):
        if _git_tree(section["source_commit"], repo_root) != section["source_tree"]:
            raise RecordError(f"{level} source tree mismatch")

    claims = _exact_keys(
        document["claims"],
        {
            "spot_value_leaf_v4_image_built",
            "cycle_free_level_one_image_built",
            "level_two_image_built_against_pinned_level_one",
            "same_host_clean_build_recorded",
            *FALSE_CLAIMS,
        },
        "claims",
    )
    for claim in (
        "spot_value_leaf_v4_image_built",
        "cycle_free_level_one_image_built",
        "level_two_image_built_against_pinned_level_one",
        "same_host_clean_build_recorded",
    ):
        _require_exact_bool(claims[claim], True, f"claims.{claim}")
    for claim in FALSE_CLAIMS:
        _require_exact_bool(claims[claim], False, f"claims.{claim}")

    policy_source = (
        repo_root / "zk/zrpf_risc0/value_aggregate_l2_policy/src/lib.rs"
    ).read_text(encoding="utf-8")
    if "PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5" not in policy_source:
        raise RecordError("L2 policy lacks the pinned L1 symbol")
    if "PROVISIONAL_VALUE_AGGREGATE_L1_IMAGE_ID_V5" in policy_source:
        raise RecordError("L2 policy still exposes a provisional L1 symbol")
    return {
        "ok": True,
        "schema": "zenodex/zrpf_value_aggregate_v5_program_build_check/v1",
        "record_sha256": observed_sha,
        "spot_value_leaf_v4_image_id": EXPECTED_SPOT_IMAGE,
        "level_one_image_id": EXPECTED_L1_IMAGE,
        "level_two_image_id": EXPECTED_L2_IMAGE,
        "artifact_bytes_rechecked": False,
        "proofs_generated": False,
        "production_authority": False,
    }


def check_record(path: Path = DEFAULT_RECORD) -> dict[str, Any]:
    try:
        document, raw = load_record(path)
        return validate_record(document, raw)
    except (OSError, RecordError, subprocess.SubprocessError) as exc:
        return {
            "ok": False,
            "schema": "zenodex/zrpf_value_aggregate_v5_program_build_check/v1",
            "errors": [str(exc)],
            "artifact_bytes_rechecked": False,
            "proofs_generated": False,
            "production_authority": False,
        }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--record", type=Path, default=DEFAULT_RECORD)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    report = check_record(args.record)
    if args.json:
        print(json.dumps(report, sort_keys=True))
    else:
        print("accepted" if report["ok"] else "rejected")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
