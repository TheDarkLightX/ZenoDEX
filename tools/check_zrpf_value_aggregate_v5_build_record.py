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
    "7fabc54a97c8d22df4bfd61ccf7d357319e64f8fbb9514f3955f11100f79298f"
)
EXPECTED_SCHEMA = "zenodex/zrpf_value_aggregate_v5_program_build_record/v1"
EXPECTED_L1_IMAGE = "0e54e3390694406b1ae0b8fd082e387c335bf508ffa5d5a8e88078ccd36d788f"
EXPECTED_L2_IMAGE = "05d847cec32d12bbc1065ee517b48cb25d53f93a527c3b41e62f64f244735e8b"
EXPECTED_L1_WORDS = [
    971199502,
    1799394310,
    4256751642,
    2084056584,
    150297395,
    2832573951,
    3430449384,
    2407034323,
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
        {"schema", "recorded_at", "profile", "toolchain", "level_one", "level_two", "claims"},
        "record",
    )
    if document["schema"] != EXPECTED_SCHEMA:
        raise RecordError("build record schema mismatch")
    observed_sha = hashlib.sha256(raw).hexdigest()
    if require_anchor and observed_sha != EXPECTED_RECORD_SHA256:
        raise RecordError("build record SHA-256 differs from governed anchor")

    level_one = _exact_keys(
        document["level_one"],
        {
            "source_commit",
            "source_tree",
            "package",
            "raw_elf_bytes",
            "raw_elf_sha256",
            "combined_program_binary_bytes",
            "combined_program_binary_sha256",
            "image_id_hex",
            "image_id_words_le",
            "self_identity_absent_from_normal_build_dev_closure",
        },
        "level_one",
    )
    level_two = _exact_keys(
        document["level_two"],
        {
            "source_commit",
            "source_tree",
            "package",
            "raw_elf_bytes",
            "raw_elf_sha256",
            "combined_program_binary_bytes",
            "combined_program_binary_sha256",
            "image_id_hex",
            "image_id_words_le",
            "pinned_level_one_image_id",
        },
        "level_two",
    )
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
    for level, section in (("level_one", level_one), ("level_two", level_two)):
        if _git_tree(section["source_commit"], repo_root) != section["source_tree"]:
            raise RecordError(f"{level} source tree mismatch")

    claims = _exact_keys(
        document["claims"],
        {
            "cycle_free_level_one_image_built",
            "level_two_image_built_against_pinned_level_one",
            "same_host_clean_build_recorded",
            *FALSE_CLAIMS,
        },
        "claims",
    )
    for claim in (
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
