#!/usr/bin/env python3
"""Build the fixed ZRPF V3 Succinct-seal mutation control artifact.

This tool constructs one canonical mutation. It does not verify a RISC0 seal.
The Rust verifier-only harness must authenticate the original tree, check the
exact mutation relation, and observe the typed cryptographic rejection.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
from pathlib import Path
from typing import Any


SCHEMA = "zenodex/zrpf_v3_succinct_seal_mutation_build/v1"
MAX_RECEIPT_BYTES = 16 * 1024 * 1024
SEAL_WORD_INDEX = 1


class MutationBuildError(ValueError):
    """Raised when mutation construction cannot preserve the fixed contract."""


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")


def sha256_hex(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def build_mutation(source_path: Path, output_path: Path) -> dict[str, Any]:
    source_bytes = _read_bounded_regular_file(source_path)
    source = _load_canonical_receipt(source_bytes)
    seal = _succinct_seal(source)
    if len(seal) <= SEAL_WORD_INDEX:
        raise MutationBuildError("Succinct seal is too short for the pinned mutation")

    original_word = seal[SEAL_WORD_INDEX]
    mutated_word = original_word ^ 1
    seal[SEAL_WORD_INDEX] = mutated_word
    mutated_bytes = canonical_json_bytes(source)
    if mutated_bytes == source_bytes:
        raise MutationBuildError("mutation did not change canonical receipt bytes")

    restored = _load_canonical_receipt(mutated_bytes)
    _succinct_seal(restored)[SEAL_WORD_INDEX] = original_word
    if canonical_json_bytes(restored) != source_bytes:
        raise MutationBuildError("mutation changes data outside the pinned seal word")

    _write_create_new(output_path, mutated_bytes)
    return {
        "authority": "mutation_construction_only",
        "control_built": True,
        "mutated_receipt_sha256": sha256_hex(mutated_bytes),
        "mutated_receipt_size_bytes": len(mutated_bytes),
        "mutation": {
            "kind": "succinct_seal_word_xor_lsb_v1",
            "seal_word_count": len(seal),
            "seal_word_index": SEAL_WORD_INDEX,
            "seal_word_mutated": mutated_word,
            "seal_word_original": original_word,
            "xor_mask": 1,
        },
        "python_verifies_risc0_seal": False,
        "schema": SCHEMA,
        "source_receipt_sha256": sha256_hex(source_bytes),
        "source_receipt_size_bytes": len(source_bytes),
        "status": "canonical_single_seal_word_mutation_built",
    }


def _read_bounded_regular_file(path: Path) -> bytes:
    try:
        metadata = path.lstat()
    except OSError as exc:
        raise MutationBuildError("source receipt metadata read failed") from exc
    if (
        not stat.S_ISREG(metadata.st_mode)
        or path.is_symlink()
        or metadata.st_size <= 0
        or metadata.st_size > MAX_RECEIPT_BYTES
    ):
        raise MutationBuildError("source receipt must be a bounded non-symlink regular file")
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise MutationBuildError("source receipt read failed") from exc
    if len(raw) != metadata.st_size:
        raise MutationBuildError("source receipt changed while it was read")
    return raw


def _load_canonical_receipt(raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise MutationBuildError(f"source receipt JSON rejected: {exc}") from exc
    if not isinstance(value, dict) or set(value) != {"inner", "journal", "metadata"}:
        raise MutationBuildError("source receipt outer fields mismatch")
    if canonical_json_bytes(value) != raw:
        raise MutationBuildError("source receipt JSON is not canonical")
    return value


def _succinct_seal(receipt: dict[str, Any]) -> list[int]:
    inner = receipt.get("inner")
    if not isinstance(inner, dict) or set(inner) != {"Succinct"}:
        raise MutationBuildError("source receipt is not structurally Succinct")
    succinct = inner.get("Succinct")
    expected_fields = {
        "claim",
        "control_id",
        "control_inclusion_proof",
        "hashfn",
        "seal",
        "verifier_parameters",
    }
    if not isinstance(succinct, dict) or set(succinct) != expected_fields:
        raise MutationBuildError("source Succinct receipt fields mismatch")
    seal = succinct.get("seal")
    if (
        not isinstance(seal, list)
        or not seal
        or any(type(word) is not int or word < 0 or word > 0xFFFF_FFFF for word in seal)
    ):
        raise MutationBuildError("source Succinct seal words are invalid")
    return seal


def _write_create_new(path: Path, raw: bytes) -> None:
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as exc:
        raise MutationBuildError("mutation output parent is unavailable") from exc
    if not parent.is_dir() or path.name in {"", ".", ".."}:
        raise MutationBuildError("mutation output path is invalid")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(parent / path.name, flags, 0o644)
    except OSError as exc:
        raise MutationBuildError("create-new mutation output failed") from exc
    try:
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise MutationBuildError("mutation output write made no progress")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    directory_descriptor = os.open(parent, os.O_RDONLY)
    try:
        os.fsync(directory_descriptor)
    finally:
        os.close(directory_descriptor)


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON number: {value}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_receipt", type=Path)
    parser.add_argument("mutated_receipt_output", type=Path)
    args = parser.parse_args()
    try:
        report = build_mutation(args.source_receipt, args.mutated_receipt_output)
    except (MutationBuildError, OSError) as exc:
        report = {
            "control_built": False,
            "errors": [str(exc)],
            "schema": SCHEMA,
            "status": "rejected",
        }
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
        return 1
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
