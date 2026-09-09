"""Illustrate a compatibility gap with two in-memory codec pairs.

This example is deliberately separate from the future ZenoLacuna workbench. It
executes only the two repository codec kernels named in ``ALLOWLIST`` and keeps
the XOR1 pair in memory. It demonstrates a missing compatibility requirement;
it does not report a defect in the published adapter.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Callable, cast

ROOT = Path(__file__).resolve().parents[4]
ALLOWLIST = {
    "encode": Path("src/kernels/python/external_signal_profile_encode_v2.py"),
    "decode": Path("src/kernels/python/external_signal_profile_decode_v2.py"),
}
RESERVED_SENTINEL = 0xFF
SEMANTIC_WORDS = tuple(range(0x80))
RESERVED_BYTES = tuple(range(0x80, 0x100))


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def _load_allowlisted_kernel(label: str) -> tuple[Callable[[int], int], dict[str, str]]:
    relative = ALLOWLIST.get(label)
    if relative is None:
        raise RuntimeError(f"unknown allowlist label: {label}")
    expected_path = ROOT / relative
    path = expected_path.resolve()
    _require(path == expected_path, f"kernel path escaped allowlist: {relative}")
    _require(path.is_file(), f"allowlisted kernel is missing: {relative}")

    source = path.read_bytes()
    source_hash = hashlib.sha256(source).hexdigest()
    # Execute the exact allowlisted bytes whose hash is recorded, without a
    # second file read that could select a different source revision.
    namespace: dict[str, Any] = {"__name__": f"_zenolacuna_allowlisted_{label}"}
    exec(compile(source, relative.as_posix(), "exec"), namespace)
    transform = namespace.get("transform")
    _require(callable(transform), f"allowlisted kernel has no transform: {relative}")
    return cast(Callable[[int], int], transform), {
        "path": relative.as_posix(), "sha256": source_hash
    }


def _byte(value: object, *, label: str) -> int:
    if type(value) is not int:
        raise RuntimeError(f"{label} returned a non-integer")
    _require(0 <= value <= 0xFF, f"{label} returned outside one byte")
    return value


def main() -> None:
    # Keep this validation run from creating bytecode beside either kernel.
    sys.dont_write_bytecode = True
    _require(sys.dont_write_bytecode, "bytecode must be disabled")

    normal_encode, encode_source = _load_allowlisted_kernel("encode")
    normal_decode, decode_source = _load_allowlisted_kernel("decode")

    def encode(value: int) -> int:
        return _byte(normal_encode(value), label="normal encode")

    def decode(value: int) -> int:
        return _byte(normal_decode(value), label="normal decode")

    def xor1_encode(value: int) -> int:
        return _byte(encode(value) ^ 1, label="XOR1 encode") if value < 0x80 else RESERVED_SENTINEL

    def xor1_decode(value: int) -> int:
        return _byte(decode(value ^ 1), label="XOR1 decode") if value < 0x80 else RESERVED_SENTINEL

    normal_roundtrips = sum(
        decode(encode(value)) == value for value in SEMANTIC_WORDS
    )
    xor1_roundtrips = sum(
        xor1_decode(xor1_encode(value)) == value for value in SEMANTIC_WORDS
    )
    normal_encode_xor1_decode_mismatches = sum(
        xor1_decode(encode(value)) != value for value in SEMANTIC_WORDS
    )
    xor1_encode_normal_decode_mismatches = sum(
        decode(xor1_encode(value)) != value for value in SEMANTIC_WORDS
    )
    reserved_encode_sentinel_count = sum(
        encode(value) == RESERVED_SENTINEL for value in RESERVED_BYTES
    )
    reserved_decode_sentinel_count = sum(
        decode(value) == RESERVED_SENTINEL for value in RESERVED_BYTES
    )
    xor1_reserved_encode_count = sum(
        xor1_encode(value) == RESERVED_SENTINEL for value in RESERVED_BYTES
    )
    xor1_reserved_decode_count = sum(
        xor1_decode(value) == RESERVED_SENTINEL for value in RESERVED_BYTES
    )

    expected = len(SEMANTIC_WORDS)
    reserved_expected = len(RESERVED_BYTES)
    _require(normal_roundtrips == expected, "normal pair lost a semantic roundtrip")
    _require(xor1_roundtrips == expected, "XOR1 pair lost a semantic roundtrip")
    _require(
        normal_encode_xor1_decode_mismatches == expected,
        "normal encode/XOR1 decode did not distinguish every word",
    )
    _require(
        xor1_encode_normal_decode_mismatches == expected,
        "XOR1 encode/normal decode did not distinguish every word",
    )
    _require(
        reserved_encode_sentinel_count == reserved_expected,
        "normal encoder did not return the reserved sentinel for all reserved words",
    )
    _require(
        reserved_decode_sentinel_count == reserved_expected,
        "normal decoder did not return the reserved sentinel for all reserved bytes",
    )
    _require(
        xor1_reserved_encode_count == reserved_expected
        and xor1_reserved_decode_count == reserved_expected,
        "XOR1 pair did not preserve reserved sentinels",
    )

    report = {
        "schema": "zenolacuna/codec-gap-example-v1",
        "illustration_only": True,
        "authority": "NONE",
        "engine_implemented": False,
        "example_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "claim_boundary": "The altered pair demonstrates an omitted compatibility decision; it is not a published-adapter defect report.",
        "source_hashes": {
            "encode_kernel": encode_source,
            "decode_kernel": decode_source,
        },
        "counts": {
            "semantic_words": expected,
            "reserved_bytes": reserved_expected,
            "normal_roundtrips": normal_roundtrips,
            "xor1_roundtrips": xor1_roundtrips,
            "normal_encode_xor1_decode_mismatches": normal_encode_xor1_decode_mismatches,
            "xor1_encode_normal_decode_mismatches": xor1_encode_normal_decode_mismatches,
            "reserved_encode_sentinel": reserved_encode_sentinel_count,
            "reserved_decode_sentinel": reserved_decode_sentinel_count,
            "xor1_reserved_encode_sentinel": xor1_reserved_encode_count,
            "xor1_reserved_decode_sentinel": xor1_reserved_decode_count,
        },
        "checks": {
            "allowlist_exact": True,
            "bytecode_disabled": sys.dont_write_bytecode,
            "normal_pair_complete": normal_roundtrips == expected,
            "xor1_pair_complete": xor1_roundtrips == expected,
            "mixed_pairs_distinguish_all": (
                normal_encode_xor1_decode_mismatches == expected
                and xor1_encode_normal_decode_mismatches == expected
            ),
            "reserved_values_return_sentinel": (
                reserved_encode_sentinel_count == reserved_expected
                and reserved_decode_sentinel_count == reserved_expected
                and xor1_reserved_encode_count == reserved_expected
                and xor1_reserved_decode_count == reserved_expected
            ),
        },
    }
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
