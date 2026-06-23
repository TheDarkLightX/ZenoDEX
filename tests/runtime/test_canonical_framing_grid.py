"""Canonical raw framing grid for uvarint and length-prefixed bytes.

Kani covers selected scalar helper boundaries, but the heap-allocating
`Vec`-returning encoders are still best pinned by deterministic cross-runtime
grids. This test uses a small independent oracle for unsigned LEB128 and
length-prefixed byte framing, then checks Python and Rust against it.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.runtime import canonical_primitives_lib as lib  # noqa: E402


def _ref_uvarint(value: int) -> bytes:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError("uvarint value outside bridge domain")
    out = bytearray()
    n = value
    while True:
        byte = n & 0x7F
        n >>= 7
        if n:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def _ref_encode_bytes(raw: bytes) -> bytes:
    return _ref_uvarint(len(raw)) + raw


def _uvarint_cases() -> list[dict]:
    values = [
        0,
        1,
        2,
        126,
        127,
        128,
        129,
        255,
        256,
        16_383,
        16_384,
        2**32 - 1,
        2**32,
        2**64 - 1,
        2**64,
        2**127 - 1,
        2**127,
        2**128 - 1,
    ]
    invalid = [-1, 2**128, True, "1"]
    return [{"op": "uvarint", "value": value} for value in values + invalid]


def _byte_cases() -> list[dict]:
    accepted = [
        b"",
        b"\x00",
        b"abc",
        bytes(range(127)),
        bytes(range(128)),
        bytes(range(256)),
    ]
    rejected = ["00", "0x0", "0xzz", "0x00 11 ", 123]
    return [{"op": "encode_bytes", "hex": "0x" + raw.hex()} for raw in accepted] + [
        {"op": "encode_bytes", "hex": value} for value in rejected
    ]


def _cases() -> list[dict]:
    return _uvarint_cases() + _byte_cases()


def test_python_framing_matches_independent_oracle():
    results = lib.py_eval_all(_cases())
    for case, result in zip(_cases(), results):
        if case["op"] == "uvarint":
            value = case["value"]
            if isinstance(value, int) and not isinstance(value, bool) and 0 <= value < 2**128:
                assert result == {
                    "index": result["index"],
                    "ok": True,
                    "bytes": "0x" + _ref_uvarint(value).hex(),
                }
            else:
                assert result["ok"] is False
        elif case["op"] == "encode_bytes":
            hex_value = case["hex"]
            if isinstance(hex_value, str) and hex_value.startswith("0x"):
                body = hex_value[2:]
                try:
                    raw = bytes.fromhex(body)
                except ValueError:
                    assert result["ok"] is False
                else:
                    is_hex = all(ch in "0123456789abcdefABCDEF" for ch in body)
                    if len(body) % 2 == 0 and is_hex:
                        assert result == {
                            "index": result["index"],
                            "ok": True,
                            "bytes": "0x" + _ref_encode_bytes(raw).hex(),
                        }
                    else:
                        assert result["ok"] is False
            else:
                assert result["ok"] is False


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.CanonicalShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def test_raw_framing_grid_matches_rust(rust_bin):
    cases = _cases()
    py = lib.py_eval_all(cases)
    rust = lib.run_rust(rust_bin, cases)
    assert any(item["ok"] for item in py)
    assert any(not item["ok"] for item in py)
    assert not lib.diff_results(py, rust)
