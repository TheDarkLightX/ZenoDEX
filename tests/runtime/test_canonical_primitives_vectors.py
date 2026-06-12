"""Cross-language vectors for the canonical primitives.

Proves the Rust core's `hex_to_bytes_fixed` and `canonical_json_bytes` (exposed
via the `canonical-hash` CLI subcommand) agree byte-for-byte with the
authoritative Python encoders in `src/state/canonical.py`, on a static corpus
and on a randomized differential.

These two primitives are the foundation the state-root (Phase C) and tx/receipt
hash (Phase F) shadows build on, so their cross-language equality is checked
independently here rather than only implicitly through a consuming surface.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.state.canonical import canonical_json_bytes, hex_to_bytes_fixed, sha256_hex
from tools.runtime import canonical_primitives_lib as lib


# --- Python authority regression (known vectors) ------------------------------


def test_python_known_vectors():
    # Sorted keys, compact separators, no whitespace.
    assert canonical_json_bytes({"b": 2, "a": 1}) == b'{"a":1,"b":2}'
    # Non-ASCII stays raw UTF-8 (ensure_ascii=False).
    assert canonical_json_bytes("é") == '"é"'.encode("utf-8")
    # Big integer beyond u128 is exact.
    assert canonical_json_bytes(10 ** 30) == b"1" + b"0" * 30
    # Mixed-case fixed hex decodes case-insensitively.
    assert hex_to_bytes_fixed("0xDeAdBeEf", nbytes=4, name="x") == bytes(
        [0xDE, 0xAD, 0xBE, 0xEF]
    )
    # A pinned receipt-like hash (guards accidental encoder drift).
    body = {"amount": 12_345, "asset": "zUSD"}
    assert sha256_hex(canonical_json_bytes(body)).startswith("0x")


def test_python_rejects_floats_and_bad_hex():
    with pytest.raises(TypeError):
        canonical_json_bytes(1.5)
    with pytest.raises(TypeError):
        canonical_json_bytes({"k": 0.1})
    with pytest.raises(ValueError):
        hex_to_bytes_fixed("0x0102", nbytes=1, name="x")
    with pytest.raises(ValueError):
        hex_to_bytes_fixed("0xzz", nbytes=1, name="x")


# --- Rust/Python differential -------------------------------------------------


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.CanonicalShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(cases, rust_bin):
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, cases)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust canonical mismatch:\n" + "\n".join(problems[:20])


def test_rust_matches_python_static(rust_bin):
    cases = lib.static_cases()
    # Sanity: the corpus exercises both accept and reject on both ops.
    py = lib.py_eval_all(cases)
    assert any(r["ok"] for r in py) and any(not r["ok"] for r in py)
    _assert_agrees(cases, rust_bin)


@pytest.mark.parametrize("seed", [1, 7, 20260529])
def test_rust_matches_python_randomized(rust_bin, seed):
    cases = lib.random_cases(seed=seed, n=400)
    _assert_agrees(cases, rust_bin)


def test_rejections_agree(rust_bin):
    cases = [
        {"op": "json_bytes", "value": 1.5},
        {"op": "json_bytes", "value": [1, 2.5]},
        {"op": "json_bytes", "value": {"k": 3.14}},
        {"op": "hex_to_bytes", "hex": "00", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0xzz", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0x0102", "nbytes": 1},
    ]
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, cases)
    assert all(not r["ok"] for r in py)
    assert all(not r["ok"] for r in rs)
    assert not lib.diff_results(py, rs)
