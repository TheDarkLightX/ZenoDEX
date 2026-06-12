"""
Regression for S2-CQ-001 (D-PROOF-COMPRESS): the recompute-batch proof verifiers
must reject a CORRUPT (not merely truncated) zlib witness with a typed ValueError
at the decompression boundary, so the verifier returns a structured fail-closed
rejection instead of crashing with a traceback (which would also leak internal
paths to stderr).

Before the fix, `_zlib_decompress_limited` let `zlib.error` from a mid-stream
byte corruption escape `_verify`'s `(TypeError, ValueError)` handler, crashing the
subprocess (exit 1). The engine treats a non-zero verifier exit as a rejection
(fail-closed), so this was not a security hole — but the verifier should fail
cleanly. v2/v3/v4 support compressed witnesses; v1 does not.
"""
from __future__ import annotations

import importlib.util
import zlib
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_PROVERS = ("recompute_batch_v2", "recompute_batch_v3", "recompute_batch_v4")


def _load(name: str):
    spec = importlib.util.spec_from_file_location(
        name, str(_REPO / "tools" / "proof_verifiers" / f"{name}.py")
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.mark.parametrize("name", _PROVERS)
def test_corrupt_zlib_witness_raises_valueerror_not_zlib_error(name):
    mod = _load(name)
    good = zlib.compress(b'{"k":123}' * 64, 6)
    corrupt = bytearray(good)
    corrupt[10] ^= 0xFF  # flip a byte mid-stream -> zlib decode error
    with pytest.raises(ValueError):
        mod._zlib_decompress_limited(bytes(corrupt), name="snap", max_out=100_000)


@pytest.mark.parametrize("name", _PROVERS)
def test_truncated_zlib_witness_still_rejected(name):
    mod = _load(name)
    good = zlib.compress(b'{"k":123}' * 64, 6)
    with pytest.raises(ValueError):
        mod._zlib_decompress_limited(good[: len(good) // 2], name="snap", max_out=100_000)


@pytest.mark.parametrize("name", _PROVERS)
def test_valid_zlib_witness_roundtrips(name):
    mod = _load(name)
    payload = b'{"hello":"world"}' * 16
    out = mod._zlib_decompress_limited(zlib.compress(payload, 6), name="snap", max_out=100_000)
    assert out == payload


@pytest.mark.parametrize("name", _PROVERS)
def test_oversized_decompression_rejected(name):
    mod = _load(name)
    big = zlib.compress(b"A" * 50_000, 9)
    with pytest.raises(ValueError):
        mod._zlib_decompress_limited(big, name="snap", max_out=1_000)
