"""Disaster-state / adversarial suite for the canonical-primitives surface.

This is the criterion-4 (disaster-state) evidence the promotion gate
(`docs/runtime/RUST_AUTHORITY_PROMOTION_GATE.md`) requires before the canonical
surface can move from Python authority to Rust authority. It complements the
happy-path differential in `test_canonical_primitives_vectors.py` with:

* authority-side adversarial invariants (run on Python alone): malformed input,
  overflow/underflow, surrogate rejection, domain-sep validation, determinism /
  canonical-normalization, and purity (no mutation on reject);
* a cross-language *disaster* differential (Python vs the Rust shadow) over an
  adversarial corpus — agreement on the hard cases, not just the easy ones;
* the first end-to-end exercise of the authority selector over a real surface:
  `rust_authority_with_python_shadow` must agree, fail closed on injected
  disagreement, and fail closed when the Rust engine is unavailable; and the
  canonical hash (this surface's state-root contribution) is identical whether
  Python or Rust is authoritative.

Canonical primitives are stateless pure functions, so the stateful disaster
rows (copied-tx replay, stale snapshot, duplicate IDs, unauthorized mutation)
do not apply; the applicable rows are malformed-bytes, overflow/underflow,
determinism, and no-op/purity, all covered here.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.state import canonical as c  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    RustUnavailable,
    decide,
)
from tools.runtime import canonical_primitives_lib as lib  # noqa: E402


# ==========================================================================
# Authority-side adversarial invariants (Python alone — always run)
# ==========================================================================

def test_uvarint_overflow_and_underflow():
    # 256-bit boundary is the documented limit (MAX_UVARINT_BITS).
    assert c.encode_uvarint(2 ** 256 - 1)  # exactly at the limit: accepted
    with pytest.raises(ValueError):
        c.encode_uvarint(2 ** 256)  # one bit over → reject
    with pytest.raises(ValueError):
        c.encode_uvarint(-1)  # underflow → reject
    with pytest.raises(ValueError):
        c.encode_uvarint(-(2 ** 64))


def test_uvarint_is_deterministic():
    for v in [0, 1, 127, 128, 255, 256, 2 ** 64, 2 ** 200, 2 ** 256 - 1]:
        assert c.encode_uvarint(v) == c.encode_uvarint(v)


def test_hex_to_bytes_malformed_inputs():
    # Wrong prefix casing, missing prefix, non-str, zero nbytes, wrong length,
    # invalid hex chars, odd nibble count.
    with pytest.raises(ValueError):
        c.hex_to_bytes_fixed("0X00", nbytes=1, name="x")  # uppercase 0X rejected
    with pytest.raises(ValueError):
        c.hex_to_bytes_fixed("00", nbytes=1, name="x")  # no 0x prefix
    with pytest.raises(TypeError):
        c.hex_to_bytes_fixed(b"0x00", nbytes=1, name="x")  # bytes, not str
    with pytest.raises(ValueError):
        c.hex_to_bytes_fixed("0x", nbytes=0, name="x")  # nbytes must be positive
    with pytest.raises(ValueError):
        c.hex_to_bytes_fixed("0x0102", nbytes=1, name="x")  # too long for nbytes
    with pytest.raises(ValueError):
        c.hex_to_bytes_fixed("0x01", nbytes=2, name="x")  # too short for nbytes
    with pytest.raises(ValueError):
        c.hex_to_bytes_fixed("0xzz", nbytes=1, name="x")  # invalid hex chars
    with pytest.raises(ValueError):
        c.hex_to_bytes_fixed("0x012", nbytes=2, name="x")  # odd nibble count


def test_json_rejects_surrogates_and_floats_at_depth():
    with pytest.raises(TypeError):
        c.canonical_json_bytes("\ud800")  # lone surrogate
    with pytest.raises(TypeError):
        c.canonical_json_bytes({"k": "\udfff"})  # surrogate in value
    with pytest.raises(TypeError):
        c.canonical_json_bytes({"a": [{"b": 1.0}]})  # float nested deep
    with pytest.raises(TypeError):
        c.canonical_json_bytes([1, [2, [3.5]]])  # float deeper still


def test_json_bool_is_not_a_float():
    # bool is an int subclass; canonical encoding must keep it as a JSON bool.
    assert c.canonical_json_bytes(True) == b"true"
    assert c.canonical_json_bytes(False) == b"false"
    assert c.canonical_json_bytes({"flag": True}) == b'{"flag":true}'


def test_domain_sep_validation():
    with pytest.raises(TypeError):
        c.domain_sep_bytes("", 1)  # empty label
    with pytest.raises(ValueError):
        c.domain_sep_bytes("a\x00b", 1)  # NUL in label
    with pytest.raises(ValueError):
        c.domain_sep_bytes("é", 1)  # non-ASCII label
    with pytest.raises(ValueError):
        c.domain_sep_bytes("x", 0)  # version must be positive
    with pytest.raises(ValueError):
        c.domain_sep_bytes("x", -1)
    # Valid is deterministic.
    assert c.domain_sep_bytes("state_root", 5) == c.domain_sep_bytes("state_root", 5)


def test_json_canonical_normalization_is_order_independent():
    # Key order must not affect canonical bytes (the normalization property).
    a = c.canonical_json_bytes({"a": 1, "b": 2, "c": 3})
    b = c.canonical_json_bytes({"c": 3, "a": 1, "b": 2})
    assert a == b == b'{"a":1,"b":2,"c":3}'
    # Nested objects normalize too.
    x = c.canonical_json_bytes({"z": {"q": 1, "p": 2}, "a": 0})
    y = c.canonical_json_bytes({"a": 0, "z": {"p": 2, "q": 1}})
    assert x == y


def test_json_is_pure_no_mutation():
    payload = {"b": 2, "a": 1, "nested": {"y": 1, "x": 2}}
    before = repr(payload)
    c.canonical_json_bytes(payload)
    assert repr(payload) == before  # input object untouched


def test_bignum_json_is_exact_beyond_u128():
    # The drift trap: values above u128 must encode exactly, not wrap.
    assert c.canonical_json_bytes(2 ** 130 + 7) == str(2 ** 130 + 7).encode()
    assert c.canonical_json_bytes(-(2 ** 200)) == str(-(2 ** 200)).encode()


# ==========================================================================
# Cross-language disaster differential (Python vs Rust shadow)
# ==========================================================================

@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.CanonicalShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _disaster_cases() -> list[dict]:
    """Adversarial json + hex cases that exercise the hard paths."""
    return [
        # bignum json (drift trap)
        {"op": "json_bytes", "value": 2 ** 256 - 1},
        {"op": "json_hash", "value": 2 ** 256 + 1},
        {"op": "json_bytes", "value": -(2 ** 200)},
        # control chars + escaping
        {"op": "json_bytes", "value": "\n\t\r\"\\\b\f"},
        {"op": "json_bytes", "value": "\x00\x01\x1f"},
        # empty containers + deep nesting
        {"op": "json_bytes", "value": {}},
        {"op": "json_bytes", "value": []},
        {"op": "json_bytes", "value": [[[[[[]]]]]]},
        {"op": "json_hash", "value": {"a": {"b": {"c": {"d": []}}}}},
        # key-order normalization (must hash identically)
        {"op": "json_hash", "value": {"a": 1, "b": 2, "c": 3}},
        {"op": "json_hash", "value": {"c": 3, "b": 2, "a": 1}},
        # float rejections (reject agreement)
        {"op": "json_bytes", "value": 1.0},
        {"op": "json_bytes", "value": [1, {"x": 2.5}]},
        # hex boundaries / malformed
        {"op": "hex_to_bytes", "hex": "0x", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0X00", "nbytes": 1},
        {"op": "hex_to_bytes", "hex": "0x012", "nbytes": 2},
        {"op": "hex_to_bytes", "hex": "0x" + "ff" * 48, "nbytes": 48},
        {"op": "hex_to_bytes", "hex": "0x" + "00" * 32, "nbytes": 32},
        {"op": "hex_to_bytes", "hex": "0xGG", "nbytes": 1},
    ]


def test_disaster_corpus_agrees(rust_bin):
    cases = _disaster_cases()
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, cases)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust disaster mismatch:\n" + "\n".join(problems[:20])
    # The corpus must actually exercise both accept and reject.
    assert any(r["ok"] for r in py) and any(not r["ok"] for r in py)


def test_key_order_hashes_identically_cross_language(rust_bin):
    cases = [
        {"op": "json_hash", "value": {"a": 1, "b": 2, "c": 3}},
        {"op": "json_hash", "value": {"c": 3, "b": 2, "a": 1}},
    ]
    py = lib.py_eval_all(cases)
    rs = lib.run_rust(rust_bin, cases)
    assert py[0]["hash"] == py[1]["hash"]  # normalization (Python)
    assert rs[0]["hash"] == rs[1]["hash"]  # normalization (Rust)
    assert py[0]["hash"] == rs[0]["hash"]  # cross-language agreement


# ==========================================================================
# Authority selector over the canonical surface (first real-surface wiring)
# ==========================================================================

def _no_diff(py_results, rust_results) -> bool:
    return not lib.diff_results(py_results, rust_results)


def test_selector_rust_authority_with_shadow_agrees(rust_bin):
    cases = _disaster_cases()
    d = decide(
        "canonical",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=lambda: lib.py_eval_all(cases),
        rust_fn=lambda: lib.run_rust(rust_bin, cases),
        compare=_no_diff,
    )
    assert d.authority == "rust"
    assert d.shadow_checked is True
    assert d.agreed is True
    # Root-stability analog: the canonical hash (this surface's state-root
    # contribution) is identical whether Python or Rust is authoritative.
    py = lib.py_eval_all(cases)
    for rust_case, py_case in zip(d.result, py):
        if rust_case["ok"] and "hash" in rust_case:
            assert rust_case["hash"] == py_case["hash"]


def test_selector_state_root_contribution_unchanged_across_modes(rust_bin):
    cases = _disaster_cases()
    d_py = decide(
        "canonical",
        AuthorityMode.PYTHON_AUTHORITY,
        python_fn=lambda: lib.py_eval_all(cases),
    )
    d_shadow = decide(
        "canonical",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=lambda: lib.py_eval_all(cases),
        rust_fn=lambda: lib.run_rust(rust_bin, cases),
        compare=_no_diff,
    )
    # Same canonical bytes/hash under both authority modes (root-preserving).
    assert _no_diff(d_py.result, d_shadow.result)


def test_selector_fails_closed_on_injected_disagreement(rust_bin):
    cases = [{"op": "json_hash", "value": {"a": 1}}]

    def tampered_rust():
        out = lib.run_rust(rust_bin, cases)
        out[0] = {**out[0], "hash": "0xdeadbeef"}  # corrupt the result
        return out

    with pytest.raises(AuthorityError):
        decide(
            "canonical",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=lambda: lib.py_eval_all(cases),
            rust_fn=tampered_rust,
            compare=_no_diff,
        )


def test_selector_fails_closed_when_rust_unavailable_under_authority():
    cases = [{"op": "json_hash", "value": {"a": 1}}]

    def rust_missing():
        raise RustUnavailable("not built")

    with pytest.raises(AuthorityError):
        decide(
            "canonical",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=lambda: lib.py_eval_all(cases),
            rust_fn=rust_missing,
            compare=_no_diff,
        )


def test_selector_rust_shadow_skips_when_unavailable():
    # In rust_shadow mode an unavailable engine is benign: Python stays authority.
    cases = [{"op": "json_hash", "value": {"a": 1}}]

    def rust_missing():
        raise RustUnavailable("not built")

    d = decide(
        "canonical",
        AuthorityMode.RUST_SHADOW,
        python_fn=lambda: lib.py_eval_all(cases),
        rust_fn=rust_missing,
        compare=_no_diff,
    )
    assert d.authority == "python"
    assert d.shadow_checked is False
