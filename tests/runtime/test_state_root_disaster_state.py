"""Disaster-state / adversarial suite for the state-root v5 surface.

Criterion-4 (disaster-state) evidence for the promotion gate
(`docs/runtime/RUST_AUTHORITY_PROMOTION_GATE.md`). The existing
`test_state_root_vectors.py` already covers most rejection paths (duplicate
decoded keys, bad hex lengths, fee_bps > 10000, invalid scalars, reject-on-both)
and `test_state_root_determinism.py` covers order-independence + sensitivity, so
this suite deliberately targets the **gaps**:

1. the u128 / u32 domain boundaries at the Python↔Rust bridge, including the
   regression for SR-DRIFT-001;
2. the first end-to-end exercise of the authority selector over the state-root
   surface (agreement, root-stability, fail-closed on drift / disagreement /
   unavailable Rust).

SR-DRIFT-001 regression: Python's `NonceTable` rejects `last_nonce >= 2^32`.
The Rust state-root shadow now enforces the same bound. The existing randomized
differential caps nonces at `0xFFFFFFFF`, so this suite keeps the exact overflow
boundary covered.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    RustUnavailable,
    decide,
)
from tools.runtime import state_root_lib as lib  # noqa: E402

_PK = "0x" + bytes([1] * 48).hex()
_PK2 = "0x" + bytes([2] * 48).hex()
_ASSET = "0x" + bytes([0x10] * 32).hex()

U128_MAX = (1 << 128) - 1
U32_MAX = (1 << 32) - 1


# ==========================================================================
# Python authority — domain boundaries (always run)
# ==========================================================================

def test_python_accepts_u128_max_amount():
    st = {"balances": [{"pubkey": _PK, "asset": _ASSET, "amount": U128_MAX}]}
    assert lib.py_eval(0, st)["ok"] is True


def test_python_accepts_bignum_above_u128():
    # Python uses arbitrary-precision ints; encode_uvarint allows up to 256 bits.
    st = {"balances": [{"pubkey": _PK, "asset": _ASSET, "amount": 1 << 128}]}
    assert lib.py_eval(0, st)["ok"] is True


def test_python_rejects_nonce_at_or_above_u32():
    # NonceTable enforces a u32 bound.
    assert lib.py_eval(0, {"nonces": [{"pubkey": _PK, "last_nonce": U32_MAX}]})["ok"] is True
    assert lib.py_eval(0, {"nonces": [{"pubkey": _PK, "last_nonce": 1 << 32}]})["ok"] is False


def test_python_rejects_malformed_pubkey_and_hex():
    # Wrong-length pubkey (not 48 bytes), non-0x asset.
    bad_pk = "0x" + bytes([1] * 47).hex()
    assert lib.py_eval(0, {"balances": [{"pubkey": bad_pk, "asset": _ASSET, "amount": 1}]})["ok"] is False
    assert lib.py_eval(0, {"balances": [{"pubkey": _PK, "asset": "10" * 32, "amount": 1}]})["ok"] is False


def test_python_root_is_deterministic_and_order_independent():
    # Stale-snapshot replay: the same snapshot always yields the same root, and
    # entry order does not matter — so a verifier only sees a change on a real
    # state change, never on re-serialization.
    s1 = {"balances": [
        {"pubkey": _PK, "asset": _ASSET, "amount": 5},
        {"pubkey": _PK2, "asset": _ASSET, "amount": 9},
    ]}
    s2 = {"balances": [
        {"pubkey": _PK2, "asset": _ASSET, "amount": 9},
        {"pubkey": _PK, "asset": _ASSET, "amount": 5},
    ]}
    r1 = lib.state_root_from_json(s1)
    assert r1 == lib.state_root_from_json(s1)  # deterministic
    assert r1 == lib.state_root_from_json(s2)  # order-independent


# ==========================================================================
# Cross-language bridge boundaries (Python vs Rust shadow)
# ==========================================================================

@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.StateRootShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def test_u128_max_amount_agrees(rust_bin):
    st = [{"balances": [{"pubkey": _PK, "asset": _ASSET, "amount": U128_MAX}]}]
    py = lib.py_eval_all(st)
    rs = lib.run_rust(rust_bin, st)
    assert py[0]["ok"] and rs[0]["ok"]
    assert not lib.diff_results(py, rs)  # identical root at the in-domain max


def test_amount_above_u128_diverges_rust_is_stricter(rust_bin):
    # Documents the upper bridge boundary: Python accepts a bignum amount the
    # Rust u128 domain cannot represent, so Rust rejects (amount_out_of_domain).
    # The live domain must therefore stay <= 2^128 - 1.
    st = [{"balances": [{"pubkey": _PK, "asset": _ASSET, "amount": 1 << 128}]}]
    py = lib.py_eval_all(st)
    rs = lib.run_rust(rust_bin, st)
    assert py[0]["ok"] is True
    assert rs[0]["ok"] is False
    assert rs[0].get("code") in {"amount_out_of_domain", "amount_too_large"}


def test_nonce_u32_overflow_rejected_by_both(rust_bin):
    st = [{"nonces": [{"pubkey": _PK, "last_nonce": 1 << 32}]}]
    py = lib.py_eval_all(st)
    rs = lib.run_rust(rust_bin, st)
    assert py[0]["ok"] is False, "Python must reject an out-of-u32 nonce"
    assert rs[0]["ok"] is False, "Rust must reject the same out-of-u32 nonce"
    assert rs[0].get("code") == "nonce_too_large"
    assert not lib.diff_results(py, rs)


def test_mixed_case_pool_asset_order_and_self_pair_rejected_by_both(rust_bin):
    # Regression for A1/A2: Python now canonicalizes real asset IDs by decoded
    # bytes at ingress, matching the Rust commitment boundary. Mixed case can no
    # longer encode a Python-valid/Rust-invalid pool or a decoded self-pair.
    states = [
        {
            "pools": [
                {
                    "pool_id": "0x" + "44" * 32,
                    "asset0": "0x" + "0B" * 32,
                    "asset1": "0x" + "0a" * 32,
                    "reserve0": 500,
                    "reserve1": 700,
                    "fee_bps": 30,
                    "lp_supply": 600,
                    "status": "active",
                    "created_at": 12,
                    "curve_tag": "CPMM",
                    "curve_params": "",
                }
            ]
        },
        {
            "pools": [
                {
                    "pool_id": "0x" + "45" * 32,
                    "asset0": "0x" + "0A" * 32,
                    "asset1": "0x" + "0a" * 32,
                    "reserve0": 500,
                    "reserve1": 700,
                    "fee_bps": 30,
                    "lp_supply": 600,
                    "status": "active",
                    "created_at": 12,
                    "curve_tag": "CPMM",
                    "curve_params": "",
                }
            ]
        },
    ]
    py = lib.py_eval_all(states)
    rs = lib.run_rust(rust_bin, states)
    assert [r["ok"] for r in py] == [False, False]
    assert [r["ok"] for r in rs] == [False, False]
    assert not lib.diff_results(py, rs)


def test_raw_duplicate_balance_keys_rejected_by_rust(rust_bin):
    # Fed raw (bypassing the dedup in to_rust_json): two entries with the same
    # (pubkey, asset). The Rust decoder must reject duplicate decoded keys.
    st = [{"balances": [
        {"pubkey": _PK, "asset": _ASSET, "amount": 1},
        {"pubkey": _PK, "asset": _ASSET, "amount": 2},
    ]}]
    rs = lib.run_rust(rust_bin, st)
    assert rs[0]["ok"] is False
    assert rs[0].get("code")  # a stable reject code is present


# ==========================================================================
# Authority selector over the state-root surface (first real-surface wiring)
# ==========================================================================

def _no_diff(py_results, rust_results) -> bool:
    return not lib.diff_results(py_results, rust_results)


def _in_domain_states() -> list[dict]:
    return lib.static_states() + lib.random_states(seed=20260529, n=40)


def test_selector_rust_authority_with_shadow_agrees_in_domain(rust_bin):
    states = _in_domain_states()
    d = decide(
        "state_root",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=lambda: lib.py_eval_all(states),
        rust_fn=lambda: lib.run_rust(rust_bin, states),
        compare=_no_diff,
    )
    assert d.authority == "rust"
    assert d.agreed is True


def test_selector_root_unchanged_across_modes(rust_bin):
    states = _in_domain_states()
    d_py = decide(
        "state_root",
        AuthorityMode.PYTHON_AUTHORITY,
        python_fn=lambda: lib.py_eval_all(states),
    )
    d_shadow = decide(
        "state_root",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=lambda: lib.py_eval_all(states),
        rust_fn=lambda: lib.run_rust(rust_bin, states),
        compare=_no_diff,
    )
    # Every committed root is identical under both authority modes.
    assert _no_diff(d_py.result, d_shadow.result)


def test_selector_rust_authority_with_shadow_rejects_nonce_overflow_in_agreement(rust_bin):
    overflow = [{"nonces": [{"pubkey": _PK, "last_nonce": 1 << 32}]}]
    d = decide(
        "state_root",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=lambda: lib.py_eval_all(overflow),
        rust_fn=lambda: lib.run_rust(rust_bin, overflow),
        compare=_no_diff,
    )
    assert d.authority == "rust"
    assert d.agreed is True
    assert d.result[0]["ok"] is False


def test_selector_fails_closed_on_injected_disagreement(rust_bin):
    states = [lib.static_states()[1]]  # a non-empty balances state

    def tampered_rust():
        out = lib.run_rust(rust_bin, states)
        out[0] = {**out[0], "state_root": "0x" + "00" * 32}
        return out

    with pytest.raises(AuthorityError):
        decide(
            "state_root",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=lambda: lib.py_eval_all(states),
            rust_fn=tampered_rust,
            compare=_no_diff,
        )


def test_selector_fails_closed_when_rust_unavailable_under_authority():
    states = [lib.static_states()[0]]

    def rust_missing():
        raise RustUnavailable("not built")

    with pytest.raises(AuthorityError):
        decide(
            "state_root",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=lambda: lib.py_eval_all(states),
            rust_fn=rust_missing,
            compare=_no_diff,
        )
