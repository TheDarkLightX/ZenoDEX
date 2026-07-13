"""Cross-language vectors for the network state root (v5).

Proves the Rust core's `state_root::compute_state_root` (via the
`verify-state-root` CLI subcommand) agrees byte-for-byte with the authoritative
Python `src/state/state_root.py`, plus independent semantic properties of the
root itself (determinism, order-independence, sensitivity, rejection).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.state.pools import compute_pool_id  # noqa: E402
from tools.runtime import state_root_lib as lib  # noqa: E402

# --- Python authority: semantic properties (no Rust) --------------------------


def _pk(b):
    return "0x" + bytes([b] * 48).hex()


def _id(b):
    return "0x" + bytes([b] * 32).hex()


def test_empty_state_deterministic():
    r1 = lib.state_root_from_json({})
    r2 = lib.state_root_from_json({"balances": [], "pools": [], "nonces": []})
    assert r1 == r2
    assert r1.startswith("0x") and len(r1) == 66


def test_order_independent():
    a = {"balances": [
        {"pubkey": _pk(1), "asset": _id(9), "amount": 100},
        {"pubkey": _pk(2), "asset": _id(8), "amount": 200},
    ]}
    b = {"balances": [
        {"pubkey": _pk(2), "asset": _id(8), "amount": 200},
        {"pubkey": _pk(1), "asset": _id(9), "amount": 100},
    ]}
    assert lib.state_root_from_json(a) == lib.state_root_from_json(b)


def test_sensitive_to_amount():
    a = {"balances": [{"pubkey": _pk(1), "asset": _id(9), "amount": 100}]}
    b = {"balances": [{"pubkey": _pk(1), "asset": _id(9), "amount": 101}]}
    assert lib.state_root_from_json(a) != lib.state_root_from_json(b)


def test_sensitive_to_fee_accumulator_dust():
    a = {"fee_accumulator": {"dust": 0}}
    b = {"fee_accumulator": {"dust": 1}}
    assert lib.state_root_from_json(a) != lib.state_root_from_json(b)


def test_invalid_hex_rejected():
    with pytest.raises((ValueError, TypeError)):
        lib.state_root_from_json({"nonces": [{"pubkey": "0x1234", "last_nonce": 1}]})


# --- Rust/Python differential -------------------------------------------------


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.StateRootShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _assert_agrees(states, rust_bin):
    # Feed Rust the *normalized* serialization of the built Python state so the
    # Rust view reflects authority-side transforms (sparsity, canonicalization,
    # curve-param normalization). All such states are valid -> all accept.
    py = lib.py_eval_all(states)
    assert all(r["ok"] for r in py), [r for r in py if not r["ok"]]
    rust_inputs = [lib.to_rust_json(s) for s in states]
    rs = lib.run_rust(rust_bin, rust_inputs)
    problems = lib.diff_results(py, rs)
    assert not problems, "Python/Rust state-root mismatch:\n" + "\n".join(problems[:20])


def test_rust_matches_python_static(rust_bin):
    states = lib.static_states()
    py = lib.py_eval_all(states)
    # The static corpus is all well-formed -> all should compute a root.
    assert all(r["ok"] for r in py)
    # Distinct non-empty states should yield distinct roots (no accidental clashes).
    roots = {r["state_root"] for r in py}
    assert len(roots) == len(py)
    _assert_agrees(states, rust_bin)


@pytest.mark.parametrize("seed", [1, 5, 42, 20260529])
def test_rust_matches_python_randomized(rust_bin, seed):
    states = lib.random_states(seed=seed, n=250)
    _assert_agrees(states, rust_bin)


def test_rust_rejects_raw_noncanonical_authority_inputs(rust_bin):
    canonical_pool = {
        "pool_id": compute_pool_id(_id(2), _id(3), 30),
        "asset0": _id(2),
        "asset1": _id(3),
        "reserve0": 1,
        "reserve1": 1,
        "fee_bps": 30,
        "lp_supply": 0,
        "status": "active",
        "created_at": 0,
        "curve_tag": "CPMM",
        "curve_params": "",
    }
    states = [
        {"balances": [{"pubkey": _pk(1), "asset": _id(9), "amount": 0}]},
        {"lp_balances": [{"pubkey": _pk(1), "pool_id": _id(9), "amount": 0}]},
        {"pools": [{**canonical_pool, "asset0": _id(3), "asset1": _id(2)}]},
        {"pools": [{**canonical_pool, "curve_tag": "BOGUS_CURVE"}]},
        {"pools": [{**canonical_pool, "curve_tag": "cpmm"}]},
        {"pools": [{**canonical_pool, "curve_params": "{}"}]},
        {"pools": [{**canonical_pool, "pool_id": _id(1)}]},
        {
            "pools": [
                {
                    **canonical_pool,
                    "pool_id": "0x" + canonical_pool["pool_id"][2:].upper(),
                }
            ]
        },
        {
            "pools": [
                {
                    **canonical_pool,
                    "curve_tag": "QUARTIC_BLEND_V1",
                    "curve_params": '{"c_den":4,"c_num":2}',
                }
            ]
        },
        {"nonces": [{"pubkey": _pk(1), "last_nonce": 2**32}]},
        {
            "lp_duration_risk": [
                {
                    "pubkey": _pk(1),
                    "pool_id": _id(9),
                    "last_mint_timestamp": 5,
                    "last_remove_timestamp": None,
                    "churn_tier": 0,
                    "last_churn_update_timestamp": None,
                }
            ]
        },
    ]
    rs = lib.run_rust(rust_bin, states)
    assert all(not r["ok"] for r in rs), rs


def test_invalid_encodings_reject_on_both(rust_bin):
    states = [
        {"nonces": [{"pubkey": "0x1234", "last_nonce": 1}]},      # short pubkey
        {"balances": [{"pubkey": _pk(1), "asset": "0xzz" + "00" * 31, "amount": 1}]},  # bad hex
        {"pools": [{"pool_id": _id(1), "asset0": _id(2), "asset1": _id(3),
                    "reserve0": 1, "reserve1": 1, "fee_bps": 10001, "lp_supply": 0,
                    "status": "active", "created_at": 0, "curve_tag": "CPMM",
                    "curve_params": ""}]},                          # fee_bps > 10000
        {"pools": [{"pool_id": _id(1), "asset0": _id(2), "asset1": _id(3),
                    "reserve0": 1, "reserve1": 1, "fee_bps": 1, "lp_supply": 0,
                    "status": "bogus", "created_at": 0, "curve_tag": "CPMM",
                    "curve_params": ""}]},                          # unknown status
    ]
    py = lib.py_eval_all(states)
    rs = lib.run_rust(rust_bin, states)
    assert all(not r["ok"] for r in py), py
    assert all(not r["ok"] for r in rs), rs
    assert not lib.diff_results(py, rs)
