"""Deterministic fuzz gate for Rust authority promotion of state-root v5."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from tools.runtime import state_root_lib as lib  # noqa: E402


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.StateRootShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def _pk(byte: int) -> str:
    return "0x" + bytes([byte] * 48).hex()


def _asset(byte: int) -> str:
    return "0x" + bytes([byte] * 32).hex()


def _invalid_states() -> list[dict]:
    pk = _pk(1)
    asset = _asset(2)
    pool = _asset(60)
    return [
        {"balances": [{"pubkey": "0x1234", "asset": asset, "amount": 1}]},
        {"balances": [{"pubkey": pk, "asset": "0xzz" + "00" * 31, "amount": 1}]},
        {"balances": [{"pubkey": pk, "asset": asset, "amount": -1}]},
        {"balances": [{"pubkey": pk, "asset": asset, "amount": True}]},
        {
            "pools": [
                {
                    "pool_id": pool,
                    "asset0": _asset(1),
                    "asset1": _asset(2),
                    "reserve0": 1,
                    "reserve1": 1,
                    "fee_bps": 10001,
                    "lp_supply": 1,
                    "status": "active",
                    "created_at": 0,
                    "curve_tag": "CPMM",
                    "curve_params": "",
                }
            ]
        },
        {
            "pools": [
                {
                    "pool_id": pool,
                    "asset0": _asset(1),
                    "asset1": _asset(2),
                    "reserve0": 1,
                    "reserve1": 1,
                    "fee_bps": 1,
                    "lp_supply": 1,
                    "status": "bogus",
                    "created_at": 0,
                    "curve_tag": "CPMM",
                    "curve_params": "",
                }
            ]
        },
        {"nonces": [{"pubkey": pk, "last_nonce": 1 << 32}]},
        {"fee_accumulator": {"dust": -1}},
        {"fee_accumulator": []},
    ]


def test_state_root_v5_fuzz_gate_valid_states_agree(rust_bin):
    states: list[dict] = []
    for seed in (2, 9, 17, 101, 20260530, 424242):
        states.extend(lib.random_states(seed=seed, n=220))

    py = lib.py_eval_all(states)
    rust_inputs = [lib.to_rust_json(state) for state in states]
    rs = lib.run_rust(rust_bin, rust_inputs)
    problems = lib.diff_results(py, rs)

    assert len(states) == 1_320
    assert all(row["ok"] for row in py)
    assert not problems, "Python/Rust state-root fuzz mismatch:\n" + "\n".join(problems[:20])


def test_state_root_v5_fuzz_gate_rejects_invalid_states_on_both(rust_bin):
    states = _invalid_states()
    py = lib.py_eval_all(states)
    rs = lib.run_rust(rust_bin, states)

    assert all(not row["ok"] for row in py), py
    assert all(not row["ok"] for row in rs), rs
    assert not lib.diff_results(py, rs)


def test_state_root_v5_fuzz_generator_is_deterministic():
    assert lib.random_states(seed=20260530, n=25) == lib.random_states(seed=20260530, n=25)
