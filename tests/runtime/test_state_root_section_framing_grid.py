"""State-root v5 section-framing grid.

Kani covers scalar state-root guards, while full section encoding and SHA-256
remain outside that tractable slice. This test pins the pre-hash framing layer:
each one-hot logical section must affect exactly its own framed body, and Rust
must compute the same root for the same section cases.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
for _path in (str(REPO), str(TOOLS_RUNTIME)):
    if _path not in sys.path:
        sys.path.insert(0, _path)

from src.state.canonical import encode_uvarint, sha256_hex  # noqa: E402
from src.state.pools import compute_pool_id  # noqa: E402
from src.state.state_root import STATE_ROOT_SECTION_LABELS, state_root_preimage  # noqa: E402
from tools.runtime import state_root_lib as lib  # noqa: E402
from tools.runtime.state_root_injectivity import (  # noqa: E402
    decode_state_root_preimage,
    decode_uvarint,
)

PK = "0x" + "11" * 48
PK2 = "0x" + "22" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32
POOL = compute_pool_id(ASSET0, ASSET1, 30)


def _pool() -> dict:
    return {
        "pool_id": POOL,
        "asset0": ASSET0,
        "asset1": ASSET1,
        "reserve0": 7,
        "reserve1": 11,
        "fee_bps": 30,
        "lp_supply": 13,
        "status": "active",
        "created_at": 5,
        "curve_tag": "CPMM",
        "curve_params": "",
    }


def _one_hot_states() -> dict[bytes, dict]:
    return {
        b"BAL": {"balances": [{"pubkey": PK, "asset": ASSET0, "amount": 1}]},
        b"POL": {"pools": [_pool()]},
        b"LPB": {"lp_balances": [{"pubkey": PK, "pool_id": POOL, "amount": 1}]},
        b"LPA": {
            "lp_duration_risk": [
                {
                    "pubkey": PK,
                    "pool_id": POOL,
                    "last_mint_timestamp": None,
                    "last_remove_timestamp": 7,
                    "churn_tier": 1,
                    "last_churn_update_timestamp": 9,
                }
            ]
        },
        b"NNC": {"nonces": [{"pubkey": PK2, "last_nonce": 1}]},
        b"FEE": {"fee_accumulator": {"dust": 1}},
    }


def _preimage(state: dict) -> bytes:
    balances, pools, lp, nonces, fee_accumulator = lib.build_tables(state)
    return state_root_preimage(
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fee_accumulator,
    )


def _sections(state: dict) -> dict[bytes, bytes]:
    return decode_state_root_preimage(_preimage(state))


def _section_count(section_body: bytes) -> int:
    value, offset = decode_uvarint(section_body)
    assert offset == 1
    return value


def test_one_hot_sections_change_exactly_one_framed_body():
    empty_sections = _sections({})
    assert set(empty_sections) == set(STATE_ROOT_SECTION_LABELS)
    for label in STATE_ROOT_SECTION_LABELS:
        assert empty_sections[label] == encode_uvarint(0)

    for label, state in _one_hot_states().items():
        sections = _sections(state)
        changed = [candidate for candidate in STATE_ROOT_SECTION_LABELS if sections[candidate] != empty_sections[candidate]]
        assert changed == [label], (label, changed)
        if label == b"FEE":
            assert sections[label] == encode_uvarint(1)
        else:
            assert _section_count(sections[label]) == 1


def test_one_hot_roots_are_distinct_and_match_preimage_hash():
    states = [{}] + list(_one_hot_states().values())
    roots = []
    for state in states:
        preimage = _preimage(state)
        root = lib.state_root_from_json(state)
        assert root == sha256_hex(preimage)
        roots.append(root)
    assert len(set(roots)) == len(roots)


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return lib.locate_or_build_cli()
    except lib.StateRootShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"rust shadow unavailable: {exc}")


def test_one_hot_section_grid_matches_rust_state_root(rust_bin):
    states = [{}] + list(_one_hot_states().values())
    py = lib.py_eval_all(states)
    rust = lib.run_rust(rust_bin, states)
    assert all(item["ok"] for item in py), py
    assert all(item["ok"] for item in rust), rust
    assert not lib.diff_results(py, rust)
