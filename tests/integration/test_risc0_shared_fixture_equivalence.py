from __future__ import annotations

import hashlib
import math

import pytest

from src.core.cpmm import MIN_LP_LOCK, compute_fee_total, swap_exact_in
from src.core.liquidity import create_pool
from src.state.canonical import canonical_json_bytes
from src.state.pools import compute_pool_id


ASSET0 = "0x" + "11" * 32
ASSET1 = "0x" + "22" * 32
SENDER = "0x" + "aa" * 48
RECIPIENT = "0x" + "bb" * 48
LP_LOCK_PUBKEY = "0x" + "00" * 48
POOL_ID = "0xcc9c112f06b5ba4cd276419759e7b3e203ede2c64aa45ba75e24fa4609d9c686"


def _snapshot_hash(snapshot: dict) -> str:
    return hashlib.sha256(canonical_json_bytes(snapshot)).hexdigest()


def _empty_snapshot() -> dict:
    return {
        "version": 1,
        "balances": [],
        "pools": [],
        "lp_balances": [],
        "fee_accumulator": {"dust": 0},
        "vault": None,
        "oracle": None,
    }


def _pool_entry(*, reserve0: int, reserve1: int) -> dict:
    return {
        "pool_id": POOL_ID,
        "asset0": ASSET0,
        "asset1": ASSET1,
        "reserve0": reserve0,
        "reserve1": reserve1,
        "fee_bps": 30,
        "lp_supply": 10_000,
        "status": "ACTIVE",
        "created_at": 0,
    }


def test_risc0_shared_fixture_pool_id_matches_python_core() -> None:
    assert compute_pool_id(ASSET0, ASSET1, 30, curve_tag="CPMM", curve_params="") == POOL_ID


def test_risc0_shared_fixture_pool_id_normalizes_hex_asset_id_case() -> None:
    lower0 = "0x" + "aa" * 32
    lower1 = "0x" + "bb" * 32
    mixed0 = "0x" + "Aa" * 32
    mixed1 = "0x" + "Bb" * 32

    assert compute_pool_id(mixed0, mixed1, 30, curve_tag="CPMM", curve_params="") == compute_pool_id(
        lower0,
        lower1,
        30,
        curve_tag="CPMM",
        curve_params="",
    )


def test_risc0_shared_fixture_create_pool_rejects_canonical_equal_hex_asset_ids() -> None:
    asset0 = "0x" + "Aa" * 32
    asset1 = "0x" + "aa" * 32
    assert asset0 < asset1

    with pytest.raises(ValueError, match="canonical order"):
        create_pool(
            asset0=asset0,
            asset1=asset1,
            amount0=10_000,
            amount1=10_000,
            fee_bps=30,
            creator_pubkey=SENDER,
        )


def test_risc0_shared_fixture_create_pool_math_matches_python_core() -> None:
    lp_supply_total = math.isqrt(10_000 * 10_000)
    assert MIN_LP_LOCK == 1_000
    assert lp_supply_total == 10_000
    assert lp_supply_total - MIN_LP_LOCK == 9_000

    pre = _empty_snapshot()
    pre["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 10_000},
        {"pubkey": SENDER, "asset": ASSET1, "amount": 20_000},
    ]
    assert _snapshot_hash(pre) == "9fcb79d0240177f11f37905ed608fca2dc60b907a0d8de157ff68a22db2874e4"

    post = _empty_snapshot()
    post["balances"] = [
        {"pubkey": SENDER, "asset": ASSET1, "amount": 10_000},
    ]
    post["pools"] = [_pool_entry(reserve0=10_000, reserve1=10_000)]
    post["lp_balances"] = [
        {"pubkey": LP_LOCK_PUBKEY, "pool_id": POOL_ID, "amount": 1_000},
        {"pubkey": SENDER, "pool_id": POOL_ID, "amount": 9_000},
    ]
    assert _snapshot_hash(post) == "cdedb50a4a2388af0f479062e0ea6d5288b7c460b55237c419b46fc5dd7b6f75"


def test_risc0_shared_fixture_insufficient_initial_liquidity_rejects_in_python_core() -> None:
    with pytest.raises(ValueError, match="insufficient initial liquidity"):
        create_pool(
            asset0=ASSET0,
            asset1=ASSET1,
            amount0=1_000,
            amount1=1_000,
            fee_bps=30,
            creator_pubkey=SENDER,
        )


def test_risc0_shared_fixture_swap_exact_in_matches_python_core() -> None:
    assert compute_fee_total(1_000, 30) == 3
    amount_out, reserves = swap_exact_in(10_000, 10_000, 1_000, 30)
    assert amount_out == 906
    assert reserves == (11_000, 9_094)

    pre = _empty_snapshot()
    pre["balances"] = [
        {"pubkey": SENDER, "asset": ASSET0, "amount": 1_000},
    ]
    pre["pools"] = [_pool_entry(reserve0=10_000, reserve1=10_000)]
    assert _snapshot_hash(pre) == "daa4d1cdf1f5082e87030c1a2962de376d05c4e73bab26e8c2857520be699d02"

    post = _empty_snapshot()
    post["balances"] = [
        {"pubkey": RECIPIENT, "asset": ASSET1, "amount": 906},
    ]
    post["pools"] = [_pool_entry(reserve0=11_000, reserve1=9_094)]
    assert _snapshot_hash(post) == "168c616c3e9cbc832f9accf6022fcf5153f4611de71115e36a6e540a1230101b"


def test_risc0_shared_fixture_zero_output_swap_rejects_in_python_core() -> None:
    with pytest.raises(ValueError, match="amount_out is zero"):
        swap_exact_in(10_000, 10_000, 2, 30)
