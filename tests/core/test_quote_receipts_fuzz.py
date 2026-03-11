from __future__ import annotations

import copy
import importlib.util
from typing import Any

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import assume, given, settings

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.quote_receipts import pool_state_fingerprint, receipt_hash, verify_route_quote_receipt
from src.state.pools import PoolState, PoolStatus

ALPHABET = "abcdefghijklmnopqrstuvwxyz0123456789_-"
TEXT = st.text(ALPHABET, min_size=0, max_size=16)
NON_EMPTY_TEXT = st.text(ALPHABET, min_size=1, max_size=16)

JSON_VALUE: st.SearchStrategy[Any] = st.recursive(
    st.none() | st.booleans() | st.integers(min_value=-1000, max_value=1000) | TEXT,
    lambda child: st.lists(child, max_size=3) | st.dictionaries(NON_EMPTY_TEXT, child, max_size=3),
    max_leaves=12,
)


def _pool(pool_id: str, reserve0: int, reserve1: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


@st.composite
def _valid_single_hop_receipt(draw: st.DrawFn) -> tuple[dict[str, Any], dict[str, PoolState]]:
    pool = _pool(
        pool_id=draw(NON_EMPTY_TEXT),
        reserve0=draw(st.integers(min_value=100, max_value=20_000)),
        reserve1=draw(st.integers(min_value=100, max_value=20_000)),
        fee_bps=draw(st.integers(min_value=0, max_value=100)),
    )
    kind = draw(st.sampled_from(["exact_in", "exact_out"]))
    forward = draw(st.booleans())
    asset_in = "A" if forward else "B"
    asset_out = "B" if forward else "A"
    reserve_in = int(pool.reserve0) if forward else int(pool.reserve1)
    reserve_out = int(pool.reserve1) if forward else int(pool.reserve0)
    if kind == "exact_in":
        valid_quotes: list[tuple[int, int]] = []
        for candidate_amount_in in range(1, min(256, reserve_in) + 1):
            try:
                amount_out, _ = swap_exact_in_for_pool(
                    pool,
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=candidate_amount_in,
                )
            except ValueError:
                continue
            valid_quotes.append((candidate_amount_in, int(amount_out)))
        assume(valid_quotes)
        amount_in, amount_out = draw(st.sampled_from(valid_quotes))
    else:
        valid_quotes = []
        for candidate_amount_out in range(1, min(64, reserve_out - 1) + 1):
            try:
                amount_in, _ = swap_exact_out_for_pool(
                    pool,
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_out=candidate_amount_out,
                )
            except ValueError:
                continue
            valid_quotes.append((int(amount_in), candidate_amount_out))
        assume(valid_quotes)
        amount_in, amount_out = draw(st.sampled_from(valid_quotes))

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": kind,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": int(amount_in),
        "amount_out": int(amount_out),
        "legs": [
            {
                "amount_in": int(amount_in),
                "amount_out": int(amount_out),
                "hops": [
                    {
                        "pool_id": pool.pool_id,
                        "asset_in": asset_in,
                        "asset_out": asset_out,
                        "amount_in": int(amount_in),
                        "amount_out": int(amount_out),
                    }
                ],
            }
        ],
        "pools": {
            pool.pool_id: pool_state_fingerprint(pool),
        },
    }
    receipt = {"body": body, "receipt_hash": receipt_hash(body)}
    return receipt, {pool.pool_id: pool}


@given(case=_valid_single_hop_receipt())
@settings(max_examples=50, deadline=None, derandomize=True)
def test_verify_route_quote_receipt_accepts_generated_single_hop_receipts(
    case: tuple[dict[str, Any], dict[str, PoolState]]
) -> None:
    receipt, pools = case
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    assert ok is True
    assert err == "ok"


@given(case=_valid_single_hop_receipt(), mutation=st.sampled_from(["hash", "pool_fingerprint", "hop_amount", "body_total"]))
@settings(max_examples=60, deadline=None, derandomize=True)
def test_verify_route_quote_receipt_fail_closes_on_mutated_receipt_fields(
    case: tuple[dict[str, Any], dict[str, PoolState]],
    mutation: str,
) -> None:
    receipt, pools = case
    mutated = copy.deepcopy(receipt)
    pool_id = next(iter(pools))
    if mutation == "hash":
        mutated["receipt_hash"] = str(mutated["receipt_hash"]) + "x"
    elif mutation == "pool_fingerprint":
        mutated["body"]["pools"][pool_id] = str(mutated["body"]["pools"][pool_id]) + "stale"
        mutated["receipt_hash"] = receipt_hash(mutated["body"])
    elif mutation == "hop_amount":
        mutated["body"]["legs"][0]["hops"][0]["amount_out"] += 1
        mutated["receipt_hash"] = receipt_hash(mutated["body"])
    else:
        mutated["body"]["amount_out"] += 1
        mutated["receipt_hash"] = receipt_hash(mutated["body"])
    ok, err = verify_route_quote_receipt(mutated, pools_by_id=pools)
    assert ok is False
    assert err != "ok"


@given(receipt=JSON_VALUE)
@settings(max_examples=80, deadline=None, derandomize=True)
def test_verify_route_quote_receipt_fuzz_never_raises_on_malformed_receipts(receipt: Any) -> None:
    ok, err = verify_route_quote_receipt(receipt, pools_by_id={})
    assert isinstance(ok, bool)
    assert isinstance(err, str)
    if ok:
        assert err == "ok"
    else:
        assert err != "ok"


@given(case=_valid_single_hop_receipt(), bad_amount=st.one_of(st.none(), st.booleans(), TEXT, st.lists(st.integers(), max_size=2), st.dictionaries(NON_EMPTY_TEXT, TEXT, max_size=2)))
@settings(max_examples=40, deadline=None, derandomize=True)
def test_verify_route_quote_receipt_rejects_non_integer_amount_fields_with_explicit_codes(
    case: tuple[dict[str, Any], dict[str, PoolState]],
    bad_amount: Any,
) -> None:
    receipt, pools = case

    bad_body = copy.deepcopy(receipt)
    bad_body["body"]["amount_in"] = bad_amount
    bad_body["receipt_hash"] = receipt_hash(bad_body["body"])
    assert verify_route_quote_receipt(bad_body, pools_by_id=pools) == (False, "bad_body_amounts")

    bad_leg = copy.deepcopy(receipt)
    bad_leg["body"]["legs"][0]["amount_in"] = bad_amount
    bad_leg["receipt_hash"] = receipt_hash(bad_leg["body"])
    assert verify_route_quote_receipt(bad_leg, pools_by_id=pools) == (False, "bad_leg_amounts")

    bad_hop = copy.deepcopy(receipt)
    bad_hop["body"]["legs"][0]["hops"][0]["amount_in"] = bad_amount
    bad_hop["receipt_hash"] = receipt_hash(bad_hop["body"])
    assert verify_route_quote_receipt(bad_hop, pools_by_id=pools) == (False, "bad_hop_amounts")
