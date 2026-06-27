# [TESTER] v1
"""
Unit tests for src/core/route_settlement.py (functional core contracts).

The engine matrix lives in tests/integration/test_dex_engine_route_settlement.py;
these tests pin the module-level parsing/validation/replay contracts against
adversarial shapes.
"""

from __future__ import annotations

import pytest

import src.core.route_settlement as route_settlement
from src.core.quote_receipts import make_route_quote_receipt, pool_state_fingerprint
from src.core.route_settlement import (
    ROUTE_REJECT_LEG_QUOTE_MISMATCH,
    ROUTE_REJECT_POOL_NOT_ACTIVE,
    ROUTE_REJECT_POOL_NOT_FOUND,
    ROUTE_REJECT_POOL_STATE_DRIFT,
    RouteBinding,
    RouteLegBinding,
    parse_route_binding_fields,
    replay_route_legs,
    resolve_route_binding_from_receipt,
    route_binding_to_fields,
    validate_route_intent_against_binding,
)
from src.core.routing import best_route_exact_in_2hop
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus

SENDER = "0x" + "ab" * 48


def _pool(pool_id: str, *, r0: int = 1_000, r1: int = 1_000, fee_bps: int = 0, status: PoolStatus = PoolStatus.ACTIVE) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=r0,
        reserve1=r1,
        fee_bps=fee_bps,
        lp_supply=1,
        status=status,
        created_at=0,
    )


def _binding_for(pools: dict) -> RouteBinding:
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=600)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools)
    binding, err = resolve_route_binding_from_receipt(receipt)
    assert binding is not None, err
    return binding


def _route_intent_fields(binding: RouteBinding, **overrides) -> Intent:
    fields = {
        "quote_receipt_hash": "0x" + "11" * 32,
        "asset_in": binding.asset_in,
        "asset_out": binding.asset_out,
        "leg_indices": list(range(len(binding.legs))),
        "total_amount_in": int(binding.total_amount_in),
        "total_min_amount_out": 0,
        "nonce": 1,
    }
    fields.update(overrides)
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ROUTE_EXACT_IN,
        intent_id="0x" + "22" * 32,
        sender_pubkey=SENDER,
        deadline=9999999999,
        fields=fields,
    )


# ---------------------------------------------------------------------------
# resolve_route_binding_from_receipt
# ---------------------------------------------------------------------------


def test_resolve_binding_round_trips_receipt_legs() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    assert binding.kind == "exact_in"
    assert binding.asset_in == "A" and binding.asset_out == "B"
    assert len(binding.legs) == 2
    assert binding.total_amount_in == sum(leg.amount_in for leg in binding.legs)
    assert binding.total_amount_out == sum(leg.amount_out for leg in binding.legs)
    assert set(binding.pool_fingerprints) == {"p1", "p2"}
    for pool_id, fp in binding.pool_fingerprints.items():
        assert fp == pool_state_fingerprint(pools[pool_id])


def test_resolve_binding_rejects_non_object_and_missing_body() -> None:
    assert resolve_route_binding_from_receipt(None)[1] == "route_receipt_not_object"
    assert resolve_route_binding_from_receipt({})[1] == "route_receipt_missing_body"
    assert resolve_route_binding_from_receipt({"body": []})[1] == "route_receipt_missing_body"


def test_resolve_binding_rejects_multi_hop_legs() -> None:
    body = {
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
        "amount_out": 9,
        "legs": [
            {
                "amount_in": 10,
                "amount_out": 9,
                "hops": [
                    {"pool_id": "pax", "asset_in": "A", "asset_out": "X", "amount_in": 10, "amount_out": 10},
                    {"pool_id": "pxb", "asset_in": "X", "asset_out": "B", "amount_in": 10, "amount_out": 9},
                ],
            }
        ],
        "pools": {"pax": "fp", "pxb": "fp"},
    }
    binding, err = resolve_route_binding_from_receipt({"body": body})
    assert binding is None
    assert err == "route_multi_hop_leg_unsupported"


def test_resolve_binding_rejects_totals_mismatch() -> None:
    body = {
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 11,  # legs sum to 10
        "amount_out": 9,
        "legs": [
            {
                "amount_in": 10,
                "amount_out": 9,
                "hops": [
                    {"pool_id": "p1", "asset_in": "A", "asset_out": "B", "amount_in": 10, "amount_out": 9}
                ],
            }
        ],
        "pools": {"p1": "fp"},
    }
    binding, err = resolve_route_binding_from_receipt({"body": body})
    assert binding is None
    assert err == "route_receipt_totals_mismatch"


def test_resolve_binding_rejects_missing_pool_fingerprint() -> None:
    body = {
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
        "amount_out": 9,
        "legs": [
            {
                "amount_in": 10,
                "amount_out": 9,
                "hops": [
                    {"pool_id": "p1", "asset_in": "A", "asset_out": "B", "amount_in": 10, "amount_out": 9}
                ],
            }
        ],
        "pools": {},
    }
    binding, err = resolve_route_binding_from_receipt({"body": body})
    assert binding is None
    assert err == "route_receipt_missing_pool_fingerprint"


def test_resolve_binding_rejects_bool_amounts() -> None:
    body = {
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
        "amount_out": 9,
        "legs": [
            {
                "amount_in": True,
                "amount_out": 9,
                "hops": [
                    {"pool_id": "p1", "asset_in": "A", "asset_out": "B", "amount_in": True, "amount_out": 9}
                ],
            }
        ],
        "pools": {"p1": "fp"},
    }
    binding, err = resolve_route_binding_from_receipt({"body": body})
    assert binding is None
    assert err == "route_receipt_bad_hop_amounts"


# ---------------------------------------------------------------------------
# route_binding_to_fields / parse_route_binding_fields round trip
# ---------------------------------------------------------------------------


def test_binding_fields_round_trip() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    intent = _route_intent_fields(binding, **route_binding_to_fields(binding))
    parsed, err = parse_route_binding_fields(intent)
    assert parsed is not None, err
    assert parsed.legs == binding.legs
    assert dict(parsed.pool_fingerprints) == dict(binding.pool_fingerprints)
    assert parsed.total_amount_in == binding.total_amount_in
    assert parsed.total_amount_out == binding.total_amount_out


def test_parse_binding_rejects_unknown_leg_fields() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    fields = route_binding_to_fields(binding)
    fields["route_legs"][0]["extra"] = 1
    intent = _route_intent_fields(binding, **fields)
    parsed, err = parse_route_binding_fields(intent)
    assert parsed is None
    assert err == "route_binding_unknown_leg_fields"


def test_parse_binding_rejects_fingerprint_pool_mismatch() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    fields = route_binding_to_fields(binding)
    fields["route_pool_fingerprints"].pop("p1")
    intent = _route_intent_fields(binding, **fields)
    parsed, err = parse_route_binding_fields(intent)
    assert parsed is None
    assert err == "route_binding_fingerprint_pool_mismatch"


def test_parse_binding_rejects_missing_legs() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    intent = _route_intent_fields(binding)  # no route_legs injected
    parsed, err = parse_route_binding_fields(intent)
    assert parsed is None
    assert err == "route_binding_missing_legs"


# ---------------------------------------------------------------------------
# validate_route_intent_against_binding
# ---------------------------------------------------------------------------


def test_validate_intent_binding_accepts_consistent() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    intent = _route_intent_fields(binding)
    assert validate_route_intent_against_binding(intent, binding) is None


def test_validate_intent_binding_rejects_total_mismatch() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    intent = _route_intent_fields(binding, total_amount_in=int(binding.total_amount_in) + 1)
    assert validate_route_intent_against_binding(intent, binding) == "route_total_amount_in_mismatch"


def test_validate_intent_binding_rejects_unsatisfiable_min_out() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    intent = _route_intent_fields(binding, total_min_amount_out=int(binding.total_amount_out) + 1)
    assert validate_route_intent_against_binding(intent, binding) == "route_min_out_unsatisfiable"


def test_validate_intent_binding_rejects_partial_coverage() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    intent = _route_intent_fields(binding, leg_indices=[0])
    assert validate_route_intent_against_binding(intent, binding) == "route_leg_coverage_mismatch"


def test_validate_intent_binding_rejects_kind_mismatch() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    intent = _route_intent_fields(binding)
    object.__setattr__(intent, "kind", IntentKind.SWAP_EXACT_IN)
    assert validate_route_intent_against_binding(intent, binding) == "route_kind_mismatch"


# ---------------------------------------------------------------------------
# replay_route_legs
# ---------------------------------------------------------------------------


def test_replay_exact_quote_match_and_threading() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    replay = replay_route_legs(binding=binding, pools=pools)
    assert replay.ok, replay.reject_reason
    assert replay.total_amount_in == binding.total_amount_in
    assert replay.total_amount_out == binding.total_amount_out
    # post-reserves conserve per pool: in added, out removed
    for leg in replay.legs:
        pool = pools[leg.pool_id]
        assert leg.new_reserve0 == int(pool.reserve0) + leg.amount_in
        assert leg.new_reserve1 == int(pool.reserve1) - leg.amount_out


def test_replay_rejects_missing_pool() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    del pools["p2"]
    replay = replay_route_legs(binding=binding, pools=pools)
    assert not replay.ok
    assert replay.reject_reason == ROUTE_REJECT_POOL_NOT_FOUND


def test_replay_rejects_inactive_pool() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    pools["p2"] = _pool("p2", status=PoolStatus.FROZEN)
    replay = replay_route_legs(binding=binding, pools=pools)
    assert not replay.ok
    assert replay.reject_reason == ROUTE_REJECT_POOL_NOT_ACTIVE


def test_replay_rejects_drifted_pool_state() -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    pools["p2"] = _pool("p2", r0=1_001)
    replay = replay_route_legs(binding=binding, pools=pools)
    assert not replay.ok
    assert replay.reject_reason == ROUTE_REJECT_POOL_STATE_DRIFT


def test_replay_rejects_lying_leg_amounts_with_matching_fingerprint() -> None:
    # Fingerprints match (pre-state pools) but the leg claims a better output
    # than the kernel derives: the exact-quote equality must catch it.
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)
    legs = list(binding.legs)
    tampered_leg = RouteLegBinding(
        pool_id=legs[0].pool_id,
        asset_in=legs[0].asset_in,
        asset_out=legs[0].asset_out,
        amount_in=legs[0].amount_in,
        amount_out=legs[0].amount_out + 1,
    )
    tampered = RouteBinding(
        kind=binding.kind,
        asset_in=binding.asset_in,
        asset_out=binding.asset_out,
        total_amount_in=binding.total_amount_in,
        total_amount_out=binding.total_amount_out + 1,
        legs=tuple([tampered_leg] + legs[1:]),
        pool_fingerprints=binding.pool_fingerprints,
    )
    replay = replay_route_legs(binding=tampered, pools=pools)
    assert not replay.ok
    assert replay.reject_reason == ROUTE_REJECT_LEG_QUOTE_MISMATCH


def test_replay_expected_kernel_value_error_rejects_route(monkeypatch) -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)

    def rejected_quote(*args, **kwargs):  # noqa: ANN002, ANN003, ARG001
        raise ValueError("injected domain rejection")

    monkeypatch.setattr(route_settlement, "swap_exact_in_for_pool", rejected_quote)

    replay = replay_route_legs(binding=binding, pools=pools)

    assert not replay.ok
    assert replay.reject_reason == ROUTE_REJECT_LEG_QUOTE_MISMATCH


def test_replay_internal_kernel_fault_is_not_masked(monkeypatch) -> None:
    pools = {"p1": _pool("p1"), "p2": _pool("p2")}
    binding = _binding_for(pools)

    def broken_quote(*args, **kwargs):  # noqa: ANN002, ANN003, ARG001
        raise RuntimeError("injected route quote fault")

    monkeypatch.setattr(route_settlement, "swap_exact_in_for_pool", broken_quote)

    with pytest.raises(RuntimeError, match="injected route quote fault"):
        replay_route_legs(binding=binding, pools=pools)
