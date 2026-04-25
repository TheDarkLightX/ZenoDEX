from __future__ import annotations

from pathlib import Path

import pytest

from src.core.routing import RouteHop, RouteLeg, RouteQuote, best_route_exact_in_2hop
from src.integration.exact_in_route_certificate import (
    EXACT_IN_ROUTE_CERTIFICATE_SCHEMA,
    MAX_MIXED_DIRECT_TWOHOP_SPLIT_AMOUNT_IN,
    build_exact_in_route_canonical_certificate,
    build_exact_in_route_canonical_certificate_for_pools,
    build_exact_in_route_guarded_quote_packet,
    build_exact_in_route_rank_projection_packet,
    build_exact_in_route_rank_projection_packet_for_pools,
    build_exact_in_route_true_key_interpretation_packet,
    build_exact_in_route_true_key_interpretation_packet_for_pools,
    build_exact_in_route_oracle_contract,
    verify_exact_in_route_canonical_certificate,
    verify_exact_in_route_guarded_quote_packet_payload,
    verify_exact_in_route_rank_projection_packet,
    verify_exact_in_route_rank_projection_packet_payload,
    verify_exact_in_route_true_key_interpretation_packet,
    verify_exact_in_route_true_key_interpretation_packet_payload,
    verify_exact_in_route_oracle_contract_payload,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from src.integration.tau_witness import ARGMIN_STREAM_CERTIFICATE_V1
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _quote_one_hop(*, pool_id: str, amount_in: int = 10, amount_out: int = 11) -> RouteQuote:
    hop = RouteHop(
        pool_id=pool_id,
        asset_in="A",
        asset_out="B",
        amount_in=amount_in,
        amount_out=amount_out,
    )
    leg = RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=amount_out)
    return RouteQuote(asset_in="A", asset_out="B", amount_in=amount_in, amount_out=amount_out, legs=(leg,))


def _quote_two_hop(
    *,
    pool0: str,
    pool1: str,
    intermediate_asset: str,
    amount_in: int = 10,
    amount_mid: int = 12,
    amount_out: int = 15,
) -> RouteQuote:
    hop0 = RouteHop(
        pool_id=pool0,
        asset_in="A",
        asset_out=intermediate_asset,
        amount_in=amount_in,
        amount_out=amount_mid,
    )
    hop1 = RouteHop(
        pool_id=pool1,
        asset_in=intermediate_asset,
        asset_out="B",
        amount_in=amount_mid,
        amount_out=amount_out,
    )
    leg = RouteLeg(hops=(hop0, hop1), amount_in=amount_in, amount_out=amount_out)
    return RouteQuote(asset_in="A", asset_out="B", amount_in=amount_in, amount_out=amount_out, legs=(leg,))


def test_exact_in_route_certificate_selects_canonical_winner() -> None:
    certificate = build_exact_in_route_canonical_certificate(
        [
            _quote_two_hop(pool0="p_b", pool1="p_c", intermediate_asset="C", amount_out=13),
            _quote_one_hop(pool_id="p_a", amount_out=14),
            _quote_one_hop(pool_id="p_b", amount_out=14),
        ]
    )

    assert certificate.winner_index == 1
    assert certificate.winner_quote == _quote_one_hop(pool_id="p_a", amount_out=14)
    assert certificate.winner_route_key_rank_u64 == 0
    assert certificate.schema == EXACT_IN_ROUTE_CERTIFICATE_SCHEMA
    assert certificate.tau_spec_id == ARGMIN_STREAM_CERTIFICATE_V1.spec_id
    assert len(certificate.candidates) == 3
    assert len(certificate.argmin_steps) == 3

    payload = certificate.to_dict()
    assert payload["schema"] == EXACT_IN_ROUTE_CERTIFICATE_SCHEMA
    assert payload["winner_index"] == 1
    assert payload["winner_quote"]["amount_out"] == 14
    assert payload["candidates"][0]["route_key"]["hop_count"] == 2
    assert payload["certificate_hash"].startswith("0x")


def test_exact_in_route_certificate_uses_candidate_index_for_duplicate_key_ties() -> None:
    duplicate_a = _quote_one_hop(pool_id="p_a", amount_out=14)
    duplicate_b = _quote_one_hop(pool_id="p_a", amount_out=14)

    certificate = build_exact_in_route_canonical_certificate([duplicate_b, duplicate_a])

    assert certificate.winner_index == 0
    assert certificate.winner_route_key_rank_u64 == 0
    assert [candidate.route_key_rank_u64 for candidate in certificate.candidates] == [0, 0]


def test_exact_in_route_certificate_matches_best_route_for_pools() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    best = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=10)
    certificate = build_exact_in_route_canonical_certificate_for_pools(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
    )

    assert best is not None
    assert certificate is not None
    assert certificate.winner_quote == best
    quotes = [candidate.quote for candidate in certificate.candidates]
    ok, err = verify_exact_in_route_canonical_certificate(quotes, certificate=certificate)
    assert ok, err


def test_exact_in_route_certificate_tau_steps_verify_when_tau_is_available() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    certificate = build_exact_in_route_canonical_certificate(
        [
            _quote_two_hop(pool0="p_b", pool1="p_c", intermediate_asset="C", amount_out=13),
            _quote_one_hop(pool_id="p_a", amount_out=14),
            _quote_one_hop(pool_id="p_b", amount_out=14),
        ]
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=Path(ARGMIN_STREAM_CERTIFICATE_V1.path),
        steps=list(certificate.argmin_steps),
        timeout_s=10.0,
    )
    assert outputs
    assert all(int(outputs.get(i, {}).get("o1", 0)) == 1 for i in range(len(certificate.argmin_steps)))


def test_exact_in_route_oracle_contract_rebuilds_for_pool_snapshot() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1001, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    contract = build_exact_in_route_oracle_contract(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
    )

    payload = contract.to_dict()
    assert payload["schema"] == "zenodex/exact-in-route-oracle-contract/v1"
    assert payload["runtime_matches_canonical"] is True
    assert payload["candidate_count"] >= 1
    assert payload["runtime_quote"] == payload["canonical_winner_quote"]
    assert payload["certificate"]["schema"] == EXACT_IN_ROUTE_CERTIFICATE_SCHEMA

    ok, err = verify_exact_in_route_oracle_contract_payload(payload)
    assert ok, err


def test_exact_in_route_oracle_contract_rejects_mixed_split_above_exhaustive_budget() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1001, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    with pytest.raises(ValueError, match="enable_mixed_direct_twohop_split"):
        build_exact_in_route_oracle_contract(
            pools_by_id=pools,
            asset_in="A",
            asset_out="B",
            amount_in=MAX_MIXED_DIRECT_TWOHOP_SPLIT_AMOUNT_IN + 1,
            enable_mixed_direct_twohop_split=True,
        )


def test_exact_in_route_oracle_contract_rejects_tampering() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1001, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    payload = build_exact_in_route_oracle_contract(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
    ).to_dict()
    payload["runtime_matches_canonical"] = False

    ok, err = verify_exact_in_route_oracle_contract_payload(payload)
    assert ok is False
    assert err == "oracle contract payload mismatch"


def test_exact_in_route_guarded_quote_packet_round_trips() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1001, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    packet = build_exact_in_route_guarded_quote_packet(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
    )

    payload = packet.to_dict()
    assert payload["schema"] == "zenodex/exact-in-route-guarded-quote-packet/v1"
    assert payload["guard_ok"] is True
    assert payload["quote"] == payload["contract"]["runtime_quote"]
    assert payload["error"] is None

    ok, err = verify_exact_in_route_guarded_quote_packet_payload(payload)
    assert ok, err


def test_exact_in_route_guarded_quote_packet_rejects_tampering() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1001, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    payload = build_exact_in_route_guarded_quote_packet(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
    ).to_dict()
    payload["guard_ok"] = False

    ok, err = verify_exact_in_route_guarded_quote_packet_payload(payload)
    assert ok is False
    assert err == "guarded quote packet payload mismatch"


def test_exact_in_route_rank_projection_packet_round_trips() -> None:
    quotes = [
        _quote_two_hop(pool0="p_b", pool1="p_c", intermediate_asset="C", amount_out=13),
        _quote_one_hop(pool_id="p_a", amount_out=14),
        _quote_one_hop(pool_id="p_b", amount_out=14),
    ]

    packet = build_exact_in_route_rank_projection_packet(quotes)

    assert packet.packet_ok is True
    assert packet.ordered_unique_keys_sorted_unique is True
    assert packet.candidate_ranks_match_projection is True
    assert packet.rank_order_preserves_true_key_order is True
    assert len(packet.ordered_unique_route_keys) == 3
    assert [candidate.route_key_rank_u64 for candidate in packet.candidates] == [2, 0, 1]

    ok, err = verify_exact_in_route_rank_projection_packet(quotes, packet=packet)
    assert ok, err
    ok, err = verify_exact_in_route_rank_projection_packet_payload(packet.to_dict())
    assert ok, err


def test_exact_in_route_rank_projection_packet_for_pools_rejects_tampering() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1001, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    packet = build_exact_in_route_rank_projection_packet_for_pools(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
    )
    assert packet is not None
    payload = packet.to_dict()
    payload["candidate_ranks_match_projection"] = False

    ok, err = verify_exact_in_route_rank_projection_packet_payload(payload)
    assert ok is False
    assert err == "rank projection packet payload mismatch"


def test_exact_in_route_true_key_interpretation_packet_round_trips() -> None:
    quotes = [
        _quote_two_hop(pool0="p_b", pool1="p_c", intermediate_asset="C", amount_out=13),
        _quote_one_hop(pool_id="p_a", amount_out=14),
        _quote_one_hop(pool_id="p_b", amount_out=14),
    ]

    packet = build_exact_in_route_true_key_interpretation_packet(quotes)

    assert packet.packet_ok is True
    assert packet.rank_projection_packet.packet_ok is True
    assert packet.winner_index_in_range is True
    assert packet.candidate_indices_match_stream is True
    assert packet.candidate_route_keys_match_quotes is True
    assert packet.winner_matches_certificate_candidate is True
    assert packet.winner_true_key_minimal is True

    ok, err = verify_exact_in_route_true_key_interpretation_packet(quotes, packet=packet)
    assert ok, err
    ok, err = verify_exact_in_route_true_key_interpretation_packet_payload(packet.to_dict())
    assert ok, err


def test_exact_in_route_true_key_interpretation_packet_for_pools_rejects_tampering() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1001, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 1000, 0),
        "p_cb": _pool("p_cb", "C", "B", 1000, 1000, 0),
    }

    packet = build_exact_in_route_true_key_interpretation_packet_for_pools(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_in=10,
    )
    assert packet is not None
    payload = packet.to_dict()
    payload["winner_true_key_minimal"] = False

    ok, err = verify_exact_in_route_true_key_interpretation_packet_payload(payload)
    assert ok is False
    assert err == "true-key interpretation packet payload mismatch"
