from __future__ import annotations

from typing import Callable

import pytest

from src.integration.exact_in_route_certificate import (
    build_exact_in_route_canonical_certificate_for_pools,
    build_exact_in_route_guarded_quote_packet,
    build_exact_in_route_oracle_contract,
    build_exact_in_route_rank_projection_packet_for_pools,
    build_exact_in_route_true_key_interpretation_packet_for_pools,
    enumerate_route_candidates_exact_in_2hop,
    verify_exact_in_route_guarded_quote_packet_payload,
    verify_exact_in_route_oracle_contract_payload,
)
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


def _pools() -> dict[str, PoolState]:
    return {
        "p_ab": _pool("p_ab", "A", "B", 10_000, 10_000, 0),
        "p_ac": _pool("p_ac", "A", "C", 10_000, 10_000, 0),
        "p_cb": _pool("p_cb", "C", "B", 10_000, 10_000, 0),
    }


def test_exact_in_route_oracle_contract_rejects_integer_mixed_split_flag() -> None:
    payload = build_exact_in_route_oracle_contract(
        pools_by_id=_pools(),
        asset_in="A",
        asset_out="B",
        amount_in=100,
        enable_mixed_direct_twohop_split=True,
    ).to_dict()
    payload["enable_mixed_direct_twohop_split"] = 1

    ok, err = verify_exact_in_route_oracle_contract_payload(payload)

    assert ok is False
    assert err == "enable_mixed_direct_twohop_split must be a bool"


def test_exact_in_route_guarded_quote_rejects_integer_mixed_split_flag() -> None:
    payload = build_exact_in_route_guarded_quote_packet(
        pools_by_id=_pools(),
        asset_in="A",
        asset_out="B",
        amount_in=100,
        enable_mixed_direct_twohop_split=True,
    ).to_dict()
    payload["contract"]["enable_mixed_direct_twohop_split"] = 1

    ok, err = verify_exact_in_route_guarded_quote_packet_payload(payload)

    assert ok is False
    assert err == "enable_mixed_direct_twohop_split must be a bool"


def test_exact_in_route_oracle_contract_rejects_bool_binding_flag() -> None:
    payload = build_exact_in_route_oracle_contract(
        pools_by_id=_pools(),
        asset_in="A",
        asset_out="B",
        amount_in=100,
        enable_mixed_direct_twohop_split=True,
    ).to_dict()
    payload["binding_ok"] = True

    ok, err = verify_exact_in_route_oracle_contract_payload(payload)

    assert ok is False
    assert err == "binding_ok must be an int"


def test_exact_in_route_oracle_contract_rejects_non_string_split_profile() -> None:
    payload = build_exact_in_route_oracle_contract(
        pools_by_id=_pools(),
        asset_in="A",
        asset_out="B",
        amount_in=100,
        enable_mixed_direct_twohop_split=True,
    ).to_dict()
    payload["split_search_profile"] = 1

    ok, err = verify_exact_in_route_oracle_contract_payload(payload)

    assert ok is False
    assert err == "split_search_profile must be a non-empty string"


def test_exact_in_route_oracle_contract_rejects_bool_pool_snapshot_int() -> None:
    payload = build_exact_in_route_oracle_contract(
        pools_by_id=_pools(),
        asset_in="A",
        asset_out="B",
        amount_in=100,
        enable_mixed_direct_twohop_split=True,
    ).to_dict()
    payload["pool_snapshots"][0]["reserve0"] = True

    ok, err = verify_exact_in_route_oracle_contract_payload(payload)

    assert ok is False
    assert err == "reserve0 must be an int"


@pytest.mark.parametrize("amount_in", [True, "100"])
def test_exact_in_route_candidates_reject_non_strict_amount_before_no_route_short_circuit(
    amount_in: object,
) -> None:
    with pytest.raises(ValueError, match="amount_in must be an int"):
        enumerate_route_candidates_exact_in_2hop(
            pools_by_id={},
            asset_in="A",
            asset_out="A",
            amount_in=amount_in,
        )


@pytest.mark.parametrize("bad_flag", [1, "yes"])
@pytest.mark.parametrize(
    "builder",
    [
        enumerate_route_candidates_exact_in_2hop,
        build_exact_in_route_canonical_certificate_for_pools,
        build_exact_in_route_oracle_contract,
        build_exact_in_route_guarded_quote_packet,
        build_exact_in_route_rank_projection_packet_for_pools,
        build_exact_in_route_true_key_interpretation_packet_for_pools,
    ],
)
def test_exact_in_route_public_builders_reject_non_bool_mixed_split_flag(
    builder: Callable[..., object],
    bad_flag: object,
) -> None:
    with pytest.raises(TypeError, match="enable_mixed_direct_twohop_split must be a bool"):
        builder(
            pools_by_id=_pools(),
            asset_in="A",
            asset_out="B",
            amount_in=100,
            enable_mixed_direct_twohop_split=bad_flag,
        )


@pytest.mark.parametrize("bad_binding", [True, "1", 2])
@pytest.mark.parametrize(
    "builder",
    [
        build_exact_in_route_canonical_certificate_for_pools,
        build_exact_in_route_oracle_contract,
        build_exact_in_route_guarded_quote_packet,
    ],
)
def test_exact_in_route_public_builders_reject_non_strict_binding_ok(
    builder: Callable[..., object],
    bad_binding: object,
) -> None:
    with pytest.raises((TypeError, ValueError), match="binding_ok"):
        builder(
            pools_by_id=_pools(),
            asset_in="A",
            asset_out="B",
            amount_in=100,
            binding_ok=bad_binding,
        )


@pytest.mark.parametrize("bad_profile", [1, ""])
@pytest.mark.parametrize(
    "builder",
    [
        enumerate_route_candidates_exact_in_2hop,
        build_exact_in_route_canonical_certificate_for_pools,
        build_exact_in_route_oracle_contract,
        build_exact_in_route_guarded_quote_packet,
        build_exact_in_route_rank_projection_packet_for_pools,
        build_exact_in_route_true_key_interpretation_packet_for_pools,
    ],
)
def test_exact_in_route_public_builders_reject_non_string_split_profile(
    builder: Callable[..., object],
    bad_profile: object,
) -> None:
    with pytest.raises(ValueError, match="split_search_profile must be a non-empty string"):
        builder(
            pools_by_id=_pools(),
            asset_in="A",
            asset_out="B",
            amount_in=100,
            split_search_profile=bad_profile,
        )


@pytest.mark.parametrize("amount_in", [True, "100"])
def test_exact_in_route_certificate_builder_rejects_non_strict_amount_before_no_route_short_circuit(
    amount_in: object,
) -> None:
    with pytest.raises(ValueError, match="amount_in must be an int"):
        build_exact_in_route_canonical_certificate_for_pools(
            pools_by_id={},
            asset_in="A",
            asset_out="A",
            amount_in=amount_in,
        )
