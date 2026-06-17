from __future__ import annotations

from collections.abc import Callable

import pytest

from src.core.split_routing_dispatch import SplitManyPoolsExactOutQuote
from src.integration.exact_out_route_certificate import (
    ExactOutManyPoolCanonicalityAudit,
    ExactOutManyPoolCertifiedAdvisoryPacket,
    ExactOutManyPoolGuardedQuotePacket,
    ExactOutManyPoolOracleContract,
    audit_exact_out_many_pool_runtime_canonicality,
    build_exact_out_many_pool_certified_advisory_packet,
    build_exact_out_many_pool_default_packet,
    build_exact_out_many_pool_guarded_quote_packet,
    build_exact_out_many_pool_oracle_contract,
    enumerate_exact_out_many_pool_candidates,
    guard_exact_out_many_pool_runtime_canonicality,
    quote_exact_out_many_pool_certified_advisory,
    quote_exact_out_many_pool_default,
    quote_exact_out_many_pool_guarded,
)
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _pool(pool_id: str) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params="",
    )


def _pools() -> tuple[PoolState, ...]:
    return (_pool("p1"), _pool("p2"))


ExactOutCall = Callable[[object], object]


def _strict_amount_entrypoints() -> tuple[tuple[str, ExactOutCall], ...]:
    return (
        (
            "enumerate",
            lambda amount: enumerate_exact_out_many_pool_candidates(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "audit",
            lambda amount: audit_exact_out_many_pool_runtime_canonicality(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "oracle_contract",
            lambda amount: build_exact_out_many_pool_oracle_contract(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "guard",
            lambda amount: guard_exact_out_many_pool_runtime_canonicality(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "guarded_quote",
            lambda amount: quote_exact_out_many_pool_guarded(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "guarded_packet",
            lambda amount: build_exact_out_many_pool_guarded_quote_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "certified_packet",
            lambda amount: build_exact_out_many_pool_certified_advisory_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "certified_quote",
            lambda amount: quote_exact_out_many_pool_certified_advisory(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "default_quote",
            lambda amount: quote_exact_out_many_pool_default(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "default_packet",
            lambda amount: build_exact_out_many_pool_default_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
    )


@pytest.mark.parametrize("amount_out_total", [True, "10"])
def test_exact_out_many_pool_public_entrypoints_reject_non_strict_amounts(
    amount_out_total: object,
) -> None:
    for _name, call in _strict_amount_entrypoints():
        with pytest.raises(ValueError, match="amount_out_total must be an int"):
            call(amount_out_total)


def test_exact_out_many_pool_public_entrypoints_still_accept_strict_integer_amount() -> None:
    results = {name: call(10) for name, call in _strict_amount_entrypoints()}

    assert isinstance(results["enumerate"], tuple)
    assert isinstance(results["audit"], ExactOutManyPoolCanonicalityAudit)
    assert isinstance(results["oracle_contract"], ExactOutManyPoolOracleContract)
    assert isinstance(results["guard"], tuple)
    assert isinstance(results["guarded_quote"], tuple)
    assert isinstance(results["guarded_packet"], ExactOutManyPoolGuardedQuotePacket)
    assert isinstance(results["certified_packet"], ExactOutManyPoolCertifiedAdvisoryPacket)
    assert isinstance(results["certified_quote"], tuple)
    assert isinstance(results["default_quote"], tuple)
    assert isinstance(results["default_packet"], ExactOutManyPoolCertifiedAdvisoryPacket)
    assert all(isinstance(quote, SplitManyPoolsExactOutQuote) for quote in results["enumerate"])
