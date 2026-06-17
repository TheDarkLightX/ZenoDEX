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
    audit_exact_out_two_pool_runtime_canonicality,
    build_exact_out_many_pool_adaptive_liveness_packet,
    build_exact_out_many_pool_audited_bounds_contract,
    build_exact_out_many_pool_bounded_advisory_quote_packet,
    build_exact_out_many_pool_bounded_workaround_packet,
    build_exact_out_many_pool_candidate_domain_contract,
    build_exact_out_many_pool_certified_advisory_packet,
    build_exact_out_many_pool_certified_winner_packet,
    build_exact_out_many_pool_default_packet,
    build_exact_out_many_pool_guarded_quote_packet,
    build_exact_out_many_pool_oracle_contract,
    build_exact_out_many_pool_prefilter_contract,
    build_exact_out_many_pool_repaired_advisory_quote_packet,
    build_exact_out_many_pool_repaired_full_domain_certified_packet,
    build_exact_out_many_pool_repaired_key_cover_interpretation_packet,
    build_exact_out_many_pool_repaired_key_cover_packet,
    build_exact_out_many_pool_repaired_replacement_shadow_packet,
    build_exact_out_many_pool_repaired_selected_domain_oracle_contract,
    enumerate_exact_out_many_pool_candidates,
    enumerate_exact_out_two_pool_candidates,
    guard_exact_out_many_pool_runtime_canonicality,
    quote_exact_out_many_pool_adaptive,
    quote_exact_out_many_pool_bounded_advisory,
    quote_exact_out_many_pool_certified_advisory,
    quote_exact_out_many_pool_default,
    quote_exact_out_many_pool_guarded,
    quote_exact_out_many_pool_repaired_advisory,
    quote_exact_out_many_pool_repaired_full_domain_certified,
    quote_exact_out_many_pool_repaired_selected_domain,
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
        (
            "enumerate_two_pool",
            lambda amount: enumerate_exact_out_two_pool_candidates(
                _pools()[0],
                _pools()[1],
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "audit_two_pool",
            lambda amount: audit_exact_out_two_pool_runtime_canonicality(
                _pools()[0],
                _pools()[1],
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "prefilter_contract",
            lambda amount: build_exact_out_many_pool_prefilter_contract(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "candidate_domain",
            lambda amount: build_exact_out_many_pool_candidate_domain_contract(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_selected_domain_oracle",
            lambda amount: build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_selected_domain_quote",
            lambda amount: quote_exact_out_many_pool_repaired_selected_domain(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_advisory_packet",
            lambda amount: build_exact_out_many_pool_repaired_advisory_quote_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_advisory_quote",
            lambda amount: quote_exact_out_many_pool_repaired_advisory(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_full_domain_packet",
            lambda amount: build_exact_out_many_pool_repaired_full_domain_certified_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_full_domain_quote",
            lambda amount: quote_exact_out_many_pool_repaired_full_domain_certified(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_key_cover_packet",
            lambda amount: build_exact_out_many_pool_repaired_key_cover_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_key_cover_interpretation",
            lambda amount: build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "bounded_workaround",
            lambda amount: build_exact_out_many_pool_bounded_workaround_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "bounded_advisory_packet",
            lambda amount: build_exact_out_many_pool_bounded_advisory_quote_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "bounded_advisory_quote",
            lambda amount: quote_exact_out_many_pool_bounded_advisory(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "audited_bounds",
            lambda amount: build_exact_out_many_pool_audited_bounds_contract(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "adaptive_liveness_packet",
            lambda amount: build_exact_out_many_pool_adaptive_liveness_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "adaptive_quote",
            lambda amount: quote_exact_out_many_pool_adaptive(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "certified_winner",
            lambda amount: build_exact_out_many_pool_certified_winner_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
        (
            "repaired_replacement_shadow",
            lambda amount: build_exact_out_many_pool_repaired_replacement_shadow_packet(
                _pools(),
                asset_in="A",
                asset_out="B",
                amount_out_total=amount,
            ),
        ),
    )


def _strict_amount_acceptance_entrypoints() -> tuple[tuple[str, ExactOutCall], ...]:
    return _strict_amount_entrypoints()[:10]


@pytest.mark.parametrize("amount_out_total", [True, "10"])
def test_exact_out_many_pool_public_entrypoints_reject_non_strict_amounts(
    amount_out_total: object,
) -> None:
    for _name, call in _strict_amount_entrypoints():
        with pytest.raises(ValueError, match="amount_out_total must be an int"):
            call(amount_out_total)


def test_exact_out_many_pool_public_entrypoints_still_accept_strict_integer_amount() -> None:
    results = {name: call(10) for name, call in _strict_amount_acceptance_entrypoints()}

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
