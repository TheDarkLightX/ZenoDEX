from __future__ import annotations

from pathlib import Path

import pytest

import src.integration.exact_out_route_certificate as exact_out_module
from src.core.split_routing_dispatch import SplitLegExactOutQuote, SplitManyPoolsExactOutQuote
from src.integration.exact_out_route_certificate import (
    EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA,
    EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA,
    EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA,
    EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
    EXACT_OUT_MANY_POOL_PROJECTION_COVER_ERROR,
    EXACT_OUT_ROUTE_CERTIFICATE_SCHEMA,
    audit_exact_out_many_pool_runtime_canonicality,
    build_exact_out_many_pool_candidate_domain_contract,
    build_exact_out_many_pool_bounded_advisory_quote_packet,
    build_exact_out_many_pool_bounded_workaround_packet,
    build_exact_out_many_pool_certified_advisory_packet,
    build_exact_out_many_pool_audited_bounds_contract,
    build_exact_out_many_pool_adaptive_liveness_packet,
    build_exact_out_many_pool_repaired_replacement_shadow_packet,
    build_exact_out_many_pool_default_packet,
    quote_exact_out_many_pool_bounded_advisory,
    quote_exact_out_many_pool_certified_advisory,
    quote_exact_out_many_pool_adaptive,
    quote_exact_out_many_pool_default,
    build_exact_out_many_pool_prefilter_contract,
    build_exact_out_many_pool_repaired_prefilter_contract,
    build_exact_out_many_pool_repaired_selected_domain_oracle_contract,
    build_exact_out_many_pool_repaired_advisory_quote_packet,
    build_exact_out_many_pool_repaired_full_domain_certified_packet,
    build_exact_out_many_pool_repaired_key_cover_packet,
    build_exact_out_many_pool_repaired_key_cover_interpretation_packet,
    build_exact_out_many_pool_certified_winner_packet,
    build_exact_out_many_pool_guarded_quote_packet,
    build_exact_out_many_pool_oracle_contract,
    build_exact_out_route_canonical_certificate,
    enumerate_exact_out_many_pool_candidates,
    enumerate_exact_out_two_pool_candidates,
    guard_exact_out_many_pool_runtime_canonicality,
    quote_exact_out_many_pool_guarded,
    quote_exact_out_many_pool_repaired_full_domain_certified,
    quote_exact_out_many_pool_repaired_selected_domain,
    verify_exact_out_many_pool_candidate_domain_contract_payload,
    verify_exact_out_many_pool_bounded_advisory_quote_packet_payload,
    verify_exact_out_many_pool_bounded_workaround_packet_payload,
    verify_exact_out_many_pool_certified_advisory_packet_payload,
    verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload,
    verify_exact_out_many_pool_default_packet_payload,
    verify_exact_out_many_pool_prefilter_contract_payload,
    verify_exact_out_many_pool_repaired_prefilter_contract_payload,
    verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload,
    verify_exact_out_many_pool_repaired_advisory_quote_packet_payload,
    verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload,
    verify_exact_out_many_pool_repaired_key_cover_packet_payload,
    verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload,
    verify_exact_out_many_pool_certified_winner_packet_payload,
    verify_exact_out_many_pool_audited_bounds_contract_payload,
    verify_exact_out_many_pool_adaptive_liveness_packet_payload,
    verify_exact_out_many_pool_guarded_quote_packet_payload,
    verify_exact_out_route_canonical_certificate,
    verify_exact_out_many_pool_oracle_contract_payload,
    verify_exact_out_route_canonical_certificate_payload,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from src.integration.tau_witness import ARGMIN_STREAM_CERTIFICATE_V1
from src.state.pools import CURVE_TAG_CPMM, CURVE_TAG_SUM_BOOST_V1, PoolState, PoolStatus


def _quote_one_leg() -> SplitManyPoolsExactOutQuote:
    return SplitManyPoolsExactOutQuote(
        amount_out_total=10,
        amount_in_total=11,
        legs=(SplitLegExactOutQuote(pool_id="pool_b", amount_out=10, amount_in=11),),
    )


def _quote_two_legs_lex_low() -> SplitManyPoolsExactOutQuote:
    return SplitManyPoolsExactOutQuote(
        amount_out_total=10,
        amount_in_total=11,
        legs=(
            SplitLegExactOutQuote(pool_id="pool_a", amount_out=4, amount_in=4),
            SplitLegExactOutQuote(pool_id="pool_c", amount_out=6, amount_in=7),
        ),
    )


def _quote_two_legs_lex_high() -> SplitManyPoolsExactOutQuote:
    return SplitManyPoolsExactOutQuote(
        amount_out_total=10,
        amount_in_total=11,
        legs=(
            SplitLegExactOutQuote(pool_id="pool_b", amount_out=4, amount_in=4),
            SplitLegExactOutQuote(pool_id="pool_c", amount_out=6, amount_in=7),
        ),
    )


def _pool(
    *,
    pool_id: str,
    reserve0: int,
    reserve1: int,
    fee_bps: int = 0,
    curve_tag: str = CURVE_TAG_CPMM,
    curve_params: object | None = None,
) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=int(fee_bps),
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=curve_tag,
        curve_params=curve_params,
    )


def test_exact_out_route_certificate_selects_canonical_winner() -> None:
    certificate = build_exact_out_route_canonical_certificate(
        [_quote_two_legs_lex_high(), _quote_one_leg(), _quote_two_legs_lex_low()]
    )

    assert certificate.winner_index == 1
    assert certificate.winner_quote == _quote_one_leg()
    assert certificate.winner_route_key_rank_u64 == 0
    assert certificate.tau_spec_id == ARGMIN_STREAM_CERTIFICATE_V1.spec_id
    assert len(certificate.candidates) == 3
    assert len(certificate.argmin_steps) == 3

    payload = certificate.to_dict()
    assert payload["schema"] == EXACT_OUT_ROUTE_CERTIFICATE_SCHEMA
    assert payload["winner_index"] == 1
    assert payload["winner_quote"]["amount_in_total"] == 11
    assert payload["candidates"][0]["route_key"]["leg_count"] == 2


def test_exact_out_route_certificate_uses_candidate_index_for_duplicate_key_ties() -> None:
    duplicate_a = _quote_one_leg()
    duplicate_b = _quote_one_leg()

    certificate = build_exact_out_route_canonical_certificate([duplicate_b, duplicate_a])

    assert certificate.winner_index == 0
    assert certificate.winner_route_key_rank_u64 == 0
    assert [candidate.route_key_rank_u64 for candidate in certificate.candidates] == [0, 0]


def test_exact_out_route_certificate_tau_steps_verify_when_tau_is_available() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    certificate = build_exact_out_route_canonical_certificate(
        [_quote_two_legs_lex_high(), _quote_one_leg(), _quote_two_legs_lex_low()]
    )
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=Path(ARGMIN_STREAM_CERTIFICATE_V1.path),
        steps=list(certificate.argmin_steps),
        timeout_s=10.0,
    )
    assert outputs
    assert all(int(outputs.get(i, {}).get("o1", 0)) == 1 for i in range(len(certificate.argmin_steps)))


def test_exact_out_route_certificate_verifier_accepts_canonical_build() -> None:
    quotes = [_quote_two_legs_lex_high(), _quote_one_leg(), _quote_two_legs_lex_low()]
    certificate = build_exact_out_route_canonical_certificate(quotes)

    ok, err = verify_exact_out_route_canonical_certificate(quotes, certificate=certificate)
    assert ok, err

    payload_ok, payload_err = verify_exact_out_route_canonical_certificate_payload(certificate.to_dict())
    assert payload_ok, payload_err


def test_exact_out_route_certificate_rejects_wrong_binding_context() -> None:
    quotes = [_quote_two_legs_lex_high(), _quote_one_leg(), _quote_two_legs_lex_low()]
    certificate = build_exact_out_route_canonical_certificate(quotes, binding_ok=1)

    ok, err = verify_exact_out_route_canonical_certificate(
        quotes,
        certificate=certificate,
        expected_binding_ok=0,
    )
    assert not ok
    assert err == "argmin steps mismatch"

    payload_ok, payload_err = verify_exact_out_route_canonical_certificate_payload(
        certificate.to_dict(),
        expected_binding_ok=0,
    )
    assert not payload_ok
    assert payload_err == "certificate payload mismatch"


def test_exact_out_route_certificate_rejects_reordered_live_candidate_stream() -> None:
    quotes = [_quote_two_legs_lex_high(), _quote_one_leg(), _quote_two_legs_lex_low()]
    certificate = build_exact_out_route_canonical_certificate(quotes)
    live_quotes = list(reversed(quotes))
    live_certificate = build_exact_out_route_canonical_certificate(live_quotes)

    payload_ok, payload_err = verify_exact_out_route_canonical_certificate_payload(certificate.to_dict())
    ok, err = verify_exact_out_route_canonical_certificate(live_quotes, certificate=certificate)

    assert payload_ok, payload_err
    assert live_certificate.winner_index == certificate.winner_index
    assert live_certificate.winner_quote == certificate.winner_quote
    assert live_certificate.candidates != certificate.candidates
    assert not ok
    assert err == "candidate list mismatch"


def test_exact_out_route_certificate_payload_verifier_rejects_tampering() -> None:
    certificate = build_exact_out_route_canonical_certificate(
        [_quote_two_legs_lex_high(), _quote_one_leg(), _quote_two_legs_lex_low()]
    )
    payload = certificate.to_dict()
    payload["winner_index"] = int(payload["winner_index"]) + 1

    ok, err = verify_exact_out_route_canonical_certificate_payload(payload)
    assert not ok
    assert err == "certificate payload mismatch"


def test_enumerate_exact_out_many_pool_candidates_builds_nonempty_bounded_domain() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=120, reserve1=50),
        _pool(pool_id="pool_b", reserve0=135, reserve1=40),
        _pool(pool_id="pool_c", reserve0=170, reserve1=70),
    )

    candidates = enumerate_exact_out_many_pool_candidates(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=8,
        max_legs=3,
        max_candidate_pools=3,
    )
    certificate = build_exact_out_route_canonical_certificate(candidates)
    ok, err = verify_exact_out_route_canonical_certificate(candidates, certificate=certificate)

    assert candidates
    assert ok, err
    assert certificate.winner_quote in candidates


def test_enumerate_exact_out_two_pool_candidates_propagates_internal_quote_fault(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pool_a = _pool(pool_id="pool_a", reserve0=100, reserve1=40)
    pool_b = _pool(pool_id="pool_b", reserve0=100, reserve1=40)

    def _domain_reject(*_args: object, **_kwargs: object) -> object:
        raise ValueError("infeasible quote")

    monkeypatch.setattr(exact_out_module, "swap_exact_out_for_pool", _domain_reject)
    with pytest.raises(ValueError, match="no feasible exact-out candidates"):
        enumerate_exact_out_two_pool_candidates(
            pool_a,
            pool_b,
            asset_in=pool_a.asset0,
            asset_out=pool_a.asset1,
            amount_out_total=4,
        )

    def _internal_fault(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("exact-out quote fault")

    monkeypatch.setattr(exact_out_module, "swap_exact_out_for_pool", _internal_fault)
    with pytest.raises(RuntimeError, match="exact-out quote fault"):
        enumerate_exact_out_two_pool_candidates(
            pool_a,
            pool_b,
            asset_in=pool_a.asset0,
            asset_out=pool_a.asset1,
            amount_out_total=4,
        )


def test_audit_exact_out_many_pool_runtime_canonicality_matches_on_small_case() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )

    audit = audit_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_enumerated_candidates=2_000,
    )

    assert audit.runtime_matches_canonical is True
    assert audit.runtime_quote == audit.canonical_winner_quote
    assert audit.candidate_count >= 1
    assert audit.audit_pool_ids == ("pool_c",)


def test_exact_out_many_pool_oracle_contract_rebuilds_small_domain() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )

    contract = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_enumerated_candidates=2_000,
    )
    payload = contract.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA
    assert payload["contract_ok"] is True
    assert payload["audit"]["runtime_matches_canonical"] is True
    assert payload["audit"]["runtime_quote"] == payload["audit"]["canonical_winner_quote"]
    assert payload["audit"]["projection_cover_audit"] is not None
    assert payload["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
    assert payload["audit"]["projection_cover_audit"]["canonical_quote_covered"] is True
    assert len(payload["pool_snapshots"]) == 3

    ok, err = verify_exact_out_many_pool_oracle_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_candidate_domain_contract_rebuilds_small_domain() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )

    contract = build_exact_out_many_pool_candidate_domain_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_enumerated_candidates=2_000,
    )
    payload = contract.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA
    assert payload["contract_ok"] is True
    assert payload["candidate_domain_nonempty"] is True
    assert payload["all_candidates_complete"] is True
    assert payload["all_candidates_leg_bounded"] is True
    assert payload["all_candidates_leg_pool_ids_sorted_unique"] is True
    assert payload["all_candidates_within_audit_pool_ids"] is True
    assert payload["candidate_count_within_budget"] is True
    assert payload["audit_pool_ids"] == ["pool_c"]
    assert payload["candidate_count"] == len(payload["candidates"])

    ok, err = verify_exact_out_many_pool_candidate_domain_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_candidate_domain_contract_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )

    payload = build_exact_out_many_pool_candidate_domain_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_enumerated_candidates=2_000,
    ).to_dict()
    payload["contract_ok"] = False

    ok, err = verify_exact_out_many_pool_candidate_domain_contract_payload(payload)
    assert not ok
    assert err == "candidate domain contract payload mismatch"


def test_exact_out_many_pool_prefilter_contract_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34, fee_bps=0),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60, fee_bps=0),
    )

    contract = build_exact_out_many_pool_prefilter_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
    )
    payload = contract.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA
    assert payload["contract_ok"] is True
    assert payload["feasible_rows_sorted_unique"] is True
    assert payload["selected_pool_ids_sorted_unique"] is True
    assert payload["selected_pool_ids_within_budget"] is True
    assert payload["selected_pool_ids_subset_of_feasible"] is True
    assert payload["selected_is_prefix_of_feasible_ranking"] is True
    assert payload["full_capacity_guard_feasible"] is True
    assert payload["selected_capacity_guard_feasible"] is True
    assert payload["selected_pool_ids"] == ["pool_a", "pool_b", "pool_c"]

    ok, err = verify_exact_out_many_pool_prefilter_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_prefilter_contract_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34, fee_bps=0),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60, fee_bps=0),
    )
    payload = build_exact_out_many_pool_prefilter_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
    ).to_dict()
    payload["selected_is_prefix_of_feasible_ranking"] = False

    ok, err = verify_exact_out_many_pool_prefilter_contract_payload(payload)
    assert not ok
    assert err == "prefilter contract payload mismatch"


def test_exact_out_many_pool_repaired_prefilter_contract_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10, fee_bps=0),
        _pool(pool_id="p1", reserve0=20, reserve1=10, fee_bps=0),
        _pool(pool_id="p2", reserve0=30, reserve1=15, fee_bps=0),
        _pool(pool_id="p3", reserve0=30, reserve1=15, fee_bps=0),
    )

    contract = build_exact_out_many_pool_repaired_prefilter_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = contract.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA
    assert payload["current_selected_pool_ids"] == ["p0", "p2", "p3"]
    assert payload["repaired_selected_pool_ids"] == ["p0", "p1"]
    assert payload["current_selected_matches_full_canonical"] is False
    assert payload["repaired_selected_domain_matches_full_canonical"] is True
    assert payload["repaired_contraction_holds"] is True
    assert payload["contract_ok"] is True

    ok, err = verify_exact_out_many_pool_repaired_prefilter_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_repaired_prefilter_contract_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10, fee_bps=0),
        _pool(pool_id="p1", reserve0=20, reserve1=10, fee_bps=0),
        _pool(pool_id="p2", reserve0=30, reserve1=15, fee_bps=0),
        _pool(pool_id="p3", reserve0=30, reserve1=15, fee_bps=0),
    )
    payload = build_exact_out_many_pool_repaired_prefilter_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["repaired_contraction_holds"] = False

    ok, err = verify_exact_out_many_pool_repaired_prefilter_contract_payload(payload)
    assert not ok
    assert err == "repaired prefilter contract payload mismatch"


def test_exact_out_many_pool_repaired_selected_domain_oracle_contract_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = contract.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA
    assert payload["repaired_selected_pool_ids"] == ["p0", "p1"]
    assert payload["repaired_selected_domain_matches_full_canonical"] is True
    assert payload["audit_pool_ids_match_repaired_selected_pool_ids"] is True
    assert payload["repaired_selected_domain_runtime_matches_canonical"] is True
    assert payload["replacement_quote_matches_full_canonical"] is True
    assert payload["repaired_projection_cover_available"] is True
    assert payload["repaired_projection_cover_holds"] is True
    assert payload["repaired_selected_domain_runtime_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]
    assert payload["repaired_selected_domain_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert payload["contract_ok"] is True

    ok, err = verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_repaired_selected_domain_oracle_contract_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["audit_pool_ids_match_repaired_selected_pool_ids"] = False

    ok, err = verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload(payload)
    assert not ok
    assert err == "repaired selected-domain oracle contract payload mismatch"


def test_quote_exact_out_many_pool_repaired_selected_domain_returns_replacement_candidate() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, contract = quote_exact_out_many_pool_repaired_selected_domain(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert err is None
    assert quote is not None
    assert quote.legs == (
        SplitLegExactOutQuote(pool_id="p0", amount_out=2, amount_in=5),
        SplitLegExactOutQuote(pool_id="p1", amount_out=2, amount_in=5),
    )
    assert contract.contract_ok is True
    assert contract.repaired_contract.repaired_selected_domain_matches_full_canonical is True
    assert contract.audit.runtime_matches_canonical is True


def test_exact_out_many_pool_repaired_replacement_shadow_packet_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    packet = build_exact_out_many_pool_repaired_replacement_shadow_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["replacement_available"] is True
    assert payload["default_effective_quote_source"] == "selected_domain_runtime"
    assert payload["effective_quote_matches_replacement_quote"] is True
    assert payload["replacement_quote_matches_selected_runtime_quote"] is True
    assert payload["replacement_quote_matches_full_canonical"] is True
    assert payload["replacement_quote_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]

    ok, err = verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_repaired_replacement_shadow_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_repaired_replacement_shadow_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["effective_quote_matches_replacement_quote"] = False

    ok, err = verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload(payload)
    assert not ok
    assert err == "repaired replacement shadow packet payload mismatch"


def test_exact_out_many_pool_repaired_advisory_quote_packet_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    packet = build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["repaired_contract"]["contract_ok"] is True
    assert payload["advisory_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]
    assert payload["runtime_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]
    assert payload["runtime_matches_advisory"] is True

    ok, err = verify_exact_out_many_pool_repaired_advisory_quote_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_repaired_advisory_quote_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["runtime_matches_advisory"] = False

    ok, err = verify_exact_out_many_pool_repaired_advisory_quote_packet_payload(payload)
    assert not ok
    assert err == "repaired advisory quote packet payload mismatch"


def test_exact_out_many_pool_repaired_full_domain_certified_packet_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    packet = build_exact_out_many_pool_repaired_full_domain_certified_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["repaired_matches_full_canonical"] is True
    assert payload["full_domain_feasible_pool_ids"] == ["p0", "p1", "p2", "p3"]
    assert payload["full_domain_candidate_count"] > 0
    assert payload["repaired_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]
    assert payload["full_domain_canonical_quote"] == payload["repaired_quote"]
    assert payload["full_domain_certificate"]["winner_quote"] == payload["full_domain_canonical_quote"]
    assert payload["repaired_packet"]["runtime_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]

    ok, err = verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload(payload)
    assert ok, err


def test_quote_exact_out_many_pool_repaired_full_domain_certified_returns_repaired_quote() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, packet = quote_exact_out_many_pool_repaired_full_domain_certified(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert err is None
    assert quote is not None
    assert packet.packet_ok is True
    assert packet.repaired_matches_full_canonical is True
    assert quote.legs == (
        SplitLegExactOutQuote(pool_id="p0", amount_out=2, amount_in=5),
        SplitLegExactOutQuote(pool_id="p1", amount_out=2, amount_in=5),
    )
    assert packet.full_domain_canonical_quote == quote


def test_exact_out_many_pool_repaired_full_domain_certified_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_repaired_full_domain_certified_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["repaired_matches_full_canonical"] = False

    ok, err = verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload(payload)
    assert not ok
    assert err == "repaired full-domain certified packet payload mismatch"


def test_exact_out_many_pool_repaired_key_cover_packet_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    packet = build_exact_out_many_pool_repaired_key_cover_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["selected_keys_subset_full_keys"] is True
    assert payload["key_cover_holds"] is True
    assert payload["selected_domain_canonical_matches_full_domain_canonical"] is True
    assert payload["selected_candidate_count"] == len(payload["selected_candidate_keys"])
    assert payload["full_candidate_count"] == len(payload["full_candidate_keys"])
    assert len(payload["domination_witnesses"]) == payload["full_candidate_count"]
    assert payload["selected_domain_contract"]["contract_ok"] is True
    assert payload["repaired_full_domain_packet"]["packet_ok"] is True
    assert payload["selected_domain_contract"]["repaired_selected_pool_ids"] == ["p0", "p1"]
    assert payload["repaired_full_domain_packet"]["full_domain_feasible_pool_ids"] == ["p0", "p1", "p2", "p3"]
    assert payload["selected_domain_contract"]["repaired_selected_domain_canonical_quote"] == payload[
        "repaired_full_domain_packet"
    ]["full_domain_canonical_quote"]
    for witness in payload["domination_witnesses"]:
        selected_key = (
            witness["selected_route_key"]["amount_in_total"],
            witness["selected_route_key"]["leg_count"],
            tuple(tuple(leg) for leg in witness["selected_route_key"]["legs_lex"]),
        )
        full_key = (
            witness["full_route_key"]["amount_in_total"],
            witness["full_route_key"]["leg_count"],
            tuple(tuple(leg) for leg in witness["full_route_key"]["legs_lex"]),
        )
        assert selected_key <= full_key

    ok, err = verify_exact_out_many_pool_repaired_key_cover_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_repaired_key_cover_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_repaired_key_cover_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["key_cover_holds"] = False

    ok, err = verify_exact_out_many_pool_repaired_key_cover_packet_payload(payload)
    assert not ok
    assert err == "repaired key-cover packet payload mismatch"


def test_exact_out_many_pool_repaired_key_cover_interpretation_packet_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    packet = build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["selected_winner_index_in_range"] is True
    assert payload["selected_winner_matches_certificate"] is True
    assert payload["selected_winner_key_minimal"] is True
    assert payload["domination_witness_indices_in_range"] is True
    assert payload["domination_witnesses_cover_full_candidates"] is True
    assert payload["domination_witness_keys_match_candidates"] is True
    assert payload["domination_witnesses_dominate"] is True
    assert payload["key_cover_packet"]["packet_ok"] is True

    ok, err = verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_repaired_key_cover_interpretation_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["domination_witnesses_cover_full_candidates"] = False

    ok, err = verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload(payload)
    assert not ok
    assert err == "repaired key-cover interpretation packet payload mismatch"


def test_exact_out_many_pool_bounded_workaround_packet_builds_and_verifies_on_repaired_prefilter_falsifier() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    packet = build_exact_out_many_pool_bounded_workaround_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["runtime_quotes_agree"] is True
    assert payload["oracle_contract"]["audit"]["runtime_matches_canonical"] is True
    assert payload["repaired_packet"]["packet_ok"] is True
    assert payload["repaired_full_domain_packet"]["packet_ok"] is True
    assert payload["repaired_full_domain_packet"]["repaired_matches_full_canonical"] is True
    assert payload["repaired_full_domain_packet"]["full_domain_canonical_quote"] == payload["repaired_packet"]["advisory_quote"]
    assert payload["runtime_matches_repaired_advisory"] is True
    assert payload["oracle_contract"]["audit"]["runtime_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]
    assert payload["repaired_packet"]["projection_cover_audit"] is not None
    assert payload["repaired_packet"]["projection_cover_audit"]["projection_cover_holds"] is True
    assert payload["repaired_packet"]["advisory_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]
    assert payload["repaired_packet"]["projection_cover_audit"]["canonical_quote_projected_path"] == [
        ["p0", 2, 5],
        ["p1", 2, 5],
    ]

    ok, err = verify_exact_out_many_pool_bounded_workaround_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_bounded_workaround_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_bounded_workaround_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["runtime_quotes_agree"] = False

    ok, err = verify_exact_out_many_pool_bounded_workaround_packet_payload(payload)
    assert not ok
    assert err == "bounded workaround packet payload mismatch"


def test_exact_out_many_pool_bounded_advisory_quote_packet_prefers_repaired_quote_on_falsifier() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, packet = quote_exact_out_many_pool_bounded_advisory(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert err is None
    assert quote is not None
    assert payload["schema"] == EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["quote_source"] == "selected_domain_runtime"
    assert payload["repaired_advisory_available"] is True
    assert payload["quote_matches_runtime"] is True
    assert payload["quote_matches_repaired_advisory"] is True
    assert payload["workaround_packet"]["repaired_full_domain_packet"]["packet_ok"] is True
    assert payload["workaround_packet"]["repaired_full_domain_packet"]["repaired_matches_full_canonical"] is True
    assert payload["advisory_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]
    assert payload["workaround_packet"]["repaired_packet"]["projection_cover_audit"] is not None
    assert payload["workaround_packet"]["repaired_packet"]["projection_cover_audit"]["projection_cover_holds"] is True
    assert payload["workaround_packet"]["oracle_contract"]["audit"]["runtime_quote"]["legs"] == [
        {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
        {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
    ]

    ok, verify_err = verify_exact_out_many_pool_bounded_advisory_quote_packet_payload(payload)
    assert ok, verify_err


def test_exact_out_many_pool_bounded_advisory_quote_packet_falls_back_to_runtime_when_aligned() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )

    packet = build_exact_out_many_pool_bounded_advisory_quote_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_full_domain_pools=6,
        max_enumerated_candidates=8_000,
    )
    payload = packet.to_dict()

    assert payload["packet_ok"] is True
    assert payload["quote_source"] == "selected_domain_runtime"
    assert payload["quote_matches_runtime"] is True
    assert payload["advisory_quote"]["amount_in_total"] == 2
    assert (
        payload["advisory_quote"]
        == payload["workaround_packet"]["oracle_contract"]["audit"]["runtime_quote"]
    )


def test_exact_out_many_pool_bounded_advisory_quote_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_bounded_advisory_quote_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["quote_source"] = "repaired_bounded_advisory"

    ok, err = verify_exact_out_many_pool_bounded_advisory_quote_packet_payload(payload)
    assert not ok
    assert err == "bounded advisory quote packet payload mismatch"


def test_exact_out_many_pool_certified_advisory_packet_builds_and_verifies_on_falsifier() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, packet = quote_exact_out_many_pool_certified_advisory(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert err is None
    assert quote is not None
    assert payload["schema"] == EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["selected_runtime_quotes_agree"] is True
    assert payload["effective_quote_source"] == "selected_domain_runtime"
    assert payload["effective_quote"] == {
        "amount_out_total": 4,
        "amount_in_total": 10,
        "legs": [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ],
    }
    assert payload["selected_domain_runtime_quote"] == {
        "amount_out_total": 4,
        "amount_in_total": 10,
        "legs": [
            {"pool_id": "p0", "amount_out": 2, "amount_in": 5},
            {"pool_id": "p1", "amount_out": 2, "amount_in": 5},
        ],
    }
    assert payload["effective_quote_matches_selected_runtime_quote"] is True
    assert payload["effective_quote_matches_repaired_advisory_quote"] is True
    assert payload["advisory_packet"]["workaround_packet"]["repaired_full_domain_packet"]["packet_ok"] is True
    assert (
        payload["advisory_packet"]["workaround_packet"]["repaired_full_domain_packet"]["repaired_matches_full_canonical"]
        is True
    )
    assert payload["selected_domain_runtime_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert payload["advisory_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert payload["selected_domain_projection_cover_available"] is True
    assert payload["selected_domain_projection_cover_holds"] is True
    assert payload["selected_domain_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert payload["selected_runtime_matches_selected_canonical_projected_path"] is True
    assert payload["repaired_projection_cover_available"] is True
    assert payload["repaired_projection_cover_holds"] is True
    assert payload["repaired_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert payload["advisory_matches_repaired_canonical_projected_path"] is True
    assert payload["effective_projection_cover_side"] == "selected_domain"
    assert payload["effective_projection_cover_holds"] is True
    assert payload["effective_canonical_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert payload["effective_quote_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert payload["effective_quote_matches_canonical_projected_path"] is True
    assert payload["certified_packet"]["packet_ok"] is True
    assert payload["advisory_packet"]["packet_ok"] is True
    assert payload["advisory_packet"]["quote_source"] == "selected_domain_runtime"
    assert payload["advisory_packet"]["workaround_packet"]["repaired_packet"]["projection_cover_audit"] is not None
    assert payload["advisory_packet"]["workaround_packet"]["repaired_packet"]["projection_cover_audit"]["projection_cover_holds"] is True

    ok, verify_err = verify_exact_out_many_pool_certified_advisory_packet_payload(payload)
    assert ok, verify_err


def test_exact_out_many_pool_certified_advisory_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_certified_advisory_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["selected_runtime_quotes_agree"] = False

    ok, err = verify_exact_out_many_pool_certified_advisory_packet_payload(payload)
    assert not ok
    assert err == "certified advisory packet payload mismatch"


def test_exact_out_many_pool_default_uses_certified_advisory_policy() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, packet = quote_exact_out_many_pool_default(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert err is None
    assert quote is not None
    assert packet.packet_ok is True
    assert packet.selected_runtime_quotes_agree is True
    assert packet.certified_packet.packet_ok is True
    assert packet.advisory_packet.quote_source == "selected_domain_runtime"
    assert packet.advisory_packet.workaround_packet.repaired_packet.projection_cover_audit is not None


def test_exact_out_many_pool_default_packet_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    packet = build_exact_out_many_pool_default_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert packet.packet_ok is True
    assert packet.selected_runtime_quotes_agree is True
    assert packet.to_dict()["effective_quote_source"] == "selected_domain_runtime"
    assert packet.to_dict()["effective_quote_matches_selected_runtime_quote"] is True
    assert packet.to_dict()["effective_quote_matches_repaired_advisory_quote"] is True
    assert packet.to_dict()["selected_domain_runtime_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert packet.to_dict()["advisory_projected_path"] == [["p0", 2, 5], ["p1", 2, 5]]
    assert packet.to_dict()["selected_domain_projection_cover_holds"] is True
    assert packet.to_dict()["repaired_projection_cover_holds"] is True
    assert packet.to_dict()["effective_projection_cover_side"] == "selected_domain"
    assert packet.to_dict()["effective_quote_matches_canonical_projected_path"] is True
    ok, err = verify_exact_out_many_pool_default_packet_payload(packet.to_dict())
    assert ok, err


def test_exact_out_many_pool_default_quote_packet_matches_default_build_packet() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, quote_packet = quote_exact_out_many_pool_default(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    build_packet = build_exact_out_many_pool_default_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert err is None
    assert quote is not None
    assert quote_packet.to_dict() == build_packet.to_dict()


def test_exact_out_many_pool_oracle_contract_aligns_runtime_on_known_counterexample() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )

    contract = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )
    payload = contract.to_dict()

    assert payload["contract_ok"] is True
    assert payload["audit"]["runtime_matches_canonical"] is True
    assert payload["audit"]["runtime_quote"]["amount_in_total"] == 2
    assert payload["audit"]["canonical_winner_quote"]["amount_in_total"] == 2
    assert payload["audit"]["runtime_projected_path"] == [["pool_b", 3, 2]]
    assert payload["audit"]["canonical_winner_projected_path"] == [["pool_b", 3, 2]]
    assert payload["audit"]["runtime_matches_canonical_projected_path"] is True
    assert payload["audit"]["projection_cover_available"] is True
    assert payload["audit"]["projection_cover_holds"] is True
    assert payload["audit"]["projection_cover_audit"] is not None
    assert payload["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
    assert payload["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 2]]

    ok, err = verify_exact_out_many_pool_oracle_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_oracle_contract_carries_projection_cover_on_mixed_curve_selected_domain() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=20, fee_bps=0, curve_tag=CURVE_TAG_SUM_BOOST_V1),
    )

    contract = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_candidate_pools=2,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )
    payload = contract.to_dict()

    assert payload["contract_ok"] is True
    assert payload["audit"]["runtime_matches_canonical"] is True
    assert payload["audit"]["runtime_projected_path"] == [["pool_b", 3, 5]]
    assert payload["audit"]["canonical_winner_projected_path"] == [["pool_b", 3, 5]]
    assert payload["audit"]["runtime_matches_canonical_projected_path"] is True
    assert payload["audit"]["projection_cover_available"] is True
    assert payload["audit"]["projection_cover_holds"] is True
    assert payload["audit"]["projection_cover_audit"] is not None
    assert payload["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
    assert payload["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]

    ok, err = verify_exact_out_many_pool_oracle_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_oracle_contract_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )
    payload = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    ).to_dict()
    payload["audit"]["projection_cover_audit"]["projection_cover_holds"] = False

    ok, err = verify_exact_out_many_pool_oracle_contract_payload(payload)
    assert not ok
    assert err == "oracle contract payload mismatch"


def test_exact_out_many_pool_oracle_contract_rejects_contract_ok_tampering() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )
    payload = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    ).to_dict()
    assert payload["contract_ok"] is True
    payload["contract_ok"] = False

    ok, err = verify_exact_out_many_pool_oracle_contract_payload(payload)
    assert not ok
    assert err == "oracle contract payload mismatch"


def test_guard_exact_out_many_pool_runtime_canonicality_accepts_small_match() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )

    ok, err, contract = guard_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_enumerated_candidates=2_000,
    )

    assert ok is True
    assert err is None
    assert contract.audit.runtime_matches_canonical is True
    assert contract.audit.runtime_quote == contract.audit.canonical_winner_quote
    assert contract.contract_ok is True
    assert contract.audit.projection_cover_audit is not None
    assert contract.audit.projection_cover_audit.projection_cover_holds is True


def test_guard_exact_out_many_pool_runtime_canonicality_accepts_known_counterexample_after_alignment() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )

    ok, err, contract = guard_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )

    assert ok is True
    assert err is None
    assert contract.audit.runtime_matches_canonical is True
    assert contract.audit.runtime_quote.amount_in_total == 2
    assert contract.audit.canonical_winner_quote.amount_in_total == 2
    assert contract.contract_ok is True
    assert contract.audit.projection_cover_audit is not None
    assert contract.audit.projection_cover_audit.projection_cover_holds is True


def test_guard_exact_out_many_pool_runtime_canonicality_accepts_mixed_curve_selected_domain() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=20, fee_bps=0, curve_tag=CURVE_TAG_SUM_BOOST_V1),
    )

    ok, err, contract = guard_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_candidate_pools=2,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )

    assert ok is True
    assert err is None
    assert contract.audit.runtime_matches_canonical is True
    assert contract.contract_ok is True
    assert contract.audit.projection_cover_audit is not None
    assert contract.audit.projection_cover_audit.projection_cover_holds is True
    assert contract.audit.projection_cover_audit.canonical_quote_projected_path == (("pool_b", 3, 5),)


def test_guard_exact_out_many_pool_runtime_canonicality_requires_projection_cover(monkeypatch: pytest.MonkeyPatch) -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )

    def _raise_projection_cover_unavailable(*_args: object, **_kwargs: object) -> object:
        raise ValueError("projection cover unavailable")

    monkeypatch.setattr(
        exact_out_module,
        "_kernel_audit_exact_out_many_pool_selected_domain_projection_cover",
        _raise_projection_cover_unavailable,
    )

    ok, err, contract = guard_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_enumerated_candidates=2_000,
    )

    assert ok is False
    assert err == EXACT_OUT_MANY_POOL_PROJECTION_COVER_ERROR
    assert contract.audit.runtime_matches_canonical is True
    assert contract.audit.projection_cover_audit is None
    assert contract.contract_ok is False
    assert contract.to_dict()["contract_ok"] is False


def test_quote_exact_out_many_pool_guarded_returns_quote_on_match() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )

    quote, err, contract = quote_exact_out_many_pool_guarded(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_enumerated_candidates=2_000,
    )

    assert err is None
    assert quote == contract.audit.runtime_quote
    assert contract.audit.runtime_matches_canonical is True
    assert contract.contract_ok is True


def test_quote_exact_out_many_pool_guarded_accepts_mixed_curve_selected_domain() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=20, fee_bps=0, curve_tag=CURVE_TAG_SUM_BOOST_V1),
    )

    quote, err, contract = quote_exact_out_many_pool_guarded(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_candidate_pools=2,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )

    assert err is None
    assert quote == contract.audit.runtime_quote
    assert contract.audit.runtime_matches_canonical is True
    assert contract.contract_ok is True
    assert contract.audit.projection_cover_audit is not None
    assert contract.audit.projection_cover_audit.projection_cover_holds is True
    assert contract.audit.projection_cover_audit.canonical_quote_projected_path == (("pool_b", 3, 5),)


def test_quote_exact_out_many_pool_guarded_accepts_known_counterexample_after_alignment() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )

    quote, err, contract = quote_exact_out_many_pool_guarded(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )

    assert err is None
    assert quote == contract.audit.runtime_quote
    assert contract.audit.runtime_matches_canonical is True
    assert contract.contract_ok is True


def test_exact_out_many_pool_guarded_quote_packet_builds_on_match() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )
    packet = build_exact_out_many_pool_guarded_quote_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_enumerated_candidates=2_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA
    assert payload["guard_ok"] is True
    assert payload["contract"]["contract_ok"] is True
    assert payload["quote"] == payload["contract"]["audit"]["runtime_quote"]

    ok, err = verify_exact_out_many_pool_guarded_quote_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_guarded_quote_packet_carries_projection_cover_on_mixed_curve_selected_domain() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=20, fee_bps=0, curve_tag=CURVE_TAG_SUM_BOOST_V1),
    )
    packet = build_exact_out_many_pool_guarded_quote_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_candidate_pools=2,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )
    payload = packet.to_dict()

    assert payload["guard_ok"] is True
    assert payload["contract"]["contract_ok"] is True
    assert payload["selected_domain_projection_cover_available"] is True
    assert payload["selected_domain_projection_cover_holds"] is True
    assert payload["selected_domain_canonical_projected_path"] == [["pool_b", 3, 5]]
    assert payload["selected_runtime_matches_selected_canonical_projected_path"] is True
    assert payload["guarded_quote"] == payload["contract"]["audit"]["runtime_quote"]
    assert payload["guarded_quote_projected_path"] == [["pool_b", 3, 5]]
    assert payload["guarded_quote_matches_runtime_quote"] is True
    assert payload["guarded_quote_matches_canonical_projected_path"] is True
    assert payload["contract"]["audit"]["projection_cover_audit"] is not None
    assert payload["contract"]["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
    assert payload["contract"]["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]

    ok, err = verify_exact_out_many_pool_guarded_quote_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_guarded_quote_packet_builds_on_known_counterexample_after_alignment_and_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )
    payload = build_exact_out_many_pool_guarded_quote_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    ).to_dict()

    assert payload["guard_ok"] is True
    assert payload["contract"]["contract_ok"] is True
    assert payload["error"] is None
    assert payload["quote"] == payload["contract"]["audit"]["runtime_quote"]

    ok, err = verify_exact_out_many_pool_guarded_quote_packet_payload(payload)
    assert ok, err

    payload["guard_ok"] = False
    ok2, err2 = verify_exact_out_many_pool_guarded_quote_packet_payload(payload)
    assert not ok2
    assert err2 == "guarded quote packet payload mismatch"


def test_exact_out_many_pool_certified_winner_packet_builds_on_match() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )
    packet = build_exact_out_many_pool_certified_winner_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_enumerated_candidates=2_000,
    )
    payload = packet.to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["domain_contract"]["contract_ok"] is True
    assert payload["guarded_packet"]["guard_ok"] is True

    ok, err = verify_exact_out_many_pool_certified_winner_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_certified_winner_packet_carries_projection_cover_on_mixed_curve_selected_domain() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=20, fee_bps=0, curve_tag=CURVE_TAG_SUM_BOOST_V1),
    )
    packet = build_exact_out_many_pool_certified_winner_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=2,
        max_candidate_pools=2,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    )
    payload = packet.to_dict()

    assert payload["packet_ok"] is True
    assert payload["selected_domain_projection_cover_available"] is True
    assert payload["selected_domain_projection_cover_holds"] is True
    assert payload["selected_domain_canonical_projected_path"] == [["pool_b", 3, 5]]
    assert payload["selected_runtime_matches_selected_canonical_projected_path"] is True
    assert payload["certified_quote"] == payload["guarded_packet"]["quote"]
    assert payload["certified_quote_projected_path"] == [["pool_b", 3, 5]]
    assert payload["certified_quote_matches_runtime_quote"] is True
    assert payload["certified_quote_matches_canonical_projected_path"] is True
    assert payload["guarded_packet"]["contract"]["audit"]["projection_cover_audit"] is not None
    assert payload["guarded_packet"]["contract"]["audit"]["projection_cover_audit"]["projection_cover_holds"] is True
    assert payload["guarded_packet"]["contract"]["audit"]["projection_cover_audit"]["canonical_quote_projected_path"] == [["pool_b", 3, 5]]

    ok, err = verify_exact_out_many_pool_certified_winner_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_certified_winner_packet_builds_on_known_counterexample_after_alignment_and_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=40, reserve1=20, fee_bps=0),
        _pool(pool_id="pool_b", reserve0=40, reserve1=63, fee_bps=0),
        _pool(pool_id="pool_c", reserve0=40, reserve1=20, fee_bps=0),
    )
    payload = build_exact_out_many_pool_certified_winner_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=3,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=16,
        max_enumerated_candidates=8_000,
    ).to_dict()

    assert payload["packet_ok"] is True
    assert payload["domain_contract"]["contract_ok"] is True
    assert payload["guarded_packet"]["guard_ok"] is True
    assert payload["guarded_packet"]["error"] is None

    ok, err = verify_exact_out_many_pool_certified_winner_packet_payload(payload)
    assert ok, err

    payload["packet_ok"] = False
    ok2, err2 = verify_exact_out_many_pool_certified_winner_packet_payload(payload)
    assert not ok2
    assert err2 == "certified winner packet payload mismatch"


def test_enumerate_exact_out_many_pool_candidates_fails_closed_on_budget_overflow() -> None:
    pools = (
        _pool(pool_id="pool_a", reserve0=160, reserve1=80),
        _pool(pool_id="pool_b", reserve0=160, reserve1=80),
        _pool(pool_id="pool_c", reserve0=160, reserve1=80),
    )

    with pytest.raises(ValueError, match="max_enumerated_candidates"):
        enumerate_exact_out_many_pool_candidates(
            pools,
            asset_in="A",
            asset_out="B",
            amount_out_total=8,
            max_legs=3,
            max_candidate_pools=3,
            max_enumerated_candidates=1,
        )


def test_exact_out_many_pool_certified_winner_packet_propagates_max_full_domain_pools() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )
    payload = build_exact_out_many_pool_certified_winner_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_full_domain_pools=9,
        max_enumerated_candidates=2_000,
    ).to_dict()

    assert payload["guarded_packet"]["contract"]["max_full_domain_pools"] == 9

    ok, err = verify_exact_out_many_pool_certified_winner_packet_payload(payload)
    assert ok, err


def test_exact_out_many_pool_audited_bounds_contract_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )
    payload = build_exact_out_many_pool_audited_bounds_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_full_domain_pools=9,
        max_enumerated_candidates=2_000,
    ).to_dict()

    assert payload["schema"] == EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA
    assert payload["contract_ok"] is True
    assert payload["selected_domain_budget_respected"] is True
    assert payload["repaired_selection_budget_respected"] is True
    assert payload["full_domain_pool_budget_respected"] is True
    assert payload["full_domain_candidate_budget_respected"] is True
    assert payload["budget_parameters_bound"] is True
    assert payload["failure_path_explicit"] is True
    assert payload["success_path_replayable"] is True
    assert payload["certified_advisory_packet"]["certified_packet"]["guarded_packet"]["contract"]["max_full_domain_pools"] == 9

    ok, err = verify_exact_out_many_pool_audited_bounds_contract_payload(payload)
    assert ok, err


def test_exact_out_many_pool_audited_bounds_contract_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="pool_b", reserve0=100, reserve1=34),
        _pool(pool_id="pool_a", reserve0=120, reserve1=40),
        _pool(pool_id="pool_c", reserve0=160, reserve1=60),
    )
    payload = build_exact_out_many_pool_audited_bounds_contract(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=6,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=6,
        max_iters=512,
        window=8,
        brute_force_max=12,
        max_full_domain_pools=9,
        max_enumerated_candidates=2_000,
    ).to_dict()

    payload["budget_parameters_bound"] = False
    ok, err = verify_exact_out_many_pool_audited_bounds_contract_payload(payload)
    assert not ok
    assert err == "audited bounds contract payload mismatch"


def test_exact_out_many_pool_adaptive_liveness_packet_builds_and_verifies() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, packet = quote_exact_out_many_pool_adaptive(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert err is None
    assert quote is not None
    assert payload["schema"] == EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["liveness_ok"] is True
    assert payload["audited_bounds_contract_ok"] is True
    assert payload["cheap_path_attempted"] is True
    assert payload["cheap_path_success"] is True
    assert payload["fallback_required"] is False
    assert payload["fallback_attempted"] is False
    assert payload["fallback_available"] is True
    assert payload["fallback_success"] is False
    assert payload["returned_success"] is True
    assert payload["explicit_failure"] is False
    assert payload["no_spurious_failure"] is True
    assert payload["effective_quote_source"] == "default_certified_advisory"
    assert payload["effective_quote"] == payload["default_effective_quote"]
    assert payload["effective_quote_matches_full_domain_canonical"] is True
    assert payload["failure_reason"] is None
    assert payload["nested_error"] is None

    ok, verify_err = verify_exact_out_many_pool_adaptive_liveness_packet_payload(payload)
    assert ok, verify_err


def test_exact_out_many_pool_adaptive_liveness_packet_explicit_failure_is_replayable() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    quote, err, packet = quote_exact_out_many_pool_adaptive(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=1,
        max_candidates=2,
        max_iters=1,
        window=0,
        brute_force_max=0,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    payload = packet.to_dict()

    assert quote is None
    assert err == "default_packet_not_ok"
    assert payload["schema"] == EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA
    assert payload["packet_ok"] is True
    assert payload["liveness_ok"] is True
    assert payload["audited_bounds_contract_ok"] is True
    assert payload["cheap_path_attempted"] is True
    assert payload["cheap_path_success"] is False
    assert payload["fallback_required"] is True
    assert payload["fallback_attempted"] is True
    assert payload["fallback_available"] is False
    assert payload["fallback_success"] is False
    assert payload["returned_success"] is False
    assert payload["explicit_failure"] is True
    assert payload["failure_reason_present"] is True
    assert payload["failure_reason"] == "default_packet_not_ok"
    assert payload["nested_error"] == "many_pool_repaired_prefilter_contract_not_ok"
    assert payload["no_spurious_failure"] is True
    assert payload["effective_quote_source"] is None
    assert payload["effective_quote"] is None

    ok, verify_err = verify_exact_out_many_pool_adaptive_liveness_packet_payload(payload)
    assert ok, verify_err


def test_exact_out_many_pool_adaptive_liveness_packet_rejects_tampering() -> None:
    pools = (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )

    payload = build_exact_out_many_pool_adaptive_liveness_packet(
        pools,
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    ).to_dict()
    payload["fallback_attempted"] = True

    ok, err = verify_exact_out_many_pool_adaptive_liveness_packet_payload(payload)
    assert not ok
    assert err == "adaptive liveness packet payload mismatch"
