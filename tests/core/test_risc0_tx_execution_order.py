from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.core.risc0_tx_execution_order import (
    MAX_EXACT_STALE_ROUTE_ORDER_TXS,
    MAX_ROUTE_PRICE_INTERVALS,
    RISC0_SPOT_PROOF_TYPE_V1,
    ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_SCHEMA_V1,
    ROUTE_PRICE_INTERVAL_AUTHORITY_SCHEMA_V1,
    ROUTE_PRICE_INTERVAL_SOURCE_VERIFICATION_STATUS_VERIFIED,
    ROUTE_PRICE_INTERVALS_ROOT_DOMAIN_V1,
    TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0,
    RoutePriceIntervalAuthorityPolicySourceV1,
    RoutePriceIntervalAuthorityPolicyV1,
    RoutePriceIntervalAuthorityV1,
    RoutePriceIntervalV1,
    TxExecutionOrderInputV1,
    build_stale_route_order_certificate_v1,
    build_tx_execution_order_certificate_v1,
    build_tx_execution_order_commitment_receipt_v0,
    normalize_tx_execution_order_context_v1,
    route_price_interval_authority_policy_root_hex_v1,
    route_price_interval_authority_root_hex_v1,
    route_price_interval_distortion_certificate_v1,
    route_price_intervals_root_bytes_v1,
    route_price_intervals_root_hex_v1,
    stale_route_order_receipt_requirement_v1,
    tx_execution_order_commitment_hex_v1,
    validate_route_price_interval_authority_v1,
    validate_route_price_interval_width_policy_v1,
    validate_stale_route_order_receipt_policy_v1,
)

ABI_CORPUS_PATH = Path(__file__).resolve().parents[1] / "fixtures" / "risc0_tx_execution_order_abi_v1.json"
ROUTE_PRICE_INTERVALS_ABI_CORPUS_PATH = (
    Path(__file__).resolve().parents[1] / "fixtures" / "risc0_route_price_intervals_abi_v1.json"
)


def _load_tx_order_abi_corpus() -> dict[str, object]:
    with ABI_CORPUS_PATH.open(encoding="utf-8") as fh:
        data = json.load(fh)
    assert isinstance(data, dict)
    return data


def _load_route_price_intervals_abi_corpus() -> dict[str, object]:
    with ROUTE_PRICE_INTERVALS_ABI_CORPUS_PATH.open(encoding="utf-8") as fh:
        data = json.load(fh)
    assert isinstance(data, dict)
    return data


def _route_price_intervals_from_json(raw_intervals: object) -> list[RoutePriceIntervalV1]:
    assert isinstance(raw_intervals, list)
    intervals: list[RoutePriceIntervalV1] = []
    for raw_interval in raw_intervals:
        assert isinstance(raw_interval, dict)
        asset = raw_interval["asset"]
        low_e8 = raw_interval["low_e8"]
        point_e8 = raw_interval["point_e8"]
        high_e8 = raw_interval["high_e8"]
        assert isinstance(asset, str)
        assert isinstance(low_e8, int)
        assert isinstance(point_e8, int)
        assert isinstance(high_e8, int)
        intervals.append(
            RoutePriceIntervalV1(
                asset=asset,
                low_e8=low_e8,
                point_e8=point_e8,
                high_e8=high_e8,
            )
        )
    return intervals


def _route_price_interval_authority(
    intervals: list[RoutePriceIntervalV1],
    *,
    price_timestamp: int = 10,
    max_staleness_seconds: int = 60,
) -> RoutePriceIntervalAuthorityV1:
    return RoutePriceIntervalAuthorityV1(
        schema=ROUTE_PRICE_INTERVAL_AUTHORITY_SCHEMA_V1,
        source_id="test-route-interval-oracle",
        source_root=bytes([7]) * 32,
        price_timestamp=price_timestamp,
        max_staleness_seconds=max_staleness_seconds,
        route_price_intervals_root=route_price_intervals_root_bytes_v1(intervals),
    )


def _route_price_interval_authority_policy(
    authority: RoutePriceIntervalAuthorityV1,
) -> RoutePriceIntervalAuthorityPolicyV1:
    return RoutePriceIntervalAuthorityPolicyV1(
        schema=ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_SCHEMA_V1,
        policy_id="test-route-interval-policy",
        sources=(
            RoutePriceIntervalAuthorityPolicySourceV1(
                source_id=authority.source_id,
                source_root=authority.source_root,
                verification_root=bytes([8]) * 32,
                verification_status=ROUTE_PRICE_INTERVAL_SOURCE_VERIFICATION_STATUS_VERIFIED,
            ),
        ),
    )


def _tx(
    sender: str,
    *,
    route_reads: tuple[str, ...] = (),
    writes: tuple[str, ...] = (),
    protected_values: tuple[tuple[str, int], ...] = (),
) -> TxExecutionOrderInputV1:
    return TxExecutionOrderInputV1(
        sender_pubkey=sender,
        route_read_pool_ids=route_reads,
        pool_write_ids=writes,
        protected_values=protected_values,
    )


def test_route_price_intervals_root_matches_rust_known_vectors() -> None:
    corpus = _load_route_price_intervals_abi_corpus()

    assert corpus["domain_ascii"] == ROUTE_PRICE_INTERVALS_ROOT_DOMAIN_V1
    assert corpus["hash"] == "sha256"
    assert corpus["string_encoding"] == "u32_be_length_prefixed_utf8"
    assert corpus["count_encoding"] == "u32_be"
    assert corpus["integer_encoding"] == "u128_be"
    assert corpus["max_intervals"] == MAX_ROUTE_PRICE_INTERVALS

    positive_cases = corpus["positive_cases"]
    assert isinstance(positive_cases, list)
    for case in positive_cases:
        assert isinstance(case, dict)
        intervals = _route_price_intervals_from_json(case["intervals"])
        assert route_price_intervals_root_hex_v1(intervals) == case["root"]


def test_route_price_intervals_root_canonicalizes_asset_order() -> None:
    intervals = [
        RoutePriceIntervalV1("ASSET2", 100_000_000, 125_000_000, 150_000_000),
        RoutePriceIntervalV1("ASSET0", 200_000_000, 200_000_000, 200_000_000),
    ]
    sorted_intervals = [
        RoutePriceIntervalV1("ASSET0", 200_000_000, 200_000_000, 200_000_000),
        RoutePriceIntervalV1("ASSET2", 100_000_000, 125_000_000, 150_000_000),
    ]

    assert route_price_intervals_root_hex_v1(intervals) == route_price_intervals_root_hex_v1(
        sorted_intervals
    )


def test_route_price_intervals_abi_corpus_negative_cases_reject_python() -> None:
    corpus = _load_route_price_intervals_abi_corpus()
    negative_cases = corpus["negative_cases"]
    assert isinstance(negative_cases, list)
    error_types = {"TypeError": TypeError, "ValueError": ValueError}

    for case in negative_cases:
        assert isinstance(case, dict)
        intervals = _route_price_intervals_from_json(case["intervals"])
        error_type = error_types[str(case["error_type"])]
        with pytest.raises(error_type, match=str(case["error"])):
            route_price_intervals_root_hex_v1(intervals)


def test_route_price_intervals_rejects_type_and_u128_boundaries() -> None:
    with pytest.raises(TypeError, match="route_price_intervals entries must be RoutePriceIntervalV1"):
        route_price_intervals_root_hex_v1([("ASSET0", 1, 1, 1)])  # type: ignore[list-item]

    with pytest.raises(TypeError, match="route price interval low_e8 must be an integer"):
        route_price_intervals_root_hex_v1([RoutePriceIntervalV1("ASSET0", True, 1, 1)])

    with pytest.raises(ValueError, match="route price interval high_e8 must be a u128"):
        route_price_intervals_root_hex_v1([RoutePriceIntervalV1("ASSET0", 0, 0, 2**128)])


def test_route_price_intervals_rejects_excessive_count() -> None:
    intervals = [
        RoutePriceIntervalV1(f"ASSET{index}", 1, 1, 1)
        for index in range(MAX_ROUTE_PRICE_INTERVALS + 1)
    ]

    with pytest.raises(ValueError, match="route price intervals exceeds max"):
        route_price_intervals_root_hex_v1(intervals)


def test_route_price_interval_distortion_certificate_bounds_width_and_value_loss() -> None:
    intervals = [
        RoutePriceIntervalV1("ASSET0", 99_000_000, 100_000_000, 101_000_000),
        RoutePriceIntervalV1("ASSET1", 200_000_000, 200_000_000, 220_000_000),
    ]

    certificate = route_price_interval_distortion_certificate_v1(
        intervals,
        protected_values=(("ASSET0", 1_000_000), ("ASSET1", 2_000_000)),
    )

    assert certificate.route_price_intervals_root == route_price_intervals_root_hex_v1(intervals)
    assert certificate.max_downside_e8 == 1_000_000
    assert certificate.max_upside_e8 == 20_000_000
    assert certificate.max_width_e8 == 20_000_000
    assert certificate.max_downside_bps == 100
    assert certificate.max_upside_bps == 1_000
    assert certificate.max_width_bps == 1_000
    assert certificate.protected_value_distortion_atoms == (
        ("ASSET0", 10_000),
        ("ASSET1", 200_000),
    )


def test_route_price_interval_distortion_rejects_unbounded_zero_point_interval() -> None:
    route_price_intervals_root_hex_v1([RoutePriceIntervalV1("ASSET0", 0, 0, 1)])

    with pytest.raises(ValueError, match="route price interval point_e8 zero with positive width"):
        route_price_interval_distortion_certificate_v1([RoutePriceIntervalV1("ASSET0", 0, 0, 1)])


def test_route_price_interval_distortion_rejects_missing_protected_value_interval() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 99, 100, 101)]

    with pytest.raises(ValueError, match="protected value asset missing route price interval"):
        route_price_interval_distortion_certificate_v1(
            intervals,
            protected_values=(("ASSET1", 1_000),),
        )


def test_route_price_interval_width_policy_monotone_for_narrower_intervals() -> None:
    wide = route_price_interval_distortion_certificate_v1([RoutePriceIntervalV1("ASSET0", 90, 100, 110)])
    narrow = route_price_interval_distortion_certificate_v1([RoutePriceIntervalV1("ASSET0", 99, 100, 101)])

    assert narrow.max_width_bps < wide.max_width_bps
    validate_route_price_interval_width_policy_v1([RoutePriceIntervalV1("ASSET0", 99, 100, 101)], max_width_bps=200)
    with pytest.raises(ValueError, match="route price interval width exceeds policy"):
        validate_route_price_interval_width_policy_v1(
            [RoutePriceIntervalV1("ASSET0", 90, 100, 110)],
            max_width_bps=200,
        )


def test_route_price_interval_authority_root_matches_rust_known_vectors() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 1, 2, 3)]
    authority = _route_price_interval_authority(intervals)
    policy = _route_price_interval_authority_policy(authority)

    assert (
        route_price_interval_authority_root_hex_v1(None)
        == "609d2988748b0a03f6952c4fbd9c4fcc376398210826d653ce6ec1bbf2fdb2b5"
    )
    assert (
        route_price_interval_authority_root_hex_v1(authority)
        == "4c5557350855d1a9ba0084567b1f37bec405d554f04102896036aef99f3c6315"
    )
    assert (
        route_price_interval_authority_policy_root_hex_v1(None)
        == "41e70305b4f8f20a1345d691514a5248b15d1bf74bb750cad2b662549225fa03"
    )
    assert (
        route_price_interval_authority_policy_root_hex_v1(policy)
        == "1fe535be0b989f27bcc851bda12d3af65fa521672db4d63b53e03228f428053f"
    )


def test_route_price_interval_authority_freshness_policy_accepts_matching_fresh_source() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 1, 2, 3)]
    authority = _route_price_interval_authority(intervals)
    policy = _route_price_interval_authority_policy(authority)

    assert (
        validate_route_price_interval_authority_v1(
            intervals,
            authority,
            policy=policy,
            block_timestamp=70,
        )
        == (
            "4c5557350855d1a9ba0084567b1f37bec405d554f04102896036aef99f3c6315",
            "1fe535be0b989f27bcc851bda12d3af65fa521672db4d63b53e03228f428053f",
        )
    )


def test_route_price_interval_authority_width_policy_rejects_fresh_uninformative_interval() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 1, 1, 10**12)]
    authority = _route_price_interval_authority(intervals)
    policy = _route_price_interval_authority_policy(authority)

    validate_route_price_interval_authority_v1(
        intervals,
        authority,
        policy=policy,
        block_timestamp=70,
    )

    with pytest.raises(ValueError, match="route price interval width exceeds policy"):
        validate_route_price_interval_authority_v1(
            intervals,
            authority,
            policy=policy,
            block_timestamp=70,
            max_interval_width_bps=100,
        )


def test_route_price_interval_authority_freshness_policy_rejects_missing_or_extra_authority() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 1, 2, 3)]
    authority = _route_price_interval_authority(intervals)

    with pytest.raises(ValueError, match="route price interval authority required"):
        validate_route_price_interval_authority_v1(intervals, None, block_timestamp=70)

    with pytest.raises(ValueError, match="route price interval authority without intervals"):
        validate_route_price_interval_authority_v1([], authority, block_timestamp=70)

    with pytest.raises(ValueError, match="route price interval authority policy required"):
        validate_route_price_interval_authority_v1(intervals, authority, block_timestamp=70)

    with pytest.raises(ValueError, match="route price interval authority policy without intervals"):
        validate_route_price_interval_authority_v1(
            [],
            None,
            policy=_route_price_interval_authority_policy(authority),
            block_timestamp=70,
        )


def test_route_price_interval_authority_freshness_policy_rejects_stale_future_and_mismatch() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 1, 2, 3)]
    stale = _route_price_interval_authority(intervals, price_timestamp=9, max_staleness_seconds=60)
    future = _route_price_interval_authority(intervals, price_timestamp=71, max_staleness_seconds=60)
    stale_policy = _route_price_interval_authority_policy(stale)
    future_policy = _route_price_interval_authority_policy(future)
    mismatch = RoutePriceIntervalAuthorityV1(
        schema=ROUTE_PRICE_INTERVAL_AUTHORITY_SCHEMA_V1,
        source_id="test-route-interval-oracle",
        source_root=bytes([7]) * 32,
        price_timestamp=10,
        max_staleness_seconds=60,
        route_price_intervals_root=bytes([9]) * 32,
    )
    mismatch_policy = _route_price_interval_authority_policy(mismatch)

    with pytest.raises(ValueError, match="route price interval authority stale"):
        validate_route_price_interval_authority_v1(
            intervals,
            stale,
            policy=stale_policy,
            block_timestamp=70,
        )

    with pytest.raises(ValueError, match="route price interval authority timestamp future"):
        validate_route_price_interval_authority_v1(
            intervals,
            future,
            policy=future_policy,
            block_timestamp=70,
        )

    with pytest.raises(ValueError, match="route price interval authority root mismatch"):
        validate_route_price_interval_authority_v1(
            intervals,
            mismatch,
            policy=mismatch_policy,
            block_timestamp=70,
        )


def test_route_price_interval_authority_policy_rejects_unverified_or_unlisted_source() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 1, 2, 3)]
    authority = _route_price_interval_authority(intervals)
    wrong_source_policy = RoutePriceIntervalAuthorityPolicyV1(
        schema=ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_SCHEMA_V1,
        policy_id="test-route-interval-policy",
        sources=(
            RoutePriceIntervalAuthorityPolicySourceV1(
                source_id=authority.source_id,
                source_root=bytes([9]) * 32,
                verification_root=bytes([8]) * 32,
                verification_status=ROUTE_PRICE_INTERVAL_SOURCE_VERIFICATION_STATUS_VERIFIED,
            ),
        ),
    )
    unverified_policy = RoutePriceIntervalAuthorityPolicyV1(
        schema=ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_SCHEMA_V1,
        policy_id="test-route-interval-policy",
        sources=(
            RoutePriceIntervalAuthorityPolicySourceV1(
                source_id=authority.source_id,
                source_root=authority.source_root,
                verification_root=bytes([8]) * 32,
                verification_status="unchecked",
            ),
        ),
    )

    with pytest.raises(ValueError, match="route price interval authority source not in policy"):
        validate_route_price_interval_authority_v1(
            intervals,
            authority,
            policy=wrong_source_policy,
            block_timestamp=70,
        )

    with pytest.raises(ValueError, match="route price interval authority policy source unverified"):
        route_price_interval_authority_policy_root_hex_v1(unverified_policy)


def test_route_price_interval_authority_rejects_empty_source_and_unbounded_staleness() -> None:
    intervals = [RoutePriceIntervalV1("ASSET0", 1, 2, 3)]
    empty_source_root = RoutePriceIntervalAuthorityV1(
        schema=ROUTE_PRICE_INTERVAL_AUTHORITY_SCHEMA_V1,
        source_id="test-route-interval-oracle",
        source_root=bytes(32),
        price_timestamp=10,
        max_staleness_seconds=60,
        route_price_intervals_root=route_price_intervals_root_bytes_v1(intervals),
    )
    unbounded_staleness = _route_price_interval_authority(
        intervals,
        max_staleness_seconds=301,
    )

    with pytest.raises(ValueError, match="route price interval authority source root empty"):
        route_price_interval_authority_root_hex_v1(empty_source_root)

    with pytest.raises(ValueError, match="route price interval authority staleness exceeds max"):
        route_price_interval_authority_root_hex_v1(unbounded_staleness)


def test_tx_execution_order_commitment_matches_rust_known_vectors() -> None:
    corpus = _load_tx_order_abi_corpus()

    assert corpus["domain_ascii"] == "tau_state_proof_tx_execution_order_v1:"
    assert corpus["hash"] == "sha256"
    assert corpus["length_encoding"] == "u32_be"
    assert corpus["index_encoding"] == "u32_be"
    assert corpus["proof_type"] == RISC0_SPOT_PROOF_TYPE_V1
    assert corpus["receipt_schema"] == TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0

    positive_cases = corpus["positive_cases"]
    assert isinstance(positive_cases, list)
    for case in positive_cases:
        assert isinstance(case, dict)
        normalized_order = case["normalized_order"]
        assert isinstance(normalized_order, list)
        assert tx_execution_order_commitment_hex_v1(normalized_order) == case["commitment"]


def test_tx_execution_order_abi_corpus_positive_cases_match_python_receipts() -> None:
    corpus = _load_tx_order_abi_corpus()
    positive_cases = corpus["positive_cases"]
    assert isinstance(positive_cases, list)

    for case in positive_cases:
        assert isinstance(case, dict)
        raw_order = case["raw_order"]
        tx_count = case["tx_count"]
        normalized_order = case["normalized_order"]
        certificate = build_tx_execution_order_certificate_v1(raw_order, tx_count=tx_count)
        assert certificate.tx_execution_order == tuple(normalized_order)
        assert certificate.tx_execution_order_commitment == case["commitment"]
        assert build_tx_execution_order_commitment_receipt_v0(certificate) == case["receipt"]


def test_tx_execution_order_abi_corpus_negative_cases_reject_python() -> None:
    corpus = _load_tx_order_abi_corpus()
    negative_cases = corpus["negative_cases"]
    assert isinstance(negative_cases, list)
    error_types = {"TypeError": TypeError, "ValueError": ValueError}

    for case in negative_cases:
        assert isinstance(case, dict)
        error_type = error_types[str(case["error_type"])]
        with pytest.raises(error_type, match=str(case["error"])):
            normalize_tx_execution_order_context_v1(
                case["raw_order"],
                tx_count=case["tx_count"],
            )


def test_tx_execution_order_certificate_defaults_absent_or_empty_to_identity() -> None:
    absent = build_tx_execution_order_certificate_v1(None, tx_count=2)
    empty = build_tx_execution_order_certificate_v1([], tx_count=2)

    assert absent.tx_execution_order == (0, 1)
    assert empty.tx_execution_order == (0, 1)
    assert (
        absent.tx_execution_order_commitment
        == tx_execution_order_commitment_hex_v1([0, 1])
        == empty.tx_execution_order_commitment
    )


def test_tx_execution_order_certificate_emits_context_patch() -> None:
    certificate = build_tx_execution_order_certificate_v1([1, 0], tx_count=2)

    assert certificate.context_patch() == {"tx_execution_order": [1, 0]}
    assert certificate.tx_execution_order_commitment == tx_execution_order_commitment_hex_v1([1, 0])


@pytest.mark.parametrize(
    ("raw_order", "error"),
    [
        ([0], "tx_execution_order length mismatch"),
        ([0, 0], "tx_execution_order duplicate index"),
        ([0, 2], "tx_execution_order index out of range"),
        ([-1, 0], "tx_execution_order entries must be u32"),
    ],
)
def test_tx_execution_order_certificate_rejects_malformed_permutations(
    raw_order: list[int],
    error: str,
) -> None:
    with pytest.raises(ValueError, match=error):
        normalize_tx_execution_order_context_v1(raw_order, tx_count=2)


@pytest.mark.parametrize("raw_order", [[True, 0], [1.5, 0], ["1", 0]])
def test_tx_execution_order_certificate_rejects_non_integer_indices(raw_order: list[object]) -> None:
    with pytest.raises(TypeError, match="tx_execution_order entries must be u32"):
        normalize_tx_execution_order_context_v1(raw_order, tx_count=2)  # type: ignore[arg-type]


@pytest.mark.parametrize("tx_count", [True, -1, 2**32])
def test_tx_execution_order_certificate_rejects_bad_tx_count(tx_count: object) -> None:
    expected = TypeError if tx_count is True else ValueError
    with pytest.raises(expected):
        build_tx_execution_order_certificate_v1(None, tx_count=tx_count)  # type: ignore[arg-type]


def test_stale_route_order_proposer_moves_route_before_different_sender_writer() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-a",), writes=("pool-a",))

    plan = build_stale_route_order_certificate_v1([writer, route])

    assert plan.tx_execution_order == (1, 0)
    assert plan.accepted_route_count == 1
    assert plan.baseline_accepted_route_count == 0
    assert plan.deferred_route_count == 0
    assert plan.context_patch() == {"tx_execution_order": [1, 0]}
    assert plan.tx_execution_order_commitment == tx_execution_order_commitment_hex_v1([1, 0])


def test_stale_route_order_proposer_prefers_unit_dominating_value_over_count() -> None:
    wide = _tx(
        "wide",
        route_reads=("pool-a", "pool-b"),
        writes=("pool-a", "pool-b"),
        protected_values=(("ASSET0", 3),),
    )
    narrow_a = _tx(
        "narrow-a",
        route_reads=("pool-a",),
        writes=("pool-a",),
        protected_values=(("ASSET0", 1),),
    )
    narrow_b = _tx(
        "narrow-b",
        route_reads=("pool-b",),
        writes=("pool-b",),
        protected_values=(("ASSET0", 1),),
    )

    plan = build_stale_route_order_certificate_v1([narrow_a, narrow_b, wide])

    assert plan.tx_execution_order == (2, 0, 1)
    assert plan.accepted_route_protected_values == (("ASSET0", 3),)
    assert plan.baseline_accepted_route_protected_values == (("ASSET0", 2),)
    assert plan.accepted_route_count == 1
    assert plan.baseline_accepted_route_count == 2


def test_stale_route_order_proposer_does_not_scalarize_cross_asset_values() -> None:
    wide = _tx(
        "wide",
        route_reads=("pool-a", "pool-b"),
        writes=("pool-a", "pool-b"),
        protected_values=(("ASSET0", 3),),
    )
    narrow_a = _tx(
        "narrow-a",
        route_reads=("pool-a",),
        writes=("pool-a",),
        protected_values=(("ASSET1", 1),),
    )
    narrow_b = _tx(
        "narrow-b",
        route_reads=("pool-b",),
        writes=("pool-b",),
        protected_values=(("ASSET1", 1),),
    )

    plan = build_stale_route_order_certificate_v1([narrow_a, narrow_b, wide])

    assert plan.tx_execution_order == (0, 1, 2)
    assert plan.accepted_route_protected_values == (("ASSET1", 2),)
    assert plan.accepted_route_count == 2


def test_stale_route_order_proposer_preserves_same_sender_order() -> None:
    writer = _tx("same-sender", writes=("pool-a",))
    route = _tx("same-sender", route_reads=("pool-a",), writes=("pool-a",))

    plan = build_stale_route_order_certificate_v1([writer, route])

    assert plan.tx_execution_order == (0, 1)
    assert plan.accepted_route_count == 0
    assert plan.baseline_accepted_route_count == 0
    assert plan.deferred_route_count == 1


def test_stale_route_order_proposer_keeps_identity_when_no_route_gain_exists() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-b",), writes=("pool-b",))

    plan = build_stale_route_order_certificate_v1([writer, route])

    assert plan.tx_execution_order == (0, 1)
    assert plan.accepted_route_count == 1
    assert plan.baseline_accepted_route_count == 1


def test_stale_route_order_proposer_rejects_large_exact_search() -> None:
    txs = [_tx(f"sender-{index}") for index in range(MAX_EXACT_STALE_ROUTE_ORDER_TXS + 1)]

    with pytest.raises(ValueError, match="stale-route order exact search tx_count exceeded"):
        build_stale_route_order_certificate_v1(txs)


def test_stale_route_order_proposer_rejects_malformed_inputs() -> None:
    with pytest.raises(ValueError, match="sender_pubkey must be a non-empty string"):
        build_stale_route_order_certificate_v1([_tx("")])

    with pytest.raises(ValueError, match="route_read_pool_ids entries must be non-empty strings"):
        build_stale_route_order_certificate_v1(
            [
                TxExecutionOrderInputV1(
                    sender_pubkey="route-sender",
                    route_read_pool_ids=("",),
                    pool_write_ids=("pool-a",),
                )
            ]
        )


def test_stale_route_order_proposer_tampered_context_has_different_commitment() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-a",), writes=("pool-a",))

    plan = build_stale_route_order_certificate_v1([writer, route])
    tampered = build_tx_execution_order_certificate_v1([0, 1], tx_count=2)

    assert plan.tx_execution_order == (1, 0)
    assert tampered.tx_execution_order == (0, 1)
    assert tampered.tx_execution_order_commitment != plan.tx_execution_order_commitment


def test_stale_route_order_policy_requires_receipt_when_route_lift_improves_liveness() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-a",), writes=("pool-a",))

    requirement = stale_route_order_receipt_requirement_v1([writer, route])

    assert requirement.required is True
    assert requirement.reason == "stale_route_liveness_improvement"
    assert requirement.tx_execution_order == (1, 0)
    assert requirement.receipt() == {
        "schema": TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0,
        "proof_type": RISC0_SPOT_PROOF_TYPE_V1,
        "tx_execution_order_commitment": tx_execution_order_commitment_hex_v1([1, 0]),
    }


def test_stale_route_order_policy_requires_receipt_when_value_improves_despite_lower_count() -> None:
    wide = _tx(
        "wide",
        route_reads=("pool-a", "pool-b"),
        writes=("pool-a", "pool-b"),
        protected_values=(("ASSET0", 3),),
    )
    narrow_a = _tx(
        "narrow-a",
        route_reads=("pool-a",),
        writes=("pool-a",),
        protected_values=(("ASSET0", 1),),
    )
    narrow_b = _tx(
        "narrow-b",
        route_reads=("pool-b",),
        writes=("pool-b",),
        protected_values=(("ASSET0", 1),),
    )

    requirement = stale_route_order_receipt_requirement_v1([narrow_a, narrow_b, wide])

    assert requirement.required is True
    assert requirement.reason == "stale_route_protected_value_improvement"
    assert requirement.tx_execution_order == (2, 0, 1)


def test_stale_route_order_policy_rejects_missing_required_receipt() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-a",), writes=("pool-a",))

    with pytest.raises(ValueError, match="tx_execution_order receipt required"):
        validate_stale_route_order_receipt_policy_v1([writer, route], [])


def test_stale_route_order_policy_accepts_matching_required_receipt() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-a",), writes=("pool-a",))
    requirement = stale_route_order_receipt_requirement_v1([writer, route])

    accepted = validate_stale_route_order_receipt_policy_v1(
        [writer, route],
        [requirement.receipt()],
    )

    assert accepted.required is True
    assert accepted.tx_execution_order == (1, 0)


def test_stale_route_order_policy_rejects_mismatched_required_receipt() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-a",), writes=("pool-a",))
    identity = build_tx_execution_order_certificate_v1([0, 1], tx_count=2)

    with pytest.raises(ValueError, match="tx_execution_order receipt commitment mismatch"):
        validate_stale_route_order_receipt_policy_v1(
            [writer, route],
            [build_tx_execution_order_commitment_receipt_v0(identity)],
        )


def test_stale_route_order_policy_rejects_ambiguous_receipts() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-a",), writes=("pool-a",))
    requirement = stale_route_order_receipt_requirement_v1([writer, route])

    with pytest.raises(ValueError, match="tx_execution_order receipt ambiguous"):
        validate_stale_route_order_receipt_policy_v1(
            [writer, route],
            [requirement.receipt(), requirement.receipt()],
        )


def test_stale_route_order_policy_does_not_require_receipt_without_liveness_gain() -> None:
    writer = _tx("writer", writes=("pool-a",))
    route = _tx("route-sender", route_reads=("pool-b",), writes=("pool-b",))

    requirement = validate_stale_route_order_receipt_policy_v1([writer, route], [])

    assert requirement.required is False
    assert requirement.reason == "no_stale_route_liveness_improvement"
    assert requirement.tx_execution_order == (0, 1)


def test_stale_route_order_policy_does_not_override_same_sender_barrier() -> None:
    writer = _tx("same-sender", writes=("pool-a",))
    route = _tx("same-sender", route_reads=("pool-a",), writes=("pool-a",))

    requirement = validate_stale_route_order_receipt_policy_v1([writer, route], [])

    assert requirement.required is False
    assert requirement.tx_execution_order == (0, 1)
