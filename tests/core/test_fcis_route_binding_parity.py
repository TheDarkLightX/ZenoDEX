"""Differential parity: exact route binding/replay vs the legacy oracle.

The legacy route implementation is used only as a differential oracle over the
supported single-hop split-route corpus.  This checkpoint authorizes no
divergence: accept/reject, first rejection code, canonical observed state-read
order, per-leg values, threaded post-reserves, and totals must agree exactly.
"""

from __future__ import annotations

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.fcis_route_binding import (
    derive_exact_route_binding_v1,
    replay_exact_route_observed_v1,
    route_binding_pins_exact_snapshot_observed_v1,
)
from src.core.fcis_route_binding_values import (
    RouteBindingOkV1,
    RouteBindingV1,
    RouteReplayOkV1,
    RouteReplayRejectCodeV1,
    RouteReplayRejectV1,
)
from src.core.quote_receipts import pool_state_fingerprint
from src.core.route_settlement import (
    RouteBinding,
    parse_route_binding_fields,
    replay_route_legs,
    replay_route_legs_committed_observed_v1,
    route_binding_pins_committed_snapshot_observed_v1,
    validate_route_intent_against_binding,
)
from src.state.intent_snapshots import OwnedIntentV1, snapshot_intent
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshots import snapshot_pool_map

INTENT_ID = "0x" + "11" * 32
SENDER = "0x" + "22" * 48
ASSET_IN = "0x" + "01" * 32
ASSET_OUT = "0x" + "02" * 32
ASSET_OTHER = "0x" + "03" * 32


def _pool(fee_bps: int, *, reserve0: int = 1_000_000, reserve1: int = 1_000_000) -> PoolState:
    pool_id = compute_pool_id(ASSET_IN, ASSET_OUT, fee_bps)
    return PoolState(
        pool_id=pool_id,
        asset0=ASSET_IN,
        asset1=ASSET_OUT,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _quoted_leg_fields(
    kind: IntentKind,
    pools: tuple[PoolState, ...],
    amounts: tuple[int, ...],
) -> list[dict[str, object]]:
    legs = []
    scratch = {pool.pool_id: (pool.reserve0, pool.reserve1) for pool in pools}
    for pool, amount in zip(pools, amounts, strict=True):
        reserve0, reserve1 = scratch[pool.pool_id]
        if kind is IntentKind.ROUTE_EXACT_IN:
            quoted, (new_in, new_out) = swap_exact_in_for_pool(
                pool, reserve_in=reserve0, reserve_out=reserve1, amount_in=amount
            )
            amount_in, amount_out = amount, quoted
        else:
            quoted, (new_in, new_out) = swap_exact_out_for_pool(
                pool, reserve_in=reserve0, reserve_out=reserve1, amount_out=amount
            )
            amount_in, amount_out = quoted, amount
        legs.append(
            {
                "pool_id": pool.pool_id,
                "asset_in": ASSET_IN,
                "asset_out": ASSET_OUT,
                "amount_in": amount_in,
                "amount_out": amount_out,
            }
        )
        scratch[pool.pool_id] = (new_in, new_out)
    return legs


def _route_fields(
    kind: IntentKind,
    pools: tuple[PoolState, ...],
    amounts: tuple[int, ...],
) -> dict[str, object]:
    legs = _quoted_leg_fields(kind, pools, amounts)
    sum_in = sum(leg["amount_in"] for leg in legs)
    sum_out = sum(leg["amount_out"] for leg in legs)
    fields: dict[str, object] = {
        "asset_in": ASSET_IN,
        "asset_out": ASSET_OUT,
        "leg_indices": list(range(len(legs))),
        "route_legs": legs,
        "route_pool_fingerprints": {pool.pool_id: pool_state_fingerprint(pool) for pool in pools},
    }
    if kind is IntentKind.ROUTE_EXACT_IN:
        fields["total_amount_in"] = sum_in
        fields["total_min_amount_out"] = 0
    else:
        fields["total_amount_out"] = sum_out
        fields["total_max_amount_in"] = sum_in
    return fields


def _admitted(kind: IntentKind, fields: dict[str, object]) -> OwnedIntentV1:
    return snapshot_intent(Intent("TauSwap", "0.1", kind, INTENT_ID, SENDER, 9, None, fields))


def _legacy_binding(intent: OwnedIntentV1) -> RouteBinding:
    binding, parse_error = parse_route_binding_fields(intent)
    assert binding is not None, parse_error
    assert validate_route_intent_against_binding(intent, binding) is None
    return binding


def _exact_binding(intent: OwnedIntentV1) -> RouteBindingV1:
    result = derive_exact_route_binding_v1(intent)
    assert type(result) is RouteBindingOkV1
    return result.binding


def _leg_tuple(leg: object) -> tuple[object, ...]:
    return (
        leg.pool_id,  # type: ignore[attr-defined]
        leg.asset_in,  # type: ignore[attr-defined]
        leg.asset_out,  # type: ignore[attr-defined]
        leg.amount_in,  # type: ignore[attr-defined]
        leg.amount_out,  # type: ignore[attr-defined]
        leg.fee_paid,  # type: ignore[attr-defined]
        leg.new_reserve0,  # type: ignore[attr-defined]
        leg.new_reserve1,  # type: ignore[attr-defined]
    )


def _assert_replay_parity(
    intent: OwnedIntentV1,
    exact_binding: RouteBindingV1,
    legacy_binding: RouteBinding,
    pools: dict[str, PoolState],
) -> None:
    committed = snapshot_pool_map(pools)
    exact_result, exact_observed = replay_exact_route_observed_v1(
        intent,
        exact_binding,
        committed,
    )
    legacy_result, legacy_observed = replay_route_legs_committed_observed_v1(
        binding=legacy_binding,
        pools=committed,
    )
    legacy_plain = replay_route_legs(binding=legacy_binding, pools=pools)
    assert legacy_result == legacy_plain

    if legacy_result.ok:
        assert type(exact_result) is RouteReplayOkV1
        assert tuple(_leg_tuple(leg) for leg in exact_result.legs) == tuple(
            _leg_tuple(leg) for leg in legacy_result.legs
        )
        assert exact_result.total_amount_in == legacy_result.total_amount_in
        assert exact_result.total_amount_out == legacy_result.total_amount_out
        assert exact_result.total_fee_paid == legacy_result.total_fee_paid
    else:
        assert type(exact_result) is RouteReplayRejectV1
        assert exact_result.code.value == legacy_result.reject_reason
    assert exact_observed == legacy_observed


def _assert_pins_parity(
    intent: OwnedIntentV1,
    exact_binding: RouteBindingV1,
    legacy_binding: RouteBinding,
    pools: dict[str, PoolState],
) -> None:
    committed = snapshot_pool_map(pools)
    exact_pins, exact_reads = route_binding_pins_exact_snapshot_observed_v1(
        intent,
        exact_binding,
        committed,
    )
    legacy_pins, legacy_reads = route_binding_pins_committed_snapshot_observed_v1(
        legacy_binding,
        committed,
    )
    assert exact_pins == legacy_pins
    assert exact_reads == legacy_reads


def _assert_case_parity(
    kind: IntentKind,
    pools: tuple[PoolState, ...],
    amounts: tuple[int, ...],
    replay_pools: dict[str, PoolState] | None = None,
) -> None:
    fields = _route_fields(kind, pools, amounts)
    intent = _admitted(kind, fields)
    exact = _exact_binding(intent)
    legacy = _legacy_binding(intent)
    pool_map = {pool.pool_id: pool for pool in pools} if replay_pools is None else replay_pools
    _assert_replay_parity(intent, exact, legacy, pool_map)
    _assert_pins_parity(intent, exact, legacy, pool_map)


def test_supported_single_hop_split_routes_match_legacy() -> None:
    pool_a, pool_b = _pool(30), _pool(31)
    for kind, pools, amounts in (
        (IntentKind.ROUTE_EXACT_IN, (pool_a,), (4_000,)),
        (IntentKind.ROUTE_EXACT_IN, (pool_a, pool_b), (4_000, 6_000)),
        (IntentKind.ROUTE_EXACT_IN, (pool_a, pool_b, pool_a), (2_000, 3_000, 1_000)),
        (IntentKind.ROUTE_EXACT_IN, (pool_a, pool_a), (4_000, 6_000)),
        (IntentKind.ROUTE_EXACT_OUT, (pool_a,), (3_000,)),
        (IntentKind.ROUTE_EXACT_OUT, (pool_a, pool_b), (3_000, 5_000)),
        (IntentKind.ROUTE_EXACT_OUT, (pool_a, pool_a), (2_000, 1_000)),
    ):
        _assert_case_parity(kind, pools, amounts)


def test_missing_pool_matches_legacy() -> None:
    pool_a, pool_b = _pool(30), _pool(31)
    _assert_case_parity(
        IntentKind.ROUTE_EXACT_IN,
        (pool_a, pool_b),
        (4_000, 6_000),
        replay_pools={pool_a.pool_id: pool_a},
    )
    _assert_case_parity(
        IntentKind.ROUTE_EXACT_OUT,
        (pool_a, pool_b),
        (3_000, 5_000),
        replay_pools={pool_b.pool_id: pool_b},
    )


def _with_status(pool: PoolState, status: PoolStatus) -> PoolState:
    return PoolState(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=pool.reserve0,
        reserve1=pool.reserve1,
        fee_bps=pool.fee_bps,
        lp_supply=pool.lp_supply,
        status=status,
        created_at=pool.created_at,
    )


def _with_reserve0(pool: PoolState, reserve0: int) -> PoolState:
    return PoolState(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=reserve0,
        reserve1=pool.reserve1,
        fee_bps=pool.fee_bps,
        lp_supply=pool.lp_supply,
        status=pool.status,
        created_at=pool.created_at,
    )


def test_inactive_pool_matches_legacy() -> None:
    pool_a, pool_b = _pool(30), _pool(31)
    frozen = {pool_a.pool_id: _with_status(pool_a, PoolStatus.FROZEN), pool_b.pool_id: pool_b}
    _assert_case_parity(
        IntentKind.ROUTE_EXACT_IN,
        (pool_a, pool_b),
        (4_000, 6_000),
        replay_pools=frozen,
    )


def test_drifted_pool_matches_legacy() -> None:
    pool_a, pool_b = _pool(30), _pool(31)
    drifted = {pool_a.pool_id: pool_a, pool_b.pool_id: _with_reserve0(pool_b, pool_b.reserve0 + 1)}
    _assert_case_parity(
        IntentKind.ROUTE_EXACT_IN,
        (pool_a, pool_b),
        (4_000, 6_000),
        replay_pools=drifted,
    )


def test_mixed_preflight_failures_select_the_canonical_first_read() -> None:
    pool_a, pool_b = _pool(30), _pool(31)
    low_id, high_id = tuple(sorted((pool_a.pool_id, pool_b.pool_id)))
    pools_by_id = {pool_a.pool_id: pool_a, pool_b.pool_id: pool_b}
    mixed = {
        low_id: _with_status(pools_by_id[low_id], PoolStatus.FROZEN),
    }
    assert high_id not in mixed
    _assert_case_parity(
        IntentKind.ROUTE_EXACT_IN,
        (pool_a, pool_b),
        (4_000, 6_000),
        replay_pools=mixed,
    )


def test_invalid_orientation_matches_legacy() -> None:
    pool = _pool(30)
    wrong_pool = PoolState(
        pool_id=compute_pool_id(ASSET_IN, ASSET_OTHER, 30),
        asset0=ASSET_IN,
        asset1=ASSET_OTHER,
        reserve0=pool.reserve0,
        reserve1=pool.reserve1,
        fee_bps=pool.fee_bps,
        lp_supply=pool.lp_supply,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    fields = _route_fields(IntentKind.ROUTE_EXACT_IN, (pool,), (4_000,))
    fields["route_legs"] = [{**fields["route_legs"][0], "pool_id": wrong_pool.pool_id}]  # type: ignore[index]
    fields["route_pool_fingerprints"] = {wrong_pool.pool_id: pool_state_fingerprint(wrong_pool)}
    intent = _admitted(IntentKind.ROUTE_EXACT_IN, fields)
    _assert_replay_parity(
        intent,
        _exact_binding(intent),
        _legacy_binding(intent),
        {wrong_pool.pool_id: wrong_pool},
    )


def test_quote_mismatch_matches_legacy() -> None:
    pool = _pool(30)
    for kind in (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT):
        fields = _route_fields(kind, (pool,), (4_000,))
        legs = fields["route_legs"]
        if kind is IntentKind.ROUTE_EXACT_IN:
            legs[0]["amount_out"] += 1  # type: ignore[index]
        else:
            legs[0]["amount_in"] += 1  # type: ignore[index]
            fields["total_max_amount_in"] = fields["total_max_amount_in"] + 1  # type: ignore[operator]
        intent = _admitted(kind, fields)
        _assert_replay_parity(
            intent,
            _exact_binding(intent),
            _legacy_binding(intent),
            {pool.pool_id: pool},
        )


def test_binding_substitution_across_commands_rejects_without_reads() -> None:
    pool = _pool(30)
    first_intent = _admitted(
        IntentKind.ROUTE_EXACT_IN,
        _route_fields(IntentKind.ROUTE_EXACT_IN, (pool,), (4_000,)),
    )
    second_intent = _admitted(
        IntentKind.ROUTE_EXACT_IN,
        _route_fields(IntentKind.ROUTE_EXACT_IN, (pool,), (5_000,)),
    )
    second_binding = _exact_binding(second_intent)
    committed = snapshot_pool_map({pool.pool_id: pool})

    result, observed = replay_exact_route_observed_v1(first_intent, second_binding, committed)
    assert type(result) is RouteReplayRejectV1
    assert result.code is RouteReplayRejectCodeV1.BINDING_INVALID
    assert observed == ()

    pins, pin_reads = route_binding_pins_exact_snapshot_observed_v1(
        first_intent, second_binding, committed
    )
    assert pins is False
    assert pin_reads == ()


def test_derivation_rejections_match_legacy_parse_and_validate() -> None:
    pool_a, pool_b = _pool(30), _pool(31)
    valid = _route_fields(IntentKind.ROUTE_EXACT_IN, (pool_a, pool_b), (4_000, 6_000))

    reject_cases: list[tuple[IntentKind, dict[str, object]]] = []
    bad_coverage = dict(valid)
    bad_coverage["leg_indices"] = [0, 2]
    reject_cases.append((IntentKind.ROUTE_EXACT_IN, bad_coverage))
    bad_endpoint = dict(valid)
    bad_endpoint["route_legs"] = [
        dict(valid["route_legs"][0]),  # type: ignore[index]
        {**valid["route_legs"][1], "asset_in": ASSET_OTHER},  # type: ignore[index]
    ]
    reject_cases.append((IntentKind.ROUTE_EXACT_IN, bad_endpoint))
    short_fingerprints = dict(valid)
    short_fingerprints["route_pool_fingerprints"] = {pool_a.pool_id: pool_state_fingerprint(pool_a)}
    reject_cases.append((IntentKind.ROUTE_EXACT_IN, short_fingerprints))
    bad_total = dict(valid)
    bad_total["total_amount_in"] = valid["total_amount_in"] + 1  # type: ignore[operator]
    reject_cases.append((IntentKind.ROUTE_EXACT_IN, bad_total))
    bad_min_out = dict(valid)
    bad_min_out["total_min_amount_out"] = 10**9
    reject_cases.append((IntentKind.ROUTE_EXACT_IN, bad_min_out))
    exact_out = _route_fields(IntentKind.ROUTE_EXACT_OUT, (pool_a, pool_b), (3_000, 5_000))
    bad_out_total = dict(exact_out)
    bad_out_total["total_amount_out"] = exact_out["total_amount_out"] + 1  # type: ignore[operator]
    reject_cases.append((IntentKind.ROUTE_EXACT_OUT, bad_out_total))
    bad_max_in = dict(exact_out)
    bad_max_in["total_max_amount_in"] = exact_out["total_max_amount_in"] - 1  # type: ignore[operator]
    reject_cases.append((IntentKind.ROUTE_EXACT_OUT, bad_max_in))

    for kind, fields in reject_cases:
        intent = _admitted(kind, fields)
        legacy_binding, legacy_parse_error = parse_route_binding_fields(intent)
        legacy_error = (
            legacy_parse_error
            if legacy_binding is None
            else validate_route_intent_against_binding(intent, legacy_binding)
        )
        exact_result = derive_exact_route_binding_v1(intent)
        assert legacy_error is not None, fields
        assert type(exact_result) is not RouteBindingOkV1, fields


def test_observed_reads_are_canonical_when_local_scratch_reuses_a_pool() -> None:
    pool = _pool(30)
    fields = _route_fields(IntentKind.ROUTE_EXACT_IN, (pool, pool), (4_000, 6_000))
    intent = _admitted(IntentKind.ROUTE_EXACT_IN, fields)
    exact = _exact_binding(intent)
    legacy = _legacy_binding(intent)
    committed = snapshot_pool_map({pool.pool_id: pool})

    _exact_result, exact_observed = replay_exact_route_observed_v1(intent, exact, committed)
    _legacy_result, legacy_observed = replay_route_legs_committed_observed_v1(
        binding=legacy,
        pools=committed,
    )

    assert exact_observed == legacy_observed == (pool.pool_id,)
