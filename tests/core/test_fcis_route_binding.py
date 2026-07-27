"""Exact route binding derivation and replay tests for FCIS M5-P4B3."""

from __future__ import annotations

import pytest

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.cpmm import compute_fee_total
from src.core.domain_limits import DEX_SWAP_AMOUNT_MAX
from src.core.fcis_route_binding import (
    _bounded_leg_amount_sums_v1,
    _RouteLegFieldsV1,
    derive_exact_route_binding_v1,
    replay_exact_route_observed_v1,
    replay_exact_route_v1,
    route_binding_pins_exact_snapshot_observed_v1,
    route_binding_pins_exact_snapshot_v1,
)
from src.core.fcis_route_binding_values import (
    RouteBindingOkV1,
    RouteBindingRejectCodeV1,
    RouteBindingRejectV1,
    RouteBindingV1,
    RouteKindV1,
    RouteReplayOkV1,
    RouteReplayRejectCodeV1,
    RouteReplayRejectV1,
)
from src.core.quote_receipts import pool_state_fingerprint
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


def _pools() -> tuple[PoolState, PoolState]:
    return _pool(30), _pool(31)


def _leg_fields(pool_id: str, amount_in: int, amount_out: int) -> dict[str, object]:
    return {
        "pool_id": pool_id,
        "asset_in": ASSET_IN,
        "asset_out": ASSET_OUT,
        "amount_in": amount_in,
        "amount_out": amount_out,
    }


def _exact_in_fields(
    pools: tuple[PoolState, ...],
    amounts_in: tuple[int, ...],
) -> dict[str, object]:
    legs = []
    sum_in = 0
    sum_out = 0
    scratch = {pool.pool_id: (pool.reserve0, pool.reserve1) for pool in pools}
    for pool, amount_in in zip(pools, amounts_in, strict=True):
        reserve0, reserve1 = scratch[pool.pool_id]
        quoted, (new_in, new_out) = swap_exact_in_for_pool(
            pool,
            reserve_in=reserve0,
            reserve_out=reserve1,
            amount_in=amount_in,
        )
        legs.append(_leg_fields(pool.pool_id, amount_in, quoted))
        scratch[pool.pool_id] = (new_in, new_out)
        sum_in += amount_in
        sum_out += quoted
    return {
        "asset_in": ASSET_IN,
        "asset_out": ASSET_OUT,
        "leg_indices": list(range(len(legs))),
        "total_amount_in": sum_in,
        "total_min_amount_out": 0,
        "route_legs": legs,
        "route_pool_fingerprints": {pool.pool_id: pool_state_fingerprint(pool) for pool in pools},
    }


def _exact_out_fields(
    pools: tuple[PoolState, ...],
    amounts_out: tuple[int, ...],
) -> dict[str, object]:
    legs = []
    sum_in = 0
    sum_out = 0
    scratch = {pool.pool_id: (pool.reserve0, pool.reserve1) for pool in pools}
    for pool, amount_out in zip(pools, amounts_out, strict=True):
        reserve0, reserve1 = scratch[pool.pool_id]
        quoted, (new_in, new_out) = swap_exact_out_for_pool(
            pool,
            reserve_in=reserve0,
            reserve_out=reserve1,
            amount_out=amount_out,
        )
        legs.append(_leg_fields(pool.pool_id, quoted, amount_out))
        scratch[pool.pool_id] = (new_in, new_out)
        sum_in += quoted
        sum_out += amount_out
    return {
        "asset_in": ASSET_IN,
        "asset_out": ASSET_OUT,
        "leg_indices": list(range(len(legs))),
        "total_amount_out": sum_out,
        "total_max_amount_in": sum_in,
        "route_legs": legs,
        "route_pool_fingerprints": {pool.pool_id: pool_state_fingerprint(pool) for pool in pools},
    }


def _intent(kind: IntentKind, fields: dict[str, object]) -> Intent:
    return Intent("TauSwap", "0.1", kind, INTENT_ID, SENDER, 9, None, fields)


def _admitted(
    fields: dict[str, object], kind: IntentKind = IntentKind.ROUTE_EXACT_IN
) -> OwnedIntentV1:
    return snapshot_intent(_intent(kind, fields))


def _derive_ok(intent: OwnedIntentV1) -> RouteBindingV1:
    result = derive_exact_route_binding_v1(intent)
    assert type(result) is RouteBindingOkV1
    return result.binding


def _derive_reject(intent: OwnedIntentV1) -> RouteBindingRejectV1:
    result = derive_exact_route_binding_v1(intent)
    assert type(result) is RouteBindingRejectV1
    return result


def _replay_reject(
    binding: RouteBindingV1,
    pools: dict[str, PoolState],
) -> tuple[RouteReplayRejectV1, tuple[str, ...]]:
    result, observed = replay_exact_route_observed_v1(binding, snapshot_pool_map(pools))
    assert type(result) is RouteReplayRejectV1
    return result, observed


def _corrupt_field_lookup(intent: OwnedIntentV1, field_name: str, replacement: object) -> None:
    replacement_index: dict[str, object] = dict(intent.fields.entries)
    replacement_index[field_name] = replacement
    object.__setattr__(intent.fields, "_index", replacement_index)


def test_exact_in_and_exact_out_bindings_derive_and_replay() -> None:
    pools = _pools()
    committed = snapshot_pool_map({pool.pool_id: pool for pool in pools})

    exact_in = _derive_ok(_admitted(_exact_in_fields(pools, (4_000, 6_000))))
    assert exact_in.kind is RouteKindV1.EXACT_IN
    assert exact_in.total_amount_in == 10_000
    assert len(exact_in.legs) == 2
    replay, observed = replay_exact_route_observed_v1(exact_in, committed)
    assert type(replay) is RouteReplayOkV1
    assert replay.total_amount_in == exact_in.total_amount_in
    assert replay.total_amount_out == exact_in.total_amount_out
    assert replay.total_fee_paid == sum(
        compute_fee_total(leg.amount_in, pool.fee_bps)
        for leg, pool in zip(exact_in.legs, pools, strict=True)
    )
    assert observed == tuple(sorted(pool.pool_id for pool in pools)) + tuple(
        leg.pool_id for leg in exact_in.legs
    )
    assert route_binding_pins_exact_snapshot_v1(exact_in, committed) is True

    exact_out = _derive_ok(
        _admitted(_exact_out_fields(pools, (3_000, 5_000)), IntentKind.ROUTE_EXACT_OUT)
    )
    assert exact_out.kind is RouteKindV1.EXACT_OUT
    replay_out = replay_exact_route_v1(exact_out, committed)
    assert type(replay_out) is RouteReplayOkV1
    assert replay_out.total_amount_out == 8_000
    assert route_binding_pins_exact_snapshot_v1(exact_out, committed) is True


def test_repeated_pool_ids_across_legs_share_threaded_reserves() -> None:
    pool = _pool(30)
    fields = _exact_in_fields((pool, pool), (4_000, 6_000))
    binding = _derive_ok(_admitted(fields))
    assert tuple(leg.pool_id for leg in binding.legs) == (pool.pool_id, pool.pool_id)

    replay, observed = replay_exact_route_observed_v1(
        binding,
        snapshot_pool_map({pool.pool_id: pool}),
    )

    assert type(replay) is RouteReplayOkV1
    first, second = replay.legs
    assert (first.new_reserve0, first.new_reserve1) != (pool.reserve0, pool.reserve1)
    expected_second_input = swap_exact_in_for_pool(
        pool,
        reserve_in=first.new_reserve0,
        reserve_out=first.new_reserve1,
        amount_in=6_000,
    )[0]
    assert second.amount_out == expected_second_input
    assert observed == (pool.pool_id, pool.pool_id, pool.pool_id)


def test_replay_rejection_precedence_and_observed_prefixes() -> None:
    pool_a, pool_b = _pools()
    binding = _derive_ok(_admitted(_exact_in_fields((pool_a, pool_b), (4_000, 6_000))))
    low_id, high_id = tuple(sorted((pool_a.pool_id, pool_b.pool_id)))
    pools_by_id = {pool_a.pool_id: pool_a, pool_b.pool_id: pool_b}

    missing = {high_id: pools_by_id[high_id]}
    result, observed = _replay_reject(binding, missing)
    assert result.code is RouteReplayRejectCodeV1.POOL_NOT_FOUND
    assert observed == (low_id,)

    frozen = PoolState(
        pool_id=pool_a.pool_id,
        asset0=pool_a.asset0,
        asset1=pool_a.asset1,
        reserve0=pool_a.reserve0,
        reserve1=pool_a.reserve1,
        fee_bps=pool_a.fee_bps,
        lp_supply=pool_a.lp_supply,
        status=PoolStatus.FROZEN,
        created_at=pool_a.created_at,
    )
    frozen_map = {**pools_by_id, pool_a.pool_id: frozen}
    result, observed = _replay_reject(binding, frozen_map)
    assert result.code is RouteReplayRejectCodeV1.POOL_NOT_ACTIVE
    assert observed[-1] == pool_a.pool_id

    drifted = PoolState(
        pool_id=pool_b.pool_id,
        asset0=pool_b.asset0,
        asset1=pool_b.asset1,
        reserve0=pool_b.reserve0 + 1,
        reserve1=pool_b.reserve1,
        fee_bps=pool_b.fee_bps,
        lp_supply=pool_b.lp_supply,
        status=pool_b.status,
        created_at=pool_b.created_at,
    )
    result, observed = _replay_reject(binding, {**pools_by_id, pool_b.pool_id: drifted})
    assert result.code is RouteReplayRejectCodeV1.POOL_STATE_DRIFT
    drift_prefix = (low_id,) if pool_b.pool_id == low_id else (low_id, high_id)
    assert observed == drift_prefix

    pins, pin_reads = route_binding_pins_exact_snapshot_observed_v1(
        binding,
        snapshot_pool_map({**pools_by_id, pool_b.pool_id: drifted}),
    )
    assert pins is False
    assert pin_reads == drift_prefix


def test_invalid_orientation_and_quote_mismatch_reject() -> None:
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
    wrong_fields = _exact_in_fields((pool,), (4_000,))
    wrong_fields["route_legs"] = [
        {**wrong_fields["route_legs"][0], "pool_id": wrong_pool.pool_id}  # type: ignore[index]
    ]
    wrong_fields["route_pool_fingerprints"] = {
        wrong_pool.pool_id: pool_state_fingerprint(wrong_pool)
    }
    wrong_binding = _derive_ok(_admitted(wrong_fields))
    result, observed = _replay_reject(wrong_binding, {wrong_pool.pool_id: wrong_pool})
    assert result.code is RouteReplayRejectCodeV1.INVALID_PARAMS
    assert observed == (wrong_pool.pool_id, wrong_pool.pool_id)

    mismatch_fields = _exact_in_fields((pool,), (4_000,))
    mismatch_fields["route_legs"] = [
        {
            **mismatch_fields["route_legs"][0],
            "amount_out": mismatch_fields["route_legs"][0]["amount_out"] + 1,
        }  # type: ignore[index]
    ]
    mismatch_binding = _derive_ok(_admitted(mismatch_fields))
    result, observed = _replay_reject(mismatch_binding, {pool.pool_id: pool})
    assert result.code is RouteReplayRejectCodeV1.LEG_QUOTE_MISMATCH
    assert observed == (pool.pool_id, pool.pool_id)


def test_reversed_leg_order_changes_binding_and_replay_when_semantic() -> None:
    pool = _pool(30)
    fields = _exact_in_fields((pool, pool), (4_000, 6_000))
    forward = _derive_ok(_admitted(fields))

    reversed_fields = dict(fields)
    reversed_fields["route_legs"] = [fields["route_legs"][1], fields["route_legs"][0]]  # type: ignore[index]
    reversed_binding = _derive_ok(_admitted(reversed_fields))

    assert forward != reversed_binding
    committed = snapshot_pool_map({pool.pool_id: pool})
    assert type(replay_exact_route_v1(forward, committed)) is RouteReplayOkV1
    replay, observed = replay_exact_route_observed_v1(reversed_binding, committed)
    assert type(replay) is RouteReplayRejectV1
    assert replay.code is RouteReplayRejectCodeV1.LEG_QUOTE_MISMATCH
    assert observed == (pool.pool_id, pool.pool_id)


def test_insertion_order_permutations_yield_equal_bindings() -> None:
    pools = _pools()
    fields = _exact_in_fields(pools, (4_000, 6_000))
    pool_a, pool_b = pools
    permuted = dict(fields)
    permuted["route_pool_fingerprints"] = {
        pool_b.pool_id: pool_state_fingerprint(pool_b),
        pool_a.pool_id: pool_state_fingerprint(pool_a),
    }

    first = _derive_ok(_admitted(fields))
    second = _derive_ok(_admitted(permuted))

    assert first == second
    assert tuple(key for key, _value in first.pool_fingerprints.entries) == tuple(
        key for key, _value in second.pool_fingerprints.entries
    )


def test_cross_field_rejection_order_and_paths() -> None:
    pools = _pools()
    valid = _exact_in_fields(pools, (4_000, 6_000))

    swap_fields = {
        "pool_id": "pool",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 1,
        "min_amount_out": 0,
    }
    reject = _derive_reject(_admitted(swap_fields, IntentKind.SWAP_EXACT_IN))
    assert reject.code is RouteBindingRejectCodeV1.KIND_MISMATCH
    assert reject.path == ()

    missing_legs = {key: value for key, value in valid.items() if key != "route_legs"}
    reject = _derive_reject(_admitted(missing_legs))
    assert reject.code is RouteBindingRejectCodeV1.STRUCTURAL_INVALID
    assert reject.path == ("route_legs",)

    missing_fingerprints = {
        key: value for key, value in valid.items() if key != "route_pool_fingerprints"
    }
    reject = _derive_reject(_admitted(missing_fingerprints))
    assert reject.code is RouteBindingRejectCodeV1.STRUCTURAL_INVALID
    assert reject.path == ("route_pool_fingerprints",)

    bad_coverage = dict(valid)
    bad_coverage["leg_indices"] = [0, 2]
    reject = _derive_reject(_admitted(bad_coverage))
    assert reject.code is RouteBindingRejectCodeV1.LEG_COVERAGE_MISMATCH
    assert reject.path == ("leg_indices",)

    bad_leg_endpoint = dict(valid)
    bad_leg_endpoint["route_legs"] = [
        dict(valid["route_legs"][0]),  # type: ignore[index]
        {**valid["route_legs"][1], "asset_in": ASSET_OTHER},  # type: ignore[index]
    ]
    reject = _derive_reject(_admitted(bad_leg_endpoint))
    assert reject.code is RouteBindingRejectCodeV1.LEG_ENDPOINT_MISMATCH
    assert reject.path == ("route_legs", 1)

    short_fingerprints = dict(valid)
    short_fingerprints["route_pool_fingerprints"] = {
        pools[0].pool_id: pool_state_fingerprint(pools[0])
    }
    reject = _derive_reject(_admitted(short_fingerprints))
    assert reject.code is RouteBindingRejectCodeV1.FINGERPRINT_POOL_MISMATCH
    assert reject.path == ("route_pool_fingerprints",)

    extra_fingerprints = dict(valid)
    extra_fingerprints["route_pool_fingerprints"] = {
        **valid["route_pool_fingerprints"],  # type: ignore[arg-type]
        "0x" + "ff" * 32: "0x" + "ee" * 32,
    }
    reject = _derive_reject(_admitted(extra_fingerprints))
    assert reject.code is RouteBindingRejectCodeV1.FINGERPRINT_POOL_MISMATCH

    bad_total = dict(valid)
    bad_total["total_amount_in"] = valid["total_amount_in"] + 1  # type: ignore[operator]
    reject = _derive_reject(_admitted(bad_total))
    assert reject.code is RouteBindingRejectCodeV1.EXACT_IN_TOTALS_MISMATCH
    assert reject.path == ("total_amount_in",)

    bad_min_out = dict(valid)
    bad_min_out["total_min_amount_out"] = (
        valid["route_legs"][0]["amount_out"] + valid["route_legs"][1]["amount_out"] + 1
    )  # type: ignore[index]
    reject = _derive_reject(_admitted(bad_min_out))
    assert reject.code is RouteBindingRejectCodeV1.EXACT_IN_TOTALS_MISMATCH
    assert reject.path == ("total_min_amount_out",)


def test_exact_out_totals_rejections() -> None:
    pools = _pools()
    valid = _exact_out_fields(pools, (3_000, 5_000))

    bad_total = dict(valid)
    bad_total["total_amount_out"] = valid["total_amount_out"] + 1  # type: ignore[operator]
    reject = _derive_reject(_admitted(bad_total, IntentKind.ROUTE_EXACT_OUT))
    assert reject.code is RouteBindingRejectCodeV1.EXACT_OUT_TOTALS_MISMATCH
    assert reject.path == ("total_amount_out",)

    bad_max_in = dict(valid)
    bad_max_in["total_max_amount_in"] = valid["total_max_amount_in"] - 1  # type: ignore[operator]
    reject = _derive_reject(_admitted(bad_max_in, IntentKind.ROUTE_EXACT_OUT))
    assert reject.code is RouteBindingRejectCodeV1.EXACT_OUT_TOTALS_MISMATCH
    assert reject.path == ("total_max_amount_in",)


def test_first_failure_wins_across_ordered_checks() -> None:
    pools = _pools()
    valid = _exact_in_fields(pools, (4_000, 6_000))

    coverage_and_fingerprints = dict(valid)
    coverage_and_fingerprints["leg_indices"] = [0, 2]
    coverage_and_fingerprints["route_pool_fingerprints"] = {
        pools[0].pool_id: pool_state_fingerprint(pools[0])
    }
    reject = _derive_reject(_admitted(coverage_and_fingerprints))
    assert reject.code is RouteBindingRejectCodeV1.LEG_COVERAGE_MISMATCH

    leg_and_totals = dict(valid)
    leg_and_totals["route_legs"] = [
        {**valid["route_legs"][0], "asset_out": ASSET_OTHER},  # type: ignore[index]
        dict(valid["route_legs"][1]),  # type: ignore[index]
    ]
    leg_and_totals["total_amount_in"] = valid["total_amount_in"] + 1  # type: ignore[operator]
    reject = _derive_reject(_admitted(leg_and_totals))
    assert reject.code is RouteBindingRejectCodeV1.LEG_ENDPOINT_MISMATCH


def test_endpoint_distinctness_reject_is_reachable_through_corruption() -> None:
    pools = _pools()
    intent = _admitted(_exact_in_fields(pools, (4_000, 6_000)))
    _corrupt_field_lookup(intent, "asset_out", ASSET_IN)

    reject = _derive_reject(intent)

    assert reject.code is RouteBindingRejectCodeV1.ENDPOINT_ASSETS_INVALID
    assert reject.path == ("asset_out",)


def test_bounded_leg_amount_sum_guard() -> None:
    at_bound = _RouteLegFieldsV1("p", "a", "b", DEX_SWAP_AMOUNT_MAX, DEX_SWAP_AMOUNT_MAX)
    assert _bounded_leg_amount_sums_v1((at_bound,) * 256) == (
        256 * DEX_SWAP_AMOUNT_MAX,
        256 * DEX_SWAP_AMOUNT_MAX,
    )
    over_bound = _RouteLegFieldsV1("p", "a", "b", DEX_SWAP_AMOUNT_MAX + 1, 1)
    assert _bounded_leg_amount_sums_v1((at_bound,) * 255 + (over_bound,)) is None


def test_caller_construction_of_authority_values_fails() -> None:
    pools = _pools()
    binding = _derive_ok(_admitted(_exact_in_fields(pools, (4_000, 6_000))))

    with pytest.raises(TypeError, match="controlled derivation"):
        RouteBindingV1(
            binding.kind,
            binding.asset_in,
            binding.asset_out,
            binding.total_amount_in,
            binding.total_amount_out,
            binding.legs,
            binding.pool_fingerprints,
            object(),
        )


def test_hostile_inputs_at_exact_apis() -> None:
    pools = _pools()
    binding = _derive_ok(_admitted(_exact_in_fields(pools, (4_000, 6_000))))
    committed = snapshot_pool_map({pool.pool_id: pool for pool in pools})

    with pytest.raises(TypeError, match="exact OwnedIntentV1"):
        derive_exact_route_binding_v1(object())  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact RouteBindingV1"):
        replay_exact_route_observed_v1(object(), committed)  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="exact committed pool map"):
        replay_exact_route_observed_v1(binding, {pool.pool_id: pool for pool in pools})  # type: ignore[arg-type]
    with pytest.raises(TypeError, match="committed pool map schema metadata mismatch"):
        route_binding_pins_exact_snapshot_observed_v1(
            binding,
            binding.pool_fingerprints,  # type: ignore[arg-type]
        )

    class _BindingLookalike:
        kind = binding.kind
        asset_in = binding.asset_in
        asset_out = binding.asset_out
        total_amount_in = binding.total_amount_in
        total_amount_out = binding.total_amount_out
        legs = binding.legs
        pool_fingerprints = binding.pool_fingerprints

    with pytest.raises(TypeError, match="exact RouteBindingV1"):
        replay_exact_route_observed_v1(_BindingLookalike(), committed)  # type: ignore[arg-type]


def test_object_setattr_corruption_returns_closed_rejection_with_no_pool_read() -> None:
    pool_a, pool_b = _pools()
    committed = snapshot_pool_map({pool_a.pool_id: pool_a, pool_b.pool_id: pool_b})

    corruption_cases = (
        ("asset_out", ASSET_IN),
        ("total_amount_in", 1),
        ("legs", ()),
    )
    for field, value in corruption_cases:
        binding = _derive_ok(_admitted(_exact_in_fields((pool_a, pool_b), (4_000, 6_000))))
        object.__setattr__(binding, field, value)
        result, observed = replay_exact_route_observed_v1(binding, committed)
        assert type(result) is RouteReplayRejectV1, field
        assert result.code is RouteReplayRejectCodeV1.BINDING_INVALID, field
        assert observed == (), field
        pins, pin_reads = route_binding_pins_exact_snapshot_observed_v1(binding, committed)
        assert pins is False, field
        assert pin_reads == (), field

    binding = _derive_ok(_admitted(_exact_in_fields((pool_a, pool_b), (4_000, 6_000))))
    object.__setattr__(binding.legs[0], "amount_in", True)
    result, observed = replay_exact_route_observed_v1(binding, committed)
    assert type(result) is RouteReplayRejectV1
    assert result.code is RouteReplayRejectCodeV1.BINDING_INVALID
    assert observed == ()

    binding = _derive_ok(_admitted(_exact_in_fields((pool_a, pool_b), (4_000, 6_000))))
    object.__setattr__(binding.pool_fingerprints, "_schema_id", "zenodex/forged/v1")
    result, observed = replay_exact_route_observed_v1(binding, committed)
    assert type(result) is RouteReplayRejectV1
    assert result.code is RouteReplayRejectCodeV1.BINDING_INVALID
    assert observed == ()

    binding = _derive_ok(_admitted(_exact_in_fields((pool_a, pool_b), (4_000, 6_000))))
    object.__setattr__(binding.legs[0], "asset_in", ASSET_OTHER)
    result, observed = replay_exact_route_observed_v1(binding, committed)
    assert type(result) is RouteReplayRejectV1
    assert result.code is RouteReplayRejectCodeV1.BINDING_INVALID
    assert observed == ()

    binding = _derive_ok(_admitted(_exact_in_fields((pool_a, pool_b), (4_000, 6_000))))
    reversed_entries = tuple(reversed(binding.pool_fingerprints.entries))
    object.__setattr__(binding.pool_fingerprints, "_entries", reversed_entries)
    result, observed = replay_exact_route_observed_v1(binding, committed)
    assert type(result) is RouteReplayRejectV1
    assert result.code is RouteReplayRejectCodeV1.BINDING_INVALID
    assert observed == ()

    binding = _derive_ok(_admitted(_exact_in_fields((pool_a, pool_b), (4_000, 6_000))))
    entries = binding.pool_fingerprints.entries
    object.__setattr__(
        binding.pool_fingerprints,
        "_entries",
        (("0x" + "ff" * 32, entries[0][1]),) + entries[1:],
    )
    result, observed = replay_exact_route_observed_v1(binding, committed)
    assert type(result) is RouteReplayRejectV1
    assert result.code is RouteReplayRejectCodeV1.BINDING_INVALID
    assert observed == ()


def test_corrupted_owned_intent_graphs_reject_closedly_at_derivation() -> None:
    pools = _pools()

    intent = _admitted(_exact_in_fields(pools, (4_000, 6_000)))
    _corrupt_field_lookup(intent, "route_legs", [])
    reject = _derive_reject(intent)
    assert reject.code is RouteBindingRejectCodeV1.STRUCTURAL_INVALID
    assert reject.path == ("route_legs",)

    intent = _admitted(_exact_in_fields(pools, (4_000, 6_000)))
    _corrupt_field_lookup(intent, "route_legs", (object(),))
    reject = _derive_reject(intent)
    assert reject.code is RouteBindingRejectCodeV1.STRUCTURAL_INVALID
    assert reject.path == ("route_legs", 0)

    intent = _admitted(_exact_in_fields(pools, (4_000, 6_000)))
    leg = intent.fields["route_legs"][0]
    leg_index: dict[str, object] = dict(leg.entries)
    leg_index["pool_id"] = "tampered"
    object.__setattr__(leg, "_index", leg_index)
    reject = _derive_reject(intent)
    assert reject.code is RouteBindingRejectCodeV1.STRUCTURAL_INVALID
    assert reject.path == ("route_legs", 0)


def test_derivation_and_replay_are_deterministic_across_repeated_calls() -> None:
    pools = _pools()
    intent = _admitted(_exact_in_fields(pools, (4_000, 6_000)))
    committed = snapshot_pool_map({pool.pool_id: pool for pool in pools})

    first = derive_exact_route_binding_v1(intent)
    second = derive_exact_route_binding_v1(intent)
    assert first == second
    assert type(first) is RouteBindingOkV1

    first_replay, first_observed = replay_exact_route_observed_v1(first.binding, committed)
    second_replay, second_observed = replay_exact_route_observed_v1(first.binding, committed)
    assert first_replay == second_replay
    assert first_observed == second_observed


def test_non_observed_wrappers_are_projections_of_observed_variants() -> None:
    pools = _pools()
    binding = _derive_ok(_admitted(_exact_in_fields(pools, (4_000, 6_000))))
    committed = snapshot_pool_map({pool.pool_id: pool for pool in pools})

    observed_replay, _reads = replay_exact_route_observed_v1(binding, committed)
    assert replay_exact_route_v1(binding, committed) == observed_replay
    observed_pins, _pin_reads = route_binding_pins_exact_snapshot_observed_v1(binding, committed)
    assert route_binding_pins_exact_snapshot_v1(binding, committed) is observed_pins
