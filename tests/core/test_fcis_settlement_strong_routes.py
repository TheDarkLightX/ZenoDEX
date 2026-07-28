"""Route and CoW composition evidence for the exact P4B4 validator."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.fcis_route_binding import (
    derive_exact_route_binding_v1,
    replay_exact_route_observed_v1,
)
from src.core.fcis_route_binding_values import (
    RouteBindingOkV1,
    RouteReplayOkV1,
)
from src.core.fcis_settlement_strong_validator import (
    evaluate_settlement_strong_exact_v1,
)
from src.core.fcis_settlement_strong_values import (
    ExactSpotPreStateV1,
    ExactStrongSettlementCandidateV1,
    ExactStrongSettlementRejectV1,
    StrongSettlementContextV1,
)
from src.core.quote_receipts import pool_state_fingerprint
from src.core.settlement_snapshots import (
    OwnedBalanceDeltaV1,
    OwnedFillV1,
    OwnedReserveDeltaV1,
    OwnedSettlementV1,
    snapshot_settlement,
)
from src.state.intent_snapshots import OwnedIntentV1, snapshot_intent
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshots import snapshot_pool_map
from tests.core.test_fcis_route_binding import (
    ASSET_IN,
    ASSET_OTHER,
    ASSET_OUT,
    SENDER,
    _admitted,
    _exact_in_fields,
    _exact_out_fields,
    _pool,
)
from tests.core.test_fcis_route_binding import (
    _pools as route_pools,
)
from tests.core.test_fcis_settlement_strong_validator import (
    ASSET0,
    ASSET1,
    INITIAL_BALANCE,
    POOL_ID,
    _balances,
    _context,
    _fill_action,
    _funded_pool,
    _lp_balances,
)

SECOND_SENDER = "0x" + "33" * 48
COW_A_ID = "0x" + "a1" * 32
COW_B_ID = "0x" + "b2" * 32
COW_AMOUNT = 1_000


def _route_context() -> StrongSettlementContextV1:
    base = _context()
    return StrongSettlementContextV1(
        settlement=replace(
            base.settlement,
            allow_snapshot_bound_quote_bindings=True,
        ),
        lp_duration_policy=base.lp_duration_policy,
    )


def _cow_context(*, enabled: bool) -> StrongSettlementContextV1:
    base = _context()
    return StrongSettlementContextV1(
        settlement=replace(base.settlement, allow_cow_netting=enabled),
        lp_duration_policy=base.lp_duration_policy,
    )


def _pre_state_for_route_pools(
    pools: tuple[PoolState, ...],
) -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=_balances(
            ((SENDER, ASSET_IN), INITIAL_BALANCE),
            ((SENDER, ASSET_OUT), INITIAL_BALANCE),
        ),
        pools=snapshot_pool_map({pool.pool_id: pool for pool in pools}),
        lp_balances=_lp_balances(),
    )


def _reserve_certificate(
    replay: RouteReplayOkV1,
) -> tuple[OwnedReserveDeltaV1, ...]:
    totals: dict[tuple[str, str], tuple[int, int]] = {}
    for leg in replay.legs:
        in_key = (leg.pool_id, leg.asset_in)
        out_key = (leg.pool_id, leg.asset_out)
        in_add, in_sub = totals.get(in_key, (0, 0))
        out_add, out_sub = totals.get(out_key, (0, 0))
        totals[in_key] = (in_add + leg.amount_in, in_sub)
        totals[out_key] = (out_add, out_sub + leg.amount_out)
    return tuple(
        OwnedReserveDeltaV1(pool_id, asset, delta_add, delta_sub)
        for (pool_id, asset), (delta_add, delta_sub) in sorted(totals.items())
    )


def _route_settlement(
    intent: OwnedIntentV1,
    replay: RouteReplayOkV1,
) -> OwnedSettlementV1:
    action = _fill_action()
    return snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="exact-route",
            included_intents=((intent.intent_id, action),),
            fills=(
                OwnedFillV1(
                    intent_id=intent.intent_id,
                    action=action,
                    reason=None,
                    amount_in_filled=replay.total_amount_in,
                    amount_out_filled=replay.total_amount_out,
                    fee_paid=replay.total_fee_paid,
                    protocol_fee_paid=None,
                    amount0_used=None,
                    amount1_used=None,
                    lp_minted=None,
                    amount0_out=None,
                    amount1_out=None,
                    lp_burned=None,
                    reserve_in_before=None,
                    reserve_out_before=None,
                ),
            ),
            balance_deltas=tuple(
                sorted(
                    (
                        OwnedBalanceDeltaV1(
                            intent.sender_pubkey,
                            ASSET_IN,
                            0,
                            replay.total_amount_in,
                        ),
                        OwnedBalanceDeltaV1(
                            intent.sender_pubkey,
                            ASSET_OUT,
                            replay.total_amount_out,
                            0,
                        ),
                    ),
                    key=lambda delta: (delta.pubkey, delta.asset),
                )
            ),
            reserve_deltas=_reserve_certificate(replay),
            lp_deltas=(),
            events=None,
        )
    )


def _route_fixture(
    kind: IntentKind,
    pools: tuple[PoolState, ...],
) -> tuple[OwnedSettlementV1, OwnedIntentV1, ExactSpotPreStateV1, RouteReplayOkV1]:
    fields = (
        _exact_in_fields(pools, tuple(4_000 + index * 2_000 for index in range(len(pools))))
        if kind is IntentKind.ROUTE_EXACT_IN
        else _exact_out_fields(
            pools,
            tuple(3_000 + index * 2_000 for index in range(len(pools))),
        )
    )
    intent = _admitted(fields, kind)
    derived = derive_exact_route_binding_v1(intent)
    assert type(derived) is RouteBindingOkV1
    pre_state = _pre_state_for_route_pools(pools)
    replay, _reads = replay_exact_route_observed_v1(
        intent,
        derived.binding,
        pre_state.pools,
    )
    assert type(replay) is RouteReplayOkV1
    return _route_settlement(intent, replay), intent, pre_state, replay


def _evaluate_route(
    settlement: OwnedSettlementV1,
    intent: OwnedIntentV1,
    pre_state: ExactSpotPreStateV1,
):
    return evaluate_settlement_strong_exact_v1(
        settlement=settlement,
        intents=(intent,),
        pre_state=pre_state,
        context=_route_context(),
    )


def _assert_reject(observed, text: str) -> None:
    assert type(observed.result) is ExactStrongSettlementRejectV1
    assert text in observed.result.reason
    assert not hasattr(observed.result, "balances")


@pytest.mark.parametrize(
    "kind",
    (IntentKind.ROUTE_EXACT_IN, IntentKind.ROUTE_EXACT_OUT),
)
def test_route_exact_in_and_out_accept_with_direct_canonical_reads(
    kind: IntentKind,
) -> None:
    pools = route_pools()
    settlement, intent, pre_state, replay = _route_fixture(kind, pools)

    observed = _evaluate_route(settlement, intent, pre_state)

    assert type(observed.result) is ExactStrongSettlementCandidateV1
    assert observed.result.balances.get(SENDER, ASSET_IN) == (
        INITIAL_BALANCE - replay.total_amount_in
    )
    assert observed.result.balances.get(SENDER, ASSET_OUT) == (
        INITIAL_BALANCE + replay.total_amount_out
    )
    assert observed.state_read_trace.pool_ids == tuple(sorted(pool.pool_id for pool in pools))


def test_route_rederivation_rejects_command_substitution() -> None:
    pools = route_pools()
    settlement, _intent, pre_state, _replay = _route_fixture(
        IntentKind.ROUTE_EXACT_IN,
        pools,
    )
    substituted = _admitted(_exact_in_fields(pools, (5_000, 6_000)))

    observed = _evaluate_route(settlement, substituted, pre_state)

    _assert_reject(observed, "route amount_in_filled mismatch")


@pytest.mark.parametrize("mutation", ("missing", "inactive", "drifted"))
def test_route_prestate_binding_rejects_missing_inactive_and_drifted_pools(
    mutation: str,
) -> None:
    pools = route_pools()
    settlement, intent, _pre_state, _replay = _route_fixture(
        IntentKind.ROUTE_EXACT_IN,
        pools,
    )
    changed: tuple[PoolState, ...]
    if mutation == "missing":
        changed = (pools[1],)
    elif mutation == "inactive":
        changed = (replace(pools[0], status=PoolStatus.FROZEN), pools[1])
    else:
        changed = (pools[0], replace(pools[1], reserve0=pools[1].reserve0 + 1))

    observed = _evaluate_route(
        settlement,
        intent,
        _pre_state_for_route_pools(changed),
    )

    _assert_reject(observed, "does not pin the pre-state snapshot")


def test_route_rejects_misoriented_pool_after_command_bound_preflight() -> None:
    nominal_pools = route_pools()
    settlement, _intent, _pre_state, _replay = _route_fixture(
        IntentKind.ROUTE_EXACT_IN,
        nominal_pools,
    )
    wrong_pool = PoolState(
        pool_id=compute_pool_id(ASSET_IN, ASSET_OTHER, 30),
        asset0=ASSET_IN,
        asset1=ASSET_OTHER,
        reserve0=1_000_000,
        reserve1=1_000_000,
        fee_bps=30,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    wrong_fields = _exact_in_fields((nominal_pools[0],), (4_000,))
    wrong_fields["route_legs"] = [{**wrong_fields["route_legs"][0], "pool_id": wrong_pool.pool_id}]
    wrong_fields["route_pool_fingerprints"] = {
        wrong_pool.pool_id: pool_state_fingerprint(wrong_pool)
    }
    wrong_intent = _admitted(wrong_fields)

    observed = _evaluate_route(
        settlement,
        wrong_intent,
        _pre_state_for_route_pools((wrong_pool,)),
    )

    _assert_reject(observed, "route replay failed")


def test_route_leg_order_is_semantic_and_noncanonical_reorder_rejects() -> None:
    pool = _pool(30)
    settlement, _intent, pre_state, _replay = _route_fixture(
        IntentKind.ROUTE_EXACT_IN,
        (pool, pool),
    )
    fields = _exact_in_fields((pool, pool), (4_000, 6_000))
    fields["route_legs"] = [fields["route_legs"][1], fields["route_legs"][0]]
    reordered = _admitted(fields)

    observed = _evaluate_route(settlement, reordered, pre_state)

    _assert_reject(observed, "route replay failed")


def test_repeated_pool_route_uses_scratch_and_reads_committed_pool_once() -> None:
    pool = _pool(30)
    settlement, intent, pre_state, replay = _route_fixture(
        IntentKind.ROUTE_EXACT_IN,
        (pool, pool),
    )

    observed = _evaluate_route(settlement, intent, pre_state)

    assert type(observed.result) is ExactStrongSettlementCandidateV1
    assert observed.state_read_trace.pool_ids == (pool.pool_id,)
    last_leg = replay.legs[-1]
    assert observed.result.pools[pool.pool_id].reserve0 == last_leg.new_reserve0
    assert observed.result.pools[pool.pool_id].reserve1 == last_leg.new_reserve1


def _cow_intent(
    intent_id: str,
    sender: str,
    asset_in: str,
    asset_out: str,
) -> OwnedIntentV1:
    return snapshot_intent(
        Intent(
            "TauSwap",
            "0.1",
            IntentKind.SWAP_EXACT_IN,
            intent_id,
            sender,
            9_999_999_999,
            None,
            {
                "pool_id": POOL_ID,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": COW_AMOUNT,
                "min_amount_out": COW_AMOUNT,
            },
        )
    )


def _cow_fill(intent_id: str) -> OwnedFillV1:
    action = _fill_action()
    return OwnedFillV1(
        intent_id=intent_id,
        action=action,
        reason="COW_NETTED",
        amount_in_filled=COW_AMOUNT,
        amount_out_filled=COW_AMOUNT,
        fee_paid=0,
        protocol_fee_paid=0,
        amount0_used=None,
        amount1_used=None,
        lp_minted=None,
        amount0_out=None,
        amount1_out=None,
        lp_burned=None,
        reserve_in_before=None,
        reserve_out_before=None,
    )


def _cow_settlement(*, symmetric: bool) -> tuple[OwnedSettlementV1, tuple[OwnedIntentV1, ...]]:
    first = _cow_intent(COW_A_ID, SENDER, ASSET0, ASSET1)
    second = _cow_intent(COW_B_ID, SECOND_SENDER, ASSET1, ASSET0)
    intents = (first, second) if symmetric else (first,)
    action = _fill_action()
    deltas: tuple[OwnedBalanceDeltaV1, ...] = (
        OwnedBalanceDeltaV1(SENDER, ASSET0, 0, COW_AMOUNT),
        OwnedBalanceDeltaV1(SENDER, ASSET1, COW_AMOUNT, 0),
    )
    if symmetric:
        deltas += (
            OwnedBalanceDeltaV1(SECOND_SENDER, ASSET0, COW_AMOUNT, 0),
            OwnedBalanceDeltaV1(SECOND_SENDER, ASSET1, 0, COW_AMOUNT),
        )
    settlement = snapshot_settlement(
        OwnedSettlementV1(
            module="TauSwap",
            version="0.1",
            batch_ref="cow-symmetric" if symmetric else "cow-asymmetric",
            included_intents=tuple((intent.intent_id, action) for intent in intents),
            fills=tuple(_cow_fill(intent.intent_id) for intent in intents),
            balance_deltas=tuple(sorted(deltas, key=lambda delta: (delta.pubkey, delta.asset))),
            reserve_deltas=(),
            lp_deltas=(),
            events=None,
        )
    )
    return settlement, intents


def _cow_pre_state() -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=_balances(
            ((SENDER, ASSET0), INITIAL_BALANCE),
            ((SENDER, ASSET1), INITIAL_BALANCE),
            ((SECOND_SENDER, ASSET0), INITIAL_BALANCE),
            ((SECOND_SENDER, ASSET1), INITIAL_BALANCE),
        ),
        pools=snapshot_pool_map({POOL_ID: _funded_pool()}),
        lp_balances=_lp_balances(),
    )


def test_cow_requires_symmetric_conservation_and_enabled_context() -> None:
    settlement, intents = _cow_settlement(symmetric=True)
    accepted = evaluate_settlement_strong_exact_v1(
        settlement=settlement,
        intents=intents,
        pre_state=_cow_pre_state(),
        context=_cow_context(enabled=True),
    )
    assert type(accepted.result) is ExactStrongSettlementCandidateV1
    assert accepted.result.pools[POOL_ID] == _cow_pre_state().pools[POOL_ID]

    asymmetric, one_intent = _cow_settlement(symmetric=False)
    rejected = evaluate_settlement_strong_exact_v1(
        settlement=asymmetric,
        intents=one_intent,
        pre_state=_cow_pre_state(),
        context=_cow_context(enabled=True),
    )
    _assert_reject(rejected, "reciprocal counterparty")

    disabled = evaluate_settlement_strong_exact_v1(
        settlement=settlement,
        intents=intents,
        pre_state=_cow_pre_state(),
        context=_cow_context(enabled=False),
    )
    _assert_reject(disabled, "COW_NETTED not allowed")
