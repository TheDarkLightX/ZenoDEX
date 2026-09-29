"""DexState owns immutable snapshots and DEX steps return owned effects.

Obligations (current-source repair of STATE-ALIAS-001..004 and 006):

- constructing or replacing a ``DexState`` copies builder content; later
  builder mutation cannot reach the committed state;
- committed members expose no mutation surface;
- an accepted step returns a ``DexEffects`` value whose settlement graph is
  recursively immutable, and the pre-state is unchanged;
- a rejected step returns no state and no effects and leaves the pre-state
  unchanged;
- the owned settlement round-trips to an equal builder from the shared
  ``compute_settlement`` path (internal representation parity).
"""

from __future__ import annotations

from dataclasses import FrozenInstanceError, replace

import pytest

from src.core.batch_clearing import apply_settlement, apply_settlement_pure, compute_settlement
from src.core.dex import (
    DexConfig,
    DexEffects,
    DexState,
    DexStepResult,
    step,
    step_with_candidate_settlement,
)
from src.core.fees import FeeSplitParams, FeeSplitResult
from src.core.settlement import (
    BalanceDelta,
    Fill,
    FillAction,
    FillSnapshot,
    LPDelta,
    ReserveDelta,
    Settlement,
    SettlementEventSnapshot,
    SettlementSnapshot,
    snapshot_settlement,
)
from src.state.balances import BalanceSnapshot, BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPSnapshot, LPTable
from src.state.nonces import NonceSnapshot, NonceTable
from src.state.pools import PoolSnapshot, PoolState, PoolStatus, PoolTableSnapshot, compute_pool_id
from src.state.state_root import compute_state_root

ALICE = "0x" + "aa" * 48
ASSET0 = "0x" + "11" * 32
ASSET1 = "0x" + "22" * 32
FEE_BPS = 30
POOL_ID = compute_pool_id(ASSET0, ASSET1, FEE_BPS)


def _iid(index: int) -> str:
    return "0x" + f"{index:064x}"


def _intent(kind: IntentKind, index: int, **fields: object) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_iid(index),
        sender_pubkey=ALICE,
        deadline=9_999_999_999,
        fields=dict(fields),
    )


def _funded_state() -> tuple[DexState, BalanceTable, dict[str, PoolState], LPTable, NonceTable]:
    balances = BalanceTable()
    balances.set(ALICE, ASSET0, 10_000_000)
    balances.set(ALICE, ASSET1, 10_000_000)
    pools: dict[str, PoolState] = {}
    lp = LPTable()
    nonces = NonceTable()
    nonces.set_last(ALICE, 3)
    state = DexState(balances=balances, pools=pools, lp_balances=lp, nonces=nonces)
    return state, balances, pools, lp, nonces


def _create_pool_intent(index: int = 1) -> Intent:
    return _intent(
        IntentKind.CREATE_POOL,
        index,
        asset0=ASSET0,
        asset1=ASSET1,
        fee_bps=FEE_BPS,
        amount0=1_000_000,
        amount1=1_000_000,
    )


def _swap_intent(index: int = 2) -> Intent:
    return _intent(
        IntentKind.SWAP_EXACT_IN,
        index,
        pool_id=POOL_ID,
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_in=1_000,
        min_amount_out=1,
    )


# ---------------------------------------------------------------------------
# STATE-ALIAS-001..004: DexState ownership
# ---------------------------------------------------------------------------


def test_dex_state_stores_snapshots_and_ignores_later_builder_mutation() -> None:
    state, balances, pools, lp, nonces = _funded_state()
    assert type(state.balances) is BalanceSnapshot
    assert type(state.pools) is PoolTableSnapshot
    assert type(state.lp_balances) is LPSnapshot
    assert type(state.nonces) is NonceSnapshot
    root_before = compute_state_root(
        balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=state.nonces
    )

    # Mallory keeps the builder references and mutates them after commit.
    balances.set(ALICE, ASSET0, 1)
    pools[POOL_ID] = PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=1,
        reserve1=1,
        fee_bps=FEE_BPS,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    lp.set(ALICE, POOL_ID, 5)
    nonces.set_last(ALICE, 99)

    assert state.balances.get(ALICE, ASSET0) == 10_000_000
    assert POOL_ID not in state.pools
    assert state.lp_balances.get(ALICE, POOL_ID) == 0
    assert state.nonces.get_last(ALICE) == 3
    assert (
        compute_state_root(
            balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=state.nonces
        )
        == root_before
    )


def test_dex_state_members_expose_no_mutation_surface() -> None:
    state, *_ = _funded_state()
    committed = step(DexConfig(), state, [_create_pool_intent()])
    assert committed.ok, committed.error
    assert committed.state is not None
    next_state = committed.state

    assert not hasattr(next_state.balances, "set")
    assert not hasattr(next_state.lp_balances, "set")
    assert not hasattr(next_state.nonces, "set_last")
    with pytest.raises(TypeError):
        next_state.pools[POOL_ID] = next_state.pools[POOL_ID]  # type: ignore[index]
    with pytest.raises(FrozenInstanceError):
        next_state.pools[POOL_ID].reserve0 = 0  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        next_state.balances = BalanceTable()  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        next_state.pools = {}  # type: ignore[misc]


def test_dex_state_replace_commits_new_snapshot_and_keeps_the_old_one() -> None:
    state, *_ = _funded_state()
    builder = state.balances.to_table()
    builder.set(ALICE, ASSET0, 42)
    updated = replace(state, balances=builder)

    assert type(updated.balances) is BalanceSnapshot
    assert updated.balances.get(ALICE, ASSET0) == 42
    assert state.balances.get(ALICE, ASSET0) == 10_000_000
    assert updated.pools is state.pools
    assert updated.nonces == state.nonces

    builder.set(ALICE, ASSET0, 7)
    assert updated.balances.get(ALICE, ASSET0) == 42

    with pytest.raises(TypeError):
        DexState(balances={}, pools={}, lp_balances=LPTable())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        DexState(balances=BalanceTable(), pools=[], lp_balances=LPTable())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        DexState(balances=BalanceTable(), pools={}, lp_balances=BalanceTable())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable(), nonces={})  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# STATE-ALIAS-006: returned effects and settlement graph
# ---------------------------------------------------------------------------


def _config() -> DexConfig:
    return DexConfig(fee_split_params=FeeSplitParams(buyback_bps=5_000, treasury_bps=3_000, rewards_bps=2_000))


def test_dex_step_returns_owned_effects_and_leaves_pre_state_unchanged() -> None:
    state, *_ = _funded_state()
    created = step(_config(), state, [_create_pool_intent(1)])
    assert created.ok, created.error
    assert created.state is not None
    pre_state = created.state
    pre_root = compute_state_root(
        balances=pre_state.balances,
        pools=pre_state.pools,
        lp_balances=pre_state.lp_balances,
        nonces=pre_state.nonces,
    )

    result = step(_config(), pre_state, [_swap_intent(2)])
    assert result.ok, result.error
    assert result.state is not None
    effects = result.effects
    assert type(effects) is DexEffects

    # Closed key set with mapping compatibility for existing readers.
    assert effects["settlement"] is effects.settlement
    assert effects["total_swap_fees"] == effects.total_swap_fees
    assert effects["fee_split"] == effects.fee_split
    assert set(effects) == {"settlement", "total_swap_fees", "fee_split"}
    assert len(effects) == 3
    assert "settlement" in effects
    with pytest.raises(KeyError):
        effects["balances"]
    with pytest.raises(FrozenInstanceError):
        effects.total_swap_fees = 0  # type: ignore[misc]

    # The settlement graph is recursively owned and immutable.
    settlement = effects.settlement
    assert type(settlement) is SettlementSnapshot
    assert type(settlement.fills) is tuple
    assert type(settlement.included_intents) is tuple
    assert all(type(fill) is FillSnapshot for fill in settlement.fills)
    assert dict(settlement.included_intents) == {_iid(2): FillAction.FILL}
    with pytest.raises(FrozenInstanceError):
        settlement.fills[0].amount_out_filled = 0  # type: ignore[misc]
    with pytest.raises(FrozenInstanceError):
        settlement.fills = ()  # type: ignore[misc]
    with pytest.raises(AttributeError):
        settlement.balance_deltas.append(None)  # type: ignore[attr-defined]
    assert effects.total_swap_fees == sum(int(fill.fee_paid or 0) for fill in settlement.fills)
    assert effects.fee_split is not None

    # Internal representation parity; the shared compute path is not an independent oracle.
    recomputed = compute_settlement(
        intents=[_swap_intent(2)],
        pools=pre_state.pools,
        balances=pre_state.balances,
        lp_balances=pre_state.lp_balances,
    )
    assert settlement.to_settlement() == recomputed
    assert snapshot_settlement(recomputed) == settlement

    # Pre-state is untouched; next state is a distinct committed value.
    assert (
        compute_state_root(
            balances=pre_state.balances,
            pools=pre_state.pools,
            lp_balances=pre_state.lp_balances,
            nonces=pre_state.nonces,
        )
        == pre_root
    )
    assert result.state.pools[POOL_ID].reserve0 == pre_state.pools[POOL_ID].reserve0 + 1_000
    assert result.state.balances.get(ALICE, ASSET0) == pre_state.balances.get(ALICE, ASSET0) - 1_000
    assert result.state is not pre_state


def test_dex_step_rejection_returns_no_state_no_effects_and_keeps_pre_state() -> None:
    state, *_ = _funded_state()
    pre_root = compute_state_root(
        balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=state.nonces
    )

    # Nonce policy rejection (non-contiguous batch nonce for ALICE whose last nonce is 3).
    bad_nonce = _intent(
        IntentKind.CREATE_POOL,
        9,
        asset0=ASSET0,
        asset1=ASSET1,
        fee_bps=FEE_BPS,
        amount0=1,
        amount1=1,
        nonce=7,
    )
    rejected = step(DexConfig(), state, [bad_nonce])
    assert rejected.ok is False
    assert rejected.state is None
    assert rejected.effects is None
    assert rejected.error

    # Non-JSON metadata is rejected at owned effects admission.
    invalid_event = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=[{"type": "metadata", "value": object()}],
    )
    rejected_candidate = step_with_candidate_settlement(
        DexConfig(settlement_validation="legacy"),
        state,
        [],
        candidate_settlement=invalid_event,
    )
    assert rejected_candidate.ok is False
    assert rejected_candidate.state is None
    assert rejected_candidate.effects is None
    assert rejected_candidate.error is not None
    assert (
        compute_state_root(
            balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=state.nonces
        )
        == pre_root
    )
    assert state.balances.get(ALICE, ASSET0) == 10_000_000
    assert state.nonces.get_last(ALICE) == 3


def test_dex_effects_and_step_result_reject_non_owned_inputs() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
    )
    effects = DexEffects(settlement=settlement, total_swap_fees=0)
    assert type(effects.settlement) is SettlementSnapshot

    with pytest.raises(TypeError):
        DexEffects(settlement={"module": "TauSwap"}, total_swap_fees=0)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        DexEffects(settlement=settlement, total_swap_fees=-1)
    with pytest.raises(TypeError):
        DexEffects(settlement=settlement, total_swap_fees=True)
    with pytest.raises(TypeError):
        DexEffects(settlement=settlement, total_swap_fees=0, fee_split="split")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        DexStepResult(ok=True, effects={"settlement": settlement})  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        DexStepResult(ok=True, state={"balances": {}})  # type: ignore[arg-type]


def _builder_settlement_with_event() -> Settlement:
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(_iid(1), FillAction.FILL), (_iid(5), FillAction.REJECT)],
        fills=[
            Fill(
                intent_id=_iid(1),
                action=FillAction.FILL,
                reason="POOL_CREATED",
                amount0_used=1_000_000,
                amount1_used=1_000_000,
                lp_minted=999_000,
            ),
            Fill(intent_id=_iid(5), action=FillAction.REJECT, reason="POOL_NOT_FOUND"),
        ],
        balance_deltas=[BalanceDelta(pubkey=ALICE, asset=ASSET0, delta_add=0, delta_sub=1_000_000)],
        reserve_deltas=[ReserveDelta(pool_id=POOL_ID, asset=ASSET0, delta_add=1_000_000, delta_sub=0)],
        lp_deltas=[LPDelta(pubkey=ALICE, pool_id=POOL_ID, delta_add=999_000, delta_sub=0)],
        events=[
            {
                "type": "CREATE_POOL",
                "pool_id": POOL_ID,
                "asset0": ASSET0,
                "asset1": ASSET1,
                "fee_bps": FEE_BPS,
                "curve_tag": "CPMM",
                "curve_params": "",
                "status": "ACTIVE",
                "created_at": 0,
            }
        ],
    )


def test_settlement_snapshot_round_trips_and_detaches_from_builder() -> None:
    builder = _builder_settlement_with_event()
    snapshot = snapshot_settlement(builder)

    # Builder tampering after the snapshot is invisible to the owned value.
    builder.fills[0].amount0_used = 1
    builder.balance_deltas[0].delta_sub += 1
    builder.events[0]["fee_bps"] = 9_999  # type: ignore[index]
    builder.included_intents.append((_iid(6), FillAction.REJECT))
    assert snapshot.fills[0].amount0_used == 1_000_000
    assert snapshot.balance_deltas[0].delta_sub == 1_000_000
    assert snapshot.events is not None and snapshot.events[0]["fee_bps"] == FEE_BPS
    assert len(snapshot.included_intents) == 2

    event = snapshot.events[0]
    assert type(event) is SettlementEventSnapshot
    assert event.get("type") == "CREATE_POOL"
    assert event == builder.events[0] | {"fee_bps": FEE_BPS}  # type: ignore[index]
    with pytest.raises(TypeError):
        event["fee_bps"] = 1  # type: ignore[index]
    with pytest.raises(KeyError):
        event[1]  # type: ignore[index]
    assert event.to_dict()["pool_id"] == POOL_ID

    rebuilt = snapshot.to_settlement()
    assert type(rebuilt) is Settlement
    assert rebuilt == _builder_settlement_with_event()
    assert snapshot_settlement(rebuilt) == snapshot
    assert snapshot_settlement(snapshot) is snapshot
    assert snapshot.balance_deltas[0].net_delta() == -1_000_000


def test_dex_effects_own_exact_fee_primitives() -> None:
    class IntegerValue(int):
        pass

    split = FeeSplitResult(
        buyback_amount=IntegerValue(2), treasury_amount=IntegerValue(1),
        rewards_amount=IntegerValue(1), dust_carried=IntegerValue(0),
    )
    effects = DexEffects(
        settlement=_builder_settlement_with_event(),
        total_swap_fees=IntegerValue(4), fee_split=split,
    )
    assert type(effects.total_swap_fees) is int
    assert effects.fee_split == split
    assert effects.fee_split is not split
    for name in ("buyback_amount", "treasury_amount", "rewards_amount", "dust_carried"):
        assert type(getattr(effects.fee_split, name)) is int


def test_settlement_snapshot_rejects_hostile_rows_and_values() -> None:
    class HostileFill(Fill):
        pass

    base = _builder_settlement_with_event()
    hostile_row = replace(base, fills=[HostileFill(intent_id=_iid(1), action=FillAction.FILL), base.fills[1]])
    with pytest.raises(TypeError):
        snapshot_settlement(hostile_row)

    bool_amount = replace(base, fills=[replace(base.fills[0], lp_minted=True), base.fills[1]])
    with pytest.raises(TypeError):
        snapshot_settlement(bool_amount)

    negative_limb = replace(base, balance_deltas=[BalanceDelta(pubkey=ALICE, asset=ASSET0, delta_add=-1, delta_sub=0)])
    with pytest.raises(TypeError):
        snapshot_settlement(negative_limb)

    non_json_event = replace(base, events=[{"type": "metadata", "value": object()}])
    with pytest.raises(TypeError):
        snapshot_settlement(non_json_event)

    # The builder tolerates stringly typed actions as long as both sides agree;
    # the owned snapshot requires the exact FillAction enum.
    string_action = replace(
        base,
        included_intents=[(_iid(1), "FILL"), (_iid(5), FillAction.REJECT)],  # type: ignore[list-item]
        fills=[replace(base.fills[0], action="FILL"), base.fills[1]],  # type: ignore[arg-type]
    )
    with pytest.raises(TypeError):
        snapshot_settlement(string_action)

    with pytest.raises(TypeError):
        snapshot_settlement({"module": "TauSwap"})  # type: ignore[arg-type]

    with pytest.raises(ValueError):
        SettlementSnapshot(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=((_iid(1), FillAction.FILL),),
            fills=(),
            balance_deltas=(),
            reserve_deltas=(),
            lp_deltas=(),
        )


def test_apply_settlement_in_place_rejects_committed_values_but_pure_apply_accepts_them() -> None:
    state, *_ = _funded_state()
    settlement = compute_settlement(
        intents=[_create_pool_intent(1)],
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
    )
    root_before = compute_state_root(
        balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=state.nonces
    )

    with pytest.raises(TypeError):
        apply_settlement(settlement, state.balances, dict(state.pools), LPTable())  # type: ignore[arg-type]
    pool_snapshot = PoolSnapshot(
        pool_id=POOL_ID, asset0=ASSET0, asset1=ASSET1,
        reserve0=0, reserve1=0, fee_bps=FEE_BPS, lp_supply=0,
        status=PoolStatus.ACTIVE, created_at=0,
    )
    with pytest.raises(TypeError):
        apply_settlement(settlement, BalanceTable(), {POOL_ID: pool_snapshot}, LPTable())  # type: ignore[arg-type]

    next_balances, next_pools, next_lp = apply_settlement_pure(
        settlement=settlement,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
    )
    assert type(next_balances) is BalanceTable
    assert type(next_pools[POOL_ID]) is PoolState
    assert type(next_lp) is LPTable
    assert next_pools[POOL_ID].reserve0 == 1_000_000
    assert (
        compute_state_root(
            balances=state.balances, pools=state.pools, lp_balances=state.lp_balances, nonces=state.nonces
        )
        == root_before
    )
    assert POOL_ID not in state.pools
