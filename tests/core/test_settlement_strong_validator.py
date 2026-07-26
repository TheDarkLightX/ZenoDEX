# [TESTER] v1

from __future__ import annotations

import copy
from dataclasses import replace
from typing import Any, cast

import src.core.settlement_strong_validator as strong_validator
from src.core.batch_clearing import apply_settlement_pure, compute_settlement, validate_settlement
from src.core.dex import DexConfig, DexState
from src.core.dex import step as dex_step
from src.core.liquidity import create_pool
from src.core.quote_receipts import pool_state_fingerprint
from src.core.settlement import BalanceDelta, Fill, FillAction, LPDelta, ReserveDelta, Settlement
from src.core.settlement_snapshots import snapshot_settlement
from src.core.settlement_strong_validator import (
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    evaluate_settlement_strong_committed_v1,
    validate_settlement_strong,
    validate_settlement_strong_committed_v1,
)
from src.state import BalanceTable, LPTable
from src.state.intent_snapshots import admit_intent_batch
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_snapshots import (
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_asset_conservation_error_names_first_nonzero_asset() -> None:
    asset = "0x" + "01" * 32
    error = strong_validator._asset_conservation_error(
        [BalanceDelta(pubkey="0x" + "11" * 48, asset=asset, delta_add=1, delta_sub=0)],
        [],
    )

    assert error == f"Asset conservation violation: {asset}, net_delta = 1"


def _setup_liquidity_context() -> tuple[str, str, str, str, PoolState, BalanceTable, LPTable]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    lp_balances = LPTable()
    lp_balances.set(pk, pool_id, lp_minted)
    lp_balances.set("0x" + "00" * 48, pool_id, pool.lp_supply - lp_minted)
    return pk, asset0, asset1, pool_id, pool, balances, lp_balances


def _setup_swap_context() -> tuple[str, str, str, str, PoolState, BalanceTable, Intent, Settlement]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(900),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    return pk, asset0, asset1, pool_id, pool, balances, intent, settlement


def _setup_create_pool_context() -> tuple[str, str, str, BalanceTable, Intent, Settlement]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(901),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
        },
    )
    settlement = compute_settlement([intent], {}, balances, LPTable())
    return pk, asset0, asset1, balances, intent, settlement


def _setup_swap_exact_out_context(
    *, reverse: bool = False
) -> tuple[str, str, str, str, PoolState, BalanceTable, Intent, Settlement]:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    if reverse:
        swap_asset_in = asset1
        swap_asset_out = asset0
    else:
        swap_asset_in = asset0
        swap_asset_out = asset1

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(904 if not reverse else 905),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": swap_asset_in,
            "asset_out": swap_asset_out,
            "amount_out": 1_000,
            "max_amount_in": 10_000,
        },
    )
    settlement = compute_settlement(
        [intent],
        {pool_id: pool},
        balances,
        LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    return pk, asset0, asset1, pool_id, pool, balances, intent, settlement


def _setup_add_liquidity_context() -> tuple[
    str, str, str, str, PoolState, BalanceTable, LPTable, Intent, Settlement
]:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(906),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    return pk, asset0, asset1, pool_id, pool, balances, lp_balances, intent, settlement


def _setup_remove_liquidity_context() -> tuple[
    str, str, str, str, PoolState, BalanceTable, LPTable, Intent, Settlement
]:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(907),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": 1_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    return pk, asset0, asset1, pool_id, pool, balances, lp_balances, intent, settlement


def _assert_exact_legacy_validation_parity(
    *,
    settlement: Settlement,
    intents: list[Intent],
    balances: BalanceTable,
    pools: dict[str, PoolState],
    lp_balances: LPTable,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
) -> tuple[bool, str | None]:
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch(intents)
    exact_balances = snapshot_balance_table(balances)
    exact_pools = snapshot_pool_map(pools)
    exact_lp_balances = snapshot_lp_table(lp_balances)
    legacy = validate_settlement_strong(
        settlement=settlement,
        intents=intents,
        pre_balances=balances,
        pre_pools=pools,
        pre_lp_balances=lp_balances,
        mode="strong_replay",
        allow_cow_netting=allow_cow_netting,
        allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
    )
    exact = validate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=exact_balances,
        pre_pools=exact_pools,
        pre_lp_balances=exact_lp_balances,
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
        mode="strong_replay",
        allow_cow_netting=allow_cow_netting,
        allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
    )
    assert exact == legacy
    return legacy


def test_exact_committed_validator_matches_legacy_facade_across_spot_actions() -> None:
    _pk, _asset0, _asset1, create_balances, create_intent, create_settlement = (
        _setup_create_pool_context()
    )
    *_swap_prefix, swap_pool, swap_balances, swap_intent, swap_settlement = _setup_swap_context()
    swap_pool_id = swap_pool.pool_id
    *_out_prefix, out_pool, out_balances, out_intent, out_settlement = (
        _setup_swap_exact_out_context()
    )
    out_pool_id = out_pool.pool_id
    (
        *_add_prefix,
        add_pool,
        add_balances,
        add_lp,
        add_intent,
        add_settlement,
    ) = _setup_add_liquidity_context()
    add_pool_id = add_pool.pool_id
    (
        *_remove_prefix,
        remove_pool,
        remove_balances,
        remove_lp,
        remove_intent,
        remove_settlement,
    ) = _setup_remove_liquidity_context()
    remove_pool_id = remove_pool.pool_id

    cases: tuple[
        tuple[Settlement, Intent, BalanceTable, dict[str, PoolState], LPTable],
        ...,
    ] = (
        (create_settlement, create_intent, create_balances, {}, LPTable()),
        (
            swap_settlement,
            swap_intent,
            swap_balances,
            {swap_pool_id: swap_pool},
            LPTable(),
        ),
        (
            out_settlement,
            out_intent,
            out_balances,
            {out_pool_id: out_pool},
            LPTable(),
        ),
        (
            add_settlement,
            add_intent,
            add_balances,
            {add_pool_id: add_pool},
            add_lp,
        ),
        (
            remove_settlement,
            remove_intent,
            remove_balances,
            {remove_pool_id: remove_pool},
            remove_lp,
        ),
    )

    for settlement, intent, balances, pools, lp_balances in cases:
        exact_balances = snapshot_balance_table(balances)
        exact_pools = snapshot_pool_map(pools)
        exact_lp_balances = snapshot_lp_table(lp_balances)
        owned_settlement = snapshot_settlement(settlement)
        owned_intents = admit_intent_batch([intent])
        legacy = validate_settlement_strong(
            settlement=copy.deepcopy(settlement),
            intents=[intent],
            pre_balances=balances,
            pre_pools=pools,
            pre_lp_balances=lp_balances,
        )
        exact = validate_settlement_strong_committed_v1(
            settlement=owned_settlement,
            intents=owned_intents,
            pre_balances=exact_balances,
            pre_pools=exact_pools,
            pre_lp_balances=exact_lp_balances,
            now=700,
            min_lp_position_age_seconds=0,
            lp_duration_policy=None,
        )
        assert exact == legacy == (True, None)

        evaluated = evaluate_settlement_strong_committed_v1(
            settlement=owned_settlement,
            intents=owned_intents,
            pre_balances=exact_balances,
            pre_pools=exact_pools,
            pre_lp_balances=exact_lp_balances,
            now=700,
            min_lp_position_age_seconds=0,
            lp_duration_policy=None,
        )
        assert type(evaluated) is StrongSettlementStateCandidateV1

        legacy_next_balances, legacy_next_pools, legacy_next_lp = apply_settlement_pure(
            copy.deepcopy(settlement),
            balances,
            pools,
            lp_balances,
        )
        assert evaluated.balances == snapshot_balance_table(legacy_next_balances)
        assert evaluated.pools == snapshot_pool_map(legacy_next_pools)
        assert (
            evaluated.lp_balances.balance_entries
            == snapshot_lp_table(legacy_next_lp).balance_entries
        )
        for delta in settlement.lp_deltas:
            if delta.delta_add > 0:
                assert (
                    evaluated.lp_balances.get_last_mint_timestamp(
                        delta.pubkey,
                        delta.pool_id,
                    )
                    == 700
                )

        # Evaluation owns a successor and cannot mutate or replace its exact pre-state.
        assert exact_balances == snapshot_balance_table(balances)
        assert exact_pools == snapshot_pool_map(pools)
        assert exact_lp_balances == snapshot_lp_table(lp_balances)


def test_exact_committed_evaluator_rejects_without_candidate_and_preserves_reason() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    tampered = replace(settlement, balance_deltas=[])
    legacy = validate_settlement_strong(
        settlement=tampered,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool.pool_id: pool},
        pre_lp_balances=LPTable(),
    )
    exact_balances = snapshot_balance_table(balances)
    exact_pools = snapshot_pool_map({pool.pool_id: pool})
    exact_lp_balances = snapshot_lp_table(LPTable())
    owned_settlement = snapshot_settlement(tampered)
    owned_intents = admit_intent_batch([intent])

    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=exact_balances,
        pre_pools=exact_pools,
        pre_lp_balances=exact_lp_balances,
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert type(evaluated) is StrongSettlementRejectV1
    assert evaluated.reason == "balance_deltas mismatch vs replay"
    assert legacy == (False, evaluated.reason)
    assert not hasattr(evaluated, "balances")
    assert not hasattr(evaluated, "pools")
    assert not hasattr(evaluated, "lp_balances")
    assert validate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=exact_balances,
        pre_pools=exact_pools,
        pre_lp_balances=exact_lp_balances,
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    ) == (False, evaluated.reason)


def test_exact_committed_evaluator_rejects_exact_batch_construction_fault(
    monkeypatch,
) -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()

    def _fail_batch_construction(**_kwargs: object) -> None:
        raise ValueError("synthetic candidate failure")

    monkeypatch.setattr(
        strong_validator,
        "SpotDeltaBatchV1",
        _fail_batch_construction,
    )
    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool.pool_id: pool}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert evaluated == StrongSettlementRejectV1(
        "exact spot command construction failed after replay: "
        "ValueError: synthetic candidate failure"
    )
    assert not hasattr(evaluated, "balances")


def test_exact_committed_evaluator_applies_lp_age_to_the_emitted_candidate() -> None:
    (
        pk,
        _asset0,
        _asset1,
        pool_id,
        pool,
        balances,
        lp_balances,
        intent,
        settlement,
    ) = _setup_remove_liquidity_context()
    lp_balances.set_last_mint_timestamp(pk, pool_id, 695)
    exact_balances = snapshot_balance_table(balances)
    exact_pools = snapshot_pool_map({pool_id: pool})
    exact_lp_balances = snapshot_lp_table(lp_balances)
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch([intent])

    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=exact_balances,
        pre_pools=exact_pools,
        pre_lp_balances=exact_lp_balances,
        now=700,
        min_lp_position_age_seconds=6,
        lp_duration_policy=None,
    )

    assert type(evaluated) is StrongSettlementRejectV1
    assert evaluated.reason == (
        "exact spot candidate rejected: position_locked:events.0.last_mint_timestamp"
    )
    assert not hasattr(evaluated, "lp_balances")
    assert exact_lp_balances.get(pk, pool_id) == lp_balances.get(pk, pool_id)
    assert exact_pools[pool_id].lp_supply == pool.lp_supply


def test_exact_committed_validator_rejects_legacy_state_values() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    runtime_exact_validator = cast(Any, validate_settlement_strong_committed_v1)
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch([intent])

    ok, error = runtime_exact_validator(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=balances,
        pre_pools={pool.pool_id: pool},
        pre_lp_balances=LPTable(),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert ok is False
    assert (
        error
        == "strong validator crashed: TypeError: replay balances must be exact committed state"
    )


def test_exact_committed_validator_rejects_legacy_command_graph() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    runtime_exact_evaluator = cast(Any, evaluate_settlement_strong_committed_v1)

    evaluated = runtime_exact_evaluator(
        settlement=settlement,
        intents=[intent],
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool.pool_id: pool}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert evaluated == StrongSettlementRejectV1(
        "exact settlement command rejected: settlement requires OwnedSettlementV1"
    )
    assert not hasattr(evaluated, "balances")


def test_exact_committed_evaluator_rejects_non_owned_intent_containers() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    runtime_exact_evaluator = cast(Any, evaluate_settlement_strong_committed_v1)
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch([intent])
    cases = (
        (list(owned_intents), "intents require an exact owned tuple"),
        ((intent,), "intent requires OwnedIntentV1"),
    )

    for malformed_intents, expected_reason in cases:
        evaluated = runtime_exact_evaluator(
            settlement=owned_settlement,
            intents=malformed_intents,
            pre_balances=snapshot_balance_table(balances),
            pre_pools=snapshot_pool_map({pool.pool_id: pool}),
            pre_lp_balances=snapshot_lp_table(LPTable()),
            now=700,
            min_lp_position_age_seconds=0,
            lp_duration_policy=None,
        )

        assert evaluated == StrongSettlementRejectV1(
            f"exact settlement command rejected: {expected_reason}"
        )
        assert not hasattr(evaluated, "balances")


def test_exact_committed_evaluator_uses_only_the_owned_command_snapshot() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch([intent])

    intent.fields["amount_in"] = 2_000
    settlement.balance_deltas.clear()
    settlement.reserve_deltas.clear()

    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool.pool_id: pool}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert type(evaluated) is StrongSettlementStateCandidateV1


def test_exact_committed_evaluator_never_invokes_legacy_command_behavior(
    monkeypatch,
) -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch([intent])

    def _legacy_escape(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("exact replay invoked a legacy command path")

    monkeypatch.setattr(Intent, "get_field", _legacy_escape)
    monkeypatch.setattr(
        strong_validator,
        "evaluate_settlement_strong_legacy_committed_for_differential_v1",
        _legacy_escape,
    )

    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool.pool_id: pool}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert type(evaluated) is StrongSettlementStateCandidateV1


def test_exact_committed_evaluator_revalidates_a_corrupted_owned_command() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch([intent])
    object.__setattr__(owned_settlement, "batch_ref", 7)

    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool.pool_id: pool}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert type(evaluated) is StrongSettlementRejectV1
    assert evaluated.reason.startswith("exact settlement command rejected: wrong_exact_type:")
    assert not hasattr(evaluated, "balances")


def test_exact_committed_evaluator_revalidates_a_corrupted_owned_intent() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    owned_settlement = snapshot_settlement(settlement)
    owned_intents = admit_intent_batch([intent])
    object.__setattr__(owned_intents[0], "deadline", "corrupted")

    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=owned_intents,
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool.pool_id: pool}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert type(evaluated) is StrongSettlementRejectV1
    assert evaluated.reason.startswith("exact settlement command rejected: wrong_exact_type:")
    assert not hasattr(evaluated, "balances")


def test_exact_committed_evaluator_rejects_corrupted_owned_invariants() -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()
    owned_settlement = snapshot_settlement(settlement)
    included = owned_settlement.included_intents[0]
    object.__setattr__(owned_settlement, "included_intents", (included, included))

    evaluated = evaluate_settlement_strong_committed_v1(
        settlement=owned_settlement,
        intents=admit_intent_batch([intent]),
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool.pool_id: pool}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
    )

    assert type(evaluated) is StrongSettlementRejectV1
    assert evaluated.reason.startswith("exact settlement command rejected:")
    assert not hasattr(evaluated, "balances")


def test_legacy_boolean_facade_never_constructs_the_duration_candidate(monkeypatch) -> None:
    *_prefix, pool, balances, intent, settlement = _setup_swap_context()

    def forbidden_candidate_builder(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("legacy validation crossed the exact candidate boundary")

    monkeypatch.setattr(
        strong_validator,
        "_build_exact_spot_batch_v1",
        forbidden_candidate_builder,
    )

    assert validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool.pool_id: pool},
        pre_lp_balances=LPTable(),
    ) == (True, None)


def test_quote_binding_error_without_context_returns_reason() -> None:
    assert strong_validator._quote_binding_error("plain reason") == "plain reason"


def test_validate_settlement_strong_fail_closed_on_internal_crash_with_detail(monkeypatch) -> None:
    def _boom(**_kwargs: object) -> tuple[bool, str | None]:
        raise RuntimeError("bad\nnews")

    monkeypatch.setattr(strong_validator, "_validate_settlement_strong_impl", _boom)
    ok, err = strong_validator.validate_settlement_strong(
        settlement=Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        ),
        intents=[],
        pre_balances=BalanceTable(),
        pre_pools={},
        pre_lp_balances=LPTable(),
    )
    assert ok is False
    assert err == "strong validator crashed: RuntimeError: bad news"


def test_validate_settlement_strong_fail_closed_on_internal_crash_without_detail(
    monkeypatch,
) -> None:
    def _boom(**_kwargs: object) -> tuple[bool, str | None]:
        raise RuntimeError()

    monkeypatch.setattr(strong_validator, "_validate_settlement_strong_impl", _boom)
    ok, err = strong_validator.validate_settlement_strong(
        settlement=Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        ),
        intents=[],
        pre_balances=BalanceTable(),
        pre_pools={},
        pre_lp_balances=LPTable(),
    )
    assert ok is False
    assert err == "strong validator crashed: RuntimeError"


def test_validate_settlement_strong_truncates_long_internal_crash_detail(monkeypatch) -> None:
    def _boom(**_kwargs: object) -> tuple[bool, str | None]:
        raise RuntimeError("x" * 400)

    monkeypatch.setattr(strong_validator, "_validate_settlement_strong_impl", _boom)
    ok, err = strong_validator.validate_settlement_strong(
        settlement=Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[],
            fills=[],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        ),
        intents=[],
        pre_balances=BalanceTable(),
        pre_pools={},
        pre_lp_balances=LPTable(),
    )
    assert ok is False
    assert err is not None
    assert err.startswith("strong validator crashed: RuntimeError: ")
    assert len(err) == len("strong validator crashed: RuntimeError: ") + 200


def test_aggregate_helpers_drop_zero_entries() -> None:
    aggregated_balance = strong_validator._aggregate_balance_deltas(
        [
            BalanceDelta(pubkey="0x" + "11" * 48, asset="0x" + "01" * 32, delta_add=0, delta_sub=0),
            BalanceDelta(pubkey="0x" + "11" * 48, asset="0x" + "02" * 32, delta_add=5, delta_sub=0),
        ]
    )
    assert aggregated_balance == [
        BalanceDelta(pubkey="0x" + "11" * 48, asset="0x" + "02" * 32, delta_add=5, delta_sub=0)
    ]

    aggregated_reserve = strong_validator._aggregate_reserve_deltas(
        [
            ReserveDelta(pool_id=_iid(1), asset="0x" + "01" * 32, delta_add=0, delta_sub=0),
            ReserveDelta(pool_id=_iid(1), asset="0x" + "02" * 32, delta_add=0, delta_sub=7),
        ]
    )
    assert aggregated_reserve == [
        ReserveDelta(pool_id=_iid(1), asset="0x" + "02" * 32, delta_add=0, delta_sub=7)
    ]

    aggregated_lp = strong_validator._aggregate_lp_deltas(
        [
            LPDelta(pubkey="0x" + "11" * 48, pool_id=_iid(2), delta_add=0, delta_sub=0),
            LPDelta(pubkey="0x" + "22" * 48, pool_id=_iid(2), delta_add=9, delta_sub=0),
            LPDelta(pubkey="0x" + "33" * 48, pool_id=_iid(2), delta_add=4, delta_sub=0),
            LPDelta(pubkey="0x" + "33" * 48, pool_id=_iid(2), delta_add=0, delta_sub=3),
        ]
    )
    assert aggregated_lp == [
        LPDelta(pubkey="0x" + "22" * 48, pool_id=_iid(2), delta_add=9, delta_sub=0),
        LPDelta(pubkey="0x" + "33" * 48, pool_id=_iid(2), delta_add=4, delta_sub=3),
    ]


def test_check_canonical_deltas_rejects_invalid_balance_scalar_fields() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[BalanceDelta(pubkey=_iid(1), asset=_iid(2), delta_add=False, delta_sub=1)],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "balance_deltas contains invalid delta_add"

    settlement.balance_deltas = [
        BalanceDelta(pubkey=_iid(1), asset=_iid(2), delta_add=1, delta_sub=False)
    ]
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "balance_deltas contains invalid delta_sub"


def test_check_canonical_deltas_rejects_invalid_reserve_scalar_fields() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[ReserveDelta(pool_id=_iid(1), asset=_iid(2), delta_add=False, delta_sub=1)],
        lp_deltas=[],
        events=None,
    )
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "reserve_deltas contains invalid delta_add"

    settlement.reserve_deltas = [
        ReserveDelta(pool_id=_iid(1), asset=_iid(2), delta_add=1, delta_sub=False)
    ]
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "reserve_deltas contains invalid delta_sub"


def test_check_canonical_deltas_rejects_invalid_lp_scalar_fields() -> None:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[LPDelta(pubkey=_iid(1), pool_id=_iid(2), delta_add=False, delta_sub=1)],
        events=None,
    )
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "lp_deltas contains invalid delta_add"

    settlement.lp_deltas = [LPDelta(pubkey=_iid(1), pool_id=_iid(2), delta_add=1, delta_sub=False)]
    ok, err = strong_validator._check_canonical_deltas(settlement)
    assert ok is False
    assert err == "lp_deltas contains invalid delta_sub"


def test_strong_validator_allows_reject_without_fill_details() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, _settlement = _setup_swap_context()
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.REJECT)],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True
    assert err is None


def test_strong_validator_rejects_unsupported_validation_mode() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="bad_mode",
    )
    assert ok is False
    assert err == "unsupported validation mode: 'bad_mode'"


def test_strong_validator_rejects_duplicate_input_intent_ids() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent, intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "duplicate intent_id in input intents"


def test_strong_validator_rejects_included_intents_mismatch() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.included_intents = [(_iid(999), FillAction.REJECT)]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert (
        err
        == f"settlement included_intents mismatch: missing=['{intent.intent_id}'] extra=['{_iid(999)}']"
    )


def test_strong_validator_rejects_duplicate_included_intents() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.included_intents = [
        (intent.intent_id, FillAction.FILL),
        (intent.intent_id, FillAction.REJECT),
    ]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "settlement included_intents contains duplicate intent_id entries"


def test_strong_validator_rejects_duplicate_fill_ids() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills = [settlement.fills[0], settlement.fills[0]]
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "settlement fills contains duplicate intent_id entries"


def test_strong_validator_rejects_extra_fill_id() -> None:
    _pk, asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills.append(
        Fill(
            intent_id=_iid(998),
            action=FillAction.REJECT,
            reason="UNSUPPORTED",
            amount_in_filled=0,
            amount_out_filled=0,
            fee_paid=0,
        )
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    del asset0
    assert ok is False
    assert err == f"settlement fills contains intent_ids not in input intents: ['{_iid(998)}']"


def test_strong_validator_rejects_missing_fill_for_filled_intent() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills = []
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing Fill for filled intent_id: {intent.intent_id}"


def test_strong_validator_rejects_fill_action_mismatch() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.fills[0].action = FillAction.REJECT
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert (
        err
        == f"Fill.action mismatch for intent_id={intent.intent_id}: FillAction.REJECT != FillAction.FILL"
    )


def test_strong_validator_rejects_invalid_recipient() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "recipient": ""},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid recipient for intent_id={intent.intent_id}"


def test_strong_validator_rejects_invalid_quote_receipt_hash() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "quote_receipt_hash": ""},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "invalid quote_receipt_hash" in err


def test_strong_validator_rejects_missing_quote_pool_fingerprint() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "quote_pool_fingerprint": ""},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "missing quote_pool_fingerprint" in err


def test_strong_validator_rejects_missing_pool_id() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    fields = dict(intent.fields or {})
    del fields["pool_id"]
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields=fields,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing pool_id for intent_id={intent.intent_id}"


def test_strong_validator_rejects_pool_not_found() -> None:
    _pk, _asset0, _asset1, _pool_id, _pool, balances, intent, settlement = _setup_swap_context()
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not found for intent_id={intent.intent_id}: {intent.get_field('pool_id')}"


def test_strong_validator_rejects_invalid_asset_ids() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "asset_out": 7},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid asset_in/out for intent_id={intent.intent_id}"


def test_strong_validator_rejects_create_pool_duplicate_existing_pool_id() -> None:
    pk, asset0, asset1, balances, intent, settlement = _setup_create_pool_context()
    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL duplicates existing pool_id={pool_id}"


def test_strong_validator_rejects_create_pool_fill_amount0_mismatch() -> None:
    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    settlement.fills[0].amount0_used += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL fill.amount0_used mismatch for intent_id={intent.intent_id}"


def test_strong_validator_rejects_create_pool_reserve_only_donation_witness() -> None:
    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    settlement.reserve_deltas[0].delta_add += 1_000_000
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas mismatch vs replay"


def test_strong_validator_rejects_create_pool_apply_error_for_insufficient_balance() -> None:
    _pk, asset0, asset1, _balances, intent, settlement = _setup_create_pool_context()
    balances = BalanceTable()
    balances.set(intent.sender_pubkey, asset0, 1)
    balances.set(intent.sender_pubkey, asset1, 1)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"CREATE_POOL balance/LP apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_swap_on_inactive_pool() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    inactive_pool = replace(pool, status=PoolStatus.FROZEN)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: inactive_pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not active for intent_id={intent.intent_id}: {PoolStatus.FROZEN}"


def test_strong_validator_rejects_swap_asset_mismatch() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    malformed_intent = Intent(
        module=intent.module,
        version=intent.version,
        kind=intent.kind,
        intent_id=intent.intent_id,
        sender_pubkey=intent.sender_pubkey,
        deadline=intent.deadline,
        fields={**(intent.fields or {}), "asset_out": intent.get_field("asset_in")},
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap asset mismatch for intent_id={intent.intent_id}"


def test_strong_validator_rejects_add_liquidity_on_inactive_pool() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(902),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: replace(pool, status=PoolStatus.FROZEN)},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not active for intent_id={intent.intent_id}: {PoolStatus.FROZEN}"


def test_strong_validator_rejects_remove_liquidity_on_inactive_pool() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(903),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": 1_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: replace(pool, status=PoolStatus.FROZEN)},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"pool not active for intent_id={intent.intent_id}: {PoolStatus.FROZEN}"


def test_legacy_validate_allows_k_decrease_but_strong_rejects() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
        },
    )

    # Malicious settlement: drains too much output from the pool (k decreases),
    # but keeps reserves non-negative and passes pure conservation checks.
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                amount_in_filled=100,
                amount_out_filled=200,  # impossible under CPMM reserves=(1000,1000) with fee_bps=30
                fee_paid=1,  # any non-negative value; legacy doesn't check
                reserve_in_before=1_000,
                reserve_out_before=1_000,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk, asset=asset1, delta_add=200, delta_sub=0),
        ],
        reserve_deltas=[
            ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=100, delta_sub=0),
            ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=0, delta_sub=200),
        ],
        lp_deltas=[],
        events=None,
    )

    ok_legacy, err_legacy = validate_settlement(
        settlement=settlement,
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
    )
    assert ok_legacy is True, err_legacy

    ok_strong, err_strong = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_strong is False
    assert err_strong is not None


def test_dex_step_preserves_created_pool_curve_config() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, expected_pool, _lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
        curve_tag="CUBIC_SUM_V1",
        curve_params={"p": 2, "q": 1},
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    state = DexState(balances=balances, pools={}, lp_balances=LPTable())
    config = DexConfig()

    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.CREATE_POOL,
            intent_id=_iid(2),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "asset0": asset0,
                "asset1": asset1,
                "fee_bps": 30,
                "amount0": 2_000_000,
                "amount1": 2_000_000,
                "curve_tag": "CUBIC_SUM_V1",
                "curve_params": {"p": 2, "q": 1},
                "nonce": 1,
            },
        )
    ]

    res = dex_step(config, state, intents)
    assert res.ok, res.error
    assert res.state is not None
    assert pool_id in res.state.pools

    got_pool = res.state.pools[pool_id]
    assert got_pool.curve_tag == expected_pool.curve_tag
    assert got_pool.curve_params == expected_pool.curve_params


def test_strong_proof_carrying_requires_swap_reserve_witnesses() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(3),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 10,
            "max_amount_in": 1_000,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    assert len(settlement.fills) == 1

    fill = settlement.fills[0]
    assert fill.reserve_in_before is not None
    assert fill.reserve_out_before is not None
    witness_in = int(fill.reserve_in_before)
    witness_out = int(fill.reserve_out_before)

    ok_replay, err_replay = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_replay is True, err_replay

    # BVA over witness presence/mismatch:
    # - missing witness: proof-carrying must reject
    # - correct witness: proof-carrying must accept
    # - off-by-one witness: proof-carrying must reject

    fill.reserve_in_before = None
    fill.reserve_out_before = None
    ok_pc, err_pc = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc is False
    assert err_pc is not None

    fill.reserve_in_before = witness_in
    fill.reserve_out_before = witness_out
    ok_pc2, err_pc2 = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc2 is True, err_pc2

    fill.reserve_in_before = witness_in + 1
    fill.reserve_out_before = witness_out
    ok_pc3, err_pc3 = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok_pc3 is False
    assert err_pc3 is not None


def test_strong_validator_rejects_nonconserving_cow_netted_settlement() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk0, asset0, 10_000)
    balances.set(pk0, asset1, 0)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(10),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "recipient": pk1,
        },
    )

    # Malicious settlement: marks a swap as COW_NETTED but does not include any
    # counterparty transfer. This would violate asset conservation if accepted.
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=200,  # created-from-nothing if no offsetting debit exists
                fee_paid=0,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=200, delta_sub=0),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok_strong, err_strong = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_strong is False
    assert err_strong is not None


def test_strong_validator_accepts_exact_reciprocal_cow_netted_pair() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk0, asset0, 1_000)
    balances.set(pk0, asset1, 0)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 1_000)
    intent0 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(920),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 50,
        },
    )
    intent1 = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(921),
        sender_pubkey=pk1,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset1,
            "asset_out": asset0,
            "amount_in": 50,
            "min_amount_out": 100,
        },
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[
            (intent0.intent_id, FillAction.FILL),
            (intent1.intent_id, FillAction.FILL),
        ],
        fills=[
            Fill(
                intent_id=intent0.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=50,
                fee_paid=0,
            ),
            Fill(
                intent_id=intent1.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=50,
                amount_out_filled=100,
                fee_paid=0,
            ),
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk0, asset=asset1, delta_add=50, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset0, delta_add=100, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=0, delta_sub=50),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent0, intent1],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )

    assert ok is True, err
    assert err is None

    exact = validate_settlement_strong_committed_v1(
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent0, intent1]),
        pre_balances=snapshot_balance_table(balances),
        pre_pools=snapshot_pool_map({pool_id: pool_state}),
        pre_lp_balances=snapshot_lp_table(LPTable()),
        now=700,
        min_lp_position_age_seconds=0,
        lp_duration_policy=None,
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert exact == (True, None)


def test_strong_validator_accepts_multiple_disjoint_cow_netted_pairs() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    pk2 = "0x" + "33" * 48
    pk3 = "0x" + "44" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk0, asset0, 1_000)
    balances.set(pk1, asset1, 1_000)
    balances.set(pk2, asset0, 1_000)
    balances.set(pk3, asset1, 1_000)

    rows = [
        (_iid(922), pk0, asset0, asset1, 100, 50),
        (_iid(923), pk1, asset1, asset0, 50, 100),
        (_iid(924), pk2, asset0, asset1, 17, 23),
        (_iid(925), pk3, asset1, asset0, 23, 17),
    ]
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=intent_id,
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": amount_out,
            },
        )
        for intent_id, sender, asset_in, asset_out, amount_in, amount_out in rows
    ]
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL) for intent in intents],
        fills=[
            Fill(
                intent_id=intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=amount_in,
                amount_out_filled=amount_out,
                fee_paid=0,
            )
            for intent, (
                _intent_id,
                _sender,
                _asset_in,
                _asset_out,
                amount_in,
                amount_out,
            ) in zip(intents, rows, strict=True)
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk0, asset=asset1, delta_add=50, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset0, delta_add=100, delta_sub=0),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=0, delta_sub=50),
            BalanceDelta(pubkey=pk2, asset=asset0, delta_add=0, delta_sub=17),
            BalanceDelta(pubkey=pk2, asset=asset1, delta_add=23, delta_sub=0),
            BalanceDelta(pubkey=pk3, asset=asset0, delta_add=17, delta_sub=0),
            BalanceDelta(pubkey=pk3, asset=asset1, delta_add=0, delta_sub=23),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=intents,
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )

    assert ok is True, err
    assert err is None


def test_strong_validator_rejects_ambiguous_and_nonreciprocal_cow_pairs() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    pk2 = "0x" + "33" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    other_pool_id = compute_pool_id(asset0, asset1, 31, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    other_pool_state = replace(pool_state, pool_id=other_pool_id, fee_bps=31)
    balances = BalanceTable()
    balances.set(pk0, asset0, 1_000)
    balances.set(pk1, asset1, 1_000)
    balances.set(pk2, asset1, 1_000)

    def _intent(
        n: int,
        sender: str,
        pool: str,
        asset_in: str,
        asset_out: str,
        amount_in: int,
        min_out: int,
    ) -> Intent:
        return Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(n),
            sender_pubkey=sender,
            deadline=9999999999,
            fields={
                "pool_id": pool,
                "asset_in": asset_in,
                "asset_out": asset_out,
                "amount_in": amount_in,
                "min_amount_out": min_out,
            },
        )

    def _settlement(rows: list[tuple[Intent, int, int]]) -> Settlement:
        return Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[
                (intent.intent_id, FillAction.FILL) for intent, _amount_in, _amount_out in rows
            ],
            fills=[
                Fill(
                    intent_id=intent.intent_id,
                    action=FillAction.FILL,
                    reason="COW_NETTED",
                    amount_in_filled=amount_in,
                    amount_out_filled=amount_out,
                    fee_paid=0,
                )
                for intent, amount_in, amount_out in rows
            ],
            balance_deltas=[],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        )

    same_direction = [
        (_intent(930, pk0, pool_id, asset0, asset1, 100, 50), 100, 50),
        (_intent(931, pk1, pool_id, asset0, asset1, 50, 100), 50, 100),
    ]
    ok, err = _assert_exact_legacy_validation_parity(
        settlement=_settlement(same_direction),
        intents=[row[0] for row in same_direction],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "exactly one reciprocal counterparty" in err

    cross_pool = [
        (_intent(932, pk0, pool_id, asset0, asset1, 100, 50), 100, 50),
        (_intent(933, pk1, other_pool_id, asset1, asset0, 50, 100), 50, 100),
    ]
    ok, err = _assert_exact_legacy_validation_parity(
        settlement=_settlement(cross_pool),
        intents=[row[0] for row in cross_pool],
        balances=balances,
        pools={pool_id: pool_state, other_pool_id: other_pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "exactly one reciprocal counterparty" in err

    mismatched = [
        (_intent(934, pk0, pool_id, asset0, asset1, 100, 40), 100, 49),
        (_intent(935, pk1, pool_id, asset1, asset0, 50, 100), 50, 100),
    ]
    ok, err = _assert_exact_legacy_validation_parity(
        settlement=_settlement(mismatched),
        intents=[row[0] for row in mismatched],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "exactly one reciprocal counterparty" in err

    ambiguous = [
        (_intent(936, pk0, pool_id, asset0, asset1, 100, 50), 100, 50),
        (_intent(937, pk1, pool_id, asset1, asset0, 50, 100), 50, 100),
        (_intent(938, pk2, pool_id, asset1, asset0, 50, 100), 50, 100),
    ]
    ok, err = _assert_exact_legacy_validation_parity(
        settlement=_settlement(ambiguous),
        intents=[row[0] for row in ambiguous],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None and "matches=[" in err


def test_strong_validator_rejects_stale_quote_receipt_pool_fingerprint() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    quoted_pool = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    drifted_pool = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_001,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(20),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_pool_fingerprint": pool_state_fingerprint(quoted_pool),
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: drifted_pool},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: drifted_pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_snapshot_bound_quote_bindings=True,
    )
    assert ok is False
    assert err is not None
    assert "quote receipt pool snapshot mismatch" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert f"quote_pool_fingerprint='{pool_state_fingerprint(quoted_pool)}'" in err
    assert "actual_pool_fingerprint=" in err


def test_strong_validator_rejects_quote_receipt_binding_on_non_swap_intent() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(21),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
            "quote_receipt_hash": "0xdeadbeef",
            "quote_pool_fingerprint": "not-applicable",
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt binding only supported for swap intents" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert "intent_kind='CREATE_POOL'" in err


def test_strong_validator_rejects_quote_receipt_leg_index_without_hash() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(22),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_receipt_leg_index": 0,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt transport metadata requires validated engine witness" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert (
        "strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation"
        in err
    )


def test_strong_validator_rejects_invalid_quote_receipt_leg_index() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(23),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_receipt_hash": "0xdeadbeef",
            "quote_pool_fingerprint": pool_state_fingerprint(pool_state),
            "quote_receipt_leg_index": -1,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "invalid quote_receipt_leg_index" in err
    assert f"intent_id='{intent.intent_id}'" in err


def test_strong_validator_rejects_unsanitized_quote_receipt_hash_without_engine_witness() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000)
    balances.set(pk, asset1, 0)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(24),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "quote_receipt_hash": "0xdeadbeef",
            "quote_pool_fingerprint": pool_state_fingerprint(pool_state),
            "quote_receipt_leg_index": 0,
        },
    )

    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool_state},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt transport metadata requires validated engine witness" in err
    assert f"intent_id='{intent.intent_id}'" in err
    assert (
        "strip quote_receipt_hash and quote_receipt_leg_index after engine witness validation"
        in err
    )


def test_strong_validator_rejects_duplicate_balance_delta_keys() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(30),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1000,
            "min_amount_out": 1,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    first_delta = settlement.balance_deltas[0]
    settlement.balance_deltas = [
        BalanceDelta(
            pubkey=first_delta.pubkey,
            asset=first_delta.asset,
            delta_add=first_delta.delta_add,
            delta_sub=400,
        ),
        BalanceDelta(
            pubkey=first_delta.pubkey,
            asset=first_delta.asset,
            delta_add=0,
            delta_sub=first_delta.delta_sub - 400,
        ),
        *settlement.balance_deltas[1:],
    ]

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas contains duplicate keys"


def test_strong_validator_rejects_zero_delta_entry() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    pool_id, pool, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=pk,
    )

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(31),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1000,
            "min_amount_out": 1,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    settlement.balance_deltas.append(
        BalanceDelta(pubkey=pk, asset=asset0, delta_add=0, delta_sub=0)
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas contains a zero entry"


def test_strong_validator_rejects_stringly_typed_create_pool_amounts() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    balances = BalanceTable()
    balances.set(pk, asset0, 10_000_000)
    balances.set(pk, asset1, 10_000_000)

    valid_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(40),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": 2_000_000,
            "amount1": 2_000_000,
        },
    )

    settlement = compute_settlement([valid_intent], {}, balances, LPTable())
    ok_valid, err_valid = validate_settlement_strong(
        settlement=settlement,
        intents=[valid_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok_valid is True, err_valid

    malformed_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=valid_intent.intent_id,
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 30,
            "amount0": "2000000",
            "amount1": 2_000_000,
        },
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL amount0 for intent_id={valid_intent.intent_id}"


def test_strong_validator_rejects_stringly_typed_add_liquidity_amounts() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()

    valid_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(41),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([valid_intent], {pool_id: pool}, balances, lp_balances)
    ok_valid, err_valid = validate_settlement_strong(
        settlement=settlement,
        intents=[valid_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok_valid is True, err_valid

    malformed_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=valid_intent.intent_id,
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": "100000",
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount0_desired for intent_id={valid_intent.intent_id}"


def test_strong_validator_rejects_stringly_typed_remove_liquidity_amounts() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    del asset0
    del asset1

    valid_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(42),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": 1_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([valid_intent], {pool_id: pool}, balances, lp_balances)
    ok_valid, err_valid = validate_settlement_strong(
        settlement=settlement,
        intents=[valid_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok_valid is True, err_valid

    malformed_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=valid_intent.intent_id,
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "lp_amount": "1000",
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[malformed_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid lp_amount for intent_id={valid_intent.intent_id}"


def test_strong_validator_rejects_duplicate_reserve_delta_keys() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    del asset0
    del asset1

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(43),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    first_delta = settlement.reserve_deltas[0]
    settlement.reserve_deltas = [
        ReserveDelta(
            pool_id=first_delta.pool_id,
            asset=first_delta.asset,
            delta_add=first_delta.delta_add // 2,
            delta_sub=0,
        ),
        ReserveDelta(
            pool_id=first_delta.pool_id,
            asset=first_delta.asset,
            delta_add=first_delta.delta_add - (first_delta.delta_add // 2),
            delta_sub=0,
        ),
        *settlement.reserve_deltas[1:],
    ]

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas contains duplicate keys"


def test_strong_validator_rejects_duplicate_lp_delta_keys() -> None:
    pk, asset0, asset1, pool_id, pool, balances, lp_balances = _setup_liquidity_context()
    del asset0
    del asset1

    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(44),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )

    settlement = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    first_delta = settlement.lp_deltas[0]
    settlement.lp_deltas = [
        LPDelta(
            pubkey=first_delta.pubkey,
            pool_id=first_delta.pool_id,
            delta_add=first_delta.delta_add // 2,
            delta_sub=0,
        ),
        LPDelta(
            pubkey=first_delta.pubkey,
            pool_id=first_delta.pool_id,
            delta_add=first_delta.delta_add - (first_delta.delta_add // 2),
            delta_sub=0,
        ),
        *settlement.lp_deltas[1:],
    ]

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas contains duplicate keys"


def test_strong_validator_accepts_reverse_direction_swap_exact_in() -> None:
    pk, asset0, asset1, pool_id, pool, balances, _intent, _settlement = _setup_swap_context()
    reverse_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(908),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset1,
            "asset_out": asset0,
            "amount_in": 1_000,
            "min_amount_out": 1,
        },
    )
    settlement = compute_settlement([reverse_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[reverse_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True, err


def test_strong_validator_accepts_reverse_direction_swap_exact_out() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = (
        _setup_swap_exact_out_context(reverse=True)
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is True, err


def test_strong_validator_rejects_exact_in_field_kernel_and_apply_failures(monkeypatch) -> None:
    _pk, asset0, asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()

    invalid_amount_intent = replace(intent, fields={**intent.fields, "amount_in": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount_in for intent_id={intent.intent_id}"

    invalid_min_out_intent = replace(intent, fields={**intent.fields, "min_amount_out": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_min_out_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid min_amount_out for intent_id={intent.intent_id}"

    amount_in_mismatch = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    amount_in_mismatch.fills[0].amount_in_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_in_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_in_filled mismatch for intent_id={intent.intent_id}"

    def _boom_exact_in(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("boom")

    monkeypatch.setattr(
        strong_validator,
        "swap_exact_in_for_committed_pool_v1",
        _boom_exact_in,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap_exact_in kernel error for intent_id={intent.intent_id}:")
    monkeypatch.undo()

    amount_out_mismatch = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    amount_out_mismatch.fills[0].amount_out_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_out_filled mismatch for intent_id={intent.intent_id}"

    slippage_intent = replace(
        intent,
        fields={
            **intent.fields,
            "min_amount_out": int(settlement.fills[0].amount_out_filled or 0) + 1,
        },
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[slippage_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap slippage for intent_id={intent.intent_id}"

    fee_mismatch = compute_settlement([intent], {pool_id: pool}, balances, LPTable())
    fee_mismatch.fills[0].fee_paid += 1
    ok, err = validate_settlement_strong(
        settlement=fee_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap fee_paid mismatch for intent_id={intent.intent_id}"

    low_balances = BalanceTable()
    low_balances.set(intent.sender_pubkey, asset0, 1)
    low_balances.set(intent.sender_pubkey, asset1, 0)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_exact_out_field_kernel_and_apply_failures(monkeypatch) -> None:
    _pk, asset0, asset1, pool_id, pool, balances, intent, settlement = (
        _setup_swap_exact_out_context()
    )

    invalid_amount_out_intent = replace(intent, fields={**intent.fields, "amount_out": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount_out_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount_out for intent_id={intent.intent_id}"

    invalid_max_in_intent = replace(intent, fields={**intent.fields, "max_amount_in": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_max_in_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid max_amount_in for intent_id={intent.intent_id}"

    amount_out_mismatch = compute_settlement(
        [intent], {pool_id: pool}, balances, LPTable(), swap_ordering="greedy_ab_refined"
    )
    amount_out_mismatch.fills[0].amount_out_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_out_filled mismatch for intent_id={intent.intent_id}"

    def _boom_exact_out(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise ValueError("boom")

    monkeypatch.setattr(
        strong_validator,
        "swap_exact_out_for_committed_pool_v1",
        _boom_exact_out,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap_exact_out kernel error for intent_id={intent.intent_id}:")
    monkeypatch.undo()

    amount_in_mismatch = compute_settlement(
        [intent], {pool_id: pool}, balances, LPTable(), swap_ordering="greedy_ab_refined"
    )
    amount_in_mismatch.fills[0].amount_in_filled += 1
    ok, err = validate_settlement_strong(
        settlement=amount_in_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap amount_in_filled mismatch for intent_id={intent.intent_id}"

    slippage_intent = replace(intent, fields={**intent.fields, "max_amount_in": 1})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[slippage_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap slippage for intent_id={intent.intent_id}"

    fee_mismatch = compute_settlement(
        [intent], {pool_id: pool}, balances, LPTable(), swap_ordering="greedy_ab_refined"
    )
    fee_mismatch.fills[0].fee_paid += 1
    ok, err = validate_settlement_strong(
        settlement=fee_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"swap fee_paid mismatch for intent_id={intent.intent_id}"

    low_balances = BalanceTable()
    low_balances.set(intent.sender_pubkey, asset0, 1)
    low_balances.set(intent.sender_pubkey, asset1, 0)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"swap apply error for intent_id={intent.intent_id}:")


def test_strong_validator_exact_out_protocol_fee_credit_feeds_later_replay() -> None:
    protocol_recipient = "0x" + "99" * 48
    pk, asset0, asset1, pool_id, pool, balances, _intent, _settlement = (
        _setup_swap_exact_out_context()
    )
    fee_source_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(9093),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 10_000,
            "max_amount_in": 1_000_000,
        },
    )
    fee_spend_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(9094),
        sender_pubkey=protocol_recipient,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 10,
            "min_amount_out": 0,
        },
    )
    settlement = compute_settlement(
        [fee_source_intent, fee_spend_intent],
        {pool_id: pool},
        balances,
        LPTable(),
        swap_ordering="limit_price",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )
    first_fill, second_fill = settlement.fills
    assert first_fill.protocol_fee_paid == 15
    assert second_fill.action == FillAction.FILL
    assert second_fill.amount_in_filled == 10
    assert balances.get(protocol_recipient, asset0) == 0

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[fee_source_intent, fee_spend_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )
    assert ok is True, err


def test_strong_validator_reverse_exact_out_protocol_fee_deltas_are_directional() -> None:
    protocol_recipient = "0x" + "99" * 48
    pk, asset0, asset1, pool_id, pool, balances, intent, _settlement = (
        _setup_swap_exact_out_context(reverse=True)
    )
    pool.reserve0 = 2_000_000
    pool.reserve1 = 3_000_000
    settlement = compute_settlement(
        [intent],
        {pool_id: pool},
        balances,
        LPTable(),
        swap_ordering="greedy_ab_refined",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )

    assert settlement.balance_deltas == [
        BalanceDelta(pubkey=pk, asset=asset0, delta_add=1_000, delta_sub=0),
        BalanceDelta(pubkey=pk, asset=asset1, delta_add=0, delta_sub=1_506),
        BalanceDelta(pubkey=protocol_recipient, asset=asset1, delta_add=2, delta_sub=0),
    ]
    assert settlement.reserve_deltas == [
        ReserveDelta(pool_id=pool_id, asset=asset0, delta_add=0, delta_sub=1_000),
        ReserveDelta(pool_id=pool_id, asset=asset1, delta_add=1_504, delta_sub=0),
    ]

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        protocol_fee_share_bps=5_000,
        protocol_fee_recipient_pubkey=protocol_recipient,
    )
    assert ok is True, err


def test_strong_validator_exact_out_apply_error_leaves_inputs_unchanged() -> None:
    _pk, asset0, asset1, pool_id, pool, _balances, intent, settlement = (
        _setup_swap_exact_out_context()
    )
    low_balances = BalanceTable()
    low_balances.set(intent.sender_pubkey, asset0, 1)
    low_balances.set(intent.sender_pubkey, asset1, 0)
    balance_snapshot = low_balances.get_all_balances()
    pool_snapshot = (pool.reserve0, pool.reserve1, pool.lp_supply)

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )

    assert ok is False
    assert err is not None
    assert err.startswith(f"swap apply error for intent_id={intent.intent_id}:")
    assert low_balances.get_all_balances() == balance_snapshot
    assert (pool.reserve0, pool.reserve1, pool.lp_supply) == pool_snapshot


def test_strong_proof_carrying_exact_out_uses_mutated_pool_for_later_fill() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, first_intent, _settlement = (
        _setup_swap_exact_out_context()
    )
    second_intent = replace(
        first_intent,
        intent_id=_iid(9092),
        fields={**first_intent.fields, "amount_out": 2_000, "max_amount_in": 20_000},
    )
    settlement = compute_settlement(
        [first_intent, second_intent],
        {pool_id: pool},
        balances,
        LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    first_fill, second_fill = settlement.fills
    assert first_fill.reserve_in_before == pool.reserve0
    assert first_fill.reserve_out_before == pool.reserve1
    assert second_fill.reserve_in_before == pool.reserve0 + int(first_fill.amount_in_filled or 0)
    assert second_fill.reserve_out_before == pool.reserve1 - int(first_fill.amount_out_filled or 0)

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[first_intent, second_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok is True, err

    second_fill.reserve_in_before = pool.reserve0
    second_fill.reserve_out_before = pool.reserve1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[first_intent, second_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_proof_carrying",
    )
    assert ok is False
    assert err == f"swap witness reserve mismatch for intent_id={second_intent.intent_id}"


def test_strong_validator_rejects_create_pool_field_and_fill_failures() -> None:
    _pk, asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()

    missing_field_intent = replace(
        intent, fields={k: v for k, v in intent.fields.items() if k != "amount1"}
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[missing_field_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing CREATE_POOL fields for intent_id={intent.intent_id}"

    invalid_asset_intent = replace(intent, fields={**intent.fields, "asset1": 7})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_asset_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL asset ids for intent_id={intent.intent_id}"

    invalid_fee_intent = replace(intent, fields={**intent.fields, "fee_bps": 10_001})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_fee_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL fee_bps for intent_id={intent.intent_id}"

    invalid_amount1_intent = replace(intent, fields={**intent.fields, "amount1": 0})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL amount1 for intent_id={intent.intent_id}"

    invalid_created_at_intent = replace(intent, fields={**intent.fields, "created_at": -1})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_created_at_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid CREATE_POOL created_at for intent_id={intent.intent_id}"

    computation_error_intent = replace(intent, fields={**intent.fields, "asset1": asset0})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[computation_error_intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"CREATE_POOL computation error for intent_id={intent.intent_id}:")

    amount1_mismatch = compute_settlement([intent], {}, balances, LPTable())
    amount1_mismatch.fills[0].amount1_used += 1
    ok, err = validate_settlement_strong(
        settlement=amount1_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL fill.amount1_used mismatch for intent_id={intent.intent_id}"

    lp_minted_mismatch = compute_settlement([intent], {}, balances, LPTable())
    lp_minted_mismatch.fills[0].lp_minted += 1
    ok, err = validate_settlement_strong(
        settlement=lp_minted_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"CREATE_POOL fill.lp_minted mismatch for intent_id={intent.intent_id}"


def test_strong_validator_rejects_add_liquidity_field_fill_and_apply_failures() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = (
        _setup_add_liquidity_context()
    )

    missing_field_intent = replace(
        intent, fields={k: v for k, v in intent.fields.items() if k != "amount1_desired"}
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[missing_field_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing ADD_LIQUIDITY fields for intent_id={intent.intent_id}"

    invalid_amount1_intent = replace(intent, fields={**intent.fields, "amount1_desired": 0})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount1_desired for intent_id={intent.intent_id}"

    invalid_amount0_min_intent = replace(intent, fields={**intent.fields, "amount0_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount0_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount0_min for intent_id={intent.intent_id}"

    invalid_amount1_min_intent = replace(intent, fields={**intent.fields, "amount1_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount1_min for intent_id={intent.intent_id}"

    computation_error_intent = replace(
        intent, fields={**intent.fields, "amount0_min": intent.get_field("amount0_desired") + 1}
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[computation_error_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"ADD_LIQUIDITY computation error for intent_id={intent.intent_id}:")

    amount0_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount0_mismatch.fills[0].amount0_used += 1
    ok, err = validate_settlement_strong(
        settlement=amount0_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"ADD_LIQUIDITY fill.amount0_used mismatch for intent_id={intent.intent_id}"

    amount1_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount1_mismatch.fills[0].amount1_used += 1
    ok, err = validate_settlement_strong(
        settlement=amount1_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"ADD_LIQUIDITY fill.amount1_used mismatch for intent_id={intent.intent_id}"

    lp_minted_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    lp_minted_mismatch.fills[0].lp_minted += 1
    ok, err = validate_settlement_strong(
        settlement=lp_minted_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"ADD_LIQUIDITY fill.lp_minted mismatch for intent_id={intent.intent_id}"

    low_balances = BalanceTable()
    low_balances.set(pk, pool.asset0, 1)
    low_balances.set(pk, pool.asset1, 1)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=low_balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"ADD_LIQUIDITY apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_remove_liquidity_field_fill_and_apply_failures() -> None:
    pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = (
        _setup_remove_liquidity_context()
    )

    missing_lp_amount_intent = replace(
        intent, fields={k: v for k, v in intent.fields.items() if k != "lp_amount"}
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[missing_lp_amount_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"missing REMOVE_LIQUIDITY lp_amount for intent_id={intent.intent_id}"

    invalid_amount0_min_intent = replace(intent, fields={**intent.fields, "amount0_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount0_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount0_min for intent_id={intent.intent_id}"

    invalid_amount1_min_intent = replace(intent, fields={**intent.fields, "amount1_min": False})
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_amount1_min_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"invalid amount1_min for intent_id={intent.intent_id}"

    computation_error_intent = replace(
        intent, fields={**intent.fields, "amount0_min": pool.reserve0}
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[computation_error_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"REMOVE_LIQUIDITY computation error for intent_id={intent.intent_id}:")

    lp_burned_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    lp_burned_mismatch.fills[0].lp_burned += 1
    ok, err = validate_settlement_strong(
        settlement=lp_burned_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"REMOVE_LIQUIDITY fill.lp_burned mismatch for intent_id={intent.intent_id}"

    amount0_out_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount0_out_mismatch.fills[0].amount0_out += 1
    ok, err = validate_settlement_strong(
        settlement=amount0_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"REMOVE_LIQUIDITY fill.amount0_out mismatch for intent_id={intent.intent_id}"

    amount1_out_mismatch = compute_settlement([intent], {pool_id: pool}, balances, lp_balances)
    amount1_out_mismatch.fills[0].amount1_out += 1
    ok, err = validate_settlement_strong(
        settlement=amount1_out_mismatch,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == f"REMOVE_LIQUIDITY fill.amount1_out mismatch for intent_id={intent.intent_id}"

    low_lp_balances = LPTable()
    low_lp_balances.set(pk, pool_id, 1)
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=low_lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"REMOVE_LIQUIDITY apply error for intent_id={intent.intent_id}:")


def test_strong_validator_rejects_replay_and_event_mismatches() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, intent, settlement = _setup_swap_context()
    settlement.balance_deltas[0].delta_sub += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "balance_deltas mismatch vs replay"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = (
        _setup_add_liquidity_context()
    )
    settlement.reserve_deltas[0].delta_add += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas mismatch vs replay"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = (
        _setup_add_liquidity_context()
    )
    settlement.lp_deltas[0].delta_add += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas mismatch vs replay"

    _pk, _asset0, _asset1, balances, intent, settlement = _setup_create_pool_context()
    settlement.events[0]["fee_bps"] += 1
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "events mismatch vs replay"


def test_check_canonical_deltas_rejects_unsorted_and_zero_reserve_lp_entries() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = (
        _setup_add_liquidity_context()
    )
    settlement.reserve_deltas = list(reversed(settlement.reserve_deltas))
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas not sorted canonically"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = (
        _setup_add_liquidity_context()
    )
    settlement.reserve_deltas.append(
        ReserveDelta(pool_id=pool_id, asset=pool.asset0, delta_add=0, delta_sub=0)
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "reserve_deltas contains a zero entry"

    _pk, _asset0, _asset1, pool_id, pool, balances, lp_balances, intent, settlement = (
        _setup_add_liquidity_context()
    )
    settlement.lp_deltas.append(
        LPDelta(pubkey=intent.sender_pubkey, pool_id=pool_id, delta_add=0, delta_sub=0)
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=lp_balances,
        mode="strong_replay",
    )
    assert ok is False
    assert err == "lp_deltas contains a zero entry"


def test_strong_validator_rejects_cow_netted_variants_and_legacy_failure() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    balances = BalanceTable()
    balances.set(pk0, asset0, 10_000)
    balances.set(pk0, asset1, 10_000)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 0)

    exact_out_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(909),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 100,
            "max_amount_in": 1_000,
            "recipient": pk1,
        },
    )
    exact_out_settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(exact_out_intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=exact_out_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=100,
                fee_paid=0,
            )
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = _assert_exact_legacy_validation_parity(
        settlement=exact_out_settlement,
        intents=[exact_out_intent],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert (
        err
        == f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={exact_out_intent.intent_id}"
    )

    exact_in_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(910),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100,
            "min_amount_out": 1,
            "recipient": pk1,
        },
    )
    cow_settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(exact_in_intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(
                intent_id=exact_in_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=50,
                fee_paid=0,
            )
        ],
        balance_deltas=[
            BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
            BalanceDelta(pubkey=pk1, asset=asset1, delta_add=50, delta_sub=0),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    disabled_ok, disabled_err = _assert_exact_legacy_validation_parity(
        settlement=cow_settlement,
        intents=[exact_in_intent],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=False,
    )
    assert disabled_ok is False
    assert disabled_err == f"COW_NETTED not allowed for intent_id={exact_in_intent.intent_id}"

    ok, err = _assert_exact_legacy_validation_parity(
        settlement=cow_settlement,
        intents=[exact_in_intent],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None
    assert err.startswith(
        f"COW_NETTED fill requires exactly one reciprocal counterparty: intent_id={exact_in_intent.intent_id}"
    )


def test_strong_validator_rejects_quote_hash_and_snapshot_binding_without_engine_witness() -> None:
    pk, asset0, asset1, pool_id, pool, balances, _intent, _settlement = _setup_swap_context()

    invalid_hash_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(911),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
            "quote_receipt_hash": "",
        },
    )
    settlement = compute_settlement([invalid_hash_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[invalid_hash_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "invalid quote_receipt_hash" in err

    unsanitized_hash_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(917),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
            "quote_receipt_hash": "0xdeadbeef",
        },
    )
    settlement = compute_settlement([unsanitized_hash_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[unsanitized_hash_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt transport metadata requires validated engine witness" in err

    snapshot_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(912),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 1_000,
            "min_amount_out": 1,
            "quote_pool_fingerprint": pool_state_fingerprint(pool),
        },
    )
    settlement = compute_settlement([snapshot_intent], {pool_id: pool}, balances, LPTable())
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[snapshot_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err is not None
    assert "quote receipt snapshot binding requires validated engine witness" in err

    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[snapshot_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_snapshot_bound_quote_bindings=True,
    )
    assert ok is True, err


def test_strong_validator_rejects_cow_netted_input_and_apply_errors() -> None:
    pk0 = "0x" + "11" * 48
    pk1 = "0x" + "22" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30, curve_tag="CPMM", curve_params="")
    pool_state = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        curve_tag="CPMM",
        curve_params="",
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(pk0, asset0, 10_000)
    balances.set(pk0, asset1, 0)
    balances.set(pk1, asset0, 0)
    balances.set(pk1, asset1, 0)

    def _settlement_for(
        intent_id: str,
        *,
        amount_in_filled: int = 100,
        amount_out_filled: int = 50,
        fee_paid: int = 0,
    ) -> Settlement:
        return Settlement(
            module="TauSwap",
            version="0.1",
            batch_ref="",
            included_intents=[(intent_id, FillAction.FILL)],
            fills=[
                Fill(
                    intent_id=intent_id,
                    action=FillAction.FILL,
                    reason="COW_NETTED",
                    amount_in_filled=amount_in_filled,
                    amount_out_filled=amount_out_filled,
                    fee_paid=fee_paid,
                )
            ],
            balance_deltas=[
                BalanceDelta(pubkey=pk0, asset=asset0, delta_add=0, delta_sub=100),
                BalanceDelta(pubkey=pk1, asset=asset1, delta_add=amount_out_filled, delta_sub=0),
            ],
            reserve_deltas=[],
            lp_deltas=[],
            events=None,
        )

    invalid_amount_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(913),
        sender_pubkey=pk0,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": False,
            "min_amount_out": 1,
            "recipient": pk1,
        },
    )
    ok, err = validate_settlement_strong(
        settlement=_settlement_for(invalid_amount_intent.intent_id),
        intents=[invalid_amount_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"invalid amount_in for intent_id={invalid_amount_intent.intent_id}"

    invalid_min_out_intent = replace(
        invalid_amount_intent,
        intent_id=_iid(914),
        fields={**invalid_amount_intent.fields, "amount_in": 100, "min_amount_out": False},
    )
    ok, err = validate_settlement_strong(
        settlement=_settlement_for(invalid_min_out_intent.intent_id),
        intents=[invalid_min_out_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool_state},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"invalid min_amount_out for intent_id={invalid_min_out_intent.intent_id}"

    base_intent = replace(
        invalid_amount_intent,
        intent_id=_iid(915),
        fields={**invalid_amount_intent.fields, "amount_in": 100, "min_amount_out": 10},
    )
    ok, err = _assert_exact_legacy_validation_parity(
        settlement=_settlement_for(base_intent.intent_id, fee_paid=1),
        intents=[base_intent],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"COW_NETTED fee_paid must be 0: intent_id={base_intent.intent_id}"

    ok, err = _assert_exact_legacy_validation_parity(
        settlement=_settlement_for(base_intent.intent_id, amount_in_filled=99),
        intents=[base_intent],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"COW_NETTED amount_in_filled mismatch: intent_id={base_intent.intent_id}"

    ok, err = _assert_exact_legacy_validation_parity(
        settlement=_settlement_for(base_intent.intent_id, amount_out_filled=9),
        intents=[base_intent],
        balances=balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err == f"COW_NETTED slippage: intent_id={base_intent.intent_id}"

    counterparty_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(919),
        sender_pubkey=pk1,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset1,
            "asset_out": asset0,
            "amount_in": 50,
            "min_amount_out": 100,
            "recipient": pk0,
        },
    )
    low_balance_pair = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[
            (base_intent.intent_id, FillAction.FILL),
            (counterparty_intent.intent_id, FillAction.FILL),
        ],
        fills=[
            Fill(
                intent_id=base_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=100,
                amount_out_filled=50,
                fee_paid=0,
            ),
            Fill(
                intent_id=counterparty_intent.intent_id,
                action=FillAction.FILL,
                reason="COW_NETTED",
                amount_in_filled=50,
                amount_out_filled=100,
                fee_paid=0,
            ),
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    low_balances = BalanceTable()
    low_balances.set(pk0, asset0, 1)
    low_balances.set(pk1, asset1, 50)
    ok, err = _assert_exact_legacy_validation_parity(
        settlement=low_balance_pair,
        intents=[base_intent, counterparty_intent],
        balances=low_balances,
        pools={pool_id: pool_state},
        lp_balances=LPTable(),
        allow_cow_netting=True,
    )
    assert ok is False
    assert err is not None
    assert err.startswith(f"COW_NETTED apply error for intent_id={base_intent.intent_id}:")


def test_strong_validator_rejects_unsupported_intent_kind() -> None:
    _pk, _asset0, _asset1, pool_id, pool, balances, _intent, _settlement = _setup_swap_context()
    weird_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind="MYSTERY_KIND",
        intent_id=_iid(916),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(weird_intent.intent_id, FillAction.FILL)],
        fills=[Fill(intent_id=weird_intent.intent_id, action=FillAction.FILL)],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_strong(
        settlement=settlement,
        intents=[weird_intent],
        pre_balances=balances,
        pre_pools={pool_id: pool},
        pre_lp_balances=LPTable(),
        mode="strong_replay",
    )
    assert ok is False
    assert err == "unsupported intent kind for strong validation: MYSTERY_KIND"
