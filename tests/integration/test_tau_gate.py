# [TESTER] v1

from __future__ import annotations

import sys
from dataclasses import replace

from src.core.liquidity import create_pool
from src.core.settlement import Fill, FillAction, Settlement
from src.integration import tau_gate
from src.integration.tau_gate import (
    TauGateConfig,
    TauSettlementModuleFlags,
    validate_settlement_swaps,
)
from src.state.intents import Intent, IntentKind


def _mk_intent_id(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_tau_gate_enabled_no_swaps_does_not_require_tau() -> None:
    intents: list[Intent] = []
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement=settlement,
        pre_pools={},
        config=TauGateConfig(enabled=True, tau_bin=None, allow_path_lookup=False),
    )
    assert ok, err


def test_tau_gate_replays_non_cpmm_create_pool_before_add_liquidity_without_tau() -> None:
    pk_a = "0x" + "11" * 48
    pk_b = "0x" + "22" * 48
    asset0 = "0x" + "03" * 32
    asset1 = "0x" + "04" * 32
    pool_id, _, _ = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=1_000,
        amount1=2_000,
        fee_bps=20,
        creator_pubkey=pk_a,
        created_at=0,
        curve_tag=" sum_boost_v1 ",
        curve_params={"mu_num": 1, "mu_den": 2},
    )
    create_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_mk_intent_id(201),
        sender_pubkey=pk_a,
        deadline=9999999999,
        fields={
            "asset0": asset0,
            "asset1": asset1,
            "fee_bps": 20,
            "amount0": 1_000,
            "amount1": 2_000,
            "curve_tag": " sum_boost_v1 ",
            "curve_params": {"mu_num": 1, "mu_den": 2},
        },
    )
    add_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_mk_intent_id(202),
        sender_pubkey=pk_b,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(create_intent.intent_id, FillAction.FILL), (add_intent.intent_id, FillAction.FILL)],
        fills=[
            Fill(intent_id=create_intent.intent_id, action=FillAction.FILL),
            Fill(intent_id=add_intent.intent_id, action=FillAction.FILL, amount0_used=10, amount1_used=20),
        ],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=[create_intent, add_intent],
        settlement=settlement,
        pre_pools={},
        config=TauGateConfig(enabled=True, tau_bin=None, allow_path_lookup=False),
    )
    assert ok, err


def test_tau_gate_catches_tau_runner_exceptions(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey="0x" + "11" * 48,
        created_at=0,
    )
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_mk_intent_id(1),
            sender_pubkey="0x" + "11" * 48,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": pool.asset0,
                "asset_out": pool.asset1,
                "min_amount_out": 1,
            },
        )
    ]
    fills = [
        Fill(
            intent_id=intents[0].intent_id,
            action=FillAction.FILL,
            amount_in_filled=1000,
            amount_out_filled=900,
        )
    ]

    def _boom(*args, **kwargs):  # type: ignore[no-untyped-def]
        raise RuntimeError("tau crashed")

    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _boom)

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intents[0].intent_id, FillAction.FILL)],
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement=settlement,
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and "RuntimeError" in err


def test_tau_gate_execution_order_uses_included_intents(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # Two independent pools + two intents; fills are deliberately reversed.
    # The gate must use settlement.included_intents order (semantic execution order),
    # not the fills list order.
    pk = "0x" + "11" * 48
    pool_id_a, pool_a, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    pool_id_b, pool_b, _ = create_pool(
        asset0="0x" + "03" * 32,
        asset1="0x" + "04" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    intent_a = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id_a,
            "asset_in": pool_a.asset0,
            "asset_out": pool_a.asset1,
            "min_amount_out": 1,
        },
    )
    intent_b = replace(
        intent_a,
        intent_id=_mk_intent_id(2),
        fields={
            "pool_id": pool_id_b,
            "asset_in": pool_b.asset0,
            "asset_out": pool_b.asset1,
            "min_amount_out": 1,
        },
    )
    intents = [intent_a, intent_b]
    fills = [
        Fill(
            intent_id=intent_b.intent_id,
            action=FillAction.FILL,
            amount_in_filled=1000,
            amount_out_filled=900,
        ),
        Fill(
            intent_id=intent_a.intent_id,
            action=FillAction.FILL,
            amount_in_filled=1000,
            amount_out_filled=900,
        ),
    ]

    def _fake_tau(*args, **kwargs):  # type: ignore[no-untyped-def]
        # Fail only step 0; caller should attribute it to the first fill in the settlement list.
        return {0: {"o1": 0}, 1: {"o1": 1}}

    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _fake_tau)

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent_a.intent_id, FillAction.FILL), (intent_b.intent_id, FillAction.FILL)],
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement=settlement,
        pre_pools={pool_id_a: pool_a, pool_id_b: pool_b},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and intent_a.intent_id in err


def test_tau_gate_requires_absolute_tau_bin_when_path_lookup_disabled() -> None:
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey="0x" + "11" * 48,
        created_at=0,
    )
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": pool.asset0,
            "asset_out": pool.asset1,
            "min_amount_out": 1,
        },
    )
    fill = Fill(
        intent_id=intent.intent_id,
        action=FillAction.FILL,
        amount_in_filled=1000,
        amount_out_filled=900,
    )
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL)],
        fills=[fill],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=settlement,
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin="tau", allow_path_lookup=False),
    )
    assert not ok
    assert err and "absolute" in err


def test_tau_gate_supports_mixed_exact_in_and_exact_out_per_pool(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pk = "0x" + "11" * 48
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    intent_in = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": pool.asset0,
            "asset_out": pool.asset1,
            "min_amount_out": 1,
        },
    )
    intent_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_mk_intent_id(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": pool.asset0,
            "asset_out": pool.asset1,
            "max_amount_in": 10_000,
        },
    )
    fills = [
        Fill(
            intent_id=intent_in.intent_id,
            action=FillAction.FILL,
            amount_in_filled=1000,
            amount_out_filled=900,
        ),
        Fill(
            intent_id=intent_out.intent_id,
            action=FillAction.FILL,
            amount_in_filled=1000,
            amount_out_filled=900,
        ),
    ]

    calls = []

    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        calls.append((spec_path.name, len(steps)))
        return {i: {"o1": 1} for i in range(len(steps))}

    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _fake_tau)

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent_in.intent_id, FillAction.FILL), (intent_out.intent_id, FillAction.FILL)],
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=[intent_in, intent_out],
        settlement=settlement,
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    assert calls == [("swap_exact_in_v1.tau", 1), ("swap_exact_out_v1.tau", 1)]


def test_tau_gate_proof_gate_range_guard_profile_runs_composed_specs(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pk = "0x" + "11" * 48
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    intent_in = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": pool.asset0,
            "asset_out": pool.asset1,
            "min_amount_out": 1,
        },
    )
    intent_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_mk_intent_id(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": pool.asset0,
            "asset_out": pool.asset1,
            "max_amount_in": 10_000,
        },
    )
    fills = [
        Fill(
            intent_id=intent_in.intent_id,
            action=FillAction.FILL,
            amount_in_filled=1000,
            amount_out_filled=900,
        ),
        Fill(
            intent_id=intent_out.intent_id,
            action=FillAction.FILL,
            amount_in_filled=950,
            amount_out_filled=800,
        ),
    ]

    calls = []

    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        calls.append((spec_path.name, dict(steps[0])))
        return {i: {"o1": 1} for i in range(len(steps))}

    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _fake_tau)

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent_in.intent_id, FillAction.FILL), (intent_out.intent_id, FillAction.FILL)],
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=[intent_in, intent_out],
        settlement=settlement,
        pre_pools={pool_id: pool},
        config=TauGateConfig(
            enabled=True,
            tau_bin=sys.executable,
            allow_path_lookup=False,
            swap_profile="proof_gate_range_guard",
        ),
    )
    assert ok, err
    assert [name for name, _step in calls] == [
        "swap_exact_in_proof_gate_v1.tau",
        "swap_bv32_safe_range_guard_v1.tau",
        "swap_exact_out_proof_gate_v1.tau",
        "swap_bv32_safe_range_guard_v1.tau",
    ]
    assert calls[0][1]["i9"] == 1 and calls[0][1]["i10"] == 1
    assert calls[1][1] == {
        "i1": 1_000_000,
        "i2": 1_000_000,
        "i3": 1000,
        "i4": 900,
        "i5": 1_001_000,
        "i6": 999_100,
    }
    assert calls[2][1]["i9"] == 1 and calls[2][1]["i10"] == 1
    assert calls[3][1] == {
        "i1": 1_001_000,
        "i2": 999_100,
        "i3": 800,
        "i4": 950,
        "i5": 1_001_950,
        "i6": 998_300,
    }


def test_tau_gate_rejects_unknown_swap_profile() -> None:
    ok, err = validate_settlement_swaps(
        intents=[],
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
        pre_pools={},
        config=TauGateConfig(enabled=True, tau_bin=None, allow_path_lookup=False, swap_profile="nope"),
    )
    assert not ok
    assert err and "swap_profile" in err


def test_tau_gate_settlement_price_profile_runs_aligned_rail(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pk = "0x" + "11" * 48
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_mk_intent_id(i),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": pool.asset0,
                "asset_out": pool.asset1,
                "min_amount_out": 1,
            },
        )
        for i in range(1, 5)
    ]
    fills = [
        Fill(
            intent_id=intent.intent_id,
            action=FillAction.FILL,
            reason="COW_NETTED",
            amount_in_filled=1000,
            amount_out_filled=900,
        )
        for intent in intents
    ]
    calls = []

    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        calls.append((spec_path.name, dict(steps[0])))
        return {0: {"o1": 1}}

    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _fake_tau)

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL) for intent in intents],
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement=settlement,
        pre_pools={pool_id: pool},
        config=TauGateConfig(
            enabled=True,
            tau_bin=sys.executable,
            allow_path_lookup=False,
            settlement_profile="aligned_price_rails_v1",
            settlement_price_history=(1000, 1001, 1002),
        ),
    )
    assert ok, err
    assert calls == [
        (
            "settlement_price_rails_aligned_v1.tau",
            {
                "i1": 1,
                "i2": 2,
                "i3": 3,
                "i4": 4,
                "i5": 1000,
                "i6": 1001,
                "i7": 1002,
            },
        )
    ]


def test_tau_gate_settlement_compact_bundle_uses_explicit_flags(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pk = "0x" + "11" * 48
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_mk_intent_id(i),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": pool.asset0,
                "asset_out": pool.asset1,
                "min_amount_out": 1,
            },
        )
        for i in range(1, 5)
    ]
    fills = [
        Fill(
            intent_id=intent.intent_id,
            action=FillAction.FILL,
            reason="COW_NETTED",
            amount_in_filled=1000,
            amount_out_filled=900,
        )
        for intent in intents
    ]
    calls = []

    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        calls.append((spec_path.name, dict(steps[0])))
        return {0: {"o1": 0 if steps[0]["i13"] == 0 else 1}}

    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _fake_tau)

    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL) for intent in intents],
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement=settlement,
        pre_pools={pool_id: pool},
        config=TauGateConfig(
            enabled=True,
            tau_bin=sys.executable,
            allow_path_lookup=False,
            settlement_profile="aligned_compact_bundle_v5",
            settlement_price_history=(1000, 1001, 1002),
            settlement_module_flags=TauSettlementModuleFlags(rebate_ok=0),
        ),
    )
    assert not ok
    assert err and "Tau gate failed" in err
    assert calls == [
        (
            "settlement_v5_aligned_compact_bundle.tau",
            {
                "i1": 1,
                "i2": 2,
                "i3": 3,
                "i4": 4,
                "i5": 1000,
                "i6": 1001,
                "i7": 1002,
                "i8": 1,
                "i9": 1,
                "i10": 1,
                "i11": 1,
                "i12": 1,
                "i13": 0,
                "i14": 1,
                "i15": 1,
                "i16": 1,
            },
        )
    ]


def test_tau_gate_settlement_profile_requires_four_intents() -> None:
    pk = "0x" + "11" * 48
    pool_id, pool, _ = create_pool(
        asset0="0x" + "01" * 32,
        asset1="0x" + "02" * 32,
        amount0=1_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=pk,
        created_at=0,
    )
    intents = [
        Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_mk_intent_id(i),
            sender_pubkey=pk,
            deadline=9999999999,
            fields={
                "pool_id": pool_id,
                "asset_in": pool.asset0,
                "asset_out": pool.asset1,
                "min_amount_out": 1,
            },
        )
        for i in range(1, 4)
    ]
    fills = [
        Fill(
            intent_id=intent.intent_id,
            action=FillAction.FILL,
            reason="COW_NETTED",
            amount_in_filled=1000,
            amount_out_filled=900,
        )
        for intent in intents
    ]
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[(intent.intent_id, FillAction.FILL) for intent in intents],
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )

    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement=settlement,
        pre_pools={pool_id: pool},
        config=TauGateConfig(
            enabled=True,
            tau_bin=sys.executable,
            allow_path_lookup=False,
            settlement_profile="aligned_price_rails_v1",
            settlement_price_history=(1000, 1001, 1002),
        ),
    )
    assert not ok
    assert err and "requires exactly 4 included intents" in err
