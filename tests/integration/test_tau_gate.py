# [TESTER] v1

from __future__ import annotations

import sys
from dataclasses import replace

from src.core.liquidity import create_pool
from src.core.settlement import Fill, FillAction
from src.integration import tau_gate
from src.integration.tau_gate import TauGateConfig, validate_settlement_swaps
from src.state.intents import Intent, IntentKind


def _mk_intent_id(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_tau_gate_enabled_no_swaps_does_not_require_tau() -> None:
    intents: list[Intent] = []
    fills: list[Fill] = []
    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement_fills=fills,
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

    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement_fills=fills,
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and "RuntimeError" in err


def test_tau_gate_fill_order_is_intent_order(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # Two independent pools + two intents; fills are deliberately reversed.
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

    ok, err = validate_settlement_swaps(
        intents=intents,
        settlement_fills=fills,
        pre_pools={pool_id_a: pool_a, pool_id_b: pool_b},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and intent_b.intent_id in err


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
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement_fills=[fill],
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

    ok, err = validate_settlement_swaps(
        intents=[intent_in, intent_out],
        settlement_fills=fills,
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    assert calls == [("swap_exact_in_v1.tau", 1), ("swap_exact_out_v1.tau", 1)]
