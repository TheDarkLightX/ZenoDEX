# [TESTER] v1

from __future__ import annotations

import sys
from dataclasses import replace

from src.core.liquidity import create_pool
from src.core.settlement import Fill, FillAction, Settlement
from src.integration import tau_gate
from src.integration.tau_gate import TauGateConfig, TauSettlementModuleFlags, validate_settlement_swaps
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


# ======================================================================
# [REFACTOR-CHARACTERIZATION] v2 — golden-first oracle for the
# validate_settlement_swaps complexity reduction.
#
# These pin CURRENT behavior of the (pre-refactor) source on exactly the
# code paths that the decomposition moves into helpers:
#   - the self-contained CREATE_POOL / ADD_LIQUIDITY / REMOVE_LIQUIDITY
#     reserve-application blocks (densest branch chunk, previously unpinned),
#   - the v4 (small-value) swap binding path (previously unexercised — all
#     legacy tests used 1_000_000 reserves so use_v4 was always False),
#   - representative per-fill rejects (precedence / fail-closed),
#   - the field-ORDER binding teeth (asymmetric distinct values so that no
#     permutation of reserve_in/reserve_out or amount_in/amount_out is a
#     fixed point — a reorder MUST change the emitted Tau input dict).
#
# Every "_fake_tau" stub is the deterministic invocation boundary: we do NOT
# require a real tau binary, but we DO pin the exact (i*) input dict that the
# field-level binding produces, which is the assurance-critical contract.
# ======================================================================

PK = "0x" + "11" * 48
A0 = "0x" + "01" * 32  # sorts first -> pool.asset0
A1 = "0x" + "02" * 32  # sorts second -> pool.asset1


def _mk_pool(amount0: int = 5000, amount1: int = 8000, fee_bps: int = 30):  # type: ignore[no-untyped-def]
    return create_pool(
        asset0=A0,
        asset1=A1,
        amount0=amount0,
        amount1=amount1,
        fee_bps=fee_bps,
        creator_pubkey=PK,
        created_at=0,
    )


def _swap_in_intent(pool, *, intent_id: int = 1, min_amount_out: int = 1):  # type: ignore[no-untyped-def]
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(intent_id),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={
            "pool_id": pool.pool_id if hasattr(pool, "pool_id") else None,
            "asset_in": pool.asset0,
            "asset_out": pool.asset1,
            "min_amount_out": min_amount_out,
        },
    )


def _settlement(included, fills):  # type: ignore[no-untyped-def]
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=included,
        fills=fills,
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )


def _capture_tau(calls):  # type: ignore[no-untyped-def]
    def _fake_tau(*, spec_path, steps, **kwargs):  # type: ignore[no-untyped-def]
        for step in steps:
            calls.append((spec_path.name, dict(step)))
        return {i: {"o1": 1} for i in range(len(steps))}

    return _fake_tau


# ---------------------------------------------------------------------- #
# (gap) v4 small-value binding path — previously unexercised. Pins the
# EXACT main-swap (i*) dict with asymmetric reserves/amounts.
# ---------------------------------------------------------------------- #
def test_characterization_swap_exact_in_v4_small_value_binding(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    # asymmetric: reserve_in=5000 != reserve_out=8000; amount_in=100 != amount_out=150
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))

    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    assert calls == [
        (
            "swap_exact_in_v4.tau",
            {"i1": 5000, "i2": 8000, "i3": 100, "i4": 30, "i5": 1, "i6": 150, "i7": 5100, "i8": 7850},
        )
    ]


def test_characterization_swap_exact_out_v4_small_value_binding(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "max_amount_in": 10000},
    )
    # asymmetric: amount_out=150 != amount_in=120
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=120, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))

    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    assert calls == [
        (
            "swap_exact_out_v4.tau",
            {"i1": 5000, "i2": 8000, "i3": 150, "i4": 30, "i5": 10000, "i6": 120, "i7": 5120, "i8": 7850},
        )
    ]


# ---------------------------------------------------------------------- #
# (gap) v1 large-reserve binding path — pins the use_v4 boundary (>0xFFFF
# falls back to v1 hi/lo limbs) AND the exact limb decomposition.
# ---------------------------------------------------------------------- #
def test_characterization_swap_exact_in_v1_large_reserve_limbs(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pool_id, pool, _ = _mk_pool(amount0=100000, amount1=200000)  # > 0xFFFF -> v1
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))

    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    assert calls == [
        (
            "swap_exact_in_v1.tau",
            {
                "i1": 1, "i2": 34464, "i3": 3, "i4": 3392, "i5": 0, "i6": 100, "i7": 30,
                "i8": 0, "i9": 1, "i10": 0, "i11": 150, "i12": 1, "i13": 34564, "i14": 3, "i15": 3242,
            },
        )
    ]


# ---------------------------------------------------------------------- #
# (gap) CREATE_POOL reserve-application block — reconstructs pool state so a
# later same-pool swap sees the right reserves. Previously unpinned.
# ---------------------------------------------------------------------- #
def test_characterization_create_pool_then_swap_uses_reconstructed_reserves(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # No pre_pools: the pool is born inside the settlement via CREATE_POOL.
    create_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"asset0": A0, "asset1": A1, "fee_bps": 30, "amount0": 5000, "amount1": 8000, "created_at": 0},
    )
    pool_id, _pool, _ = _mk_pool(amount0=5000, amount1=8000)  # same id deterministically
    swap_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(2),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": A0, "asset_out": A1, "min_amount_out": 1},
    )
    create_fill = Fill(intent_id=create_intent.intent_id, action=FillAction.FILL, lp_minted=1)
    swap_fill = Fill(intent_id=swap_intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))

    ok, err = validate_settlement_swaps(
        intents=[create_intent, swap_intent],
        settlement=_settlement(
            [(create_intent.intent_id, FillAction.FILL), (swap_intent.intent_id, FillAction.FILL)],
            [create_fill, swap_fill],
        ),
        pre_pools={},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    # The swap must observe the freshly reconstructed reserves (5000/8000), proving CREATE_POOL applied.
    assert calls == [
        (
            "swap_exact_in_v4.tau",
            {"i1": 5000, "i2": 8000, "i3": 100, "i4": 30, "i5": 1, "i6": 150, "i7": 5100, "i8": 7850},
        )
    ]


# ---------------------------------------------------------------------- #
# (gap) ADD_LIQUIDITY then swap — reserves grow by amount{0,1}_used before
# the swap snapshot is taken. Pins the add-liquidity reserve mutation.
# ---------------------------------------------------------------------- #
def test_characterization_add_liquidity_then_swap_grows_reserves(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    add_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    swap_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(2),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": A0, "asset_out": A1, "min_amount_out": 1},
    )
    add_fill = Fill(intent_id=add_intent.intent_id, action=FillAction.FILL, amount0_used=1000, amount1_used=2000, lp_minted=1)
    swap_fill = Fill(intent_id=swap_intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))

    ok, err = validate_settlement_swaps(
        intents=[add_intent, swap_intent],
        settlement=_settlement(
            [(add_intent.intent_id, FillAction.FILL), (swap_intent.intent_id, FillAction.FILL)],
            [add_fill, swap_fill],
        ),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    # reserves became 5000+1000=6000 / 8000+2000=10000 before the swap snapshot.
    assert calls == [
        (
            "swap_exact_in_v4.tau",
            {"i1": 6000, "i2": 10000, "i3": 100, "i4": 30, "i5": 1, "i6": 150, "i7": 6100, "i8": 9850},
        )
    ]


# ---------------------------------------------------------------------- #
# (gap) REMOVE_LIQUIDITY then swap — reserves shrink by amount{0,1}_out.
# ---------------------------------------------------------------------- #
def test_characterization_remove_liquidity_then_swap_shrinks_reserves(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    rem_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    swap_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(2),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": A0, "asset_out": A1, "min_amount_out": 1},
    )
    rem_fill = Fill(intent_id=rem_intent.intent_id, action=FillAction.FILL, amount0_out=1000, amount1_out=2000, lp_burned=1)
    swap_fill = Fill(intent_id=swap_intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))

    ok, err = validate_settlement_swaps(
        intents=[rem_intent, swap_intent],
        settlement=_settlement(
            [(rem_intent.intent_id, FillAction.FILL), (swap_intent.intent_id, FillAction.FILL)],
            [rem_fill, swap_fill],
        ),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    # reserves became 5000-1000=4000 / 8000-2000=6000 before the swap snapshot.
    assert calls == [
        (
            "swap_exact_in_v4.tau",
            {"i1": 4000, "i2": 6000, "i3": 100, "i4": 30, "i5": 1, "i6": 150, "i7": 4100, "i8": 5850},
        )
    ]


# ---------------------------------------------------------------------- #
# (gap) representative per-fill rejects (fail-closed; precedence first-wins).
# ---------------------------------------------------------------------- #
def test_characterization_reject_swap_asset_not_in_pool() -> None:
    pool_id, pool, _ = _mk_pool()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": "0x" + "09" * 32, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and "assets not in pool" in err


def test_characterization_reject_invalid_amount_in_filled() -> None:
    pool_id, pool, _ = _mk_pool()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    # amount_in_filled <= 0 must reject before any tau work.
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=0, amount_out_filled=150)
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and "Invalid amount_in_filled" in err


def test_characterization_reject_pool_not_found() -> None:
    # Swap references a pool_id absent from pre_pools => fail-closed reject.
    # Reachable per-fill guard, previously unpinned.
    pool_id, pool, _ = _mk_pool()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": "0x" + "ab" * 32, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},  # the referenced pool is NOT here
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and "Pool not found" in err


def test_characterization_cow_netted_skips_tau(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # COW_NETTED fills do not touch reserves and must NOT invoke any swap spec.
    pool_id, pool, _ = _mk_pool()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, reason="COW_NETTED", amount_in_filled=100, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))

    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    assert calls == []  # no tau invocation for a netted fill


# ---------------------------------------------------------------------- #
# (fallback / fail-closed) a builder ValueError (fee_bps out of range) must
# be caught by the top-level except and become a deterministic (False, msg),
# NOT propagate. Guards concern (e): the try/except must wrap the binding.
# ---------------------------------------------------------------------- #
def test_characterization_builder_value_error_is_fail_closed() -> None:
    # Force a build_*_step ValueError from INSIDE the gate's binding: a
    # large-reserve pool (>0xFFFF) selects the v1 limb path, whose split_u32
    # rejects an amount that overflows u32. The top-level except must convert
    # this to a deterministic (False, msg), NOT let it propagate.
    pool_id, pool, _ = _mk_pool(amount0=100000, amount1=200000)  # > 0xFFFF -> v1
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    # amount_in_filled = 2**40 overflows u32 inside split_u32 -> ValueError.
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=2 ** 40, amount_out_filled=150)
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok
    assert err and "ValueError" in err and "u32" in err  # caught, not propagated


# ---------------------------------------------------------------------- #
# (fallback / fail-closed) tau binary not found => REJECT (not pass).
# ---------------------------------------------------------------------- #
def test_characterization_tau_bin_missing_is_fail_closed() -> None:
    pool_id, pool, _ = _mk_pool()
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    # tau_bin=None and allow_path_lookup=False, but there IS tau work -> must reject.
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=None, allow_path_lookup=False),
    )
    assert not ok
    assert err and "tau_bin not configured" in err


# ======================================================================
# [REFACTOR-TEETH] v2 — mutation-catching tests. Each pins the FULL (i*)
# dict of a main swap step with asymmetric distinct values so that NO
# permutation of the bound fields is a fixed point. If the refactor drops
# or reorders a bound swap field, or rebinds reserve_in<->reserve_out or
# amount_in<->amount_out, these dicts change and the test FAILS.
#
# Verified to bite: each was confirmed RED under its named mutation applied
# to src/integration/tau_gate.py, then reverted (see task log).
# ======================================================================


def _run_capture_swap_in_v4(monkeypatch, calls):  # type: ignore[no-untyped-def]
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))
    return validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )


def test_teeth_swap_in_v4_full_binding_dict(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # CATCHES: dropping or reordering any of reserve_in/reserve_out/amount_in/
    # amount_out/fee_bps/min_amount_out/new_reserve_in/new_reserve_out in the
    # exact-in v4 binding. reserve_in(5000)!=reserve_out(8000),
    # amount_in(100)!=amount_out(150) => every i* slot is uniquely identifying.
    calls: list = []
    ok, err = _run_capture_swap_in_v4(monkeypatch, calls)
    assert ok, err
    assert len(calls) == 1
    name, step = calls[0]
    assert name == "swap_exact_in_v4.tau"
    # Full positional binding contract (i1..i8). A reserve_in<->reserve_out
    # swap would make i1==8000 (RED); an amount_in<->amount_out swap would
    # make i3==150,i6==100 (RED).
    assert step == {"i1": 5000, "i2": 8000, "i3": 100, "i4": 30, "i5": 1, "i6": 150, "i7": 5100, "i8": 7850}
    # Explicit non-fixed-point guards (belt-and-suspenders vs. permutations):
    assert step["i1"] != step["i2"]  # reserve_in != reserve_out
    assert step["i3"] != step["i6"]  # amount_in != amount_out
    assert step["i7"] == step["i1"] + step["i3"]  # new_reserve_in = reserve_in + amount_in
    assert step["i8"] == step["i2"] - step["i6"]  # new_reserve_out = reserve_out - amount_out


def test_teeth_swap_out_v4_full_binding_dict(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # CATCHES: drop/reorder in the exact-OUT v4 binding, esp. the amount_out
    # vs amount_in and max_amount_in slots (different positional order than IN).
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "max_amount_in": 10000},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=120, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    name, step = calls[0]
    assert name == "swap_exact_out_v4.tau"
    # i3=amount_out(150), i5=max_amount_in(10000), i6=amount_in(120): a swap of
    # amount_in<->amount_out makes i3==120,i6==150 (RED).
    assert step == {"i1": 5000, "i2": 8000, "i3": 150, "i4": 30, "i5": 10000, "i6": 120, "i7": 5120, "i8": 7850}
    assert step["i3"] != step["i6"]  # amount_out != amount_in
    assert step["i7"] == step["i1"] + step["i6"]  # new_reserve_in = reserve_in + amount_in
    assert step["i8"] == step["i2"] - step["i3"]  # new_reserve_out = reserve_out - amount_out


def test_teeth_proof_gate_range_guard_full_binding_dicts(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # CATCHES: drop/reorder in BOTH composed specs of the proof_gate profile,
    # including the range-guard delta_primary/delta_secondary ordering
    # (delta_primary=amount_in, delta_secondary=amount_out for exact-in).
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1),
        sender_pubkey=PK,
        deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(
            enabled=True, tau_bin=sys.executable, allow_path_lookup=False, swap_profile="proof_gate_range_guard"
        ),
    )
    assert ok, err
    assert [n for n, _ in calls] == ["swap_exact_in_proof_gate_v1.tau", "swap_bv32_safe_range_guard_v1.tau"]
    # proof-gate main step (i1..i8 == v4 binding; i9/i10/i11 are the gate flags).
    assert calls[0][1] == {
        "i1": 5000, "i2": 8000, "i3": 100, "i4": 30, "i5": 1, "i6": 150, "i7": 5100, "i8": 7850,
        "i9": 1, "i10": 1, "i11": 1,
    }
    # range-guard: delta_primary=amount_in(100), delta_secondary=amount_out(150).
    # A delta_primary<->delta_secondary swap makes i3==150,i4==100 (RED).
    assert calls[1][1] == {"i1": 5000, "i2": 8000, "i3": 100, "i4": 150, "i5": 5100, "i6": 7850}
    assert calls[1][1]["i3"] != calls[1][1]["i4"]  # delta_primary != delta_secondary


def test_teeth_per_pool_execution_order_affects_reserve_snapshot(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # CATCHES: losing the per-pool sequential reserve threading (e.g. if the
    # refactor snapshots all swaps from pre-state instead of applying each
    # swap before the next in the same pool). Two same-pool swaps: the 2nd
    # MUST see reserves moved by the 1st.
    pool_id, pool, _ = _mk_pool(amount0=5000, amount1=8000)
    i1 = Intent(
        module="TauSwap", version="0.1", kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1), sender_pubkey=PK, deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    i2 = replace(i1, intent_id=_mk_intent_id(2))
    f1 = Fill(intent_id=i1.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)
    f2 = Fill(intent_id=i2.intent_id, action=FillAction.FILL, amount_in_filled=200, amount_out_filled=300)
    calls: list = []
    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _capture_tau(calls))
    ok, err = validate_settlement_swaps(
        intents=[i1, i2],
        settlement=_settlement(
            [(i1.intent_id, FillAction.FILL), (i2.intent_id, FillAction.FILL)], [f1, f2]
        ),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert ok, err
    # Both swaps share one pool -> one batched segment of two steps.
    # _capture_tau appends one (name, step) tuple per step, so calls has 2 entries.
    assert [n for n, _ in calls] == ["swap_exact_in_v4.tau", "swap_exact_in_v4.tau"]
    # step0 sees the original reserves 5000/8000.
    assert calls[0][1] == {"i1": 5000, "i2": 8000, "i3": 100, "i4": 30, "i5": 1, "i6": 150, "i7": 5100, "i8": 7850}
    # step1 MUST see reserves moved by step0: reserve_in=5100, reserve_out=7850.
    # If per-pool threading is lost, i1/i2 would still read 5000/8000 (RED).
    assert calls[1][1] == {"i1": 5100, "i2": 7850, "i3": 200, "i4": 30, "i5": 1, "i6": 300, "i7": 5300, "i8": 7550}
    assert calls[1][1]["i1"] == calls[0][1]["i7"]  # step1.reserve_in == step0.new_reserve_in
    assert calls[1][1]["i2"] == calls[0][1]["i8"]  # step1.reserve_out == step0.new_reserve_out


def test_teeth_fallback_stays_fail_closed_on_runner_exception(monkeypatch) -> None:  # type: ignore[no-untyped-def]
    # CATCHES: a refactor that moves the tool invocation OUTSIDE the top-level
    # try/except (so a runner crash propagates instead of becoming (False,msg)).
    pool_id, pool, _ = _mk_pool()
    intent = Intent(
        module="TauSwap", version="0.1", kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_mk_intent_id(1), sender_pubkey=PK, deadline=9999999999,
        fields={"pool_id": pool_id, "asset_in": pool.asset0, "asset_out": pool.asset1, "min_amount_out": 1},
    )
    fill = Fill(intent_id=intent.intent_id, action=FillAction.FILL, amount_in_filled=100, amount_out_filled=150)

    def _boom(*a, **k):  # type: ignore[no-untyped-def]
        raise RuntimeError("tau crashed")

    monkeypatch.setattr(tau_gate, "run_tau_spec_steps", _boom)
    ok, err = validate_settlement_swaps(
        intents=[intent],
        settlement=_settlement([(intent.intent_id, FillAction.FILL)], [fill]),
        pre_pools={pool_id: pool},
        config=TauGateConfig(enabled=True, tau_bin=sys.executable, allow_path_lookup=False),
    )
    assert not ok  # crash converted to rejection, never raised
    assert err and "RuntimeError" in err
