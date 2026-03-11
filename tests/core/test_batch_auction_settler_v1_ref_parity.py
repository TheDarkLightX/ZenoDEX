# [TESTER] v1

from __future__ import annotations

import importlib.util
import random
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import FillAction, Settlement
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable

SENDER = "0x" + "11" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "batch_auction_settler_v1" / "python_ref" / "batch_auction_settler_v1_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.batch_auction_settler_v1.python_ref.batch_auction_settler_v1_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _make_pool_and_balances(*, reserve0: int, reserve1: int, total_amount_in: int) -> tuple[str, dict[str, Any], BalanceTable]:
    pool_id, pool, _ = create_pool(
        asset0=ASSET0,
        asset1=ASSET1,
        amount0=reserve0,
        amount1=reserve1,
        fee_bps=30,
        creator_pubkey=SENDER,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, total_amount_in + reserve0 + reserve1)
    balances.set(SENDER, ASSET1, 0)
    return pool_id, {pool_id: pool}, balances


def _make_intents(pool_id: str, amount_ins: list[int], min_amount_outs: list[int]) -> list[Intent]:
    assert len(amount_ins) == len(min_amount_outs)
    intents: list[Intent] = []
    for i, (amount_in, min_amount_out) in enumerate(
        zip(amount_ins, min_amount_outs, strict=True),
        start=1,
    ):
        intents.append(
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(i),
                sender_pubkey=SENDER,
                deadline=9999999999,
                fields={
                    "pool_id": pool_id,
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "amount_in": int(amount_in),
                    "min_amount_out": int(min_amount_out),
                },
            )
        )
    return intents


def _require_all_filled_exact_in(intents: list[Intent], settlement: Settlement) -> dict[str, Any]:
    fill_by_id = {fill.intent_id: fill for fill in settlement.fills}
    assert len(fill_by_id) == len(intents)
    for intent in intents:
        fill = fill_by_id[intent.intent_id]
        assert fill.action == FillAction.FILL
        assert fill.amount_in_filled is not None
        assert fill.amount_out_filled is not None
        assert int(fill.amount_in_filled) == int(intent.get_field("amount_in"))
    return fill_by_id


def _bridge_min_amount_outs(base_intents: list[Intent], base_settlement: Settlement) -> list[int]:
    fill_by_id = _require_all_filled_exact_in(base_intents, base_settlement)
    mins: list[int] = []
    for index, intent in enumerate(base_intents):
        actual_out = int(fill_by_id[intent.intent_id].amount_out_filled)
        # Boundary coverage: alternate between "at" and "just below" actual output.
        mins.append(max(0, actual_out - (index % 2)))
    return mins


def _replay_shared_aggregate_trace(intents: list[Intent], settlement: Settlement) -> Any:
    fill_by_id = _require_all_filled_exact_in(intents, settlement)
    state = REF.init_state()

    total_input = 0
    total_guaranteed = 0
    total_actual = 0
    total_filled_input = 0

    for intent in intents:
        amount_in = int(intent.get_field("amount_in"))
        min_amount_out = int(intent.get_field("min_amount_out"))
        total_input += amount_in
        total_guaranteed += min_amount_out
        result = REF.step(
            state,
            REF.Command(
                tag="add_intent",
                args={
                    "amount_in": amount_in,
                    "min_amount_out": min_amount_out,
                    "auth_ok": True,
                },
            ),
        )
        assert result.ok, result.error
        assert result.state is not None
        state = result.state

    result = REF.step(state, REF.Command(tag="close_collection", args={"operator_auth": True}))
    assert result.ok, result.error
    assert result.state is not None
    state = result.state

    remainder_after_outputs = int(total_input)
    for fill in settlement.fills:
        if fill.action != FillAction.FILL:
            continue
        assert fill.amount_in_filled is not None
        assert fill.amount_out_filled is not None
        total_filled_input += int(fill.amount_in_filled)
        total_actual += int(fill.amount_out_filled)
    remainder_after_outputs -= total_actual
    clearing_price_bps = max(1, min(100_000, (int(total_actual) * 10_000) // max(1, int(total_filled_input))))
    surplus_bps = min(9_999, max(0, (remainder_after_outputs * 10_000) // max(1, total_input)))

    result = REF.step(
        state,
        REF.Command(
            tag="submit_solution",
            args={
                "solver_id": 1,
                "proposed_clearing_price_bps": clearing_price_bps,
                "surplus_extracted_bps": surplus_bps,
                "clearing_valid_witness": True,
            },
        ),
    )
    assert result.ok, result.error
    assert result.state is not None
    state = result.state

    result = REF.step(state, REF.Command(tag="finalize_winner", args={"operator_auth": True}))
    assert result.ok, result.error
    assert result.state is not None
    state = result.state

    for intent in intents:
        fill = fill_by_id[intent.intent_id]
        result = REF.step(
            state,
            REF.Command(
                tag="execute_fill",
                args={
                    "fill_input_amount": int(fill.amount_in_filled),
                    "fill_output_amount": int(fill.amount_out_filled),
                    "fill_min_guaranteed": int(intent.get_field("min_amount_out")),
                    "fill_valid_witness": True,
                },
            ),
        )
        assert result.ok, result.error
        assert result.state is not None
        state = result.state

    result = REF.step(
        state,
        REF.Command(
            tag="complete_batch",
            args={
                "protocol_fee_amount": remainder_after_outputs,
                "solver_reward_amount": 0,
                "conservation_witness": True,
            },
        ),
    )
    assert result.ok, result.error
    assert result.state is not None

    ref_state = result.state
    assert ref_state.phase == "Complete"
    assert ref_state.intent_count == len(intents)
    assert ref_state.settled_count == len(intents)
    assert ref_state.total_input_collected == total_input
    assert ref_state.total_guaranteed_output == total_guaranteed
    assert ref_state.total_actual_output == total_actual
    assert ref_state.total_filled_input == total_filled_input
    assert ref_state.fees_captured == remainder_after_outputs
    assert ref_state.solver_reward == 0
    assert ref_state.winning_solver_id == 1
    return ref_state


@pytest.mark.parametrize("swap_ordering", ["optimal_ab_bounded", "greedy_ab_refined"])
def test_batch_auction_ref_parity_on_shared_aggregates_small_grid(swap_ordering: str) -> None:
    reserves = [2_000, 5_000, 10_000]
    amount_pairs = [(3, 3), (5, 7), (7, 11), (10, 20)]

    for reserve in reserves:
        for amount_a, amount_b in amount_pairs:
            amount_ins = [amount_a, amount_b]
            pool_id, pools, balances = _make_pool_and_balances(
                reserve0=reserve,
                reserve1=reserve,
                total_amount_in=sum(amount_ins),
            )

            provisional_intents = _make_intents(pool_id, amount_ins, [0, 0])
            provisional = compute_settlement(
                intents=provisional_intents,
                pools=pools,
                balances=balances,
                lp_balances=LPTable(),
                swap_ordering=swap_ordering,
            )
            min_amount_outs = _bridge_min_amount_outs(provisional_intents, provisional)
            intents = _make_intents(pool_id, amount_ins, min_amount_outs)
            settlement = compute_settlement(
                intents=intents,
                pools=pools,
                balances=balances,
                lp_balances=LPTable(),
                swap_ordering=swap_ordering,
            )

            ref_state = _replay_shared_aggregate_trace(intents, settlement)
            assert ref_state.total_guaranteed_output == sum(min_amount_outs)


def test_batch_auction_ref_parity_on_shared_aggregates_random_bounded_batches() -> None:
    rng = random.Random(0)

    for _ in range(100):
        intent_count = rng.randint(1, 6)
        amount_ins = [rng.randint(3, 25) for _ in range(intent_count)]
        reserve = max(2_000, (sum(amount_ins) * 20) + 50)
        pool_id, pools, balances = _make_pool_and_balances(
            reserve0=reserve,
            reserve1=reserve,
            total_amount_in=sum(amount_ins),
        )

        provisional_intents = _make_intents(pool_id, amount_ins, [0] * intent_count)
        provisional = compute_settlement(
            intents=provisional_intents,
            pools=pools,
            balances=balances,
            lp_balances=LPTable(),
            swap_ordering="optimal_ab_bounded",
        )
        intents = _make_intents(pool_id, amount_ins, _bridge_min_amount_outs(provisional_intents, provisional))
        settlement = compute_settlement(
            intents=intents,
            pools=pools,
            balances=balances,
            lp_balances=LPTable(),
            swap_ordering="optimal_ab_bounded",
        )

        ref_state = _replay_shared_aggregate_trace(intents, settlement)
        assert ref_state.total_input_collected == sum(amount_ins)


def test_batch_auction_ref_parity_intent_count_boundary_at_max_32() -> None:
    amount_ins = [3 + (index % 3) for index in range(32)]
    reserve = max(2_000, (sum(amount_ins) * 30) + 100)
    pool_id, pools, balances = _make_pool_and_balances(
        reserve0=reserve,
        reserve1=reserve,
        total_amount_in=sum(amount_ins),
    )

    provisional_intents = _make_intents(pool_id, amount_ins, [0] * len(amount_ins))
    provisional = compute_settlement(
        intents=provisional_intents,
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    intents = _make_intents(pool_id, amount_ins, _bridge_min_amount_outs(provisional_intents, provisional))
    settlement = compute_settlement(
        intents=intents,
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    ref_state = _replay_shared_aggregate_trace(intents, settlement)
    assert ref_state.intent_count == 32
    assert ref_state.settled_count == 32
