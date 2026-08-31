# [TESTER] v1

from __future__ import annotations

from types import SimpleNamespace

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.liquidity import create_pool
from src.core.settlement import FillAction, Settlement
from src.kernels.python.batch_auction_settler_v1_witness import (
    BatchAuctionAggregateSnapshot,
    replay_supported_batch_auction_exact_in_witness,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable

SENDER = "0x" + "11" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _make_pool_and_balances(*, reserve0: int, reserve1: int, total_amount_in: int) -> tuple[str, dict[str, object], BalanceTable]:
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
    balances.set(SENDER, ASSET1, total_amount_in + reserve0 + reserve1)
    return pool_id, {pool_id: pool}, balances


def _make_exact_in_intent(
    *, intent_id: str, pool_id: str, amount_in: int, min_amount_out: int, asset_in: str = ASSET0, asset_out: str = ASSET1
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=intent_id,
        sender_pubkey=SENDER,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": int(amount_in),
            "min_amount_out": int(min_amount_out),
        },
    )


def _make_supported_batch() -> tuple[list[Intent], Settlement, dict[str, object], BalanceTable]:
    pool_id, pools, balances = _make_pool_and_balances(reserve0=10_000, reserve1=10_000, total_amount_in=18)
    intents = [
        _make_exact_in_intent(intent_id=_iid(1), pool_id=pool_id, amount_in=7, min_amount_out=1),
        _make_exact_in_intent(intent_id=_iid(2), pool_id=pool_id, amount_in=11, min_amount_out=1),
    ]
    settlement = compute_settlement(
        intents=intents,
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="optimal_ab_bounded",
    )
    return intents, settlement, pools, balances


def _replace_first_intent_field(
    intents: list[Intent],
    _settlement: Settlement,
    *,
    key: str,
    value: object,
) -> None:
    intents[0] = intents[0].with_field(key, value)


def test_batch_auction_witness_replays_supported_exact_in_batch() -> None:
    intents, settlement, _pools, _balances = _make_supported_batch()

    witness = replay_supported_batch_auction_exact_in_witness(intents=intents, settlement=settlement)
    assert witness is not None

    fill_by_id = {fill.intent_id: fill for fill in settlement.fills}
    assert witness == BatchAuctionAggregateSnapshot(
        intent_count=2,
        total_input_collected=18,
        total_guaranteed_output=2,
        total_actual_output=int(fill_by_id[_iid(1)].amount_out_filled or 0)
        + int(fill_by_id[_iid(2)].amount_out_filled or 0),
        total_filled_input=18,
        fees_captured=18
        - (
            int(fill_by_id[_iid(1)].amount_out_filled or 0)
            + int(fill_by_id[_iid(2)].amount_out_filled or 0)
        ),
    )


def test_batch_auction_witness_skips_exact_out_batches() -> None:
    pool_id, pool, _ = create_pool(
        asset0=ASSET0,
        asset1=ASSET1,
        amount0=10_000,
        amount1=10_000,
        fee_bps=30,
        creator_pubkey=SENDER,
        created_at=0,
    )
    balances = BalanceTable()
    balances.set(SENDER, ASSET0, 100_000)
    balances.set(SENDER, ASSET1, 100_000)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(3),
        sender_pubkey=SENDER,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": ASSET0,
            "asset_out": ASSET1,
            "amount_out": 100,
            "max_amount_in": 1_000,
        },
    )
    settlement = compute_settlement(
        intents=[intent],
        pools={pool_id: pool},
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )

    witness = replay_supported_batch_auction_exact_in_witness(intents=[intent], settlement=settlement)
    assert witness is None


def test_batch_auction_witness_skips_mixed_direction_or_special_fill_reason() -> None:
    pool_id, pools, balances = _make_pool_and_balances(reserve0=12_000, reserve1=12_000, total_amount_in=16)
    forward = _make_exact_in_intent(intent_id=_iid(4), pool_id=pool_id, amount_in=7, min_amount_out=1)
    reverse = _make_exact_in_intent(
        intent_id=_iid(5),
        pool_id=pool_id,
        amount_in=9,
        min_amount_out=1,
        asset_in=ASSET1,
        asset_out=ASSET0,
    )
    mixed_settlement = compute_settlement(
        intents=[forward, reverse],
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    assert replay_supported_batch_auction_exact_in_witness(
        intents=[forward, reverse],
        settlement=mixed_settlement,
    ) is None

    supported_intents = [
        _make_exact_in_intent(intent_id=_iid(6), pool_id=pool_id, amount_in=7, min_amount_out=1),
        _make_exact_in_intent(intent_id=_iid(7), pool_id=pool_id, amount_in=9, min_amount_out=1),
    ]
    supported_settlement = compute_settlement(
        intents=supported_intents,
        pools=pools,
        balances=balances,
        lp_balances=LPTable(),
        swap_ordering="greedy_ab_refined",
    )
    supported_settlement.fills[0].reason = "COW_NETTED"
    assert supported_settlement.fills[0].action == FillAction.FILL
    assert replay_supported_batch_auction_exact_in_witness(
        intents=supported_intents,
        settlement=supported_settlement,
    ) is None


@pytest.mark.parametrize(
    "mutate",
    [
        lambda intents, settlement: intents.clear(),
        lambda intents, settlement: settlement.included_intents.pop(),
        lambda intents, settlement: _replace_first_intent_field(intents, settlement, key="pool_id", value=""),
        lambda intents, settlement: _replace_first_intent_field(intents, settlement, key="asset_in", value=""),
        lambda intents, settlement: _replace_first_intent_field(intents, settlement, key="asset_out", value=ASSET0),
        lambda intents, settlement: _replace_first_intent_field(intents, settlement, key="amount_in", value=0),
        lambda intents, settlement: _replace_first_intent_field(
            intents,
            settlement,
            key="min_amount_out",
            value=-1,
        ),
        lambda intents, settlement: settlement.included_intents.__setitem__(0, (intents[0].intent_id, FillAction.REJECT)),
        lambda intents, settlement: settlement.fills.pop(),
        lambda intents, settlement: setattr(settlement.fills[0], "action", FillAction.REJECT),
        lambda intents, settlement: setattr(settlement.fills[0], "amount_in_filled", 6),
        lambda intents, settlement: setattr(settlement.fills[0], "amount_out_filled", -1),
    ],
)
def test_batch_auction_witness_skips_unsupported_or_malformed_batches(mutate) -> None:
    intents, settlement, _pools, _balances = _make_supported_batch()
    mutate(intents, settlement)
    assert replay_supported_batch_auction_exact_in_witness(intents=intents, settlement=settlement) is None


def test_batch_auction_witness_skips_batches_outside_notional_domain() -> None:
    intents, settlement, _pools, _balances = _make_supported_batch()
    settlement.fills[0].amount_out_filled = int(intents[0].get_field("amount_in")) + int(intents[1].get_field("amount_in")) + 1
    assert replay_supported_batch_auction_exact_in_witness(intents=intents, settlement=settlement) is None

    intents, settlement, _pools, _balances = _make_supported_batch()
    intents[0] = intents[0].with_field(
        "min_amount_out",
        int(intents[0].get_field("amount_in")) + int(intents[1].get_field("amount_in")) + 1,
    )
    assert replay_supported_batch_auction_exact_in_witness(intents=intents, settlement=settlement) is None


def test_batch_auction_witness_raises_when_ref_completion_state_is_not_complete(monkeypatch) -> None:
    from src.kernels.python import batch_auction_settler_v1_witness as witness_mod

    intents, settlement, _pools, _balances = _make_supported_batch()
    fake_state = SimpleNamespace(
        phase="Settling",
        intent_count=2,
        total_input_collected=18,
        total_guaranteed_output=2,
        total_actual_output=16,
        total_filled_input=18,
        fees_captured=2,
    )
    monkeypatch.setattr(witness_mod, "_step_or_raise", lambda *_args, **_kwargs: fake_state)
    with pytest.raises(RuntimeError, match="ended in non-complete phase"):
        replay_supported_batch_auction_exact_in_witness(intents=intents, settlement=settlement)


def test_batch_auction_step_or_raise_surfaces_ref_errors() -> None:
    from src.kernels.python import batch_auction_settler_v1_witness as witness_mod

    class _Ref:
        class Command:
            def __init__(self, *, tag: str, args: dict[str, object]) -> None:
                self.tag = tag
                self.args = args

        @staticmethod
        def step(_state: object, _cmd: object) -> object:
            return SimpleNamespace(ok=False, state=None, error="boom")

    with pytest.raises(RuntimeError, match="execute_fill failed: boom"):
        witness_mod._step_or_raise(_Ref(), object(), tag="execute_fill", args={})


def test_batch_auction_load_generated_ref_handles_missing_and_existing_module(monkeypatch) -> None:
    from src.kernels.python import batch_auction_settler_v1_witness as witness_mod

    module_name = "generated.batch_auction_settler_v1.python_ref.batch_auction_settler_v1_ref"
    witness_mod._load_generated_ref.cache_clear()
    monkeypatch.setattr(witness_mod.Path, "exists", lambda _self: False)
    with pytest.raises(FileNotFoundError, match="generated ref not found"):
        witness_mod._load_generated_ref()

    witness_mod._load_generated_ref.cache_clear()
    marker = object()
    monkeypatch.setattr(witness_mod.Path, "exists", lambda _self: True)
    monkeypatch.setitem(witness_mod.sys.modules, module_name, marker)
    assert witness_mod._load_generated_ref() is marker
    witness_mod.sys.modules.pop(module_name, None)


def test_batch_auction_load_generated_ref_rejects_missing_spec(monkeypatch) -> None:
    from src.kernels.python import batch_auction_settler_v1_witness as witness_mod

    witness_mod._load_generated_ref.cache_clear()
    monkeypatch.setattr(witness_mod.Path, "exists", lambda _self: True)
    monkeypatch.setattr(witness_mod.importlib.util, "spec_from_file_location", lambda *_args, **_kwargs: None)
    witness_mod.sys.modules.pop("generated.batch_auction_settler_v1.python_ref.batch_auction_settler_v1_ref", None)
    with pytest.raises(RuntimeError, match="could not load module spec"):
        witness_mod._load_generated_ref()


def test_batch_auction_load_generated_ref_rejects_spec_without_loader(monkeypatch) -> None:
    from src.kernels.python import batch_auction_settler_v1_witness as witness_mod

    witness_mod._load_generated_ref.cache_clear()
    monkeypatch.setattr(witness_mod.Path, "exists", lambda _self: True)
    monkeypatch.setattr(
        witness_mod.importlib.util,
        "spec_from_file_location",
        lambda *_args, **_kwargs: SimpleNamespace(loader=None),
    )
    witness_mod.sys.modules.pop("generated.batch_auction_settler_v1.python_ref.batch_auction_settler_v1_ref", None)
    with pytest.raises(RuntimeError, match="could not load module spec"):
        witness_mod._load_generated_ref()
