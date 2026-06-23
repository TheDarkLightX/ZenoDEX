from __future__ import annotations

import itertools

from src.core.batch_clearing import compute_settlement
from src.core.settlement import FillAction
from src.core.settlement_admission import (
    INVALID_SETTLEMENT_INTENT_REASON,
    admit_settlement_intents,
)
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _intent(kind: IntentKind, n: int, **fields: object) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=kind,
        intent_id=_iid(n),
        sender_pubkey="0x" + "11" * 48,
        deadline=9999999999,
        fields=dict(fields),
    )


def test_admit_settlement_intents_classifies_create_pool_pool_and_invalid_lanes() -> None:
    create_pool = _intent(IntentKind.CREATE_POOL, 1, asset0="A", asset1="B")
    pool_swap = _intent(IntentKind.SWAP_EXACT_IN, 2, pool_id="pool-a")
    missing_pool = _intent(IntentKind.SWAP_EXACT_OUT, 3)
    empty_pool = _intent(IntentKind.ADD_LIQUIDITY, 4, pool_id="")

    admission = admit_settlement_intents([missing_pool, create_pool, pool_swap, empty_pool])

    assert admission.create_pool_intents == (create_pool,)
    assert admission.pool_intents[0].pool_id == "pool-a"
    assert admission.intents_by_pool() == {"pool-a": [pool_swap]}
    assert [r.intent.intent_id for r in admission.rejected_intents] == [
        missing_pool.intent_id,
        empty_pool.intent_id,
    ]
    assert [r.to_fill().reason for r in admission.rejected_intents] == [
        INVALID_SETTLEMENT_INTENT_REASON,
        INVALID_SETTLEMENT_INTENT_REASON,
    ]


def test_compute_settlement_preserves_legacy_non_pool_reject_ordering() -> None:
    invalid_without_pool = _intent(IntentKind.SWAP_EXACT_IN, 1)
    unknown_pool = _intent(
        IntentKind.SWAP_EXACT_IN,
        2,
        pool_id="missing-pool",
        asset_in="A",
        asset_out="B",
        amount_in=1,
        min_amount_out=0,
    )

    settlement = compute_settlement(
        [invalid_without_pool, unknown_pool],
        pools={},
        balances=BalanceTable(),
        lp_balances=LPTable(),
    )

    assert [(fill.intent_id, fill.action, fill.reason) for fill in settlement.fills] == [
        (unknown_pool.intent_id, FillAction.REJECT, "POOL_NOT_FOUND"),
        (invalid_without_pool.intent_id, FillAction.REJECT, INVALID_SETTLEMENT_INTENT_REASON),
    ]
    assert settlement.included_intents == [
        (unknown_pool.intent_id, FillAction.REJECT),
        (invalid_without_pool.intent_id, FillAction.REJECT),
    ]


def test_admission_partition_is_exact_over_small_structural_corpus() -> None:
    cases = [
        (IntentKind.CREATE_POOL, {}),
        (IntentKind.SWAP_EXACT_IN, {"pool_id": "pool-a"}),
        (IntentKind.SWAP_EXACT_OUT, {"pool_id": "pool-b"}),
        (IntentKind.REMOVE_LIQUIDITY, {"pool_id": ""}),
        (IntentKind.ADD_LIQUIDITY, {"pool_id": False}),
        (IntentKind.SWAP_EXACT_IN, {}),
    ]

    for seq_idx, case_seq in enumerate(itertools.product(cases, repeat=3), start=1):
        intents = [
            _intent(kind, seq_idx * 10 + offset, **fields)
            for offset, (kind, fields) in enumerate(case_seq)
        ]
        admission = admit_settlement_intents(intents)

        admitted_ids = [i.intent_id for i in admission.create_pool_intents]
        admitted_ids.extend(entry.intent.intent_id for entry in admission.pool_intents)
        admitted_ids.extend(entry.intent.intent_id for entry in admission.rejected_intents)

        assert sorted(admitted_ids) == sorted(intent.intent_id for intent in intents)
        assert len(admitted_ids) == len(set(admitted_ids))

        assert all(intent.kind == IntentKind.CREATE_POOL for intent in admission.create_pool_intents)
        assert all(entry.pool_id for entry in admission.pool_intents)
        assert all(entry.reason == INVALID_SETTLEMENT_INTENT_REASON for entry in admission.rejected_intents)
