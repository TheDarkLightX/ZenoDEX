# [TESTER] v1

from __future__ import annotations

from src.core.intent_normal_form import is_in_normal_form, normalize_intents, require_normal_form
from src.state.intents import Intent, IntentKind


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def test_normal_form_sorts_swaps_by_effective_limit_price_desc_then_intent_id() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    # Higher min_out/amount_in => higher effective limit price.
    swap_low = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
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
    swap_high = Intent(
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
            "amount_in": 1000,
            "min_amount_out": 2,
        },
    )

    normalized = normalize_intents([swap_low, swap_high]).intent_ids
    assert normalized == [swap_high.intent_id, swap_low.intent_id]


def test_normal_form_is_idempotent_and_detectable() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    swap_a = Intent(
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
            "amount_in": 1000,
            "min_amount_out": 1,
        },
    )
    swap_b = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
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

    ordered = [swap_a, swap_b]
    assert is_in_normal_form(ordered)
    require_normal_form(ordered)

    normalized_once = normalize_intents(ordered).intent_ids
    normalized_twice = normalize_intents(normalize_intents(ordered).intents).intent_ids
    assert normalized_once == normalized_twice

