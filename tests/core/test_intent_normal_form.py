# [TESTER] v1

from __future__ import annotations

import pytest

from src.core.intent_normal_form import (
    _swap_limit_price,
    is_in_normal_form,
    iter_pool_partitions,
    normalize_intents,
    require_normal_form,
)
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


def test_normal_form_places_create_pool_before_pool_actions_and_unknown_tail() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    create_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(3),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30, "amount0": 10, "amount1": 20},
    )
    add_liquidity = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "submission_order": 9},
    )
    no_pool_tail = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(4),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={},
    )
    swap = Intent(
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

    normalized = normalize_intents([no_pool_tail, add_liquidity, create_pool, swap]).intent_ids
    assert normalized == [create_pool.intent_id, swap.intent_id, add_liquidity.intent_id, no_pool_tail.intent_id]


def test_normal_form_sorts_exact_out_swaps_by_effective_limit_price_desc() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    worse_price = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 100,
            "max_amount_in": 100,
        },
    )
    better_price = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 100,
            "max_amount_in": 50,
        },
    )

    normalized = normalize_intents([worse_price, better_price]).intent_ids
    assert normalized == [better_price.intent_id, worse_price.intent_id]


def test_normal_form_strict_lp_order_requires_submission_order() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32

    add_liquidity = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )

    with pytest.raises(ValueError, match="missing submission_order"):
        normalize_intents([add_liquidity], strict_lp_order=True)


def test_normal_form_non_strict_lp_order_falls_back_to_intent_id() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32

    later = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    earlier = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.REMOVE_LIQUIDITY,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )

    normalized = normalize_intents([later, earlier], strict_lp_order=False).intent_ids
    assert normalized == [earlier.intent_id, later.intent_id]


def test_normal_form_rejects_invalid_swap_fields() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    bad_exact_in = Intent(
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
            "amount_in": 0,
            "min_amount_out": 1,
        },
    )
    bad_exact_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 1,
            "max_amount_in": 0,
        },
    )

    with pytest.raises(ValueError, match="amount_in must be > 0"):
        normalize_intents([bad_exact_in])
    with pytest.raises(ValueError, match="swap.max_amount_in must be > 0"):
        normalize_intents([bad_exact_out])


def test_iter_pool_partitions_groups_by_normalized_pool_order() -> None:
    pk = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    asset2 = "0x" + "03" * 32
    pool_a = "0x" + "aa" * 32
    pool_b = "0x" + "bb" * 32

    create_pool = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id=_iid(5),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30, "amount0": 10, "amount1": 20},
    )
    pool_b_swap = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_b,
            "asset_in": asset1,
            "asset_out": asset2,
            "amount_in": 50,
            "min_amount_out": 1,
        },
    )
    pool_a_swap = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_a,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 50,
            "min_amount_out": 1,
        },
    )

    partitions = list(iter_pool_partitions([pool_b_swap, create_pool, pool_a_swap]))
    assert [pool_id for pool_id, _ in partitions] == [None, pool_a, pool_b]
    assert [bucket[0].intent_id for _, bucket in partitions] == [create_pool.intent_id, pool_a_swap.intent_id, pool_b_swap.intent_id]


def test_normal_form_rejects_non_int_and_non_string_fields() -> None:
    pk = "0x" + "11" * 48

    bad_pool_id = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(10),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": ""},
    )
    with pytest.raises(ValueError, match="intent.fields.pool_id must be a non-empty string"):
        normalize_intents([bad_pool_id])

    bad_submission_order = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(11),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": "0x" + "aa" * 32, "submission_order": True},
    )
    with pytest.raises(ValueError, match="lp.submission_order must be an int"):
        normalize_intents([bad_submission_order])


def test_normal_form_rejects_negative_min_out_and_nonpositive_exact_out_amount() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32

    negative_min_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(12),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 10,
            "min_amount_out": -1,
        },
    )
    with pytest.raises(ValueError, match="swap.min_amount_out must be >= 0"):
        normalize_intents([negative_min_out])

    nonpositive_exact_out = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_OUT,
        intent_id=_iid(13),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_out": 0,
            "max_amount_in": 1,
        },
    )
    with pytest.raises(ValueError, match="swap.amount_out must be > 0"):
        normalize_intents([nonpositive_exact_out])


def test_swap_limit_price_rejects_non_swap_intent() -> None:
    pk = "0x" + "11" * 48
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(14),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": "0x" + "aa" * 32, "submission_order": 1},
    )
    with pytest.raises(ValueError, match="not a swap intent"):
        _swap_limit_price(intent)


def test_normal_form_places_defensive_unknown_kind_after_known_pool_actions() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    swap = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(15),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": "0x" + "01" * 32,
            "asset_out": "0x" + "02" * 32,
            "amount_in": 10,
            "min_amount_out": 1,
        },
    )
    unknown = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(16),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id},
    )
    object.__setattr__(unknown, "kind", "UNKNOWN_KIND")

    normalized = normalize_intents([unknown, swap]).intent_ids
    assert normalized == [swap.intent_id, unknown.intent_id]


def test_require_normal_form_rejects_out_of_order_batch() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    later = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(18),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": "0x" + "01" * 32,
            "asset_out": "0x" + "02" * 32,
            "amount_in": 10,
            "min_amount_out": 1,
        },
    )
    earlier = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(17),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": "0x" + "01" * 32,
            "asset_out": "0x" + "02" * 32,
            "amount_in": 10,
            "min_amount_out": 1,
        },
    )
    with pytest.raises(ValueError, match="intents not in normal form"):
        require_normal_form([later, earlier])


def test_iter_pool_partitions_groups_multiple_intents_in_same_bucket() -> None:
    pk = "0x" + "11" * 48
    pool_id = "0x" + "aa" * 32
    first = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(19),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={
            "pool_id": pool_id,
            "asset_in": "0x" + "01" * 32,
            "asset_out": "0x" + "02" * 32,
            "amount_in": 10,
            "min_amount_out": 2,
        },
    )
    second = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(20),
        sender_pubkey=pk,
        deadline=9999999999,
        fields={"pool_id": pool_id, "submission_order": 7},
    )

    partitions = list(iter_pool_partitions([second, first]))
    assert len(partitions) == 1
    assert partitions[0][0] == pool_id
    assert [intent.intent_id for intent in partitions[0][1]] == [first.intent_id, second.intent_id]
