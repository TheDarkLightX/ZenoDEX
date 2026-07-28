"""Focused semantic and construction tests for the exact P4B4 settlement index."""

from __future__ import annotations

import ast
import inspect
from dataclasses import replace
from types import MappingProxyType

import pytest

import src.core.fcis_settlement_index as settlement_index_module
from src.core.fcis_settlement_index import (
    ExactSettlementIndexRejectV1,
    ExactSettlementIndexV1,
    derive_exact_settlement_index_admitted_v1,
)
from src.core.settlement import BalanceDelta, Fill, FillAction, Settlement
from src.core.settlement_snapshots import OwnedSettlementV1, snapshot_settlement
from src.state.intent_snapshots import OwnedIntentV1, admit_intent_batch, snapshot_intent
from src.state.intents import Intent, IntentKind

ASSET_A = "0x" + "01" * 32
ASSET_B = "0x" + "02" * 32
SENDER_A = "0x" + "11" * 48
SENDER_B = "0x" + "22" * 48
POOL_ID = "pool-a"


def _intent_id(index: int) -> str:
    return "0x" + f"{index:064x}"


def _swap_intent(
    index: int,
    *,
    asset_in: str = ASSET_A,
    asset_out: str = ASSET_B,
    amount_in: int = 100,
    minimum_out: int = 1,
) -> Intent:
    return Intent(
        "TauSwap",
        "0.1",
        IntentKind.SWAP_EXACT_IN,
        _intent_id(index),
        SENDER_A if asset_in == ASSET_A else SENDER_B,
        1_000,
        None,
        {
            "pool_id": POOL_ID,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount_in,
            "min_amount_out": minimum_out,
        },
    )


def _route_intent(index: int) -> Intent:
    return Intent(
        "TauSwap",
        "0.1",
        IntentKind.ROUTE_EXACT_IN,
        _intent_id(index),
        SENDER_A,
        1_000,
        None,
        {
            "asset_in": ASSET_A,
            "asset_out": ASSET_B,
            "leg_indices": [0],
            "total_amount_in": 100,
            "total_min_amount_out": 1,
        },
    )


def _create_pool_intent(index: int) -> Intent:
    return Intent(
        "TauSwap",
        "0.1",
        IntentKind.CREATE_POOL,
        _intent_id(index),
        SENDER_A,
        1_000,
        None,
        {
            "asset0": ASSET_A,
            "asset1": ASSET_B,
            "fee_bps": 30,
            "amount0": 1_000,
            "amount1": 1_000,
        },
    )


def _fill(
    intent: Intent,
    *,
    action: FillAction = FillAction.FILL,
    reason: str | None = None,
    amount_in: int = 100,
    amount_out: int = 50,
    fee_paid: int = 1,
) -> Fill:
    return Fill(
        intent_id=intent.intent_id,
        action=action,
        reason=reason,
        amount_in_filled=amount_in if action is FillAction.FILL else None,
        amount_out_filled=amount_out if action is FillAction.FILL else None,
        fee_paid=fee_paid if action is FillAction.FILL else None,
    )


def _settlement(
    included: list[tuple[Intent, FillAction]],
    fills: list[Fill],
    *,
    events: list[dict[str, str]] | None = None,
) -> Settlement:
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch",
        included_intents=[(intent.intent_id, action) for intent, action in included],
        fills=fills,
        balance_deltas=[
            BalanceDelta(SENDER_A, ASSET_A, 0, 1),
            BalanceDelta(SENDER_A, ASSET_B, 1, 0),
        ],
        reserve_deltas=[],
        lp_deltas=[],
        events=events,
    )


def _derive(
    settlement: Settlement | OwnedSettlementV1,
    intents: list[Intent] | tuple[OwnedIntentV1, ...],
    *,
    allow_cow_netting: bool = False,
) -> ExactSettlementIndexV1 | ExactSettlementIndexRejectV1:
    owned_settlement = (
        settlement if type(settlement) is OwnedSettlementV1 else snapshot_settlement(settlement)
    )
    owned_intents = intents if type(intents) is tuple else admit_intent_batch(intents)
    return derive_exact_settlement_index_admitted_v1(
        owned_settlement,
        owned_intents,
        allow_cow_netting=allow_cow_netting,
    )


def _assert_reject(
    result: ExactSettlementIndexV1 | ExactSettlementIndexRejectV1,
    reason: str,
) -> None:
    assert type(result) is ExactSettlementIndexRejectV1
    assert result.reason == reason
    assert not hasattr(result, "entries")
    assert not hasattr(result, "settlement")


def test_exact_index_preserves_declared_order_and_derives_deterministically() -> None:
    first = _swap_intent(1)
    second = _swap_intent(2)
    settlement = _settlement(
        [(first, FillAction.FILL), (second, FillAction.FILL)],
        [_fill(first), _fill(second)],
        events=[{"kind": "first"}, {"kind": "second"}],
    )

    left = _derive(settlement, [first, second])
    right = _derive(settlement, [first, second])

    assert type(left) is ExactSettlementIndexV1
    assert left == right
    assert tuple(entry.intent_id for entry in left.entries) == (
        first.intent_id,
        second.intent_id,
    )
    assert tuple(fill.intent_id for fill in left.settlement.fills) == (
        first.intent_id,
        second.intent_id,
    )
    assert tuple(delta.asset for delta in left.settlement.balance_deltas) == (
        ASSET_A,
        ASSET_B,
    )
    assert left.settlement.events is not None
    assert tuple(event["kind"] for event in left.settlement.events) == ("first", "second")


def test_direct_index_construction_requires_private_authority() -> None:
    intent = _swap_intent(1)
    valid = _derive(
        _settlement([(intent, FillAction.FILL)], [_fill(intent)]),
        [intent],
    )
    assert type(valid) is ExactSettlementIndexV1

    with pytest.raises(TypeError, match="controlled derivation"):
        ExactSettlementIndexV1(
            valid.input_intents,
            valid.settlement,
            valid.entries,
            valid.cow_pairs,
            valid.allow_cow_netting,
            None,  # type: ignore[arg-type]
        )


def test_duplicate_input_intent_precedes_settlement_checks() -> None:
    intent = _swap_intent(1)
    settlement = snapshot_settlement(_settlement([(intent, FillAction.FILL)], [_fill(intent)]))
    owned = snapshot_intent(intent)

    result = derive_exact_settlement_index_admitted_v1(
        settlement,
        (owned, owned),
        allow_cow_netting=False,
    )

    _assert_reject(result, "duplicate intent_id in input intents")


def test_coverage_mismatch_precedes_duplicate_included_intents() -> None:
    first = _swap_intent(1)
    second = _swap_intent(2)
    settlement = snapshot_settlement(_settlement([(first, FillAction.REJECT)], []))
    repeated = settlement.included_intents[0]
    object.__setattr__(settlement, "included_intents", (repeated, repeated))

    result = derive_exact_settlement_index_admitted_v1(
        settlement,
        admit_intent_batch([first, second]),
        allow_cow_netting=False,
    )

    _assert_reject(
        result,
        f"settlement included_intents mismatch: missing=['{second.intent_id}'] extra=[]",
    )


def test_duplicate_included_and_duplicate_fill_rows_reject() -> None:
    intent = _swap_intent(1)
    included_duplicate = snapshot_settlement(_settlement([(intent, FillAction.REJECT)], []))
    entry = included_duplicate.included_intents[0]
    object.__setattr__(included_duplicate, "included_intents", (entry, entry))
    _assert_reject(
        _derive(included_duplicate, [intent]),
        "settlement included_intents contains duplicate intent_id entries",
    )

    fill_duplicate = snapshot_settlement(_settlement([(intent, FillAction.FILL)], [_fill(intent)]))
    fill = fill_duplicate.fills[0]
    object.__setattr__(fill_duplicate, "fills", (fill, fill))
    _assert_reject(
        _derive(fill_duplicate, [intent]),
        "settlement fills contains duplicate intent_id entries",
    )


def test_missing_extra_and_wrong_action_fill_reject_in_frozen_order() -> None:
    first = _swap_intent(1)
    second = _swap_intent(2)
    missing = snapshot_settlement(_settlement([(first, FillAction.FILL)], [_fill(first)]))
    object.__setattr__(missing, "fills", ())
    _assert_reject(
        _derive(missing, [first]),
        f"missing Fill for filled intent_id: {first.intent_id}",
    )

    extra_fill = snapshot_settlement(
        _settlement([(second, FillAction.FILL)], [_fill(second)])
    ).fills[0]
    extra = snapshot_settlement(_settlement([(first, FillAction.FILL)], [_fill(first)]))
    object.__setattr__(extra, "fills", (extra_fill,))
    _assert_reject(
        _derive(extra, [first]),
        f"settlement fills contains intent_ids not in input intents: ['{second.intent_id}']",
    )

    rejected_fill = snapshot_settlement(
        _settlement(
            [(first, FillAction.REJECT)],
            [_fill(first, action=FillAction.REJECT, reason="NO")],
        )
    ).fills[0]
    mismatch = snapshot_settlement(_settlement([(first, FillAction.FILL)], [_fill(first)]))
    object.__setattr__(mismatch, "fills", (rejected_fill,))
    _assert_reject(
        _derive(mismatch, [first]),
        f"Fill.action mismatch for intent_id={first.intent_id}: REJECT != FILL",
    )


def test_rejected_intent_cannot_retain_a_detailed_fill() -> None:
    intent = _swap_intent(1)
    settlement = _settlement(
        [(intent, FillAction.REJECT)],
        [_fill(intent, action=FillAction.REJECT, reason="NO_LIQUIDITY")],
    )

    result = _derive(settlement, [intent])

    _assert_reject(result, f"unexpected Fill for rejected intent_id: {intent.intent_id}")


def test_fill_rows_follow_included_fill_order() -> None:
    first = _swap_intent(1)
    second = _swap_intent(2)
    settlement = _settlement(
        [(first, FillAction.FILL), (second, FillAction.FILL)],
        [_fill(second), _fill(first)],
    )

    result = _derive(settlement, [first, second])

    _assert_reject(result, "settlement fills must follow included FILL order")


def test_cow_pair_is_exact_symmetric_and_context_gated() -> None:
    first = _swap_intent(1, amount_in=100, minimum_out=50)
    second = _swap_intent(
        2,
        asset_in=ASSET_B,
        asset_out=ASSET_A,
        amount_in=50,
        minimum_out=100,
    )
    settlement = _settlement(
        [(first, FillAction.FILL), (second, FillAction.FILL)],
        [
            _fill(first, reason="COW_NETTED", amount_in=100, amount_out=50, fee_paid=0),
            _fill(second, reason="COW_NETTED", amount_in=50, amount_out=100, fee_paid=0),
        ],
    )

    disabled = _derive(settlement, [first, second])
    _assert_reject(
        disabled,
        f"COW_NETTED not allowed for intent_id={first.intent_id}",
    )

    accepted = _derive(settlement, [first, second], allow_cow_netting=True)
    assert type(accepted) is ExactSettlementIndexV1
    assert tuple((pair.lower_intent_id, pair.upper_intent_id) for pair in accepted.cow_pairs) == (
        (first.intent_id, second.intent_id),
    )

    corrupted = snapshot_settlement(settlement)
    nonreciprocal = replace(corrupted.fills[1], amount_out_filled=101)
    object.__setattr__(corrupted, "fills", (corrupted.fills[0], nonreciprocal))
    rejected = _derive(corrupted, [first, second], allow_cow_netting=True)
    assert type(rejected) is ExactSettlementIndexRejectV1
    assert rejected.reason.startswith(
        f"COW_NETTED fill requires exactly one reciprocal counterparty: intent_id={first.intent_id}"
    )


def test_route_ids_and_route_phase_are_canonical() -> None:
    route_low = _route_intent(2)
    route_high = _route_intent(3)
    create = _create_pool_intent(1)
    swap = _swap_intent(4)
    canonical = _settlement(
        [
            (create, FillAction.REJECT),
            (route_low, FillAction.REJECT),
            (route_high, FillAction.REJECT),
            (swap, FillAction.REJECT),
        ],
        [],
    )
    assert type(_derive(canonical, [swap, route_high, create, route_low])) is ExactSettlementIndexV1

    descending = _settlement(
        [
            (create, FillAction.REJECT),
            (route_high, FillAction.REJECT),
            (route_low, FillAction.REJECT),
            (swap, FillAction.REJECT),
        ],
        [],
    )
    _assert_reject(
        _derive(descending, [create, route_low, route_high, swap]),
        "route intents must be settled in ascending intent_id order",
    )

    wrong_phase = _settlement(
        [
            (swap, FillAction.REJECT),
            (route_low, FillAction.REJECT),
        ],
        [],
    )
    _assert_reject(
        _derive(wrong_phase, [swap, route_low]),
        "non-canonical settlement phase order at intent_id="
        f"{route_low.intent_id}: routes require CREATE_POOL before route "
        "before other pool intents",
    )


@pytest.mark.parametrize("invalid_policy", (0, 1, None, "false"))
def test_cow_policy_requires_exact_boolean(invalid_policy: object) -> None:
    intent = _swap_intent(1)
    with pytest.raises(TypeError, match="exact Boolean"):
        derive_exact_settlement_index_admitted_v1(
            snapshot_settlement(_settlement([(intent, FillAction.FILL)], [_fill(intent)])),
            admit_intent_batch([intent]),
            allow_cow_netting=invalid_policy,  # type: ignore[arg-type]
        )


def test_substitution_and_hostile_mutation_are_exposed_by_fresh_derivation() -> None:
    first = _swap_intent(1)
    second = _swap_intent(2)
    index = _derive(
        _settlement([(first, FillAction.FILL)], [_fill(first)]),
        [first],
    )
    assert type(index) is ExactSettlementIndexV1

    object.__setattr__(index.entries[0], "intent", snapshot_intent(second))
    rebuilt = derive_exact_settlement_index_admitted_v1(
        index.settlement,
        index.input_intents,
        allow_cow_netting=index.allow_cow_netting,
    )
    assert type(rebuilt) is ExactSettlementIndexV1
    assert rebuilt != index

    corrupted_input = snapshot_settlement(_settlement([(first, FillAction.FILL)], [_fill(first)]))
    action = corrupted_input.included_intents[0][1]
    object.__setattr__(
        corrupted_input,
        "included_intents",
        ((second.intent_id, action),),
    )
    rejected = derive_exact_settlement_index_admitted_v1(
        corrupted_input,
        index.input_intents,
        allow_cow_netting=False,
    )
    _assert_reject(
        rejected,
        "settlement included_intents mismatch: "
        f"missing=['{first.intent_id}'] extra=['{second.intent_id}']",
    )


def test_index_sink_has_no_recursive_admission_facade() -> None:
    tree = ast.parse(inspect.getsource(settlement_index_module))
    imported_names = {
        alias.name
        for node in ast.walk(tree)
        if isinstance(node, (ast.Import, ast.ImportFrom))
        for alias in node.names
    }
    function_names = {node.name for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)}

    assert "admit_intent_batch" not in imported_names
    assert "snapshot_settlement" not in imported_names
    assert "revalidate_exact_settlement_index_v1" not in function_names
    assert "revalidate_exact_settlement_index_v1" not in settlement_index_module.__all__


def test_mixed_membership_failures_keep_exact_precedence() -> None:
    first = _swap_intent(1)
    second = _swap_intent(2)

    included_and_fill_duplicates = snapshot_settlement(
        _settlement([(first, FillAction.FILL)], [_fill(first)])
    )
    included = included_and_fill_duplicates.included_intents[0]
    fill = included_and_fill_duplicates.fills[0]
    object.__setattr__(
        included_and_fill_duplicates,
        "included_intents",
        (included, included),
    )
    object.__setattr__(included_and_fill_duplicates, "fills", (fill, fill))
    _assert_reject(
        _derive(included_and_fill_duplicates, [first]),
        "settlement included_intents contains duplicate intent_id entries",
    )

    duplicate_and_extra_fills = snapshot_settlement(
        _settlement([(first, FillAction.FILL)], [_fill(first)])
    )
    extra = snapshot_settlement(_settlement([(second, FillAction.FILL)], [_fill(second)])).fills[0]
    object.__setattr__(duplicate_and_extra_fills, "fills", (extra, extra))
    _assert_reject(
        _derive(duplicate_and_extra_fills, [first]),
        "settlement fills contains duplicate intent_id entries",
    )

    extra_and_missing = snapshot_settlement(_settlement([(first, FillAction.FILL)], [_fill(first)]))
    object.__setattr__(extra_and_missing, "fills", (extra,))
    _assert_reject(
        _derive(extra_and_missing, [first]),
        f"settlement fills contains intent_ids not in input intents: ['{second.intent_id}']",
    )

    missing_before_mismatch = snapshot_settlement(
        _settlement(
            [(first, FillAction.FILL), (second, FillAction.FILL)],
            [_fill(first), _fill(second)],
        )
    )
    rejected_second = snapshot_settlement(
        _settlement(
            [(second, FillAction.REJECT)],
            [_fill(second, action=FillAction.REJECT, reason="NO")],
        )
    ).fills[0]
    object.__setattr__(missing_before_mismatch, "fills", (rejected_second,))
    _assert_reject(
        _derive(missing_before_mismatch, [first, second]),
        f"missing Fill for filled intent_id: {first.intent_id}",
    )


def test_cow_missing_required_min_amount_out_rejects_without_defaulting() -> None:
    first = snapshot_intent(_swap_intent(1, amount_in=100, minimum_out=0))
    second = snapshot_intent(
        _swap_intent(
            2,
            asset_in=ASSET_B,
            asset_out=ASSET_A,
            amount_in=50,
            minimum_out=0,
        )
    )
    without_minimum = tuple(entry for entry in first.fields.entries if entry[0] != "min_amount_out")
    object.__setattr__(first.fields, "_entries", without_minimum)
    object.__setattr__(
        first.fields,
        "_index",
        MappingProxyType(dict(without_minimum)),
    )
    settlement = snapshot_settlement(
        _settlement(
            [
                (_swap_intent(1, amount_in=100, minimum_out=0), FillAction.FILL),
                (
                    _swap_intent(
                        2,
                        asset_in=ASSET_B,
                        asset_out=ASSET_A,
                        amount_in=50,
                        minimum_out=0,
                    ),
                    FillAction.FILL,
                ),
            ],
            [
                _fill(
                    _swap_intent(1, amount_in=100, minimum_out=0),
                    reason="COW_NETTED",
                    amount_in=100,
                    amount_out=50,
                    fee_paid=0,
                ),
                _fill(
                    _swap_intent(
                        2,
                        asset_in=ASSET_B,
                        asset_out=ASSET_A,
                        amount_in=50,
                        minimum_out=0,
                    ),
                    reason="COW_NETTED",
                    amount_in=50,
                    amount_out=100,
                    fee_paid=0,
                ),
            ],
        )
    )
    rejected = derive_exact_settlement_index_admitted_v1(
        settlement,
        (first, second),
        allow_cow_netting=True,
    )
    assert type(rejected) is ExactSettlementIndexRejectV1
    assert rejected.reason == f"invalid min_amount_out for intent_id={first.intent_id}"

    with_none = snapshot_intent(_swap_intent(1, amount_in=100, minimum_out=0))
    none_entries = tuple(
        (name, None if name == "min_amount_out" else value)
        for name, value in with_none.fields.entries
    )
    object.__setattr__(with_none.fields, "_entries", none_entries)
    object.__setattr__(
        with_none.fields,
        "_index",
        MappingProxyType(dict(none_entries)),
    )
    rejected = derive_exact_settlement_index_admitted_v1(
        settlement,
        (with_none, second),
        allow_cow_netting=True,
    )
    _assert_reject(
        rejected,
        f"invalid min_amount_out for intent_id={with_none.intent_id}",
    )
