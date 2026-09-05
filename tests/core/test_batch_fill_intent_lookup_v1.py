"""Frozen parity controls for accepted-fill intent resolution."""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

import pytest

import src.core.batch_clearing as batch_clearing_module
import src.core.batch_clearing_compute as compute_module
from src.core.settlement import Fill, FillAction
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

_POOL_ID = "pool-fill-intent-lookup"
_POLICY = compute_module._SettlementPolicy(
    swap_ordering="greedy_ab_refined",
    protocol_fee_share_bps=0,
    protocol_fee_recipient_pubkey=None,
)
_Phase = Callable[..., None]
_ClearFn = Callable[..., list[Fill]]
_ApplyFn = Callable[..., None]


def _iid(index: int) -> str:
    return "0x" + f"{index:064x}"


def _intent(index: int, sender: str) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(index),
        sender_pubkey=sender,
        deadline=9_999_999_999,
        fields={"pool_id": _POOL_ID},
    )


def _new_state() -> compute_module._SettlementExecutionState:
    pool = PoolState(
        pool_id=_POOL_ID,
        asset0="A",
        asset1="B",
        reserve0=100,
        reserve1=100,
        fee_bps=30,
        lp_supply=100,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    return compute_module._SettlementExecutionState(
        pool_states={_POOL_ID: pool},
        balances=BalanceTable(),
        lp_balances=LPTable(),
        buffers=compute_module._new_settlement_buffers(),
    )


def _unused_factory(*_args: object, **_kwargs: object) -> object:
    raise AssertionError("unused factory was called")


def _unused_apply(*_args: object, **_kwargs: object) -> None:
    raise AssertionError("unused application hook was called")


def _factories(
    clear_fn: _ClearFn, apply_fn: _ApplyFn
) -> compute_module._SettlementComputeFactories:
    return compute_module._SettlementComputeFactories(
        copy_balance_table_fn=lambda value: value,
        copy_lp_table_fn=lambda value: value,
        try_create_pool_fn=_unused_factory,
        apply_create_pool_to_locals_fn=_unused_factory,
        clear_batch_single_pool_fn=clear_fn,
        apply_filled_intent_to_locals_fn=apply_fn,
    )


def _observe(state: compute_module._SettlementExecutionState) -> tuple[object, ...]:
    pool = state.pool_states[_POOL_ID]
    return (
        tuple((fill.intent_id, fill.action, fill.reason) for fill in state.buffers.fills),
        tuple(state.buffers.included_intents),
        tuple(
            (delta.pubkey, delta.asset, delta.delta_add, delta.delta_sub)
            for delta in state.buffers.balance_deltas
        ),
        tuple(
            (delta.pool_id, delta.asset, delta.delta_add, delta.delta_sub)
            for delta in state.buffers.reserve_deltas
        ),
        tuple(
            (delta.pubkey, delta.pool_id, delta.delta_add, delta.delta_sub)
            for delta in state.buffers.lp_deltas
        ),
        tuple(state.buffers.events),
        (pool.reserve0, pool.reserve1, pool.lp_supply),
    )


def _legacy_process_pool_intent_phase(
    state: compute_module._SettlementExecutionState,
    intents_by_pool: dict[str, list[Intent]],
    *,
    policy: compute_module._SettlementPolicy,
    factories: compute_module._SettlementComputeFactories,
) -> None:
    """Frozen pre-change oracle for the affected phase only."""

    for pool_id in sorted(intents_by_pool.keys()):
        pool_intents = intents_by_pool[pool_id]
        if pool_id not in state.pool_states:
            for intent in pool_intents:
                state.buffers.included_intents.append((intent.intent_id, FillAction.REJECT))
                state.buffers.fills.append(
                    Fill(
                        intent_id=intent.intent_id,
                        action=FillAction.REJECT,
                        reason="POOL_NOT_FOUND",
                    )
                )
            continue

        pool_state = state.pool_states[pool_id]
        fills = factories.clear_batch_single_pool_fn(
            pool_intents,
            pool_state,
            state.balances,
            state.lp_balances,
            swap_ordering=policy.swap_ordering,
            protocol_fee_share_bps=policy.protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=policy.protocol_fee_recipient_pubkey,
            swap_tiebreak_seed=policy.swap_tiebreak_seed,
        )
        for fill in fills:
            state.buffers.fills.append(fill)
            state.buffers.included_intents.append((fill.intent_id, fill.action))
            if fill.action != FillAction.FILL:
                continue
            intent = next(
                candidate for candidate in pool_intents if candidate.intent_id == fill.intent_id
            )
            factories.apply_filled_intent_to_locals_fn(
                intent=intent,
                fill=fill,
                pool_id=pool_id,
                pool_state=pool_state,
                balances=state.balances,
                lp_balances=state.lp_balances,
                balance_deltas=state.buffers.balance_deltas,
                reserve_deltas=state.buffers.reserve_deltas,
                lp_deltas=state.buffers.lp_deltas,
                protocol_fee_recipient_pubkey=policy.protocol_fee_recipient_pubkey,
            )
        state.pool_states[pool_id] = pool_state


def _run_phase(
    phase: _Phase,
    intents: list[Intent],
    clear_fn: _ClearFn,
    apply_fn: _ApplyFn,
) -> tuple[object, ...]:
    state = _new_state()
    phase(
        state,
        {_POOL_ID: intents},
        policy=_POLICY,
        factories=_factories(clear_fn, apply_fn),
    )
    return _observe(state)


def _owned_inputs(count: int) -> tuple[list[Intent], list[Fill]]:
    intents = [_intent(index + 1, f"sender-{index + 1}") for index in range(count)]
    fills = [
        Fill(intent_id=intent.intent_id, action=FillAction.FILL) for intent in reversed(intents)
    ]
    return intents, fills


def _run_owned_phase(phase: _Phase, count: int) -> tuple[object, ...]:
    intents, fills = _owned_inputs(count)

    def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
        return fills

    return _run_phase(
        phase,
        intents,
        clear_fn,
        batch_clearing_module._apply_filled_intent_to_locals,
    )


@pytest.mark.parametrize("count", (1, 4, 32))
def test_owned_plain_fills_match_frozen_legacy_phase(count: int) -> None:
    assert _run_owned_phase(
        compute_module._process_pool_intent_phase,
        count,
    ) == _run_owned_phase(_legacy_process_pool_intent_phase, count)


def test_duplicate_intent_id_preserves_first_match_selection() -> None:
    first = _intent(1, "first-winner")
    duplicate = _intent(1, "duplicate-loser")
    later = _intent(2, "later")
    fills = [
        Fill(intent_id=later.intent_id, action=FillAction.FILL),
        Fill(intent_id=first.intent_id, action=FillAction.FILL),
    ]

    def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
        return fills

    expected = _run_phase(
        _legacy_process_pool_intent_phase,
        [first, duplicate, later],
        clear_fn,
        batch_clearing_module._apply_filled_intent_to_locals,
    )

    observed = _run_phase(
        compute_module._process_pool_intent_phase,
        [first, duplicate, later],
        clear_fn,
        batch_clearing_module._apply_filled_intent_to_locals,
    )

    assert observed == expected
    balance_deltas = cast(tuple[tuple[str, str, int, int], ...], observed[2])
    assert balance_deltas[2][0] == "first-winner"


def test_missing_owned_fill_id_preserves_legacy_stop_iteration_and_prior_buffers() -> None:
    def run(phase: _Phase) -> tuple[type[BaseException], str, tuple[object, ...]]:
        intents = [_intent(1, "known")]
        fills = [Fill(intent_id=_iid(999), action=FillAction.FILL)]

        def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
            return fills

        state = _new_state()
        try:
            phase(
                state,
                {_POOL_ID: intents},
                policy=_POLICY,
                factories=_factories(
                    clear_fn,
                    batch_clearing_module._apply_filled_intent_to_locals,
                ),
            )
        except BaseException as exc:
            return type(exc), str(exc), _observe(state)
        raise AssertionError("missing fill identifier unexpectedly resolved")

    observed = run(compute_module._process_pool_intent_phase)
    expected = run(_legacy_process_pool_intent_phase)

    assert observed == expected
    assert observed[0] is StopIteration
    assert observed[1] == ""


def test_rejected_only_fills_leave_unused_intents_unread() -> None:
    class ExplodingIntent:
        @property
        def intent_id(self) -> str:
            raise AssertionError("rejected-only path read an unused intent identifier")

    fill = Fill(intent_id=_iid(1), action=FillAction.REJECT, reason="REJECTED")

    def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
        return [fill]

    observed = _run_phase(
        compute_module._process_pool_intent_phase,
        [ExplodingIntent()],
        clear_fn,
        _unused_apply,
    )
    expected = _run_phase(
        _legacy_process_pool_intent_phase,
        [ExplodingIntent()],
        clear_fn,
        _unused_apply,
    )

    assert observed == expected
    assert observed[0] == ((fill.intent_id, FillAction.REJECT, "REJECTED"),)
    assert observed[1] == ((fill.intent_id, FillAction.REJECT),)


def test_subclassed_intent_identifier_falls_back_to_frozen_equality_order() -> None:
    class TracingText(str):
        calls: list[str] = []

        def __eq__(self, other: object) -> bool:
            type(self).calls.append(str(other))
            return str.__eq__(self, other)

        __hash__ = str.__hash__

    def run(phase: _Phase) -> tuple[tuple[object, ...], list[str]]:
        TracingText.calls = []
        intent = _intent(1, "subclassed-id")
        object.__setattr__(intent, "intent_id", TracingText(intent.intent_id))
        fill = Fill(intent_id=_iid(1), action=FillAction.FILL)

        def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
            return [fill]

        observed = _run_phase(
            phase,
            [intent],
            clear_fn,
            batch_clearing_module._apply_filled_intent_to_locals,
        )
        return observed, list(TracingText.calls)

    observed, observed_calls = run(compute_module._process_pool_intent_phase)
    expected, expected_calls = run(_legacy_process_pool_intent_phase)

    assert observed == expected
    assert observed_calls == expected_calls == [_iid(1)]


def test_malformed_fill_identifier_falls_back_without_hashing_the_identifier() -> None:
    class AlwaysMatchingIdentifier:
        calls: list[str] = []

        def __eq__(self, other: object) -> bool:
            type(self).calls.append(str(other))
            return True

        def __hash__(self) -> int:
            raise AssertionError("malformed fill identifier was hashed")

    def run(phase: _Phase) -> tuple[tuple[str, ...], list[str]]:
        AlwaysMatchingIdentifier.calls = []
        intent = _intent(1, "malformed-fill")
        fill = Fill(
            intent_id=cast(str, AlwaysMatchingIdentifier()),
            action=FillAction.FILL,
        )

        def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
            return [fill]

        observed = _run_phase(
            phase,
            [intent],
            clear_fn,
            batch_clearing_module._apply_filled_intent_to_locals,
        )
        balance_deltas = cast(tuple[tuple[str, str, int, int], ...], observed[2])
        return tuple(delta[0] for delta in balance_deltas), list(AlwaysMatchingIdentifier.calls)

    observed, observed_calls = run(compute_module._process_pool_intent_phase)
    expected, expected_calls = run(_legacy_process_pool_intent_phase)

    assert observed == expected == ("malformed-fill", "malformed-fill")
    assert observed_calls == expected_calls == [_iid(1)]


def test_fill_subclass_preserves_frozen_legacy_lookup_contract() -> None:
    class DerivedFill(Fill):
        pass

    intent = _intent(1, "derived-fill")
    fill = DerivedFill(intent_id=intent.intent_id, action=FillAction.FILL)

    def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
        return [fill]

    observed = _run_phase(
        compute_module._process_pool_intent_phase,
        [intent],
        clear_fn,
        batch_clearing_module._apply_filled_intent_to_locals,
    )
    expected = _run_phase(
        _legacy_process_pool_intent_phase,
        [intent],
        clear_fn,
        batch_clearing_module._apply_filled_intent_to_locals,
    )

    assert observed == expected


def _run_mutating_apply_callback(phase: _Phase) -> tuple[object, ...]:
    first = _intent(1, "first")
    stale = _intent(2, "stale")
    replacement = _intent(2, "replacement")
    intents = [first, stale]
    fills = [
        Fill(intent_id=first.intent_id, action=FillAction.FILL),
        Fill(intent_id=stale.intent_id, action=FillAction.FILL),
    ]
    state = _new_state()

    def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
        return fills

    def mutating_apply(**kwargs: object) -> None:
        intent = cast(Intent, kwargs["intent"])
        fill = cast(Fill, kwargs["fill"])
        state.buffers.events.append({"sender": intent.sender_pubkey, "fill_id": fill.intent_id})
        if fill.intent_id == first.intent_id:
            intents[1] = replacement

    phase(
        state,
        {_POOL_ID: intents},
        policy=_POLICY,
        factories=_factories(clear_fn, mutating_apply),
    )
    return _observe(state)


def test_generic_application_callback_mutation_preserves_legacy_state_and_event_order() -> None:
    observed = _run_mutating_apply_callback(compute_module._process_pool_intent_phase)
    expected = _run_mutating_apply_callback(_legacy_process_pool_intent_phase)

    assert observed == expected
    assert observed[5] == (
        {"sender": "first", "fill_id": _iid(1)},
        {"sender": "replacement", "fill_id": _iid(2)},
    )


def test_exact_fill_action_hook_mutation_keeps_later_lookup_on_legacy_contract() -> None:
    class MutatingRejectAction:
        def __init__(self, mutate_pool_intents: Callable[[], None]) -> None:
            self._mutate_pool_intents = mutate_pool_intents

        def __ne__(self, other: object) -> bool:
            assert other is FillAction.FILL
            self._mutate_pool_intents()
            return True

        def __eq__(self, other: object) -> bool:
            return type(self) is type(other)

    def run(phase: _Phase) -> tuple[object, ...]:
        first = _intent(1, "first")
        stale = _intent(2, "stale")
        replacement = _intent(2, "replacement")
        intents = [first, stale]

        def replace_stale_intent() -> None:
            intents[1] = replacement

        fills = [
            Fill(intent_id=first.intent_id, action=FillAction.FILL),
            Fill(
                intent_id=first.intent_id,
                action=cast(FillAction, MutatingRejectAction(replace_stale_intent)),
                reason="MUTATING_REJECT",
            ),
            Fill(intent_id=stale.intent_id, action=FillAction.FILL),
        ]

        def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
            return fills

        return _run_phase(
            phase,
            intents,
            clear_fn,
            batch_clearing_module._apply_filled_intent_to_locals,
        )

    observed = run(compute_module._process_pool_intent_phase)
    expected = run(_legacy_process_pool_intent_phase)

    assert observed == expected
    balance_deltas = cast(tuple[tuple[str, str, int, int], ...], observed[2])
    assert balance_deltas[-1][0] == "replacement"


def test_monkeypatched_apply_callback_identity_does_not_authorize_retained_index(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def run(phase: _Phase) -> tuple[tuple[object, ...], list[str]]:
        first = _intent(1, "first")
        stale = _intent(2, "stale")
        replacement = _intent(2, "replacement")
        intents = [first, stale]
        selected_senders: list[str] = []
        fills = [
            Fill(intent_id=first.intent_id, action=FillAction.FILL),
            Fill(intent_id=stale.intent_id, action=FillAction.FILL),
        ]

        def clear_fn(*_args: object, **_kwargs: object) -> list[Fill]:
            return fills

        def mutating_apply(**kwargs: object) -> None:
            intent = cast(Intent, kwargs["intent"])
            selected_senders.append(intent.sender_pubkey)
            if intent.intent_id == first.intent_id:
                intents[1] = replacement

        monkeypatch.setattr(
            batch_clearing_module,
            "_apply_filled_intent_to_locals",
            mutating_apply,
        )
        return (
            _run_phase(
                phase,
                intents,
                clear_fn,
                batch_clearing_module._apply_filled_intent_to_locals,
            ),
            selected_senders,
        )

    observed = run(compute_module._process_pool_intent_phase)
    expected = run(_legacy_process_pool_intent_phase)

    assert observed == expected
    assert observed[1] == ["first", "replacement"]


def test_clear_callback_mutation_preserves_legacy_lookup() -> None:
    original = _intent(1, "original")
    replacement = _intent(1, "replacement")
    fill = Fill(intent_id=replacement.intent_id, action=FillAction.FILL)

    def clear_fn(pool_intents: list[Intent], *_args: object, **_kwargs: object) -> list[Fill]:
        pool_intents[:] = [replacement]
        return [fill]

    expected = _run_phase(
        _legacy_process_pool_intent_phase,
        [original],
        clear_fn,
        batch_clearing_module._apply_filled_intent_to_locals,
    )

    observed = _run_phase(
        compute_module._process_pool_intent_phase,
        [original],
        clear_fn,
        batch_clearing_module._apply_filled_intent_to_locals,
    )

    assert observed == expected
    balance_deltas = cast(tuple[tuple[str, str, int, int], ...], observed[2])
    assert balance_deltas[0][0] == "replacement"
