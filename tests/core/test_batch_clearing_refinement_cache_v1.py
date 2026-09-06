"""Exact parity of the cached adjacent-swap B refiner (candidate v1, not a policy change).

Obligation: ``refine_b_ordering_with_simulator`` bound to the real reserve simulator returns the
same intent objects in the same positions as the unchanged generic refiner
``refine_b_ordering_with_eval`` driven by the unchanged evaluator ``_eval_ordering_ab``, on every
fixture below, with never more simulator calls. The unchanged slow path is the independent
reference (oracle grade 3: an independent executable model inside the repo); a hand-computed
fee-free fixture pins the full-resimulation counterexample and kills the unconditional-reuse
mutant (oracle grade 2: fixed vector).

Nonclaims: no optimality claim, no default policy or cap change, no universal asymptotic
improvement; wall-clock time is never asserted.
"""

from __future__ import annotations

import dataclasses
import itertools
import random
from enum import Enum
from typing import Callable

import pytest

import src.core.batch_clearing_mci_ordering as mci_ordering
import src.core.batch_clearing_ordering as batch_clearing_ordering
from src.core.batch_clearing import compute_settlement, validate_settlement
from src.core.batch_clearing_mci_ordering import (
    refine_b_ordering_with_eval,
    refine_b_ordering_with_simulator,
)
from src.core.liquidity import create_pool
from src.core.settlement import FillAction, Settlement
from src.integration.dex_engine import _settlement_commitment_dict
from src.state.balances import BalanceTable
from src.state.canonical import canonical_json_bytes
from src.state.intents import Intent, IntentKind
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus

ASSET0 = "A"
ASSET1 = "B"
POOL_ID = "pool_ab"
HEX_ASSET0 = "0x" + "01" * 32
HEX_ASSET1 = "0x" + "02" * 32

# Unchanged production functions captured at import time: the slow reference must not depend on
# any monkeypatch a test installs later.
_REAL_SIMULATE = batch_clearing_ordering._simulate_swap_reserves
_REAL_EVAL = batch_clearing_ordering._eval_ordering_ab


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


def _sender(n: int) -> str:
    return "0x" + f"{n:02x}" * 48


def _make_pool(reserve0: int, reserve1: int, fee_bps: int) -> PoolState:
    return PoolState(
        pool_id=POOL_ID,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1_000_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _make_intent(
    idx: int,
    *,
    amount_in: int,
    min_amount_out: int,
    sender_id: int = 1,
    asset_in: str = ASSET0,
    asset_out: str = ASSET1,
    kind: IntentKind = IntentKind.SWAP_EXACT_IN,
) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        intent_id=_iid(idx),
        sender_pubkey=_sender(sender_id),
        kind=kind,
        deadline=9_999_999_999,
        fields={
            "pool_id": POOL_ID,
            "asset_in": asset_in,
            "asset_out": asset_out,
            "amount_in": amount_in,
            "min_amount_out": min_amount_out,
        },
    )


def _quote_out(
    pool: PoolState,
    reserves: tuple[int, int],
    amount_in: int,
    *,
    asset_in: str = ASSET0,
    asset_out: str = ASSET1,
) -> int:
    """Executed amount_out for ``amount_in`` at ``reserves`` (0 when not executable)."""
    probe = _make_intent(0, amount_in=amount_in, min_amount_out=0, asset_in=asset_in, asset_out=asset_out)
    a, surplus, _ = _REAL_SIMULATE(probe, pool, reserves)
    return surplus if a > 0 else 0


def _reserves(pool: PoolState) -> tuple[int, int]:
    return (pool.reserve0, pool.reserve1)


def _reference_refine(ordering: list[Intent], pool: PoolState, reserves: tuple[int, int]) -> list[Intent]:
    """Unchanged slow path: generic refiner + unchanged full evaluator."""
    return refine_b_ordering_with_eval(
        ordering,
        pool_state=pool,
        reserves=reserves,
        eval_ordering_ab_fn=_REAL_EVAL,
    )


def _cached_refine(ordering: list[Intent], pool: PoolState, reserves: tuple[int, int]) -> list[Intent]:
    return refine_b_ordering_with_simulator(
        ordering,
        pool_state=pool,
        reserves=reserves,
        simulate_swap_fn=_REAL_SIMULATE,
    )


def _ids(ordering: list[Intent]) -> list[str]:
    return [intent.intent_id for intent in ordering]


def _assert_same_objects(actual: list[Intent], expected: list[Intent]) -> None:
    assert _ids(actual) == _ids(expected)
    assert all(left is right for left, right in zip(actual, expected, strict=True))


def _intent_value_snapshot(intent: Intent) -> dict[str, object]:
    snapshot = dataclasses.asdict(intent)
    snapshot["fields"] = intent.to_wire_fields()
    return snapshot


def _capture_input_snapshot(
    ordering: list[Intent], pool: PoolState
) -> tuple[list[Intent], dict[str, object], tuple[dict[str, object], ...]]:
    return (
        list(ordering),
        dataclasses.asdict(pool),
        tuple(_intent_value_snapshot(intent) for intent in ordering),
    )


def _assert_input_unchanged(
    ordering: list[Intent],
    pool: PoolState,
    snapshot: tuple[list[Intent], dict[str, object], tuple[dict[str, object], ...]],
) -> None:
    original_ordering, original_pool, original_intents = snapshot
    _assert_same_objects(ordering, original_ordering)
    assert dataclasses.asdict(pool) == original_pool, "pool input values mutated"
    assert tuple(_intent_value_snapshot(intent) for intent in ordering) == original_intents, (
        "intent input values mutated"
    )


_Simulator = Callable[[Intent, PoolState, tuple[int, int]], tuple[int, int, tuple[int, int]]]


def _evaluate_with_simulator(
    ordering: list[Intent],
    pool_state: PoolState,
    reserves: tuple[int, int],
    *,
    simulate_swap_fn: _Simulator,
) -> tuple[int, int]:
    """Independent generic evaluator used only for pure simulator exception parity tests."""
    total_a = 0
    total_b = 0
    current_reserves = reserves
    for intent in ordering:
        a, b, new_reserves = simulate_swap_fn(intent, pool_state, current_reserves)
        if a > 0:
            total_a += a
            total_b += b
            current_reserves = new_reserves
    return total_a, total_b


def _capture_exception(run: Callable[[], object]) -> tuple[type[Exception], tuple[object, ...], str]:
    try:
        run()
    except Exception as exc:
        return type(exc), exc.args, str(exc)
    raise AssertionError("expected the refinement call to raise")


def _assert_pure_simulator_exception_parity(
    ordering: list[Intent],
    pool: PoolState,
    reserves: tuple[int, int],
    simulate_swap_fn: _Simulator,
    *,
    expected_message: str,
) -> None:
    original_snapshot = _capture_input_snapshot(ordering, pool)
    original_reserves = reserves

    cached_exception = _capture_exception(
        lambda: refine_b_ordering_with_simulator(
            ordering,
            pool_state=pool,
            reserves=reserves,
            simulate_swap_fn=simulate_swap_fn,
        )
    )
    _assert_input_unchanged(ordering, pool, original_snapshot)
    assert reserves == original_reserves

    generic_exception = _capture_exception(
        lambda: refine_b_ordering_with_eval(
            ordering,
            pool_state=pool,
            reserves=reserves,
            eval_ordering_ab_fn=lambda candidate, candidate_pool, candidate_reserves: _evaluate_with_simulator(
                candidate,
                candidate_pool,
                candidate_reserves,
                simulate_swap_fn=simulate_swap_fn,
            ),
        )
    )
    _assert_input_unchanged(ordering, pool, original_snapshot)
    assert reserves == original_reserves

    assert cached_exception == generic_exception
    assert cached_exception == (ValueError, (expected_message,), expected_message)


def test_input_snapshot_oracle_detects_nested_intent_mutation() -> None:
    pool = _make_pool(10_000, 10_000, 30)
    first = _make_intent(9, amount_in=100, min_amount_out=0)
    second = _make_intent(10, amount_in=200, min_amount_out=0)
    ordering = [first, second]
    snapshot = _capture_input_snapshot(ordering, pool)

    def _mutating_simulator(
        intent: Intent, _pool_state: PoolState, reserves: tuple[int, int]
    ) -> tuple[int, int, tuple[int, int]]:
        if intent is first:
            mutated = intent.with_field("nested", {"value": 99})
            object.__setattr__(intent, "fields", mutated.fields)
        return 0, 0, reserves

    # This deterministic simulator satisfies the pure-function shape except for caller
    # preservation. The independent snapshot oracle must expose that separate violation.
    refine_b_ordering_with_simulator(
        ordering,
        pool_state=pool,
        reserves=(100, 100),
        simulate_swap_fn=_mutating_simulator,
    )
    with pytest.raises(AssertionError, match="intent input values mutated"):
        _assert_input_unchanged(ordering, pool, snapshot)


def test_pure_simulator_exception_parity_in_initial_prefix_fold() -> None:
    pool = _make_pool(10_000, 10_000, 30)
    first = _make_intent(0, amount_in=100, min_amount_out=0)
    failing = _make_intent(1, amount_in=200, min_amount_out=0)
    tail = _make_intent(2, amount_in=300, min_amount_out=0)
    ordering = [first, failing, tail]
    reserves = (100, 100)
    expected_message = f"initial-fold:{failing.intent_id}:reserves={(101, 100)}"

    def _simulate(
        intent: Intent, _pool_state: PoolState, current_reserves: tuple[int, int]
    ) -> tuple[int, int, tuple[int, int]]:
        if intent.intent_id == failing.intent_id and current_reserves == (101, 100):
            raise ValueError(expected_message)
        return 1, 2, (current_reserves[0] + 1, current_reserves[1])

    _assert_pure_simulator_exception_parity(
        ordering,
        pool,
        reserves,
        _simulate,
        expected_message=expected_message,
    )


def test_pure_simulator_exception_parity_in_swapped_pair() -> None:
    pool = _make_pool(10_000, 10_000, 30)
    first = _make_intent(3, amount_in=100, min_amount_out=0)
    failing = _make_intent(4, amount_in=200, min_amount_out=0)
    tail = _make_intent(5, amount_in=300, min_amount_out=0)
    ordering = [first, failing, tail]
    reserves = (100, 100)
    expected_message = f"swapped-pair:{failing.intent_id}:reserves={reserves}"

    def _simulate(
        intent: Intent, _pool_state: PoolState, current_reserves: tuple[int, int]
    ) -> tuple[int, int, tuple[int, int]]:
        if intent.intent_id == failing.intent_id and current_reserves == reserves:
            raise ValueError(expected_message)
        return 1, 2, (current_reserves[0] + 1, current_reserves[1])

    _assert_pure_simulator_exception_parity(
        ordering,
        pool,
        reserves,
        _simulate,
        expected_message=expected_message,
    )


def test_pure_simulator_exception_parity_in_recomputed_suffix() -> None:
    pool = _make_pool(10_000, 10_000, 30)
    first = _make_intent(6, amount_in=100, min_amount_out=0)
    second = _make_intent(7, amount_in=200, min_amount_out=0)
    failing = _make_intent(8, amount_in=300, min_amount_out=0)
    ordering = [first, second, failing]
    reserves = (100, 100)
    recomputed_reserves = (201, 100)
    expected_message = f"recomputed-suffix:{failing.intent_id}:reserves={recomputed_reserves}"

    def _simulate(
        intent: Intent, _pool_state: PoolState, current_reserves: tuple[int, int]
    ) -> tuple[int, int, tuple[int, int]]:
        if intent.intent_id == failing.intent_id and current_reserves == recomputed_reserves:
            raise ValueError(expected_message)
        if intent.intent_id == first.intent_id:
            return 1, 2, (current_reserves[0] + 1, current_reserves[1])
        if intent.intent_id == second.intent_id:
            return 1, 2, (current_reserves[0] * 2, current_reserves[1])
        return 1, 2, (current_reserves[0] + 1, current_reserves[1])

    _assert_pure_simulator_exception_parity(
        ordering,
        pool,
        reserves,
        _simulate,
        expected_message=expected_message,
    )


def _counterexample_fixture() -> tuple[PoolState, list[Intent]]:
    """Fee-free pool (1000, 1000); hand-computed CPMM floors.

    x: 1000 in -> 500 out from fresh reserves.
    y: 500 in, min_out 333 = its fresh quote; after x it would get 100 and fail.
    z: 1000 in, min_out 150; gets 166 after x alone, only 114 after y then x.
    """
    pool = _make_pool(1_000, 1_000, 0)
    x = _make_intent(0, amount_in=1_000, min_amount_out=0)
    y = _make_intent(1, amount_in=500, min_amount_out=333)
    z = _make_intent(2, amount_in=1_000, min_amount_out=150)
    return pool, [x, y, z]


def _accepted_swap_fixture() -> tuple[PoolState, list[Intent]]:
    """Fee-free pool (1000, 1000): p fills only when first, so [q, p] -> [p, q] raises A."""
    pool = _make_pool(1_000, 1_000, 0)
    q = _make_intent(0, amount_in=500, min_amount_out=0)
    p = _make_intent(1, amount_in=200, min_amount_out=166)
    return pool, [q, p]


def _fixture_catalogue() -> list[tuple[str, PoolState, list[Intent]]]:
    fixtures: list[tuple[str, PoolState, list[Intent]]] = []

    pool = _make_pool(2_000_000, 1_000_000, 30)
    fixtures.append(
        (
            "all_fill_fee30",
            pool,
            [
                _make_intent(0, amount_in=500, min_amount_out=1),
                _make_intent(1, amount_in=1_700, min_amount_out=1, sender_id=2),
                _make_intent(2, amount_in=2_900, min_amount_out=1, sender_id=3),
                _make_intent(3, amount_in=800, min_amount_out=1),
                _make_intent(4, amount_in=4_100, min_amount_out=1, sender_id=2),
            ],
        )
    )

    pool = _make_pool(1_000_000, 1_000_000, 30)
    binding: list[Intent] = []
    for idx, amount in enumerate([20_000, 35_000, 12_500, 50_000, 8_000]):
        fresh_out = _quote_out(pool, _reserves(pool), amount)
        binding.append(
            _make_intent(
                idx,
                amount_in=amount,
                min_amount_out=fresh_out - (idx * 37) % 300,
                sender_id=idx % 2 + 1,
            )
        )
    fixtures.append(("binding_min_out_fee30", pool, binding))

    pool = _make_pool(1_000, 1_000, 0)
    fixtures.append(
        (
            "fee_zero_dust_and_zero_amount",
            pool,
            [
                _make_intent(0, amount_in=1, min_amount_out=0),
                _make_intent(1, amount_in=0, min_amount_out=0),
                _make_intent(2, amount_in=300, min_amount_out=0),
                _make_intent(3, amount_in=250, min_amount_out=100),
                _make_intent(4, amount_in=5, min_amount_out=0),
            ],
        )
    )

    pool = _make_pool(50_000, 50_000, 10_000)
    fixtures.append(
        (
            "fee_100_percent_nothing_executable",
            pool,
            [_make_intent(idx, amount_in=1_000 + idx, min_amount_out=0) for idx in range(4)],
        )
    )

    pool = _make_pool(500_000, 2_000_000, 30)
    reverse: list[Intent] = []
    for idx, amount in enumerate([10_000, 40_000, 25_000, 60_000, 15_000]):
        fresh_out = _quote_out(pool, _reserves(pool), amount, asset_in=ASSET1, asset_out=ASSET0)
        min_out = fresh_out - idx if idx % 2 == 0 else 1
        reverse.append(
            _make_intent(
                idx,
                amount_in=amount,
                min_amount_out=min_out,
                sender_id=idx % 3 + 1,
                asset_in=ASSET1,
                asset_out=ASSET0,
            )
        )
    fixtures.append(("reverse_direction_asymmetric_pool", pool, reverse))

    pool = _make_pool(1_000_000, 1_000_000, 30)
    fresh_reverse = _quote_out(pool, _reserves(pool), 30_000, asset_in=ASSET1, asset_out=ASSET0)
    fresh_forward = _quote_out(pool, _reserves(pool), 12_000)
    fixtures.append(
        (
            "mixed_direction",
            pool,
            [
                _make_intent(0, amount_in=30_000, min_amount_out=1),
                _make_intent(
                    1,
                    amount_in=30_000,
                    min_amount_out=fresh_reverse,
                    asset_in=ASSET1,
                    asset_out=ASSET0,
                ),
                _make_intent(2, amount_in=12_000, min_amount_out=fresh_forward - 10),
                _make_intent(3, amount_in=45_000, min_amount_out=1, asset_in=ASSET1, asset_out=ASSET0),
                _make_intent(4, amount_in=5_000, min_amount_out=0),
            ],
        )
    )

    pool = _make_pool(3_000_000, 3_000_000, 30)
    shared = _make_intent(7, amount_in=9_000, min_amount_out=1)
    twin = _make_intent(7, amount_in=9_500, min_amount_out=_quote_out(pool, _reserves(pool), 9_500) - 5)
    assert shared.intent_id == twin.intent_id and shared is not twin
    fixtures.append(
        (
            "repeated_senders_duplicate_ids_and_repeated_object",
            pool,
            [
                shared,
                twin,
                _make_intent(8, amount_in=20_000, min_amount_out=1, sender_id=1),
                shared,
                _make_intent(9, amount_in=4_000, min_amount_out=_quote_out(pool, _reserves(pool), 4_000)),
            ],
        )
    )

    pool = _make_pool(800_000, 1_200_000, 30)
    fixtures.append(
        (
            "exact_out_foreign_and_same_asset_contribute_nothing",
            pool,
            [
                _make_intent(0, amount_in=10_000, min_amount_out=1, kind=IntentKind.SWAP_EXACT_OUT),
                _make_intent(1, amount_in=10_000, min_amount_out=1, asset_in="C"),
                _make_intent(2, amount_in=10_000, min_amount_out=1, asset_out=ASSET0),
                _make_intent(3, amount_in=25_000, min_amount_out=_quote_out(pool, _reserves(pool), 25_000)),
                _make_intent(4, amount_in=6_000, min_amount_out=1),
            ],
        )
    )

    pool = _make_pool(1_000_000, 1_000_000, 30)
    fixtures.append(
        (
            "impossible_min_out_except_one",
            pool,
            [_make_intent(idx, amount_in=10_000 + idx, min_amount_out=2 * (10_000 + idx)) for idx in range(4)]
            + [_make_intent(4, amount_in=7_000, min_amount_out=1)],
        )
    )

    pool = _make_pool(1_000_003, 999_997, 30)
    fixtures.append(
        (
            "rounding_atoms_all_fill_n6",
            pool,
            [
                _make_intent(idx, amount_in=amount, min_amount_out=1, sender_id=idx % 2 + 1)
                for idx, amount in enumerate([1_001, 1_002, 1_003, 999, 1_000, 1_004])
            ],
        )
    )

    pool = _make_pool(750_000, 1_500_000, 5)
    binding6: list[Intent] = []
    for idx, amount in enumerate([9_000, 21_000, 4_500, 33_000, 14_000, 2_500]):
        fresh_out = _quote_out(pool, _reserves(pool), amount)
        binding6.append(
            _make_intent(idx, amount_in=amount, min_amount_out=fresh_out - (idx * 19) % 90, sender_id=idx % 3 + 1)
        )
    fixtures.append(("binding_min_out_fee5_n6", pool, binding6))

    counter_pool, counter_intents = _counterexample_fixture()
    fixtures.append(("hand_computed_counterexample", counter_pool, counter_intents))
    accept_pool, accept_intents = _accepted_swap_fixture()
    fixtures.append(("hand_computed_accepted_swap", accept_pool, accept_intents))
    return fixtures


_CATALOGUE = _fixture_catalogue()
_CATALOGUE_PARAMS = [pytest.param(pool, intents, id=name) for name, pool, intents in _CATALOGUE]


def _all_fill_batch(n: int) -> tuple[PoolState, list[Intent]]:
    pool = _make_pool(2_000_000, 1_000_000, 30)
    intents = [
        _make_intent(idx, amount_in=500 + (idx * 37) % 3_000, min_amount_out=1, sender_id=idx % 16 + 1)
        for idx in range(n)
    ]
    return pool, intents


def _binding_batch(n: int, seed: int) -> tuple[PoolState, list[Intent]]:
    pool = _make_pool(2_000_000, 1_000_000, 30)
    rng = random.Random(seed)
    intents: list[Intent] = []
    for idx in range(n):
        amount = rng.randint(200, 50_000)
        fresh_out = _quote_out(pool, _reserves(pool), amount)
        slack = rng.randint(0, max(1, (fresh_out + 1) // 40))
        intents.append(
            _make_intent(
                idx,
                amount_in=amount,
                min_amount_out=max(1, fresh_out + 1 - slack),
                sender_id=idx % 16 + 1,
            )
        )
    return pool, intents


def _random_batch(rng: random.Random, trial: int) -> tuple[PoolState, list[Intent]]:
    reserve0 = rng.randint(500, 200_000)
    reserve1 = rng.randint(500, 200_000)
    pool = _make_pool(reserve0, reserve1, rng.choice([0, 1, 5, 30, 100, 300]))
    reserves = _reserves(pool)
    count = rng.randint(2, 12)
    reverse_batch = rng.randint(0, 99) < 20
    mixed_batch = rng.randint(0, 99) < 15
    intents: list[Intent] = []
    for idx in range(count):
        forward = rng.randint(0, 1) == 0 if mixed_batch else not reverse_batch
        asset_in, asset_out = (ASSET0, ASSET1) if forward else (ASSET1, ASSET0)
        cap = reserve0 if forward else reserve1
        amount_in = rng.randint(1, max(1, min(20_000, cap // 4)))
        fresh_out = _quote_out(pool, reserves, amount_in, asset_in=asset_in, asset_out=asset_out)
        mode = rng.randint(0, 99)
        if mode < 35:
            min_out = 0
        elif mode < 80:
            min_out = max(0, fresh_out - rng.randint(0, max(1, fresh_out // 50)))
        elif mode < 90:
            min_out = fresh_out + 1 + rng.randint(0, 5)
        else:
            min_out = rng.randint(0, max(1, fresh_out))
        kind = IntentKind.SWAP_EXACT_OUT if rng.randint(0, 19) == 0 else IntentKind.SWAP_EXACT_IN
        intents.append(
            _make_intent(
                trial * 64 + idx,
                amount_in=amount_in,
                min_amount_out=min_out,
                sender_id=rng.randint(1, 3),
                asset_in=asset_in,
                asset_out=asset_out,
                kind=kind,
            )
        )
    return pool, intents


def test_zero_and_one_intent_return_fresh_copies_without_simulation() -> None:
    pool = _make_pool(1_000, 1_000, 30)
    reserves = _reserves(pool)

    def _forbidden(*_args: object) -> tuple[int, int, tuple[int, int]]:
        pytest.fail("no evaluation may run for n <= 1")

    single = [_make_intent(0, amount_in=100, min_amount_out=1)]
    for ordering in ([], single):
        cached = refine_b_ordering_with_simulator(
            ordering, pool_state=pool, reserves=reserves, simulate_swap_fn=_forbidden
        )
        generic = refine_b_ordering_with_eval(
            ordering, pool_state=pool, reserves=reserves, eval_ordering_ab_fn=_forbidden
        )
        production = batch_clearing_ordering._refine_b_ordering(ordering, pool_state=pool, reserves=reserves)
        for result in (cached, generic, production):
            assert result is not ordering
            _assert_same_objects(result, ordering)


@pytest.mark.parametrize("pool,intents", _CATALOGUE_PARAMS)
def test_cached_refiner_matches_reference_on_every_permutation(pool: PoolState, intents: list[Intent]) -> None:
    reserves = _reserves(pool)
    for permutation in itertools.permutations(intents):
        ordering = list(permutation)
        snapshot = _capture_input_snapshot(ordering, pool)
        expected = _reference_refine(ordering, pool, reserves)
        _assert_input_unchanged(ordering, pool, snapshot)
        actual = _cached_refine(ordering, pool, reserves)
        _assert_input_unchanged(ordering, pool, snapshot)
        _assert_same_objects(actual, expected)
        assert actual is not ordering
        assert sorted(id(intent) for intent in actual) == sorted(id(intent) for intent in ordering)


@pytest.mark.parametrize("pool,intents", _CATALOGUE_PARAMS)
def test_production_wrapper_runs_cached_helper_and_matches_reference(
    monkeypatch: pytest.MonkeyPatch, pool: PoolState, intents: list[Intent]
) -> None:
    calls = {"cached": 0, "generic": 0}
    original_cached = batch_clearing_ordering.refine_b_ordering_with_simulator
    original_generic = batch_clearing_ordering.refine_b_ordering_with_eval

    def _probe_cached(*args: object, **kwargs: object) -> list[Intent]:
        calls["cached"] += 1
        return original_cached(*args, **kwargs)

    def _probe_generic(*args: object, **kwargs: object) -> list[Intent]:
        calls["generic"] += 1
        return original_generic(*args, **kwargs)

    monkeypatch.setattr(batch_clearing_ordering, "refine_b_ordering_with_simulator", _probe_cached)
    monkeypatch.setattr(batch_clearing_ordering, "refine_b_ordering_with_eval", _probe_generic)

    reserves = _reserves(pool)
    for ordering in (list(intents), list(reversed(intents))):
        snapshot = _capture_input_snapshot(ordering, pool)
        expected = _reference_refine(ordering, pool, reserves)
        _assert_input_unchanged(ordering, pool, snapshot)
        actual = batch_clearing_ordering._refine_b_ordering(ordering, pool_state=pool, reserves=reserves)
        _assert_input_unchanged(ordering, pool, snapshot)
        _assert_same_objects(actual, expected)
    assert calls == {"cached": 2, "generic": 0}


def test_all_ties_leave_every_permutation_unchanged() -> None:
    pool, intents = next(
        (pool, intents) for name, pool, intents in _CATALOGUE if name == "fee_100_percent_nothing_executable"
    )
    reserves = _reserves(pool)
    for permutation in itertools.permutations(intents):
        ordering = list(permutation)
        assert _REAL_EVAL(ordering, pool, reserves) == (0, 0)
        _assert_same_objects(_cached_refine(ordering, pool, reserves), ordering)


def test_seeded_corpus_matches_reference_and_exercises_reuse_resimulation_and_acceptance(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    counters = {"reused": 0, "resimulated": 0, "accepted": 0}
    original_reusable = mci_ordering._suffix_is_reusable
    original_after = mci_ordering._cache_after_accepted_swap

    def _count_reusable(post_pair: tuple[int, int], cached: tuple[int, int]) -> bool:
        reusable = original_reusable(post_pair, cached)
        counters["reused" if reusable else "resimulated"] += 1
        return reusable

    def _count_accepted(cache: object, candidate: object) -> object:
        counters["accepted"] += 1
        return original_after(cache, candidate)

    monkeypatch.setattr(mci_ordering, "_suffix_is_reusable", _count_reusable)
    monkeypatch.setattr(mci_ordering, "_cache_after_accepted_swap", _count_accepted)

    batches = [(pool, intents) for _name, pool, intents in _CATALOGUE]
    rng = random.Random(20260906)
    batches.extend(_random_batch(rng, trial) for trial in range(120))

    for pool, intents in batches:
        reserves = _reserves(pool)
        snapshot = _capture_input_snapshot(intents, pool)
        expected = _reference_refine(intents, pool, reserves)
        _assert_input_unchanged(intents, pool, snapshot)
        actual = _cached_refine(intents, pool, reserves)
        _assert_input_unchanged(intents, pool, snapshot)
        _assert_same_objects(actual, expected)

    # The hand-computed fixtures alone guarantee each branch ran at least once; the corpus adds
    # accepted swaps whose cache update must stay coherent for later candidates.
    assert counters["reused"] > 0
    assert counters["resimulated"] > 0
    assert counters["accepted"] > 0


def test_simulator_call_count_never_exceeds_reference(monkeypatch: pytest.MonkeyPatch) -> None:
    batches = [(name, pool, intents) for name, pool, intents in _CATALOGUE]
    for n in (32, 64):
        pool, intents = _all_fill_batch(n)
        batches.append((f"all_fill_n{n}", pool, intents))
        pool, intents = _binding_batch(n, seed=3)
        batches.append((f"binding_n{n}", pool, intents))
    pool, intents = _binding_batch(128, seed=3)
    batches.append(("binding_n128", pool, intents))

    calls = {"n": 0}

    def _counting_simulate(intent: Intent, pool_state: PoolState, reserves: tuple[int, int]) -> object:
        calls["n"] += 1
        return _REAL_SIMULATE(intent, pool_state, reserves)

    # Both paths resolve the simulator through this module attribute at call time: the unchanged
    # evaluator inside the reference, and the production wrapper for the cached helper.
    monkeypatch.setattr(batch_clearing_ordering, "_simulate_swap_reserves", _counting_simulate)

    evidence: list[tuple[str, int, int, int]] = []
    for name, pool, intents in batches:
        reserves = _reserves(pool)
        snapshot = _capture_input_snapshot(intents, pool)
        calls["n"] = 0
        expected = refine_b_ordering_with_eval(
            intents,
            pool_state=pool,
            reserves=reserves,
            eval_ordering_ab_fn=batch_clearing_ordering._eval_ordering_ab,
        )
        _assert_input_unchanged(intents, pool, snapshot)
        reference_calls = calls["n"]
        calls["n"] = 0
        actual = batch_clearing_ordering._refine_b_ordering(intents, pool_state=pool, reserves=reserves)
        _assert_input_unchanged(intents, pool, snapshot)
        cached_calls = calls["n"]
        _assert_same_objects(actual, expected)
        evidence.append((name, len(intents), reference_calls, cached_calls))

    for name, count, reference_calls, cached_calls in evidence:
        assert cached_calls <= reference_calls, (name, count, reference_calls, cached_calls)
        if count >= 3:
            # Every candidate at position i >= 1 costs at most n - i < n calls even when it
            # re-simulates, so the strict inequality holds for any reuse rate.
            assert cached_calls < reference_calls, (name, count, reference_calls, cached_calls)
        if count >= 16:
            # Arithmetic bound independent of the reuse rate: worst case n + p * (n(n+1)/2 - 1)
            # against n + p * n(n-1) is below two thirds for n >= 16. A tighter ratio on a fixture
            # is evidence, not a gate.
            assert 3 * cached_calls <= 2 * reference_calls, (name, count, reference_calls, cached_calls)


def test_full_resimulation_counterexample_when_post_pair_reserves_differ() -> None:
    pool, intents = _counterexample_fixture()
    x, y, z = intents
    reserves = (1_000, 1_000)

    cache = mci_ordering._build_prefix_cache(intents, pool, reserves, _REAL_SIMULATE)
    assert cache.states == (
        (0, 0, (1_000, 1_000)),
        (1_000, 500, (2_000, 500)),
        (1_000, 500, (2_000, 500)),
        (2_000, 516, (3_000, 334)),
    )

    candidate = mci_ordering._simulate_adjacent_swap(intents, 0, cache, pool, _REAL_SIMULATE)
    assert candidate.suffix_reused is False
    assert candidate.tail_states[1][2] == (2_500, 401)
    assert candidate.tail_states[1][2] != cache.states[2][2]
    assert (candidate.total_a, candidate.total_b) == (1_500, 266)
    assert _REAL_EVAL([y, x, z], pool, reserves) == (1_500, 266)
    assert not mci_ordering._is_strict_ab_improvement(1_500, 266, 2_000, 516)

    # Crediting the stale cached suffix instead would claim (2_500, 282) and accept the swap.
    stale_a = candidate.tail_states[1][0] + (cache.states[3][0] - cache.states[2][0])
    stale_b = candidate.tail_states[1][1] + (cache.states[3][1] - cache.states[2][1])
    assert (stale_a, stale_b) == (2_500, 282)
    assert mci_ordering._is_strict_ab_improvement(stale_a, stale_b, 2_000, 516)

    # The adjacent pair (z, y) at position 1 leaves the cached end reserves, so its suffix is reused.
    reused = mci_ordering._simulate_adjacent_swap(intents, 1, cache, pool, _REAL_SIMULATE)
    assert reused.suffix_reused is True
    assert (reused.total_a, reused.total_b) == (2_000, 516)

    _assert_same_objects(_cached_refine(intents, pool, reserves), [x, y, z])
    _assert_same_objects(_reference_refine(intents, pool, reserves), [x, y, z])


def test_mutant_unconditional_suffix_reuse_changes_the_refined_ordering(monkeypatch: pytest.MonkeyPatch) -> None:
    pool, intents = _counterexample_fixture()
    x, y, z = intents
    reserves = (1_000, 1_000)
    _assert_same_objects(_reference_refine(intents, pool, reserves), [x, y, z])
    _assert_same_objects(_cached_refine(intents, pool, reserves), [x, y, z])

    def _always_reusable(_post_pair: tuple[int, int], _cached: tuple[int, int]) -> bool:
        return True

    monkeypatch.setattr(mci_ordering, "_suffix_is_reusable", _always_reusable)
    mutant = _cached_refine(intents, pool, reserves)
    assert _ids(mutant) != _ids([x, y, z])
    assert _ids(mutant) == _ids([y, x, z])


def test_accepted_swap_fixture_invalidates_cache_and_matches_reference() -> None:
    pool, intents = _accepted_swap_fixture()
    q, p = intents
    reserves = (1_000, 1_000)
    assert _REAL_EVAL([q, p], pool, reserves) == (500, 333)
    assert _REAL_EVAL([p, q], pool, reserves) == (700, 245)
    _assert_same_objects(_reference_refine(intents, pool, reserves), [p, q])
    _assert_same_objects(_cached_refine(intents, pool, reserves), [p, q])


@pytest.mark.parametrize("pool,intents", _CATALOGUE_PARAMS)
def test_prefix_cache_after_accepted_swap_equals_fresh_rebuild(pool: PoolState, intents: list[Intent]) -> None:
    reserves = _reserves(pool)
    rng = random.Random(7)
    orderings = [list(intents), list(reversed(intents))]
    orderings.extend(rng.sample(intents, len(intents)) for _ in range(6))
    for ordering in orderings:
        cache = mci_ordering._build_prefix_cache(ordering, pool, reserves, _REAL_SIMULATE)
        assert len(cache.states) == len(ordering) + 1
        assert cache.states[0] == (0, 0, reserves)
        assert cache.states[-1][:2] == _REAL_EVAL(ordering, pool, reserves)
        for position in range(len(ordering) - 1):
            candidate = mci_ordering._simulate_adjacent_swap(ordering, position, cache, pool, _REAL_SIMULATE)
            swapped = list(ordering)
            swapped[position], swapped[position + 1] = swapped[position + 1], swapped[position]
            assert (candidate.total_a, candidate.total_b) == _REAL_EVAL(swapped, pool, reserves)
            rebuilt = mci_ordering._build_prefix_cache(swapped, pool, reserves, _REAL_SIMULATE)
            assert mci_ordering._cache_after_accepted_swap(cache, candidate) == rebuilt


def test_fold_step_ignores_nonpositive_contributions_exactly_like_eval_ordering_ab() -> None:
    pool = _make_pool(1_000, 1_000, 30)
    intent = _make_intent(0, amount_in=100, min_amount_out=0)
    state = (5, 7, (11, 13))

    def _zero_a(*_args: object) -> tuple[int, int, tuple[int, int]]:
        return 0, 40, (999, 999)

    def _negative_a(*_args: object) -> tuple[int, int, tuple[int, int]]:
        return -3, 5, (1, 1)

    def _positive_a(*_args: object) -> tuple[int, int, tuple[int, int]]:
        return 2, -4, (21, 22)

    assert mci_ordering._fold_simulated_swap(state, intent, pool, _zero_a) == state
    assert mci_ordering._fold_simulated_swap(state, intent, pool, _negative_a) == state
    assert mci_ordering._fold_simulated_swap(state, intent, pool, _positive_a) == (7, 3, (21, 22))


def test_synthetic_pure_simulator_parity_including_nonpositive_contributions() -> None:
    pool = _make_pool(10_000, 10_000, 30)
    intents = [_make_intent(idx, amount_in=10 + idx, min_amount_out=0) for idx in range(7)]

    def _synthetic(intent: Intent, _pool_state: PoolState, reserves: tuple[int, int]) -> tuple[int, int, tuple[int, int]]:
        # Pure in (intent, reserves): a toy transition on the reserve pair with all three regimes.
        r0, r1 = reserves
        amount = intent.get_field("amount_in")
        seed = (amount * 7_919 + r0 * 31 + r1) % 97
        if seed % 5 == 0:
            return 0, 40, (r0 + 999, r1)
        if seed % 7 == 0:
            return -3, 5, (r0 + 1, r1 + 1)
        a = seed + 1
        b = (seed * 13) % 17 - 8
        return a, b, ((r0 + a) % 1_000, (r1 * 3 + b) % 1_000)

    def _canonical_fold(ordering: list[Intent], pool_state: PoolState, reserves: tuple[int, int]) -> tuple[int, int]:
        total_a = 0
        total_b = 0
        current = reserves
        for intent in ordering:
            a, b, new_reserves = _synthetic(intent, pool_state, current)
            if a > 0:
                total_a += a
                total_b += b
                current = new_reserves
        return total_a, total_b

    rng = random.Random(11)
    for _ in range(40):
        ordering = rng.sample(intents, len(intents))
        reserves = (rng.randint(0, 999), rng.randint(0, 999))
        snapshot = _capture_input_snapshot(ordering, pool)
        expected = refine_b_ordering_with_eval(
            ordering, pool_state=pool, reserves=reserves, eval_ordering_ab_fn=_canonical_fold
        )
        _assert_input_unchanged(ordering, pool, snapshot)
        actual = refine_b_ordering_with_simulator(
            ordering, pool_state=pool, reserves=reserves, simulate_swap_fn=_synthetic
        )
        _assert_input_unchanged(ordering, pool, snapshot)
        _assert_same_objects(actual, expected)


def test_generic_evaluator_semantics_and_seam_rebinding_are_preserved(monkeypatch: pytest.MonkeyPatch) -> None:
    pool = _make_pool(2_000_000, 2_000_000, 30)
    reserves = _reserves(pool)
    first = _make_intent(0, amount_in=100, min_amount_out=1)
    second = _make_intent(1, amount_in=120, min_amount_out=1)
    order = [first, second]

    # A non-additive evaluator keyed only on the id sequence: the generic refiner must honour it.
    eval_map = {
        (first.intent_id, second.intent_id): (1, 1),
        (second.intent_id, first.intent_id): (2, 2),
    }
    stub_calls = {"n": 0}

    def _stub(ordering: list[Intent], *_args: object) -> tuple[int, int]:
        stub_calls["n"] += 1
        return eval_map[tuple(intent.intent_id for intent in ordering)]

    snapshot = _capture_input_snapshot(order, pool)
    generic = refine_b_ordering_with_eval(order, pool_state=pool, reserves=reserves, eval_ordering_ab_fn=_stub)
    _assert_input_unchanged(order, pool, snapshot)
    _assert_same_objects(generic, [second, first])
    # base + accepted swap + rejected swap-back on the second pass: full evaluation each time.
    assert stub_calls["n"] == 3

    calls = {"cached": 0}
    original_cached = batch_clearing_ordering.refine_b_ordering_with_simulator

    def _probe_cached(*args: object, **kwargs: object) -> list[Intent]:
        calls["cached"] += 1
        return original_cached(*args, **kwargs)

    # Rebinding the module evaluator routes the production wrapper to the generic path with the stub.
    monkeypatch.setattr(batch_clearing_ordering, "refine_b_ordering_with_simulator", _probe_cached)
    monkeypatch.setattr(batch_clearing_ordering, "_eval_ordering_ab", _stub)
    seam = batch_clearing_ordering._refine_b_ordering(order, pool_state=pool, reserves=reserves)
    _assert_input_unchanged(order, pool, snapshot)
    _assert_same_objects(seam, [second, first])
    assert calls["cached"] == 0
    monkeypatch.undo()

    # With the canonical evaluator restored the wrapper uses the cache and matches the reference.
    monkeypatch.setattr(batch_clearing_ordering, "refine_b_ordering_with_simulator", _probe_cached)
    restored = batch_clearing_ordering._refine_b_ordering(order, pool_state=pool, reserves=reserves)
    _assert_input_unchanged(order, pool, snapshot)
    _assert_same_objects(restored, _reference_refine(order, pool, reserves))
    assert calls["cached"] == 1


def _settlement_batch() -> tuple[dict[str, PoolState], BalanceTable, list[Intent]]:
    _pool_id, pool, _lp_minted = create_pool(
        asset0=HEX_ASSET0,
        asset1=HEX_ASSET1,
        amount0=2_000_000,
        amount1=1_000_000,
        fee_bps=30,
        creator_pubkey=_sender(9),
        created_at=0,
    )
    pools = {pool.pool_id: pool}
    senders = [_sender(1), _sender(2), _sender(3)]
    balances = BalanceTable()
    for sender, amount in zip(senders, (10_000_000, 25_000, 10_000_000), strict=True):
        balances.set(sender, HEX_ASSET0, amount)
        balances.set(sender, HEX_ASSET1, 0)

    reserves = _reserves(pool)
    intents: list[Intent] = []
    for idx, amount in enumerate([12_000, 30_000, 7_500, 45_000, 20_000, 3_000, 60_000, 15_000]):
        base_fields = {
            "pool_id": pool.pool_id,
            "asset_in": HEX_ASSET0,
            "asset_out": HEX_ASSET1,
            "amount_in": amount,
            "min_amount_out": 0,
        }
        probe = Intent(
            module="TauSwap",
            version="0.1",
            kind=IntentKind.SWAP_EXACT_IN,
            intent_id=_iid(400 + idx),
            sender_pubkey=senders[0],
            deadline=9_999_999_999,
            fields=base_fields,
        )
        _a, fresh_out, _r = _REAL_SIMULATE(probe, pool, reserves)
        if idx == 0:
            min_out = 0
        elif idx == 6:
            min_out = 2 * amount
        else:
            min_out = max(0, fresh_out - (idx * 53) % 400)
        intents.append(
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(500 + idx),
                sender_pubkey=senders[idx % 3],
                deadline=9_999_999_999,
                fields={**base_fields, "min_amount_out": min_out},
            )
        )
    return pools, balances, intents


def _canonicalize_json_value(value: object) -> object:
    """Convert the complete dataclass projection without silently stringifying unknown values."""
    if isinstance(value, Enum):
        return value.value
    if value is None or type(value) in (bool, int, str):
        return value
    if isinstance(value, list):
        return [_canonicalize_json_value(item) for item in value]
    if isinstance(value, tuple):
        return [_canonicalize_json_value(item) for item in value]
    if isinstance(value, dict):
        converted: dict[str, object] = {}
        for key, item in value.items():
            if type(key) is not str:
                raise TypeError(f"unsupported settlement serialization key: {type(key).__name__}")
            converted[key] = _canonicalize_json_value(item)
        return converted
    raise TypeError(f"unsupported settlement serialization value: {type(value).__name__}")


def _serialize_settlement(settlement: Settlement) -> bytes:
    payload = _canonicalize_json_value(dataclasses.asdict(settlement))
    if not isinstance(payload, dict):
        raise TypeError("settlement dataclass projection must be an object")
    return canonical_json_bytes(payload)


def _capture_settlement_input_snapshot(
    pools: dict[str, PoolState], balances: BalanceTable, intents: list[Intent]
) -> tuple[
    tuple[tuple[str, PoolState], ...],
    tuple[tuple[str, dict[str, object]], ...],
    tuple[tuple[str, str, int], ...],
    tuple[Intent, ...],
    tuple[dict[str, object], ...],
]:
    return (
        tuple((pool_id, pool) for pool_id, pool in sorted(pools.items())),
        tuple(
            (pool_id, dataclasses.asdict(pool))
            for pool_id, pool in sorted(pools.items())
        ),
        tuple(
            (pubkey, asset, amount)
            for (pubkey, asset), amount in sorted(balances.get_all_balances().items())
        ),
        tuple(intents),
        tuple(_intent_value_snapshot(intent) for intent in intents),
    )


def _assert_settlement_inputs_unchanged(
    pools: dict[str, PoolState],
    balances: BalanceTable,
    intents: list[Intent],
    snapshot: tuple[
        tuple[tuple[str, PoolState], ...],
        tuple[tuple[str, dict[str, object]], ...],
        tuple[tuple[str, str, int], ...],
        tuple[Intent, ...],
        tuple[dict[str, object], ...],
    ],
) -> None:
    original_pool_objects, original_pools, original_balances, original_intent_objects, original_intents = snapshot
    assert tuple(pool_id for pool_id, _pool in sorted(pools.items())) == tuple(
        pool_id for pool_id, _pool in original_pool_objects
    )
    assert all(pools[pool_id] is pool for pool_id, pool in original_pool_objects)
    assert tuple(
        (pool_id, dataclasses.asdict(pool))
        for pool_id, pool in sorted(pools.items())
    ) == original_pools
    assert tuple(
        (pubkey, asset, amount)
        for (pubkey, asset), amount in sorted(balances.get_all_balances().items())
    ) == original_balances
    _assert_same_objects(intents, list(original_intent_objects))
    assert tuple(_intent_value_snapshot(intent) for intent in intents) == original_intents


def test_full_settlement_serialization_preserves_order_metadata_events_and_reasons() -> None:
    pools, balances, intents = _settlement_batch()
    settlement = compute_settlement(intents, pools, balances, LPTable(), swap_ordering="greedy_ab_refined")

    reordered_intents = list(settlement.included_intents)
    reordered_intents[0], reordered_intents[-1] = reordered_intents[-1], reordered_intents[0]
    changed_fills = list(settlement.fills)
    changed_fills[0] = dataclasses.replace(changed_fills[0], reason="serialization-reason")
    variants = (
        dataclasses.replace(settlement, included_intents=reordered_intents),
        dataclasses.replace(settlement, batch_ref="serialization-metadata"),
        dataclasses.replace(settlement, events=[{"event": "serialization-metadata"}]),
        dataclasses.replace(settlement, fills=changed_fills),
    )

    for variant in variants:
        assert variant != settlement
        assert _serialize_settlement(variant) != _serialize_settlement(settlement)


def test_compute_settlement_greedy_ab_refined_serialized_parity_with_reference_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pools, balances, intents = _settlement_batch()
    input_snapshot = _capture_settlement_input_snapshot(pools, balances, intents)
    probes = {"cached": 0, "generic": 0}
    original_cached = batch_clearing_ordering.refine_b_ordering_with_simulator
    original_generic = batch_clearing_ordering.refine_b_ordering_with_eval

    def _probe_cached(*args: object, **kwargs: object) -> list[Intent]:
        probes["cached"] += 1
        return original_cached(*args, **kwargs)

    def _probe_generic(*args: object, **kwargs: object) -> list[Intent]:
        probes["generic"] += 1
        return original_generic(*args, **kwargs)

    monkeypatch.setattr(batch_clearing_ordering, "refine_b_ordering_with_simulator", _probe_cached)
    monkeypatch.setattr(batch_clearing_ordering, "refine_b_ordering_with_eval", _probe_generic)

    cached_settlement = compute_settlement(intents, pools, balances, LPTable(), swap_ordering="greedy_ab_refined")
    _assert_settlement_inputs_unchanged(pools, balances, intents, input_snapshot)
    assert probes == {"cached": 1, "generic": 0}
    ok, err = validate_settlement(cached_settlement, balances, pools, LPTable())
    assert ok, err

    # Scoped reference path: rebind the module evaluator to a delegate with identical semantics.
    # The identity guard in `_refine_b_ordering` then routes to the unchanged generic refiner
    # driving the unchanged evaluator, inside the same dispatcher.
    canonical = batch_clearing_ordering._CANONICAL_EVAL_ORDERING_AB

    def _reference_evaluator(ordering: list[Intent], pool_state: PoolState, reserves: tuple[int, int]) -> tuple[int, int]:
        return canonical(ordering, pool_state, reserves)

    monkeypatch.setattr(batch_clearing_ordering, "_eval_ordering_ab", _reference_evaluator)
    probes["cached"] = 0
    probes["generic"] = 0
    reference_settlement = compute_settlement(
        intents, pools, balances, LPTable(), swap_ordering="greedy_ab_refined"
    )
    _assert_settlement_inputs_unchanged(pools, balances, intents, input_snapshot)
    assert probes == {"cached": 0, "generic": 1}

    # Dataclass equality covers every field recursively, including order, batch metadata, events,
    # and per-fill rejection reasons. The full canonical serialization retains the same fields.
    assert cached_settlement == reference_settlement
    assert cached_settlement.included_intents == reference_settlement.included_intents
    assert cached_settlement.batch_ref == reference_settlement.batch_ref
    assert cached_settlement.events == reference_settlement.events
    assert [fill.reason for fill in cached_settlement.fills] == [
        fill.reason for fill in reference_settlement.fills
    ]
    assert _serialize_settlement(cached_settlement) == _serialize_settlement(reference_settlement)
    assert canonical_json_bytes(_settlement_commitment_dict(cached_settlement)) == canonical_json_bytes(
        _settlement_commitment_dict(reference_settlement)
    )
    actions = {fill.action for fill in cached_settlement.fills}
    assert actions == {FillAction.FILL, FillAction.REJECT}
