"""PR-gated binding for the Lean nonce batch-wrapper theorem.

The Lean module `Proofs.ZenoDEXNonceBatchWrapper` proves the non-circular theorem
shape required by review:

    batchAccepts(groups) = true -> every accepted nonce is in the sender-local
    strict post-batch range.

This test binds the LIVE `validate_and_apply_intent_nonce_batch` authority to an
independent Python transcription of the same grouped/sorted fold law over a
finite domain sweep. It deliberately stays inside the theorem's domain:
canonical senders, positive u32 nonces, and `require_all_nonces=True`.

Scope kept honest: this is a proof-to-runtime binding for the batch wrapper's
accept/reject decision and final per-sender state on the swept domain. It is not
a cross-language differential and it does not clear any CBC column by itself.
"""

from __future__ import annotations

import itertools
from collections.abc import Callable, Iterable, Sequence

import pytest

from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch

SENDER_A = "0x" + "11" * 48
SENDER_B = "0x" + "22" * 48
SENDER_C = "0x" + "33" * 48
SENDERS = (SENDER_A, SENDER_B, SENDER_C)
_INTENT_ID = "0x" + "ab" * 32

Validator = Callable[
    [NonceTable, Sequence[Intent]],
    tuple[bool, str | None, NonceTable | None],
]


def _intent(sender: str, nonce: int) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_INTENT_ID,
        sender_pubkey=sender,
        deadline=10**12,
        fields={"nonce": nonce},
    )


def _table(lasts: dict[str, int]) -> NonceTable:
    table = NonceTable()
    for sender, last in lasts.items():
        if last:
            table.set_last(sender, last)
    return table


def _snapshot(table: NonceTable) -> dict[str, int]:
    return dict(table.get_all())


def _live_validator(table: NonceTable, intents: Sequence[Intent]) -> tuple[bool, str | None, NonceTable | None]:
    return validate_and_apply_intent_nonce_batch(
        nonces=table,
        intents=intents,
        require_all_nonces=True,
    )


def _fold_accepts(last: int, sorted_nonces: Sequence[int]) -> tuple[bool, int]:
    cursor = last
    for nonce in sorted_nonces:
        if nonce != cursor + 1:
            return False, last
        cursor = nonce
    return True, cursor


def _lean_sorted_fold_model(
    lasts: dict[str, int],
    pairs: Sequence[tuple[str, int]],
) -> tuple[bool, dict[str, int]]:
    """Independent transcription of the Lean sorted-fold model.

    Group by sender, sort each sender's nonces, accept only if every sender-local
    fold sees the strict successor at each step. Rejection is atomic: the final
    state is the input state.
    """
    grouped: dict[str, list[int]] = {}
    for sender, nonce in pairs:
        grouped.setdefault(sender, []).append(nonce)

    final = dict(lasts)
    for sender, nonces in grouped.items():
        ok, new_last = _fold_accepts(final.get(sender, 0), sorted(nonces))
        if not ok:
            return False, dict(lasts)
        final[sender] = new_last
    return True, final


def _assert_validator_matches_model(
    *,
    validator: Validator,
    lasts: dict[str, int],
    pairs: Sequence[tuple[str, int]],
) -> None:
    table = _table(lasts)
    before = _snapshot(table)
    intents = [_intent(sender, nonce) for sender, nonce in pairs]
    expected_ok, expected_state = _lean_sorted_fold_model(lasts, pairs)

    ok, reason, updated = validator(table, intents)

    assert _snapshot(table) == before, "validator mutated input nonce table"
    assert ok is expected_ok, (pairs, lasts, ok, expected_ok, reason)
    if expected_ok:
        assert reason is None
        assert updated is not None
        assert _snapshot(updated) == {sender: last for sender, last in expected_state.items() if last}
    else:
        assert updated is None, "reject must not return a partially updated table"


def _sweep_cases() -> Iterable[tuple[dict[str, int], list[tuple[str, int]]]]:
    start_states = [
        {},
        {SENDER_A: 1},
        {SENDER_A: 2, SENDER_B: 1},
        {SENDER_A: 3, SENDER_B: 2, SENDER_C: 1},
    ]
    base_batches = [
        [],
        [(SENDER_A, 1)],
        [(SENDER_A, 1), (SENDER_A, 2)],
        [(SENDER_A, 2)],
        [(SENDER_A, 1), (SENDER_A, 1)],
        [(SENDER_A, 1), (SENDER_B, 1)],
        [(SENDER_A, 2), (SENDER_A, 3), (SENDER_B, 2)],
        [(SENDER_A, 4), (SENDER_B, 3), (SENDER_C, 2)],
        [(SENDER_A, 2), (SENDER_B, 1), (SENDER_A, 3), (SENDER_B, 2)],
    ]
    for lasts in start_states:
        for pairs in base_batches:
            # Exercise order independence for batches with up to four intents.
            seen: set[tuple[tuple[str, int], ...]] = set()
            for perm in itertools.permutations(pairs):
                if perm in seen:
                    continue
                seen.add(perm)
                yield lasts, list(perm)

    # Exhaustive small domain: two senders, lengths 1..3, nonces near the
    # boundaries that distinguish accept, duplicate, stale, and gap.
    for last_a in range(0, 3):
        for last_b in range(0, 3):
            lasts = {SENDER_A: last_a, SENDER_B: last_b}
            choices = [1, 2, 3, 4]
            for size in range(1, 4):
                for senders in itertools.product((SENDER_A, SENDER_B), repeat=size):
                    for nonces in itertools.product(choices, repeat=size):
                        yield lasts, list(zip(senders, nonces))


def test_live_nonce_batch_matches_lean_sorted_fold_model() -> None:
    checked = 0
    accepted = 0
    rejected = 0
    for lasts, pairs in _sweep_cases():
        _assert_validator_matches_model(validator=_live_validator, lasts=lasts, pairs=pairs)
        ok, _state = _lean_sorted_fold_model(lasts, pairs)
        checked += 1
        accepted += int(ok)
        rejected += int(not ok)

    assert checked >= 1000, checked
    assert accepted >= 10, accepted
    assert rejected >= 100, rejected


def test_teeth_gap_accepting_validator_is_caught() -> None:
    """A planted validator that accepts gaps must fail the binding checker."""

    def broken_gap_accepting_validator(
        table: NonceTable,
        intents: Sequence[Intent],
    ) -> tuple[bool, str | None, NonceTable | None]:
        updated = NonceTable()
        for sender, last in table.get_all().items():
            updated.set_last(sender, last)
        grouped: dict[str, list[int]] = {}
        for intent in intents:
            grouped.setdefault(intent.sender_pubkey, []).append(int(intent.fields["nonce"]))
        for sender, nonces in grouped.items():
            updated.set_last(sender, max(nonces))
        return True, None, updated

    with pytest.raises(AssertionError, match="True, False|False, True"):
        _assert_validator_matches_model(
            validator=broken_gap_accepting_validator,
            lasts={},
            pairs=[(SENDER_A, 2)],
        )


def test_teeth_partial_apply_reject_validator_is_caught() -> None:
    """A planted validator that leaks a partial update on reject must fail."""

    def broken_partial_apply_validator(
        table: NonceTable,
        intents: Sequence[Intent],
    ) -> tuple[bool, str | None, NonceTable | None]:
        updated = NonceTable()
        for sender, last in table.get_all().items():
            updated.set_last(sender, last)
        grouped: dict[str, list[int]] = {}
        for intent in intents:
            grouped.setdefault(intent.sender_pubkey, []).append(int(intent.fields["nonce"]))
        for sender, nonces in grouped.items():
            ok, new_last = _fold_accepts(updated.get_last(sender), sorted(nonces))
            if not ok:
                return False, "nonce sequence invalid", updated
            updated.set_last(sender, new_last)
        return True, None, updated

    with pytest.raises(AssertionError, match="partially updated"):
        _assert_validator_matches_model(
            validator=broken_partial_apply_validator,
            lasts={},
            pairs=[(SENDER_A, 1), (SENDER_B, 3)],
        )
