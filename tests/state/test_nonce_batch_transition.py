from __future__ import annotations

from itertools import permutations
from typing import Any, cast

from src.core.nonce_batch_transition import (
    IntentNonceBatchCodeV1,
    IntentNonceBatchOkV1,
    IntentNonceBatchRejectV1,
    validate_and_apply_intent_nonce_batch_committed_v1,
)
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch
from src.state.state_snapshot_values import CommittedNonceTableV1
from src.state.state_snapshots import snapshot_nonce_table


def _pubkey(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 48


def _intent(index: int, *, sender: str, nonce: object | None) -> Intent:
    fields: dict[str, object] = {}
    if nonce is not None:
        fields["nonce"] = nonce
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + f"{index:064x}",
        sender_pubkey=sender,
        deadline=99,
        fields=cast(dict[str, Any], fields),
    )


def _prestate(
    *entries: tuple[str, int],
) -> tuple[NonceTable, CommittedNonceTableV1]:
    legacy = NonceTable()
    for sender, nonce in entries:
        legacy.set_last(sender, nonce)
    return legacy, snapshot_nonce_table(legacy)


def test_exact_nonce_batch_matches_legacy_and_retains_one_canonical_candidate() -> None:
    sender_a = _pubkey(1)
    sender_b = _pubkey(2)
    intents = [
        _intent(1, sender=sender_b, nonce=2),
        _intent(2, sender=sender_a, nonce=6),
        _intent(3, sender=sender_b, nonce=1),
        _intent(4, sender=sender_a, nonce=5),
    ]
    legacy, exact = _prestate((sender_a, 4))

    legacy_ok, legacy_error, legacy_next = validate_and_apply_intent_nonce_batch(
        nonces=legacy,
        intents=intents,
        require_all_nonces=True,
    )
    exact_result = validate_and_apply_intent_nonce_batch_committed_v1(
        nonces=exact,
        intents=intents,
        require_all_nonces=True,
    )

    assert legacy_ok is True
    assert legacy_error is None
    assert legacy_next is not None
    assert type(exact_result) is IntentNonceBatchOkV1
    assert exact_result.patch is not None
    assert exact_result.state == snapshot_nonce_table(legacy_next)
    assert tuple(advance.pubkey for advance in exact_result.patch.advances) == (
        sender_a,
        sender_b,
    )
    assert exact.entries == ((sender_a, 4),)
    assert legacy.get_all() == {sender_a: 4}


def test_exact_nonce_batch_accepted_result_is_permutation_invariant() -> None:
    sender_a = _pubkey(1)
    sender_b = _pubkey(2)
    atoms = (
        _intent(1, sender=sender_a, nonce=1),
        _intent(2, sender=sender_a, nonce=2),
        _intent(3, sender=sender_b, nonce=1),
    )
    _legacy, exact = _prestate()

    results = tuple(
        validate_and_apply_intent_nonce_batch_committed_v1(
            nonces=exact,
            intents=list(ordering),
            require_all_nonces=True,
        )
        for ordering in permutations(atoms)
    )

    assert all(type(result) is IntentNonceBatchOkV1 for result in results)
    assert all(result == results[0] for result in results)


def test_exact_nonce_batch_noop_reuses_validated_immutable_prestate() -> None:
    sender = _pubkey(1)
    legacy, exact = _prestate((sender, 7))

    empty = validate_and_apply_intent_nonce_batch_committed_v1(
        nonces=exact,
        intents=[],
        require_all_nonces=True,
    )
    nonce_free = validate_and_apply_intent_nonce_batch_committed_v1(
        nonces=exact,
        intents=[_intent(1, sender=sender, nonce=None)],
        require_all_nonces=False,
    )

    assert empty == IntentNonceBatchOkV1(exact, None)
    assert nonce_free == IntentNonceBatchOkV1(exact, None)
    assert empty.state is exact
    assert nonce_free.state is exact
    assert legacy.get_all() == {sender: 7}


def test_exact_nonce_batch_rejections_match_mounted_public_precedence() -> None:
    sender = _pubkey(1)
    cases = (
        ([_intent(1, sender=sender, nonce=None)], True),
        ([_intent(1, sender=sender, nonce=True)], True),
        (
            [
                _intent(1, sender=sender, nonce=1),
                _intent(2, sender=_pubkey(2), nonce=None),
            ],
            False,
        ),
        (
            [
                _intent(1, sender=sender, nonce=1),
                _intent(2, sender=sender, nonce=1),
            ],
            True,
        ),
        ([_intent(1, sender=sender, nonce=2)], True),
        ([_intent(1, sender="not-hex", nonce=1)], True),
    )

    for intents, require_all in cases:
        legacy, exact = _prestate()
        legacy_ok, legacy_error, legacy_next = validate_and_apply_intent_nonce_batch(
            nonces=legacy,
            intents=intents,
            require_all_nonces=require_all,
        )
        exact_result = validate_and_apply_intent_nonce_batch_committed_v1(
            nonces=exact,
            intents=intents,
            require_all_nonces=require_all,
        )

        assert legacy_ok is False
        assert legacy_next is None
        assert type(exact_result) is IntentNonceBatchRejectV1
        assert exact_result.public_reason == legacy_error
        assert not hasattr(exact_result, "state")
        assert not hasattr(exact_result, "patch")
        assert exact.entries == ()


def test_exact_nonce_batch_revalidates_prestate_even_when_batch_is_empty() -> None:
    _legacy, exact = _prestate((_pubkey(1), 4))
    owned_map = object.__getattribute__(exact, "_last")
    object.__setattr__(owned_map, "_entries", ((_pubkey(1), True),))

    result = validate_and_apply_intent_nonce_batch_committed_v1(
        nonces=exact,
        intents=[],
        require_all_nonces=True,
    )

    assert type(result) is IntentNonceBatchRejectV1
    assert result.code is IntentNonceBatchCodeV1.INVALID_PRESTATE
    assert result.public_reason.startswith("nonce policy rejected: invalid_prestate")
    assert not hasattr(result, "state")


def test_exact_nonce_batch_rejects_open_container_and_policy_types() -> None:
    _legacy, exact = _prestate()
    runtime = cast(Any, validate_and_apply_intent_nonce_batch_committed_v1)

    wrong_intents = runtime(
        nonces=exact,
        intents={},
        require_all_nonces=True,
    )
    wrong_policy = runtime(
        nonces=exact,
        intents=[],
        require_all_nonces=1,
    )

    assert wrong_intents == IntentNonceBatchRejectV1(
        IntentNonceBatchCodeV1.WRONG_EXACT_TYPE,
        "nonce policy rejected",
    )
    assert wrong_policy == IntentNonceBatchRejectV1(
        IntentNonceBatchCodeV1.WRONG_EXACT_TYPE,
        "nonce policy rejected",
    )
