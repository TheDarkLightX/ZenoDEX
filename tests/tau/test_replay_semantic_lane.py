from __future__ import annotations

from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch


def _intent(*, sender_pubkey: str, intent_id_byte: str, nonce: int | None) -> Intent:
    fields = {} if nonce is None else {"nonce": nonce}
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + intent_id_byte * 32,
        sender_pubkey=sender_pubkey,
        deadline=9999999999,
        fields=fields,
    )


def test_replay_semantics_accept_contiguous_batch_and_advance_last_nonce() -> None:
    sender = "0x" + "11" * 48
    nonces = NonceTable()
    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=nonces,
        intents=[
            _intent(sender_pubkey=sender, intent_id_byte="01", nonce=2),
            _intent(sender_pubkey=sender.upper().replace("0X", "0x"), intent_id_byte="02", nonce=1),
        ],
        require_all_nonces=True,
    )

    assert ok is True
    assert err is None
    assert updated is not None
    assert updated.get_last(sender) == 2


def test_replay_semantics_reject_duplicate_and_gap_nonces() -> None:
    sender = "0x" + "22" * 48
    nonces = NonceTable()

    ok_dup, err_dup, _ = validate_and_apply_intent_nonce_batch(
        nonces=nonces,
        intents=[
            _intent(sender_pubkey=sender, intent_id_byte="03", nonce=1),
            _intent(sender_pubkey=sender, intent_id_byte="04", nonce=1),
        ],
        require_all_nonces=True,
    )
    assert ok_dup is False
    assert err_dup == "duplicate nonce in batch"

    ok_gap, err_gap, _ = validate_and_apply_intent_nonce_batch(
        nonces=nonces,
        intents=[
            _intent(sender_pubkey=sender, intent_id_byte="05", nonce=1),
            _intent(sender_pubkey=sender, intent_id_byte="06", nonce=3),
        ],
        require_all_nonces=True,
    )
    assert ok_gap is False
    assert err_gap == "nonce sequence invalid"


def test_replay_semantics_reject_mixed_nonce_presence() -> None:
    sender = "0x" + "33" * 48
    nonces = NonceTable()

    ok, err, _ = validate_and_apply_intent_nonce_batch(
        nonces=nonces,
        intents=[
            _intent(sender_pubkey=sender, intent_id_byte="07", nonce=1),
            _intent(sender_pubkey=sender, intent_id_byte="08", nonce=None),
        ],
        require_all_nonces=False,
    )

    assert ok is False
    assert err == "nonce presence must be consistent across batch"


def test_replay_semantics_canonicalize_sender_pubkey_stream() -> None:
    sender = "0x" + "44" * 48
    sender_variant = "0x" + ("44" * 48).upper()
    nonces = NonceTable()

    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=nonces,
        intents=[_intent(sender_pubkey=sender_variant, intent_id_byte="09", nonce=1)],
        require_all_nonces=True,
    )

    assert ok is True
    assert err is None
    assert updated is not None
    assert updated.get_last(sender) == 1
    assert updated.get_last(sender_variant) == 1
