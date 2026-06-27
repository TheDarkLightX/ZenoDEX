"""BVA tests for replay-protection nonces (`src/state/nonces.py`)."""

from __future__ import annotations

import pytest

import src.state.nonces as nonce_mod
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, copy_nonce_table, validate_and_apply_intent_nonce_batch

PK_48B = "0x" + "11" * 48


def _intent(*, sender: str = PK_48B, nonce: int | None) -> Intent:
    fields = {"pool_id": "0x" + "aa" * 32, "asset_in": "0x" + "01" * 32, "asset_out": "0x" + "02" * 32, "amount_in": 1, "min_amount_out": 0}
    if nonce is not None:
        fields["nonce"] = nonce
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "33" * 32,
        sender_pubkey=sender,
        deadline=1,
        fields=fields,
    )


class TestNonceTableBVA:
    def test_get_last_default_zero(self) -> None:
        t = NonceTable()
        assert t.get_last(PK_48B) == 0

    def test_set_last_canonicalizes_pubkey(self) -> None:
        t = NonceTable()
        pk_raw_upper_no0x = ("AA" * 48)  # raw hex, uppercase, no 0x
        pk_canon = "0x" + ("aa" * 48)

        t.set_last(pk_raw_upper_no0x, 7)
        assert t.get_last(pk_canon) == 7

    @pytest.mark.parametrize(
        "last_nonce,expect_ok,reason",
        [
            (-1, False, "just below min=0"),
            (0, True, "at min"),
            (1, True, "just above min"),
            (0xFFFFFFFF - 1, True, "just below max u32"),
            (0xFFFFFFFF, True, "at max u32"),
            (0xFFFFFFFF + 1, False, "just above max u32"),
            (True, False, "bool is not an int nonce"),
        ],
    )
    def test_set_last_nonce_bounds(self, last_nonce: int, expect_ok: bool, reason: str) -> None:
        t = NonceTable()
        if expect_ok:
            t.set_last(PK_48B, last_nonce)
            assert t.get_last(PK_48B) == int(last_nonce)
        else:
            with pytest.raises((TypeError, ValueError), match="nonce|u32|int|non-negative|pubkey"):
                t.set_last(PK_48B, last_nonce)

    @pytest.mark.parametrize(
        "pubkey,reason",
        [
            ("", "empty"),
            ("0x", "just prefix"),
            ("0x" + "11" * 47, "just below 48 bytes"),
            ("0x" + "11" * 49, "just above 48 bytes"),
            ("0x" + ("1g" * 48), "non-hex char"),
            (" " + PK_48B + " ", "whitespace around is accepted by canonicalizer"),
        ],
    )
    def test_pubkey_length_and_hex_validation(self, pubkey: str, reason: str) -> None:
        t = NonceTable()
        if reason.startswith("whitespace"):
            t.set_last(pubkey, 1)
            assert t.get_last(PK_48B) == 1
        else:
            with pytest.raises((TypeError, ValueError)):
                t.set_last(pubkey, 1)


def test_validate_and_apply_nonce_batch_rejects_mixed_nonce_presence_when_backward_compat_mode() -> None:
    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=NonceTable(),
        intents=[_intent(nonce=1), _intent(sender="0x" + "22" * 48, nonce=None)],
        require_all_nonces=False,
    )
    assert ok is False
    assert err == "nonce presence must be consistent across batch"
    assert updated is None


def test_validate_and_apply_nonce_batch_accepts_nonce_free_batch_in_backward_compat_mode() -> None:
    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=NonceTable(),
        intents=[_intent(nonce=None)],
        require_all_nonces=False,
    )
    assert ok is True
    assert err is None
    assert updated is not None


def test_nonce_table_rejects_invalid_stored_nonce_and_copy_canonicalizes() -> None:
    table = NonceTable()
    table._last[PK_48B] = True  # type: ignore[assignment]
    with pytest.raises(ValueError, match="invalid stored nonce"):
        table.get_last(PK_48B)

    src = NonceTable()
    src.set_last(PK_48B.upper().replace("0X", "0x"), 9)
    copied = copy_nonce_table(src)
    assert copied.get(PK_48B) == 9

    copied.apply_accept(PK_48B, 10)
    assert copied.get_last(PK_48B) == 10


@pytest.mark.parametrize("bad_nonce", [True, 0, -1, 0xFFFFFFFF + 1])
def test_validate_and_apply_nonce_batch_rejects_invalid_nonce_values(bad_nonce: int) -> None:
    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=NonceTable(),
        intents=[_intent(nonce=bad_nonce)],
        require_all_nonces=True,
    )
    assert ok is False
    assert err == "Missing/invalid nonce"
    assert updated is None


def test_validate_and_apply_nonce_batch_rejects_invalid_sender_pubkey() -> None:
    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=NonceTable(),
        intents=[_intent(sender="not-hex", nonce=1)],
        require_all_nonces=True,
    )
    assert ok is False
    assert err is not None
    assert "invalid sender_pubkey for nonce accounting" in err
    assert updated is None


def test_validate_and_apply_nonce_batch_propagates_nonce_parser_bug(monkeypatch: pytest.MonkeyPatch) -> None:
    def _programmer_error(*_args, **_kwargs):
        raise RuntimeError("unexpected nonce parser bug")

    monkeypatch.setattr(nonce_mod, "_require_int_u32_pos", _programmer_error)

    with pytest.raises(RuntimeError, match="unexpected nonce parser bug"):
        validate_and_apply_intent_nonce_batch(
            nonces=NonceTable(),
            intents=[_intent(nonce=1)],
            require_all_nonces=True,
        )


def test_validate_and_apply_nonce_batch_propagates_sender_canonicalizer_bug(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    intent = _intent(nonce=1)

    def _programmer_error(*_args, **_kwargs):
        raise RuntimeError("unexpected sender canonicalizer bug")

    monkeypatch.setattr(nonce_mod, "canonical_hex_fixed_allow_0x", _programmer_error)

    with pytest.raises(RuntimeError, match="unexpected sender canonicalizer bug"):
        validate_and_apply_intent_nonce_batch(
            nonces=NonceTable(),
            intents=[intent],
            require_all_nonces=True,
        )


def test_validate_and_apply_nonce_batch_returns_copy_for_empty_batch() -> None:
    table = NonceTable()
    table.set_last(PK_48B, 4)
    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=table,
        intents=[],
        require_all_nonces=True,
    )
    assert ok is True
    assert err is None
    assert updated is not None
    assert updated is not table
    assert updated.get_last(PK_48B) == 4
