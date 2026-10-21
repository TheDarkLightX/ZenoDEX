"""C-1: consensus accept path must enforce canonical committed identifiers.

A signed swap with a non-canonical `recipient`, or a create-pool with non-hex
`asset0`/`asset1`, was admitted by the accept path (recipient validated only as a
non-empty string; create-pool validated only for ordering/non-emptiness) but the
resulting post-state is un-committable: `compute_state_root` decodes pubkeys via
`hex_to_bytes_fixed(nbytes=48)` and assets via `hex_to_bytes_fixed(nbytes=32)`
and raises on any non-canonical value (accept ⊄ committable).

`_require_canonical_committed_identifiers` closes the gap in the consensus posture
(gated on `require_intent_signatures` so the friendly-name dev/test regime is
untouched). These tests pin the guard and its consistency with the root encoder.
"""

from __future__ import annotations

import pytest

import src.integration.dex_engine as dex_engine
from src.core.dex import DexState
from src.integration.dex_engine import (
    DexEngineConfig,
    _require_canonical_committed_identifiers,
    apply_ops,
)
from src.integration.operations import SignedIntentEnvelope
from src.state import BalanceTable, LPTable
from src.state.canonical import hex_to_bytes_fixed
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable

_PK = "0x" + "11" * 48
_A0 = "0x" + "11" * 32
_A1 = "0x" + "22" * 32


def _swap(recipient: str) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "cc" * 32,
        sender_pubkey=_PK,
        deadline=10**12,
        fields={
            "pool_id": "0x" + "dd" * 32,
            "asset_in": _A0,
            "asset_out": _A1,
            "amount_in": 1000,
            "min_amount_out": 0,
            "recipient": recipient,
        },
    )


def _create_pool(asset0: str, asset1: str) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.CREATE_POOL,
        intent_id="0x" + "ee" * 32,
        sender_pubkey=_PK,
        deadline=10**12,
        fields={"asset0": asset0, "asset1": asset1, "fee_bps": 30, "amount0": 1000, "amount1": 1000},
    )


def test_rejects_non_canonical_recipient():
    assert _require_canonical_committed_identifiers([_swap("not_hex_recipient")]) == "non-canonical recipient"


def test_rejects_case_variant_recipient_that_root_would_dedup():
    # Mixed-case 0x is non-canonical for the root (which lowercases/decodes).
    assert _require_canonical_committed_identifiers([_swap("0x" + "AB" * 48)]) == "non-canonical recipient"


def test_accepts_canonical_recipient():
    assert _require_canonical_committed_identifiers([_swap("0x" + "22" * 48)]) is None


def _swap_from(sender: str) -> Intent:
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "cc" * 32,
        sender_pubkey=sender,
        deadline=10**12,
        fields={
            "pool_id": "0x" + "dd" * 32,
            "asset_in": _A0,
            "asset_out": _A1,
            "amount_in": 1000,
            "min_amount_out": 0,
            "recipient": "0x" + "22" * 48,
        },
    )


def test_rejects_non_canonical_sender_pubkey():
    # sender becomes a committed balance/LP key (swap default recipient, create-pool
    # creator LP); signature verification accepts mixed-case/raw, so it must be checked.
    assert _require_canonical_committed_identifiers([_swap_from("0x" + "AB" * 48)]) == "non-canonical sender_pubkey"
    assert _require_canonical_committed_identifiers([_swap_from("11" * 48)]) == "non-canonical sender_pubkey"


def test_accepts_canonical_sender_pubkey():
    assert _require_canonical_committed_identifiers([_swap_from("0x" + "11" * 48)]) is None


def test_recipient_default_absent_is_accepted():
    # No explicit recipient -> defaults to the (signature-constrained) sender; not flagged.
    intent = _swap("0x" + "22" * 48)
    intent.fields.pop("recipient")
    assert _require_canonical_committed_identifiers([intent]) is None


def test_rejects_non_canonical_pool_asset():
    assert _require_canonical_committed_identifiers([_create_pool(_A0, "zzz_not_hex_asset")]) == "non-canonical pool asset"


def test_accepts_canonical_pool_assets():
    assert _require_canonical_committed_identifiers([_create_pool(_A0, _A1)]) is None


def test_guard_is_consistent_with_root_encoder():
    # accept ⊆ committable: anything the guard accepts must decode under the exact
    # nbytes the root encoder uses; anything it rejects must be un-rootable.
    good_recipient = "0x" + "22" * 48
    assert _require_canonical_committed_identifiers([_swap(good_recipient)]) is None
    hex_to_bytes_fixed(good_recipient, nbytes=48, name="recipient")  # must not raise

    bad_recipient = "not_hex_recipient"
    assert _require_canonical_committed_identifiers([_swap(bad_recipient)]) == "non-canonical recipient"
    with pytest.raises(ValueError):
        hex_to_bytes_fixed(bad_recipient, nbytes=48, name="recipient")


def _patch_engine_until_identifier_gate(monkeypatch: pytest.MonkeyPatch, intent: Intent) -> None:
    monkeypatch.setattr(dex_engine, "parse_signed_intents", lambda operations: [SignedIntentEnvelope(intent=intent)])
    monkeypatch.setattr(dex_engine, "parse_settlement_envelope", lambda operations: None)
    monkeypatch.setattr(
        dex_engine,
        "_build_signing_payloads",
        lambda signed_intents, *, max_intent_bytes, max_total_intent_bytes: ([{}], [b"{}"]),
    )
    monkeypatch.setattr(dex_engine, "_verify_all_intent_signatures", lambda *args, **kwargs: (True, None))
    monkeypatch.setattr(dex_engine, "_validate_quote_receipt_witnesses", lambda **kwargs: (None, {}))
    monkeypatch.setattr(
        dex_engine,
        "compute_settlement",
        lambda **kwargs: (_ for _ in ()).throw(AssertionError("settlement compute must not run")),
    )


def test_apply_ops_rejects_non_canonical_sender_before_settlement(monkeypatch: pytest.MonkeyPatch):
    intent = _swap_from("0x" + "AB" * 48)
    intent.fields["nonce"] = 1
    _patch_engine_until_identifier_gate(monkeypatch, intent)

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=True),
        state=DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable(), nonces=NonceTable()),
        operations={"2": []},
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == "non-canonical sender_pubkey"


def test_apply_ops_preserves_nonce_reject_precedence_before_canonical_sender(monkeypatch: pytest.MonkeyPatch):
    intent = _swap_from("0x" + "AB" * 48)
    intent.fields["nonce"] = 1
    _patch_engine_until_identifier_gate(monkeypatch, intent)
    nonces = NonceTable()
    nonces.set_last("0x" + "ab" * 48, 1)

    res = apply_ops(
        config=DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=True),
        state=DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable(), nonces=nonces),
        operations={"2": []},
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == "nonce sequence invalid"
