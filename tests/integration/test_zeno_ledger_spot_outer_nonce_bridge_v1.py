"""Deterministic bridge from strict outer tx nonce to one runtime intent."""

from __future__ import annotations

from copy import deepcopy

import pytest

from src.integration.zeno_ledger_v0 import _normalize_dex_operations_for_apply_v0


def _intent(*, nonce: int | None = None) -> dict[str, object]:
    value: dict[str, object] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "11" * 32,
        "sender_pubkey": "0x" + "aa" * 48,
        "deadline": 1_999_999_999,
        "pool_id": "0x" + "22" * 32,
        "asset_in": "0x" + "33" * 32,
        "asset_out": "0x" + "44" * 32,
        "amount_in": 1,
        "min_amount_out": 0,
        "recipient": "0x" + "aa" * 48,
    }
    if nonce is not None:
        value["nonce"] = nonce
    return value


def test_single_strict_intent_inherits_outer_transaction_nonce_without_mutation() -> None:
    operations = {"2": [_intent()]}
    original = deepcopy(operations)

    normalized = _normalize_dex_operations_for_apply_v0(
        operations,
        outer_transaction_nonce=7,
    )

    assert normalized["2"][0]["nonce"] == 7
    assert operations == original


def test_existing_inner_nonce_must_equal_outer_transaction_nonce() -> None:
    with pytest.raises(ValueError, match="intent nonce does not match outer transaction nonce"):
        _normalize_dex_operations_for_apply_v0(
            {"2": [_intent(nonce=8)]},
            outer_transaction_nonce=7,
        )


def test_multiple_nonce_free_intents_reject_ambiguous_single_ingress_mapping() -> None:
    with pytest.raises(ValueError, match="multiple nonce-free intents"):
        _normalize_dex_operations_for_apply_v0(
            {"2": [_intent(), _intent()]},
            outer_transaction_nonce=7,
        )


@pytest.mark.parametrize("nonce", [True, 0, -1, 1 << 32])
def test_outer_transaction_nonce_must_be_positive_u32(nonce: object) -> None:
    with pytest.raises(ValueError, match="outer transaction nonce"):
        _normalize_dex_operations_for_apply_v0(
            {"2": [_intent()]},
            outer_transaction_nonce=nonce,
        )


def test_signed_pair_receives_nonce_inside_only_the_intent_payload() -> None:
    normalized = _normalize_dex_operations_for_apply_v0(
        {"2": [[_intent(), "0xsignature"]]},
        outer_transaction_nonce=7,
    )

    assert normalized["2"][0][0]["nonce"] == 7
    assert normalized["2"][0][1] == "0xsignature"
