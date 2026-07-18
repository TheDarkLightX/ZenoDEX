from __future__ import annotations

from dataclasses import FrozenInstanceError

import pytest

from src.integration.tau_native_identity import (
    TauChainKeyIndex,
    TauNativeBalanceSnapshot,
)

RAW = "11" * 48
CANONICAL = "0x" + RAW


@pytest.mark.parametrize("chain_key", [RAW, CANONICAL])
def test_identity_snapshot_normalizes_one_exact_tau_key(chain_key: str) -> None:
    source = {chain_key: 20}
    snapshot = TauNativeBalanceSnapshot.from_chain_balances(source)
    source[chain_key] = 999

    binding = snapshot.binding_for(
        CANONICAL,
        preferred_chain_key=RAW,
        name="test principal",
    )

    assert binding.canonical_pubkey == CANONICAL
    assert binding.chain_key == chain_key
    assert binding.balance == 20
    with pytest.raises(FrozenInstanceError):
        binding.balance = 0  # type: ignore[misc]


def test_identity_index_rejects_duplicate_normalization_class() -> None:
    with pytest.raises(ValueError, match="ambiguous identity spellings"):
        TauChainKeyIndex.from_chain_keys((RAW, CANONICAL))


@pytest.mark.parametrize(
    ("chain_balances", "error_type", "message"),
    [
        ({7: 20}, TypeError, "chain_balances key"),
        ({RAW: True}, TypeError, "must be an int"),
        ({RAW: -1}, ValueError, "must be non-negative"),
    ],
)
def test_identity_snapshot_rejects_malformed_boundary_values(
    chain_balances: dict[object, object],
    error_type: type[Exception],
    message: str,
) -> None:
    with pytest.raises(error_type, match=message):
        TauNativeBalanceSnapshot.from_chain_balances(chain_balances)


def test_identity_index_preserves_preferred_spelling_for_absent_principal() -> None:
    index = TauChainKeyIndex.from_chain_keys(())

    binding = index.binding_for(
        CANONICAL,
        preferred_chain_key=RAW,
        name="absent recipient",
    )

    assert binding.canonical_pubkey == CANONICAL
    assert binding.chain_key == RAW


def test_identity_index_rejects_mismatched_preferred_principal() -> None:
    index = TauChainKeyIndex.from_chain_keys(())

    with pytest.raises(ValueError, match="does not match canonical identity"):
        index.binding_for(
            CANONICAL,
            preferred_chain_key="22" * 48,
            name="absent recipient",
        )


def test_tau_dex_signed_intent_canonicalization_owns_its_copy() -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    intent = {
        "module": "TauSwap",
        "sender_pubkey": RAW,
        "recipient": RAW,
    }
    operations = {"5": [[intent, "signature"]]}

    selected = plugin._select_dex_ops(operations)

    canonical_intent = selected["2"][0][0]
    assert canonical_intent["sender_pubkey"] == CANONICAL
    assert canonical_intent["recipient"] == CANONICAL
    assert selected["2"][0][1] == "signature"
    assert intent["sender_pubkey"] == RAW
    assert intent["recipient"] == RAW


@pytest.mark.parametrize("field", ["sender_pubkey", "recipient"])
def test_tau_dex_intent_rejects_malformed_principal(field: str) -> None:
    from src.integration import tau_testnet_dex_plugin as plugin

    intent = {
        "module": "TauSwap",
        "sender_pubkey": RAW,
        "recipient": RAW,
    }
    intent[field] = "not-a-pubkey"

    with pytest.raises(ValueError, match=f"intent.{field}"):
        plugin._select_dex_ops({"5": [intent]})
