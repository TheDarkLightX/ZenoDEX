"""
Regression for S5-INFO-001 (D-KEY-001): the signed Tau tx payload (BLS signature
+ operation bodies — replay-capable authority material) must NOT appear in the
default API response. Both the perps wallet and zUSD tau wallet now redact it to
a hash / non-sensitive metadata unless an explicit env flag opts back in.

This is an exhaustive check over the sensitive fields: the signature must never
survive into the default response, for either surface.
"""
from __future__ import annotations

import json

import pytest

from src.integration import perps_wallet_api as pw
from src.integration import zusd_tau_wallet_api as zw

_SIG = "0x" + "ab" * 96
_PAYLOAD = {
    "sender_pubkey": "0x" + "11" * 48,
    "sequence_number": 5,
    "expiration_time": 1000,
    "fee_limit": 7,
    "operations": {"22": {"market_id": "m", "secret_op_body": "DO_NOT_LEAK"}},
    "signature": _SIG,
}


@pytest.mark.parametrize("flag", ["PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD"])
def test_perps_payload_redacted_by_default(monkeypatch, flag):
    monkeypatch.delenv(flag, raising=False)
    red = pw._redacted_tau_tx_payload(_PAYLOAD)
    blob = json.dumps(red)
    # The replay-capable signature and operation bodies must be gone.
    assert red.get("redacted") is True
    assert "signature" not in red and _SIG not in blob
    assert "operations" not in red and "DO_NOT_LEAK" not in blob
    # The response still exposes non-sensitive routing metadata.
    assert red["operation_streams"] == ["8"]
    assert red["sender_pubkey"] == _PAYLOAD["sender_pubkey"]
    assert "payload_hash" in red


def test_perps_payload_full_only_with_optin(monkeypatch):
    monkeypatch.setenv("PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD", "1")
    assert pw._redacted_tau_tx_payload(_PAYLOAD) == _PAYLOAD


def test_zusd_payload_redacted_by_default(monkeypatch):
    monkeypatch.delenv("ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD", raising=False)
    red = zw._redacted_tau_tx_payload(_PAYLOAD)
    blob = json.dumps(red)
    assert red.get("signature_redacted") is True
    assert "signature" not in red and _SIG not in blob
    assert red["operations"] == _PAYLOAD["operations"]  # operations preserved


def test_zusd_payload_full_only_with_optin(monkeypatch):
    monkeypatch.setenv("ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD", "1")
    assert zw._redacted_tau_tx_payload(_PAYLOAD) == _PAYLOAD


@pytest.mark.parametrize("fn", [lambda p: __import__("src.integration.perps_wallet_api", fromlist=["x"])._redacted_tau_tx_payload(p)])
def test_none_payload_is_none(fn):
    assert fn(None) is None
    assert zw._redacted_tau_tx_payload(None) is None
