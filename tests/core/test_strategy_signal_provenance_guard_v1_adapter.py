from __future__ import annotations

import pytest

from src.integration.autotrader_signals import (
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
)
from src.kernels.python.strategy_signal_provenance_guard_v1_adapter import (
    check_signal_provenance,
    signal_source_kind_code,
    signal_trust_tier_code,
)


def _packet(**overrides: object) -> QuoteReceiptSignalPacket:
    data = {
        "current_epoch": 5,
        "quote_epoch": 5,
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 100,
        "amount_out": 181,
        "receipt_hash": "hash.1",
        "source_id": "route_quote_receipt",
        "source_kind": SignalSourceKind.ROUTE_QUOTE_RECEIPT,
        "trust_tier": SignalTrustTier.VERIFIED,
        "quote_receipt_present": True,
        "quote_receipt_verified": True,
        "quote_epoch_present": True,
        "source_available": True,
        "auth_ok": True,
        "binding_ok": True,
    }
    data.update(overrides)
    return QuoteReceiptSignalPacket(**data)


def test_check_signal_provenance_accepts_verified_quote_packet() -> None:
    result = check_signal_provenance(packet=_packet(), require_quote_receipts=True)
    assert result.ok is True
    assert result.error is None


def test_check_signal_provenance_rejects_source_unavailable() -> None:
    result = check_signal_provenance(packet=_packet(source_available=False), require_quote_receipts=True)
    assert result.ok is False
    assert result.error == "signal_source_unavailable"


def test_check_signal_provenance_rejects_bad_auth_and_binding() -> None:
    auth = check_signal_provenance(packet=_packet(auth_ok=False), require_quote_receipts=True)
    assert auth.ok is False
    assert auth.error == "signal_auth_invalid"

    binding = check_signal_provenance(packet=_packet(binding_ok=False), require_quote_receipts=True)
    assert binding.ok is False
    assert binding.error == "signal_binding_invalid"


def test_check_signal_provenance_rejects_unsupported_source_kind_and_trust_tier() -> None:
    source_kind = check_signal_provenance(
        packet=_packet(source_kind=SignalSourceKind.ATTESTED_EXTERNAL),
        require_quote_receipts=True,
    )
    assert source_kind.ok is False
    assert source_kind.error == "signal_source_kind_unsupported:attested_external"

    trust = check_signal_provenance(
        packet=_packet(trust_tier=SignalTrustTier.ADVISORY),
        require_quote_receipts=True,
    )
    assert trust.ok is False
    assert trust.error == "signal_trust_tier_insufficient:advisory"


def test_check_signal_provenance_rejects_missing_receipt_fields() -> None:
    missing_receipt = check_signal_provenance(
        packet=_packet(quote_receipt_present=False),
        require_quote_receipts=True,
    )
    assert missing_receipt.ok is False
    assert missing_receipt.error == "signal_quote_receipt_missing"

    missing_epoch = check_signal_provenance(
        packet=_packet(quote_epoch_present=False),
        require_quote_receipts=True,
    )
    assert missing_epoch.ok is False
    assert missing_epoch.error == "signal_quote_epoch_missing"

    invalid_receipt = check_signal_provenance(
        packet=_packet(quote_receipt_verified=False),
        require_quote_receipts=True,
    )
    assert invalid_receipt.ok is False
    assert invalid_receipt.error == "signal_quote_receipt_invalid"


def test_check_signal_provenance_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="packet must be a QuoteReceiptSignalPacket"):
        check_signal_provenance(packet="bad", require_quote_receipts=True)
    with pytest.raises(TypeError, match="require_quote_receipts must be a bool"):
        check_signal_provenance(packet=_packet(), require_quote_receipts=1)


def test_signal_provenance_code_helpers_reject_bad_enum_types() -> None:
    assert signal_source_kind_code(SignalSourceKind.ROUTE_QUOTE_RECEIPT) == 1
    assert signal_source_kind_code(SignalSourceKind.LOCAL_PROTOCOL_STATE) == 2
    assert signal_source_kind_code(SignalSourceKind.ATTESTED_EXTERNAL) == 3
    assert signal_source_kind_code(SignalSourceKind.ADVISORY_EXTERNAL) == 4
    assert signal_trust_tier_code(SignalTrustTier.ADVISORY) == 0
    assert signal_trust_tier_code(SignalTrustTier.ATTESTED) == 1
    assert signal_trust_tier_code(SignalTrustTier.VERIFIED) == 2
    assert signal_trust_tier_code(SignalTrustTier.PROTOCOL) == 3
    with pytest.raises(TypeError, match="value must be a SignalSourceKind"):
        signal_source_kind_code("bad")
    with pytest.raises(TypeError, match="value must be a SignalTrustTier"):
        signal_trust_tier_code("bad")
