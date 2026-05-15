from __future__ import annotations

from dataclasses import dataclass

from ...integration.autotrader_signals import (
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
)


def signal_source_kind_code(value: SignalSourceKind) -> int:
    if not isinstance(value, SignalSourceKind):
        raise TypeError("value must be a SignalSourceKind")
    mapping = {
        SignalSourceKind.ROUTE_QUOTE_RECEIPT: 1,
        SignalSourceKind.LOCAL_PROTOCOL_STATE: 2,
        SignalSourceKind.ATTESTED_EXTERNAL: 3,
        SignalSourceKind.ADVISORY_EXTERNAL: 4,
    }
    return mapping[value]


def signal_trust_tier_code(value: SignalTrustTier) -> int:
    if not isinstance(value, SignalTrustTier):
        raise TypeError("value must be a SignalTrustTier")
    mapping = {
        SignalTrustTier.ADVISORY: 0,
        SignalTrustTier.ATTESTED: 1,
        SignalTrustTier.VERIFIED: 2,
        SignalTrustTier.PROTOCOL: 3,
    }
    return mapping[value]


@dataclass(frozen=True)
class StrategySignalProvenanceResult:
    ok: bool
    source_kind_ok: bool
    trust_tier_ok: bool
    quote_receipt_ok: bool
    auth_ok: bool
    binding_ok: bool
    source_available: bool
    error: str | None = None


def check_signal_provenance(
    *,
    packet: QuoteReceiptSignalPacket,
    require_quote_receipts: bool,
) -> StrategySignalProvenanceResult:
    if not isinstance(packet, QuoteReceiptSignalPacket):
        raise TypeError("packet must be a QuoteReceiptSignalPacket")
    if not isinstance(require_quote_receipts, bool):
        raise TypeError("require_quote_receipts must be a bool")

    source_kind_ok = packet.source_kind is SignalSourceKind.ROUTE_QUOTE_RECEIPT
    trust_tier_ok = packet.trust_tier in (SignalTrustTier.VERIFIED, SignalTrustTier.PROTOCOL)
    quote_receipt_ok = (
        (not require_quote_receipts)
        or (packet.quote_receipt_present and packet.quote_receipt_verified and packet.quote_epoch_present)
    )
    auth_ok = bool(packet.auth_ok)
    binding_ok = bool(packet.binding_ok)
    source_available = bool(packet.source_available)

    if not source_available:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=source_kind_ok,
            trust_tier_ok=trust_tier_ok,
            quote_receipt_ok=quote_receipt_ok,
            auth_ok=auth_ok,
            binding_ok=binding_ok,
            source_available=False,
            error="signal_source_unavailable",
        )
    if not auth_ok:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=source_kind_ok,
            trust_tier_ok=trust_tier_ok,
            quote_receipt_ok=quote_receipt_ok,
            auth_ok=False,
            binding_ok=binding_ok,
            source_available=True,
            error="signal_auth_invalid",
        )
    if not binding_ok:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=source_kind_ok,
            trust_tier_ok=trust_tier_ok,
            quote_receipt_ok=quote_receipt_ok,
            auth_ok=True,
            binding_ok=False,
            source_available=True,
            error="signal_binding_invalid",
        )
    if not source_kind_ok:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=False,
            trust_tier_ok=trust_tier_ok,
            quote_receipt_ok=quote_receipt_ok,
            auth_ok=True,
            binding_ok=True,
            source_available=True,
            error=f"signal_source_kind_unsupported:{packet.source_kind.value}",
        )
    if not trust_tier_ok:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=True,
            trust_tier_ok=False,
            quote_receipt_ok=quote_receipt_ok,
            auth_ok=True,
            binding_ok=True,
            source_available=True,
            error=f"signal_trust_tier_insufficient:{packet.trust_tier.value}",
        )
    if require_quote_receipts and not packet.quote_receipt_present:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=True,
            trust_tier_ok=True,
            quote_receipt_ok=False,
            auth_ok=True,
            binding_ok=True,
            source_available=True,
            error="signal_quote_receipt_missing",
        )
    if require_quote_receipts and not packet.quote_epoch_present:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=True,
            trust_tier_ok=True,
            quote_receipt_ok=False,
            auth_ok=True,
            binding_ok=True,
            source_available=True,
            error="signal_quote_epoch_missing",
        )
    if not quote_receipt_ok:
        return StrategySignalProvenanceResult(
            ok=False,
            source_kind_ok=True,
            trust_tier_ok=True,
            quote_receipt_ok=False,
            auth_ok=True,
            binding_ok=True,
            source_available=True,
            error="signal_quote_receipt_invalid",
        )
    return StrategySignalProvenanceResult(
        ok=True,
        source_kind_ok=True,
        trust_tier_ok=True,
        quote_receipt_ok=True,
        auth_ok=True,
        binding_ok=True,
        source_available=True,
    )
