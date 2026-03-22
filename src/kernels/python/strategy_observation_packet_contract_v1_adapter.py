from __future__ import annotations

from dataclasses import dataclass

from ...integration.autotrader_signals import (
    AutoTraderObservationPacket,
    SignalSourceKind,
    SignalTrustTier,
)


@dataclass(frozen=True)
class StrategyObservationPacketContractResult:
    ok: bool
    primary_mode_ok: bool
    trusted_primary_ok: bool
    primary_packet_ok: bool
    external_counts_ok: bool
    external_signal_count: int
    advisory_external_count: int
    trusted_external_count: int
    error: str | None = None


def _trusted_primary(packet: AutoTraderObservationPacket) -> bool:
    signal = packet.primary_signal
    if signal.source_kind is SignalSourceKind.ROUTE_QUOTE_RECEIPT:
        return signal.trust_tier in (SignalTrustTier.VERIFIED, SignalTrustTier.PROTOCOL)
    if signal.source_kind is SignalSourceKind.LOCAL_PROTOCOL_STATE:
        return signal.trust_tier is SignalTrustTier.PROTOCOL
    if signal.source_kind is SignalSourceKind.ATTESTED_EXTERNAL:
        return signal.trust_tier in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED)
    return False


def _advisory_primary(packet: AutoTraderObservationPacket) -> bool:
    signal = packet.primary_signal
    return (
        signal.source_kind is SignalSourceKind.ADVISORY_EXTERNAL
        and signal.trust_tier is SignalTrustTier.ADVISORY
    )


def _primary_packet_ok(packet: AutoTraderObservationPacket) -> bool:
    signal = packet.primary_signal
    return (
        signal.quote_receipt_present
        and signal.quote_receipt_verified
        and signal.quote_epoch_present
        and signal.source_available
        and signal.auth_ok
        and signal.binding_ok
    )


def _advisory_external_count(packet: AutoTraderObservationPacket) -> int:
    return sum(
        1
        for signal in packet.external_signals
        if signal.source_kind is SignalSourceKind.ADVISORY_EXTERNAL
        and signal.trust_tier is SignalTrustTier.ADVISORY
        and signal.advisory_only
    )


def _trusted_external_count(packet: AutoTraderObservationPacket) -> int:
    return sum(
        1
        for signal in packet.external_signals
        if signal.source_kind is SignalSourceKind.ATTESTED_EXTERNAL
        and signal.trust_tier in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED)
        and signal.auth_ok
        and signal.freshness_ok
        and not signal.advisory_only
    )


def check_strategy_observation_packet_contract(
    *,
    packet: AutoTraderObservationPacket,
) -> StrategyObservationPacketContractResult:
    if not isinstance(packet, AutoTraderObservationPacket):
        raise TypeError("packet must be an AutoTraderObservationPacket")

    external_signal_count = len(packet.external_signals)
    advisory_external_count = _advisory_external_count(packet)
    trusted_external_count = _trusted_external_count(packet)
    trusted_primary_ok = _trusted_primary(packet)
    advisory_primary_ok = _advisory_primary(packet)
    primary_mode_ok = trusted_primary_ok or advisory_primary_ok
    primary_packet_ok = _primary_packet_ok(packet)
    external_counts_ok = (
        advisory_external_count <= external_signal_count
        and trusted_external_count <= external_signal_count
        and advisory_external_count + trusted_external_count == external_signal_count
    )
    error: str | None = None
    if not primary_mode_ok:
        error = "primary_signal_mode_invalid"
    elif not primary_packet_ok:
        error = "primary_signal_invalid"
    elif not external_counts_ok:
        error = "external_signal_partition_invalid"

    return StrategyObservationPacketContractResult(
        ok=primary_mode_ok and primary_packet_ok and external_counts_ok,
        primary_mode_ok=primary_mode_ok,
        trusted_primary_ok=trusted_primary_ok,
        primary_packet_ok=primary_packet_ok,
        external_counts_ok=external_counts_ok,
        external_signal_count=external_signal_count,
        advisory_external_count=advisory_external_count,
        trusted_external_count=trusted_external_count,
        error=error,
    )
